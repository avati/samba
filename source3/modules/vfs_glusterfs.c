/*
   Unix SMB/CIFS implementation.

   Wrap GlusterFS GFAPI calls in vfs functions.

   Copyright (c) 2013 Anand Avati <avati@redhat.com>

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/

#include "includes.h"
#include "smbd/smbd.h"
#include <stdio.h>
#include <sys/acl.h>
#include "api/glfs.h"
#include "modules/vfs_posixacl.h"

#define DEFAULT_VOLFILE_SERVER "localhost"

/*
  TODO
  ----
  Short term:
  - AIO support
  - sendfile/recvfile support
  - vfs_gluster_sys_acl_get_file dynamic xattr size
*/

/* Helpers to provide 'integer' fds */

/* This is global. gfapi's FD operations do not
   require filesystem context.
*/

static glfs_fd_t **glfd_fd;
static int glfd_fd_size;
static int glfd_fd_used;

static int glfd_fd_store(glfs_fd_t *glfd)
{
	int i;
	void *tmp;

	if (glfd_fd_size == glfd_fd_used) {
		if (glfd_fd_size >= INT_MAX - 1) {
			errno = ENOMEM;
			return -1;
		}

		tmp = talloc_realloc(glfd_fd, glfd_fd, glfs_fd_t *,
				     glfd_fd_size + 1);
		if (!tmp) {
			errno = ENOMEM;
			return -1;
		}

		glfd_fd = tmp;
		glfd_fd[glfd_fd_size] = 0;
		glfd_fd_size++;
	}

	for (i = 0; i < glfd_fd_size; i++)
		if (!glfd_fd[i])
			break;
	glfd_fd_used++;
	glfd_fd[i] = glfd;
	return i;
}

static glfs_fd_t *glfd_fd_get(int i)
{
	if (i < 0 || i >= glfd_fd_size)
		return NULL;
	return glfd_fd[i];
}

static glfs_fd_t *glfd_fd_clear(int i)
{
	glfs_fd_t *glfd = NULL;

	if (i < 0 || i >= glfd_fd_size)
		return NULL;

	glfd = glfd_fd[i];

	glfd_fd[i] = 0;
	glfd_fd_used--;
	return glfd;
}

/* Helper to convert stat to stat_ex */

static void smb_stat_ex_from_stat(struct stat_ex *dst, const struct stat *src)
{
	ZERO_STRUCTP(dst);

	dst->st_ex_dev = src->st_dev;
	dst->st_ex_ino = src->st_ino;
	dst->st_ex_mode = src->st_mode;
	dst->st_ex_nlink = src->st_nlink;
	dst->st_ex_uid = src->st_uid;
	dst->st_ex_gid = src->st_gid;
	dst->st_ex_rdev = src->st_rdev;
	dst->st_ex_size = src->st_size;
	dst->st_ex_atime.tv_sec = src->st_atime;
#ifdef STAT_HAVE_NSEC
	dst->st_ex_atime.tv_nsec = src->st_atime_nsec;
#endif
	dst->st_ex_mtime.tv_sec = src->st_mtime;
#ifdef STAT_HAVE_NSEC
	dst->st_ex_mtime.tv_nsec = src->st_mtime_nsec;
#endif
	dst->st_ex_ctime.tv_sec = src->st_ctime;
#ifdef STAT_HAVE_NSEC
	dst->st_ex_ctime.tv_nsec = src->st_ctime_nsec;
#endif
	dst->st_ex_btime.tv_sec = src->st_mtime;
#ifdef STAT_HAVE_NSEC
	dst->st_ex_btime.tv_nsec = src->st_mtime_nsec;
#endif
	dst->st_ex_blksize = src->st_blksize;
	dst->st_ex_blocks = src->st_blocks;
}

/* pre-opened glfs_t */

static struct {
	char *volume;
	glfs_t *fs;
	int ref;
} *glfs_preopened;
static int glfs_preopened_size;
static int glfs_preopened_used;

int glfs_set_preopened(const char *volume, glfs_t *fs)
{
	int i;

	if (glfs_preopened_size == glfs_preopened_used) {
		void *tmp;

		if (glfs_preopened_size >= INT_MAX - 1) {
			errno = ENOMEM;
			return -1;
		}

		tmp = talloc_realloc(glfs_preopened, glfs_preopened,
				     typeof(*glfs_preopened),
				     (glfs_preopened_size + 1));
		if (!tmp) {
			errno = ENOMEM;
			return -1;
		}
		glfs_preopened = tmp;
		glfs_preopened[glfs_preopened_size].volume = 0;
		glfs_preopened_size++;
	}

	for (i = 0; i < glfs_preopened_size; i++)
		if (!glfs_preopened[i].volume)
			break;

	glfs_preopened[i].volume = talloc_strdup(NULL, volume);
	glfs_preopened[i].fs = fs;
	glfs_preopened[i].ref = 1;

	return i;
}

static glfs_t *glfs_find_preopened(const char *volume)
{
	int i;

	for (i = 0; i < glfs_preopened_size; i++) {
		if (glfs_preopened[i].volume &&
		    strcmp(glfs_preopened[i].volume, volume) == 0) {
			glfs_preopened[i].ref++;
			return glfs_preopened[i].fs;
		}
	}

	return NULL;
}

static void glfs_clear_preopened(glfs_t *fs)
{
	int i;

	for (i = 0; i < glfs_preopened_size; i++) {
		if (glfs_preopened[i].fs == fs) {
			if (--glfs_preopened[i].ref)
				return;

			talloc_free(glfs_preopened[i].volume);
			glfs_fini(glfs_preopened[i].fs);
			ZERO_STRUCTP(&glfs_preopened[i]);
			return;
		}
	}

	assert(!"filesystem context not found");
}

/* Disk Operations */

static int vfs_gluster_connect(struct vfs_handle_struct *handle,
			       const char *service,
			       const char *user)
{
	const char *volfile_server;
	const char *volume;
	const char *logfile;
	int loglevel;
	glfs_t *fs;
	int ret;

	logfile = lp_parm_const_string(SNUM(handle->conn), "glusterfs",
				       "logfile", NULL);

	loglevel = lp_parm_int(SNUM(handle->conn), "glusterfs", "loglevel", -1);

	volfile_server = lp_parm_const_string(SNUM(handle->conn), "glusterfs",
					       "volfile_server", NULL);
	if (!volfile_server)
		volfile_server = DEFAULT_VOLFILE_SERVER;

	volume = lp_parm_const_string(SNUM(handle->conn), "glusterfs", "volume",
				      NULL);
	if (!volume)
		volume = service;

	fs = glfs_find_preopened(volume);
	if (fs)
		goto found;

	fs = glfs_new(volume);
	if (!fs)
		return -1;

	ret = glfs_set_volfile_server(fs, "tcp", volfile_server, 0);
	if (ret) {
		glfs_fini(fs);
		return -1;
	}

	ret =
	    glfs_set_xlator_option(fs, "*-md-cache", "cache-posix-acl", "true");
	if (ret) {
		glfs_fini(fs);
		return -1;
	}

	ret = glfs_set_logging(fs, logfile, loglevel);
	if (ret) {
		glfs_fini(fs);
		return -1;
	}

	ret = glfs_init(fs);
	if (ret) {
		glfs_fini(fs);
		return -1;
	}

	ret = glfs_set_preopened(volume, fs);
	if (ret == -1) {
		glfs_fini(fs);
		return -1;
	}
found:
	handle->data = fs;
	return 0;
}

static void vfs_gluster_disconnect(struct vfs_handle_struct *handle)
{
	glfs_t *fs = NULL;

	fs = handle->data;

	glfs_clear_preopened(fs);
}

static uint64_t vfs_gluster_disk_free(struct vfs_handle_struct *handle,
				      const char *path, bool small_query,
				      uint64_t *bsize_p, uint64_t *dfree_p,
				      uint64_t *dsize_p)
{
	struct statvfs statvfs = { 0, };
	uint64_t dfree = 0;
	int ret;

	ret = glfs_statvfs(handle->data, path, &statvfs);
	if (ret)
		return -1;

	dfree = statvfs.f_bsize * statvfs.f_bavail;

	if (bsize_p)
		*bsize_p = statvfs.f_bsize;
	if (dfree_p)
		*dfree_p = dfree;
	if (dsize_p)
		*dsize_p = statvfs.f_bsize * statvfs.f_blocks;

	return dfree;
}

static int vfs_gluster_get_quota(struct vfs_handle_struct *handle,
				 enum SMB_QUOTA_TYPE qtype, unid_t id,
				 SMB_DISK_QUOTA *qt)
{
	errno = ENOSYS;
	return -1;
}

static int
vfs_gluster_set_quota(struct vfs_handle_struct *handle,
		      enum SMB_QUOTA_TYPE qtype, unid_t id, SMB_DISK_QUOTA *qt)
{
	errno = ENOSYS;
	return -1;
}

static int vfs_gluster_statvfs(struct vfs_handle_struct *handle,
			       const char *path,
			       struct vfs_statvfs_struct *vfs_statvfs)
{
	struct statvfs statvfs = { 0, };
	int ret;

	ret = glfs_statvfs(handle->data, path, &statvfs);
	if (ret)
		return -1;

	ZERO_STRUCTP(vfs_statvfs);

	vfs_statvfs->OptimalTransferSize = statvfs.f_frsize;
	vfs_statvfs->BlockSize = statvfs.f_bsize;
	vfs_statvfs->TotalBlocks = statvfs.f_blocks;
	vfs_statvfs->BlocksAvail = statvfs.f_bfree;
	vfs_statvfs->UserBlocksAvail = statvfs.f_bavail;
	vfs_statvfs->TotalFileNodes = statvfs.f_files;
	vfs_statvfs->FreeFileNodes = statvfs.f_ffree;
	vfs_statvfs->FsIdentifier = statvfs.f_fsid;
	vfs_statvfs->FsCapabilities =
	    FILE_CASE_SENSITIVE_SEARCH | FILE_CASE_PRESERVED_NAMES;

	return ret;
}

static uint32_t vfs_gluster_fs_capabilities(struct vfs_handle_struct *handle,
					    enum timestamp_set_resolution *p_ts_res)
{
	uint32_t caps = FILE_CASE_SENSITIVE_SEARCH | FILE_CASE_PRESERVED_NAMES;

#ifdef STAT_HAVE_NSEC
	*p_ts_res = TIMESTAMP_SET_NT_OR_BETTER;
#endif

	return caps;
}

static DIR *vfs_gluster_opendir(struct vfs_handle_struct *handle,
				const char *path, const char *mask,
				uint32 attributes)
{
	glfs_fd_t *fd;

	fd = glfs_opendir(handle->data, path);

	return (DIR *) fd;
}

static DIR *vfs_gluster_fdopendir(struct vfs_handle_struct *handle,
				  files_struct *fsp, const char *mask,
				  uint32 attributes)
{
	return (DIR *) glfd_fd_get(fsp->fh->fd);
}

static int vfs_gluster_closedir(struct vfs_handle_struct *handle, DIR *dirp)
{
	return glfs_closedir((void *)dirp);
}

static struct dirent *vfs_gluster_readdir(struct vfs_handle_struct *handle,
					  DIR *dirp, SMB_STRUCT_STAT *sbuf)
{
	static char direntbuf[512];
	int ret;
	struct stat stat;
	struct dirent *dirent = 0;

	if (sbuf)
		ret = glfs_readdirplus_r((void *)dirp, &stat, (void *)direntbuf,
					 &dirent);
	else
		ret = glfs_readdir_r((void *)dirp, (void *)direntbuf, &dirent);

	if (ret || !dirent)
		return NULL;

	if (sbuf)
		smb_stat_ex_from_stat(sbuf, &stat);

	return dirent;
}

static long vfs_gluster_telldir(struct vfs_handle_struct *handle, DIR *dirp)
{
	return glfs_telldir((void *)dirp);
}

static void vfs_gluster_seekdir(struct vfs_handle_struct *handle, DIR *dirp,
				long offset)
{
	glfs_seekdir((void *)dirp, offset);
}

static void vfs_gluster_rewinddir(struct vfs_handle_struct *handle, DIR *dirp)
{
	glfs_seekdir((void *)dirp, 0);
}

static void vfs_gluster_init_search_op(struct vfs_handle_struct *handle,
				       DIR *dirp)
{
	return;
}

static int vfs_gluster_mkdir(struct vfs_handle_struct *handle, const char *path,
			     mode_t mode)
{
	return glfs_mkdir(handle->data, path, mode);
}

static int vfs_gluster_rmdir(struct vfs_handle_struct *handle, const char *path)
{
	return glfs_rmdir(handle->data, path);
}

static int vfs_gluster_open(struct vfs_handle_struct *handle,
			    struct smb_filename *smb_fname, files_struct *fsp,
			    int flags, mode_t mode)
{
	glfs_fd_t *glfd;

	if (flags & O_DIRECTORY)
		glfd = glfs_opendir(handle->data, smb_fname->base_name);
	else if (flags & O_CREAT)
		glfd =
		    glfs_creat(handle->data, smb_fname->base_name, flags, mode);
	else
		glfd = glfs_open(handle->data, smb_fname->base_name, flags);

	if (!glfd)
		return -1;

	return glfd_fd_store(glfd);
}

static int vfs_gluster_close(struct vfs_handle_struct *handle,
			     files_struct *fsp)
{
	return glfs_close(glfd_fd_clear(fsp->fh->fd));
}

static ssize_t vfs_gluster_read(struct vfs_handle_struct *handle,
				files_struct *fsp, void *data, size_t n)
{
	return glfs_read(glfd_fd_get(fsp->fh->fd), data, n, 0);
}

static ssize_t vfs_gluster_pread(struct vfs_handle_struct *handle,
				 files_struct *fsp, void *data, size_t n,
				 off_t offset)
{
	return glfs_pread(glfd_fd_get(fsp->fh->fd), data, n, offset, 0);
}

static struct tevent_req *vfs_gluster_pread_send(struct vfs_handle_struct
						 *handle, TALLOC_CTX *mem_ctx,
						 struct tevent_context *ev,
						 files_struct *fsp, void *data,
						 size_t n, off_t offset)
{
	errno = ENOTSUP;
	return NULL;
}

static ssize_t vfs_gluster_pread_recv(struct tevent_req *req, int *err)
{
	errno = ENOTSUP;
	return -1;
}

static ssize_t vfs_gluster_write(struct vfs_handle_struct *handle,
				 files_struct *fsp, const void *data, size_t n)
{
	return glfs_write(glfd_fd_get(fsp->fh->fd), data, n, 0);
}

static ssize_t vfs_gluster_pwrite(struct vfs_handle_struct *handle,
				  files_struct *fsp, const void *data,
				  size_t n, off_t offset)
{
	return glfs_pwrite(glfd_fd_get(fsp->fh->fd), data, n, offset, 0);
}

static struct tevent_req *vfs_gluster_pwrite_send(struct vfs_handle_struct
						  *handle, TALLOC_CTX *mem_ctx,
						  struct tevent_context *ev,
						  files_struct *fsp,
						  const void *data, size_t n,
						  off_t offset)
{
	errno = ENOTSUP;
	return NULL;
}

static ssize_t vfs_gluster_pwrite_recv(struct tevent_req *req, int *err)
{
	errno = ENOTSUP;
	return -1;
}

static off_t vfs_gluster_lseek(struct vfs_handle_struct *handle,
			       files_struct *fsp, off_t offset, int whence)
{
	return glfs_lseek(glfd_fd_get(fsp->fh->fd), offset, whence);
}

static ssize_t vfs_gluster_sendfile(struct vfs_handle_struct *handle, int tofd,
				    files_struct *fromfsp,
				    const DATA_BLOB *hdr,
				    off_t offset, size_t n)
{
	errno = ENOTSUP;
	return -1;
}

static ssize_t vfs_gluster_recvfile(struct vfs_handle_struct *handle,
				    int fromfd, files_struct *tofsp,
				    off_t offset, size_t n)
{
	errno = ENOTSUP;
	return -1;
}

static int vfs_gluster_rename(struct vfs_handle_struct *handle,
			      const struct smb_filename *smb_fname_src,
			      const struct smb_filename *smb_fname_dst)
{
	return glfs_rename(handle->data, smb_fname_src->base_name,
			   smb_fname_dst->base_name);
}

static int vfs_gluster_fsync(struct vfs_handle_struct *handle,
			     files_struct *fsp)
{
	return glfs_fsync(glfd_fd_get(fsp->fh->fd));
}

static struct tevent_req *vfs_gluster_fsync_send(struct vfs_handle_struct
						 *handle, TALLOC_CTX *mem_ctx,
						 struct tevent_context *ev,
						 files_struct *fsp)
{
	errno = ENOTSUP;
	return NULL;
}

static int vfs_gluster_fsync_recv(struct tevent_req *req, int *err)
{
	errno = ENOTSUP;
	return -1;
}

static int vfs_gluster_stat(struct vfs_handle_struct *handle,
			    struct smb_filename *smb_fname)
{
	struct stat st;
	int ret;

	ret = glfs_stat(handle->data, smb_fname->base_name, &st);
	if (ret == 0)
		smb_stat_ex_from_stat(&smb_fname->st, &st);
	return ret;
}

static int vfs_gluster_fstat(struct vfs_handle_struct *handle,
			     files_struct *fsp, SMB_STRUCT_STAT *sbuf)
{
	struct stat st;
	int ret;

	ret = glfs_fstat(glfd_fd_get(fsp->fh->fd), &st);
	if (ret == 0)
		smb_stat_ex_from_stat(sbuf, &st);
	return ret;
}

static int vfs_gluster_lstat(struct vfs_handle_struct *handle,
			     struct smb_filename *smb_fname)
{
	struct stat st;
	int ret;

	ret = glfs_lstat(handle->data, smb_fname->base_name, &st);
	if (ret == 0)
		smb_stat_ex_from_stat(&smb_fname->st, &st);
	return ret;
}

static uint64_t vfs_gluster_get_alloc_size(struct vfs_handle_struct *handle,
					   files_struct *fsp,
					   const SMB_STRUCT_STAT *sbuf)
{
	return sbuf->st_ex_blocks * 512;
}

static int vfs_gluster_unlink(struct vfs_handle_struct *handle,
			      const struct smb_filename *smb_fname)
{
	return glfs_unlink(handle->data, smb_fname->base_name);
}

static int vfs_gluster_chmod(struct vfs_handle_struct *handle,
			     const char *path, mode_t mode)
{
	return glfs_chmod(handle->data, path, mode);
}

static int vfs_gluster_fchmod(struct vfs_handle_struct *handle,
			      files_struct *fsp, mode_t mode)
{
	return glfs_fchmod(glfd_fd_get(fsp->fh->fd), mode);
}

static int vfs_gluster_chown(struct vfs_handle_struct *handle,
			     const char *path, uid_t uid, gid_t gid)
{
	return glfs_chown(handle->data, path, uid, gid);
}

static int vfs_gluster_fchown(struct vfs_handle_struct *handle,
			      files_struct *fsp, uid_t uid, gid_t gid)
{
	return glfs_fchown(glfd_fd_get(fsp->fh->fd), uid, gid);
}

static int vfs_gluster_lchown(struct vfs_handle_struct *handle,
			      const char *path, uid_t uid, gid_t gid)
{
	return glfs_lchown(handle->data, path, uid, gid);
}

static int vfs_gluster_chdir(struct vfs_handle_struct *handle, const char *path)
{
	return glfs_chdir(handle->data, path);
}

static char *vfs_gluster_getwd(struct vfs_handle_struct *handle)
{
	char *cwd;
	char *ret;

	cwd = calloc(1, PATH_MAX + 1);
	if (!cwd)
		return NULL;

	ret = glfs_getcwd(handle->data, cwd, PATH_MAX);
	if (!ret)
		free(cwd);
	return ret;
}

static int vfs_gluster_ntimes(struct vfs_handle_struct *handle,
			      const struct smb_filename *smb_fname,
			      struct smb_file_time *ft)
{
	struct timespec times[2];

	times[0].tv_sec = ft->atime.tv_sec;
	times[0].tv_nsec = ft->atime.tv_nsec;
	times[1].tv_sec = ft->mtime.tv_sec;
	times[1].tv_nsec = ft->mtime.tv_nsec;

	return glfs_utimens(handle->data, smb_fname->base_name, times);
}

static int vfs_gluster_ftruncate(struct vfs_handle_struct *handle,
				 files_struct *fsp, off_t offset)
{
	return glfs_ftruncate(glfd_fd_get(fsp->fh->fd), offset);
}

static int vfs_gluster_fallocate(struct vfs_handle_struct *handle,
				 struct files_struct *fsp,
				 enum vfs_fallocate_mode mode,
				 off_t offset, off_t len)
{
	errno = ENOTSUP;
	return -1;
}

static char *vfs_gluster_realpath(struct vfs_handle_struct *handle,
				  const char *path)
{
	return glfs_realpath(handle->data, path, 0);
}

static bool vfs_gluster_lock(struct vfs_handle_struct *handle,
			     files_struct *fsp, int op, off_t offset,
			     off_t count, int type)
{
	struct flock flock = { 0, };
	int ret;

	flock.l_type = type;
	flock.l_whence = SEEK_SET;
	flock.l_start = offset;
	flock.l_len = count;
	flock.l_pid = 0;

	ret = glfs_posix_lock(glfd_fd_get(fsp->fh->fd), op, &flock);

	if (op == F_GETLK) {
		/* lock query, true if someone else has locked */
		if ((ret != -1) &&
		    (flock.l_type != F_UNLCK) &&
		    (flock.l_pid != 0) && (flock.l_pid != getpid()))
			return true;
		/* not me */
		return false;
	}

	if (ret == -1)
		return false;

	return true;
}

static int vfs_gluster_kernel_flock(struct vfs_handle_struct *handle,
				    files_struct *fsp, uint32 share_mode,
				    uint32_t access_mask)
{
	return 0;
}

static int vfs_gluster_linux_setlease(struct vfs_handle_struct *handle,
				      files_struct *fsp, int leasetype)
{
	errno = ENOSYS;
	return -1;
}

static bool vfs_gluster_getlock(struct vfs_handle_struct *handle,
				files_struct *fsp, off_t *poffset,
				off_t *pcount, int *ptype, pid_t *ppid)
{
	struct flock flock = { 0, };
	int ret;

	flock.l_type = *ptype;
	flock.l_whence = SEEK_SET;
	flock.l_start = *poffset;
	flock.l_len = *pcount;
	flock.l_pid = 0;

	ret = glfs_posix_lock(glfd_fd_get(fsp->fh->fd), F_GETLK, &flock);

	if (ret == -1)
		return false;

	*ptype = flock.l_type;
	*poffset = flock.l_start;
	*pcount = flock.l_len;
	*ppid = flock.l_pid;

	return true;
}

static int vfs_gluster_symlink(struct vfs_handle_struct *handle,
			       const char *oldpath, const char *newpath)
{
	return glfs_symlink(handle->data, oldpath, newpath);
}

static int vfs_gluster_readlink(struct vfs_handle_struct *handle,
				const char *path, char *buf, size_t bufsiz)
{
	return glfs_readlink(handle->data, path, buf, bufsiz);
}

static int vfs_gluster_link(struct vfs_handle_struct *handle,
			    const char *oldpath, const char *newpath)
{
	return glfs_link(handle->data, oldpath, newpath);
}

static int vfs_gluster_mknod(struct vfs_handle_struct *handle, const char *path,
			     mode_t mode, SMB_DEV_T dev)
{
	return glfs_mknod(handle->data, path, mode, dev);
}

static NTSTATUS vfs_gluster_notify_watch(struct vfs_handle_struct *handle,
					 struct sys_notify_context *ctx,
					 const char *path, uint32_t *filter,
					 uint32_t *subdir_filter,
					 void (*callback) (struct sys_notify_context *ctx,
							   void *private_data,
							   struct notify_event *ev),
					 void *private_data, void *handle_p)
{
	return NT_STATUS_OK;
}

static int vfs_gluster_chflags(struct vfs_handle_struct *handle,
			       const char *path, unsigned int flags)
{
	errno = ENOSYS;
	return -1;
}

static int vfs_gluster_get_real_filename(struct vfs_handle_struct *handle,
					 const char *path, const char *name,
					 TALLOC_CTX *mem_ctx, char **found_name)
{
	int ret;
	char key_buf[NAME_MAX + 64];
	char val_buf[NAME_MAX + 1];

	if (strlen(name) >= NAME_MAX) {
		errno = ENAMETOOLONG;
		return -1;
	}

	snprintf(key_buf, NAME_MAX + 64,
		 "trusted.glusterfs.get_real_filename:%s", name);

	ret = glfs_getxattr(handle->data, path, key_buf, val_buf, NAME_MAX + 1);
	if (ret == -1 && errno == ENODATA) {
		errno = EOPNOTSUPP;
		return -1;
	}

	*found_name = talloc_strdup(mem_ctx, val_buf);
	if (!*found_name) {
		errno = ENOMEM;
		return -1;
	}
	return 0;
}

static const char *vfs_gluster_connectpath(struct vfs_handle_struct *handle,
					   const char *filename)
{
	return handle->conn->connectpath;
}

/* EA Operations */

static ssize_t vfs_gluster_getxattr(struct vfs_handle_struct *handle,
				    const char *path, const char *name,
				    void *value, size_t size)
{
	return glfs_getxattr(handle->data, path, name, value, size);
}

static ssize_t vfs_gluster_fgetxattr(struct vfs_handle_struct *handle,
				     files_struct *fsp, const char *name,
				     void *value, size_t size)
{
	return glfs_fgetxattr(glfd_fd_get(fsp->fh->fd), name, value, size);
}

static ssize_t vfs_gluster_listxattr(struct vfs_handle_struct *handle,
				     const char *path, char *list, size_t size)
{
	return glfs_listxattr(handle->data, path, list, size);
}

static ssize_t vfs_gluster_flistxattr(struct vfs_handle_struct *handle,
				      files_struct *fsp, char *list,
				      size_t size)
{
	return glfs_flistxattr(glfd_fd_get(fsp->fh->fd), list, size);
}

static int vfs_gluster_removexattr(struct vfs_handle_struct *handle,
				   const char *path, const char *name)
{
	return glfs_removexattr(handle->data, path, name);
}

static int vfs_gluster_fremovexattr(struct vfs_handle_struct *handle,
				    files_struct *fsp, const char *name)
{
	return glfs_fremovexattr(glfd_fd_get(fsp->fh->fd), name);
}

static int vfs_gluster_setxattr(struct vfs_handle_struct *handle,
				const char *path, const char *name,
				const void *value, size_t size, int flags)
{
	return glfs_setxattr(handle->data, path, name, value, size, flags);
}

static int vfs_gluster_fsetxattr(struct vfs_handle_struct *handle,
				 files_struct *fsp, const char *name,
				 const void *value, size_t size, int flags)
{
	return glfs_fsetxattr(glfd_fd_get(fsp->fh->fd), name, value, size,
			      flags);
}

/* AIO Operations */

static bool vfs_gluster_aio_force(struct vfs_handle_struct *handle,
				  files_struct *fsp)
{
	return false;
}

/* Offline Operations */

static bool vfs_gluster_is_offline(struct vfs_handle_struct *handle,
				   const struct smb_filename *fname,
				   SMB_STRUCT_STAT *sbuf)
{
	return false;
}

static int vfs_gluster_set_offline(struct vfs_handle_struct *handle,
				   const struct smb_filename *fname)
{
	errno = ENOTSUP;
	return -1;
}

/* Posix ACL Operations */

static SMB_ACL_T vfs_gluster_sys_acl_get_file(struct vfs_handle_struct *handle,
					      const char *path_p,
					      SMB_ACL_TYPE_T type,
					      TALLOC_CTX *mem_ctx)
{
	struct smb_acl_t *result;
	acl_t acl;
	char *buf;
	char *key;
	ssize_t ret;

	switch (type) {
	case SMB_ACL_TYPE_ACCESS:
		key = "system.posix_acl_access";
		break;
	case SMB_ACL_TYPE_DEFAULT:
		key = "system.posix_acl_default";
		break;
	default:
		errno = EINVAL;
		return NULL;
	}

	ret = glfs_getxattr(handle->data, path_p, key, 0, 0);
	if (ret <= 0)
		return NULL;

	buf = alloca(ret);
	ret = glfs_getxattr(handle->data, path_p, key, buf, ret);
	if (ret <= 0)
		return NULL;

	acl = acl_copy_int(buf);

	if (!acl)
		return NULL;

	result = smb_acl_to_internal(acl, mem_ctx);
	acl_free(acl);
	return result;
}

static SMB_ACL_T vfs_gluster_sys_acl_get_fd(struct vfs_handle_struct *handle,
					    struct files_struct *fsp,
					    TALLOC_CTX *mem_ctx)
{
	struct smb_acl_t *result;
	acl_t acl;
	int ret;
	char *buf;

	ret = glfs_fgetxattr(glfd_fd_get(fsp->fh->fd),
			     "system.posix_acl_access", 0, 0);
	if (ret <= 0)
		return NULL;

	buf = alloca(ret);
	ret = glfs_fgetxattr(glfd_fd_get(fsp->fh->fd),
			     "system.posix_acl_access", buf, ret);
	if (ret <= 0)
		return NULL;

	acl = acl_copy_int(buf);
	if (!acl)
		return NULL;

	result = smb_acl_to_internal(acl, mem_ctx);
	acl_free(acl);
	return result;
}

static int vfs_gluster_sys_acl_set_file(struct vfs_handle_struct *handle,
					const char *name,
					SMB_ACL_TYPE_T acltype,
					SMB_ACL_T theacl)
{
	int ret;
	char *key;
	char *buf;
	acl_t acl;
	ssize_t size;

	switch (acltype) {
	case SMB_ACL_TYPE_ACCESS:
		key = "system.posix_acl_access";
		break;
	case SMB_ACL_TYPE_DEFAULT:
		key = "system.posix_acl_default";
		break;
	default:
		errno = EINVAL;
		return -1;
	}

	acl = smb_acl_to_posix(theacl);
	if (!acl)
		return -1;
	size = acl_size(acl);
	buf = alloca(size);

	size = acl_copy_ext(buf, acl, size);
	if (size == -1)
		return -1;

	ret = glfs_setxattr(handle->data, name, key, buf, size, 0);

	acl_free(acl);

	return ret;
}

static int vfs_gluster_sys_acl_set_fd(struct vfs_handle_struct *handle,
				      struct files_struct *fsp,
				      SMB_ACL_T theacl)
{
	int ret;
	char *key;
	char *buf;
	acl_t acl;
	ssize_t size;

	acl = smb_acl_to_posix(theacl);
	if (!acl)
		return -1;

	size = acl_size(acl);
	buf = alloca(size);

	size = acl_copy_ext(buf, acl, size);
	if (size == -1)
		return -1;

	ret = glfs_fsetxattr(glfd_fd_get(fsp->fh->fd),
			     "system.posix_acl_access", buf, size, 0);
	acl_free(acl);

	return ret;
}

static int vfs_gluster_sys_acl_delete_def_file(struct vfs_handle_struct *handle,
					       const char *path)
{
	return glfs_removexattr(handle->data, path, "system.posix_acl_default");
}

static struct vfs_fn_pointers glusterfs_fns = {

	/* Disk Operations */

	.connect_fn = vfs_gluster_connect,
	.disconnect_fn = vfs_gluster_disconnect,
	.disk_free_fn = vfs_gluster_disk_free,
	.get_quota_fn = vfs_gluster_get_quota,
	.set_quota_fn = vfs_gluster_set_quota,
	.statvfs_fn = vfs_gluster_statvfs,
	.fs_capabilities_fn = vfs_gluster_fs_capabilities,

	.get_dfs_referrals_fn = NULL,

	/* Directory Operations */

	.opendir_fn = vfs_gluster_opendir,
	.fdopendir_fn = vfs_gluster_fdopendir,
	.readdir_fn = vfs_gluster_readdir,
	.seekdir_fn = vfs_gluster_seekdir,
	.telldir_fn = vfs_gluster_telldir,
	.rewind_dir_fn = vfs_gluster_rewinddir,
	.mkdir_fn = vfs_gluster_mkdir,
	.rmdir_fn = vfs_gluster_rmdir,
	.closedir_fn = vfs_gluster_closedir,
	.init_search_op_fn = vfs_gluster_init_search_op,

	/* File Operations */

	.open_fn = vfs_gluster_open,
	.create_file_fn = NULL,
	.close_fn = vfs_gluster_close,
	.read_fn = vfs_gluster_read,
	.pread_fn = vfs_gluster_pread,
	.pread_send_fn = vfs_gluster_pread_send,
	.pread_recv_fn = vfs_gluster_pread_recv,
	.write_fn = vfs_gluster_write,
	.pwrite_fn = vfs_gluster_pwrite,
	.pwrite_send_fn = vfs_gluster_pwrite_send,
	.pwrite_recv_fn = vfs_gluster_pwrite_recv,
	.lseek_fn = vfs_gluster_lseek,
	.sendfile_fn = vfs_gluster_sendfile,
	.recvfile_fn = vfs_gluster_recvfile,
	.rename_fn = vfs_gluster_rename,
	.fsync_fn = vfs_gluster_fsync,
	.fsync_send_fn = vfs_gluster_fsync_send,
	.fsync_recv_fn = vfs_gluster_fsync_recv,

	.stat_fn = vfs_gluster_stat,
	.fstat_fn = vfs_gluster_fstat,
	.lstat_fn = vfs_gluster_lstat,
	.get_alloc_size_fn = vfs_gluster_get_alloc_size,
	.unlink_fn = vfs_gluster_unlink,

	.chmod_fn = vfs_gluster_chmod,
	.fchmod_fn = vfs_gluster_fchmod,
	.chown_fn = vfs_gluster_chown,
	.fchown_fn = vfs_gluster_fchown,
	.lchown_fn = vfs_gluster_lchown,
	.chdir_fn = vfs_gluster_chdir,
	.getwd_fn = vfs_gluster_getwd,
	.ntimes_fn = vfs_gluster_ntimes,
	.ftruncate_fn = vfs_gluster_ftruncate,
	.fallocate_fn = vfs_gluster_fallocate,
	.lock_fn = vfs_gluster_lock,
	.kernel_flock_fn = vfs_gluster_kernel_flock,
	.linux_setlease_fn = vfs_gluster_linux_setlease,
	.getlock_fn = vfs_gluster_getlock,
	.symlink_fn = vfs_gluster_symlink,
	.readlink_fn = vfs_gluster_readlink,
	.link_fn = vfs_gluster_link,
	.mknod_fn = vfs_gluster_mknod,
	.realpath_fn = vfs_gluster_realpath,
	.notify_watch_fn = vfs_gluster_notify_watch,
	.chflags_fn = vfs_gluster_chflags,
	.file_id_create_fn = NULL,
	.copy_chunk_send_fn = NULL,
	.copy_chunk_recv_fn = NULL,
	.streaminfo_fn = NULL,
	.get_real_filename_fn = vfs_gluster_get_real_filename,
	.connectpath_fn = vfs_gluster_connectpath,

	.brl_lock_windows_fn = NULL,
	.brl_unlock_windows_fn = NULL,
	.brl_cancel_windows_fn = NULL,
	.strict_lock_fn = NULL,
	.strict_unlock_fn = NULL,
	.translate_name_fn = NULL,
	.fsctl_fn = NULL,

	/* NT ACL Operations */
	.fget_nt_acl_fn = NULL,
	.get_nt_acl_fn = NULL,
	.fset_nt_acl_fn = NULL,
	.audit_file_fn = NULL,

	/* Posix ACL Operations */
	.chmod_acl_fn = NULL,	/* passthrough to default */
	.fchmod_acl_fn = NULL,	/* passthrough to default */
	.sys_acl_get_file_fn = vfs_gluster_sys_acl_get_file,
	.sys_acl_get_fd_fn = vfs_gluster_sys_acl_get_fd,
	.sys_acl_blob_get_file_fn = posix_sys_acl_blob_get_file,
	.sys_acl_blob_get_fd_fn = posix_sys_acl_blob_get_fd,
	.sys_acl_set_file_fn = vfs_gluster_sys_acl_set_file,
	.sys_acl_set_fd_fn = vfs_gluster_sys_acl_set_fd,
	.sys_acl_delete_def_file_fn = vfs_gluster_sys_acl_delete_def_file,

	/* EA Operations */
	.getxattr_fn = vfs_gluster_getxattr,
	.fgetxattr_fn = vfs_gluster_fgetxattr,
	.listxattr_fn = vfs_gluster_listxattr,
	.flistxattr_fn = vfs_gluster_flistxattr,
	.removexattr_fn = vfs_gluster_removexattr,
	.fremovexattr_fn = vfs_gluster_fremovexattr,
	.setxattr_fn = vfs_gluster_setxattr,
	.fsetxattr_fn = vfs_gluster_fsetxattr,

	/* AIO Operations */
	.aio_force_fn = vfs_gluster_aio_force,

	/* Offline Operations */
	.is_offline_fn = vfs_gluster_is_offline,
	.set_offline_fn = vfs_gluster_set_offline,

	/* Durable handle Operations */
	.durable_cookie_fn = NULL,
	.durable_disconnect_fn = NULL,
	.durable_reconnect_fn = NULL,
};

NTSTATUS vfs_glusterfs_init(void);
NTSTATUS vfs_glusterfs_init(void)
{
	return smb_register_vfs(SMB_VFS_INTERFACE_VERSION,
				"glusterfs", &glusterfs_fns);
}
