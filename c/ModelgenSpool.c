#include <lean/lean.h>

#include <errno.h>
#include <limits.h>
#include <stdint.h>
#include <stdio.h>

#if defined(_WIN32)
#include <io.h>
#else
#include <fcntl.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>
#endif

static lean_obj_res modelgen_io_error(int error, b_lean_obj_arg path) {
    return lean_io_result_mk_error(lean_decode_io_error(error, path));
}

lean_obj_res modelgen_spool_seek(b_lean_obj_arg handle, uint64_t offset) {
    if (offset > INT64_MAX) {
        return modelgen_io_error(EINVAL, NULL);
    }
    FILE *file = (FILE *)lean_get_external_data(handle);
    int result;
#if defined(_WIN32)
    result = _fseeki64(file, (__int64)offset, SEEK_SET);
#else
    if (sizeof(off_t) < sizeof(int64_t)) {
        return modelgen_io_error(ENOSYS, NULL);
    }
    result = fseeko(file, (off_t)offset, SEEK_SET);
#endif
    if (result != 0) {
        return modelgen_io_error(errno, NULL);
    }
    return lean_io_result_mk_ok(lean_box(0));
}

/*
 * The production workspace boundary is deliberately Linux-only for now.  It
 * validates an existing trusted parent and creates the child with mode 0700
 * atomically; unsupported platforms fail closed in Lean before this symbol is
 * called.
 */
lean_obj_res modelgen_spool_mkdir_private_at(
        b_lean_obj_arg parent_path, b_lean_obj_arg leaf_name) {
#if defined(__linux__)
    char const *parent = lean_string_cstr(parent_path);
    char const *leaf = lean_string_cstr(leaf_name);
    int parent_fd = open(parent, O_RDONLY | O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC);
    if (parent_fd < 0) {
        return modelgen_io_error(errno, parent_path);
    }
    struct stat status;
    if (fstat(parent_fd, &status) != 0) {
        int error = errno;
        close(parent_fd);
        return modelgen_io_error(error, parent_path);
    }
    if (status.st_uid != geteuid() || (status.st_mode & (S_IWGRP | S_IWOTH)) != 0) {
        close(parent_fd);
        return modelgen_io_error(EACCES, parent_path);
    }
    if (mkdirat(parent_fd, leaf, S_IRWXU) != 0) {
        int error = errno;
        close(parent_fd);
        return modelgen_io_error(error, leaf_name);
    }
    close(parent_fd);
    return lean_io_result_mk_ok(lean_box(0));
#else
    (void)parent_path;
    (void)leaf_name;
    return modelgen_io_error(ENOSYS, NULL);
#endif
}
