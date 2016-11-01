/* -*- Mode: C; tab-width: 4; indent-tabs-mode: nil; c-basic-offset: 4 -*- */

#ifndef _CDC_H
#define _CDC_H

#include <glib.h>
#include <stdint.h>

#define BLOCK_SZ        (1024*1024*1)
#define BLOCK_MIN_SZ    (1024*256)
#define BLOCK_MAX_SZ    (1024*1024*4)
#define BLOCK_WIN_SZ    48

#define NAME_MAX_SZ     4096

#define BREAK_VALUE     0x0013    ///0x0513


#ifdef HAVE_MD5
#include "md5.h"
#define get_checksum md5
#define CHECKSUM_LENGTH 16
#else
#include <openssl/sha.h>
#define get_checksum sha1
#define CHECKSUM_LENGTH 20
#endif

#ifndef O_BINARY
#define O_BINARY 0
#endif

struct _CDCFileDescriptor;
struct _CDCDescriptor;
struct SeafileCrypt;

extern gint64 num_bytes_read_for_chunking;
extern gint64 time_spent_chunking;

typedef int (*WriteblockFunc)(const char *repo_id,
                              int version,
                              struct _CDCDescriptor *chunk_descr,
                              struct SeafileCrypt *crypt,
                              uint8_t *checksum,
                              gboolean write_data);

/* define chunk file header and block entry */
typedef struct _CDCFileDescriptor {
    uint32_t block_min_sz;
    uint32_t block_max_sz;
    uint32_t block_sz;
    uint64_t file_size;

    uint32_t block_nr;
    uint8_t *blk_sha1s;
    int max_block_nr;
    uint8_t  file_sum[CHECKSUM_LENGTH];

    WriteblockFunc write_block;

    char repo_id[37];
    int version;

    /* Add tracking of chunk offsets to ease incremental chunking. */
    uint64_t *blk_offsets;

    /* Add tracking of chunk livliness (whether they have been
       affected by a modification */
    uint8_t *live_chunk_list;
} CDCFileDescriptor;

typedef struct _CDCDescriptor {
    uint64_t offset;
    uint32_t len;
    uint8_t  checksum[CHECKSUM_LENGTH];
    char    *block_buf;
    int result;
} CDCDescriptor;

int file_chunk_cdc(int fd_src,
                   CDCFileDescriptor *file_descr,
                   struct SeafileCrypt *crypt,
                   uint64_t expected_size,
                   gboolean write_data);

int incremental_filename_chunk_cdc(const char *filename,
                       CDCFileDescriptor *file_descr,
                       struct SeafileCrypt *crypt,
                       uint64_t *offsets,
                       uint64_t chunk_offset,
                       char **existing_blocks,
                       int num_unchanged,
                       gboolean write_data);
int early_stop_filename_chunk_cdc(const char *filename,
                                  CDCFileDescriptor *file_descr,
                                  struct SeafileCrypt *crypt,
                                  uint64_t *offsets,
                                  uint64_t chunk_offset,
                                  char **existing_blocks,
                                  GArray *live_blocks,
                                  int num_unchanged,
                                  gboolean write_data,
                                  uint64_t num_chunks);

int filename_chunk_cdc(const char *filename,
                       CDCFileDescriptor *file_descr,
                       struct SeafileCrypt *crypt,
                       gboolean write_data);

void cdc_init ();

int init_cdc_file_descriptor (int fd,
                              uint64_t file_size,
                              CDCFileDescriptor *file_descr);

#endif
