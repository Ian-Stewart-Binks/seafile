/* -*- Mode: C; tab-width: 4; indent-tabs-mode: nil; c-basic-offset: 4 -*- */

#include "common.h"

#include "log.h"

#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>
#include <fcntl.h>
#include <string.h>
#include <sys/stat.h>
#include <errno.h>
#include <glib/gstdio.h>
#include <glib.h>

#include "utils.h"

#include "cdc.h"
#include "../seafile-crypt.h"

#include "rabin-checksum.h"
#define finger rabin_checksum
#define rolling_finger rabin_rolling_checksum

#define READ_SIZE 1024 * 4

#define BYTE_TO_HEX(b)  (((b)>=10)?('a'+b-10):('0'+b))

gint64 num_bytes_read_for_chunking;
gint64 time_spent_chunking;

static void print_live_block_list(char *path, GArray *array) {
  int i;
  uint64_t elem;
  for (i = 0; i < array->len; i++) {
    elem = g_array_index(array, uint64_t, i);
    seaf_warning("CDC-EARLY: live list: %d\n", elem);
  }
}


static int default_write_chunk (CDCDescriptor *chunk_descr)
{
    char filename[NAME_MAX_SZ];
    char chksum_str[CHECKSUM_LENGTH *2 + 1];
    int fd_chunk, ret;

    memset(chksum_str, 0, sizeof(chksum_str));
    rawdata_to_hex (chunk_descr->checksum, chksum_str, CHECKSUM_LENGTH);
    snprintf (filename, NAME_MAX_SZ, "./%s", chksum_str);
    fd_chunk = g_open (filename, O_RDWR | O_CREAT | O_BINARY, 0644);
    seaf_warning("CDC: Wrote to file with name %s\n", filename);
    if (fd_chunk < 0)
        return -1;    
    
    ret = writen (fd_chunk, chunk_descr->block_buf, chunk_descr->len);
    close (fd_chunk);
    return ret;
}

int init_cdc_file_descriptor (int fd,
                              uint64_t file_size,
                              CDCFileDescriptor *file_descr)
{
    int max_block_nr = 0;
    int block_min_sz = 0;

    file_descr->block_nr = 0;

    if (file_descr->block_min_sz <= 0)
        file_descr->block_min_sz = BLOCK_MIN_SZ;
    if (file_descr->block_max_sz <= 0)
        file_descr->block_max_sz = BLOCK_MAX_SZ;
    if (file_descr->block_sz <= 0)
        file_descr->block_sz = BLOCK_SZ;

    if (file_descr->write_block == NULL)
        file_descr->write_block = (WriteblockFunc)default_write_chunk;

    block_min_sz = file_descr->block_min_sz;
    max_block_nr = ((file_size + block_min_sz - 1) / block_min_sz);
    file_descr->blk_sha1s = (uint8_t *)calloc (sizeof(uint8_t),
                                               max_block_nr * CHECKSUM_LENGTH);

    /* Allocate space for the chunk offsets. */
    file_descr->blk_offsets = (uint64_t *)calloc (sizeof(uint64_t), max_block_nr);
    
    /* Allocate space for live chunks based on corresponding offset, calloc ensures that no
       chunk is initially considered live
       */
    file_descr->live_chunk_list = (uint8_t *)calloc (sizeof(uint8_t), max_block_nr);
    file_descr->max_block_nr = max_block_nr;

    return 0;
}

#define WRITE_CDC_BLOCK(block_sz, write_data)                \
do {                                                         \
    int _block_sz = (block_sz);                              \
    chunk_descr.len = _block_sz;                             \
    chunk_descr.offset = offset;                             \
    ret = file_descr->write_block (file_descr->repo_id,      \
                                   file_descr->version,      \
                                   &chunk_descr,             \
            crypt, chunk_descr.checksum,                     \
                                   (write_data));            \
    if (ret < 0) {                                           \
        free (buf);                                          \
        g_warning ("CDC: failed to write chunk.\n");         \
        return -1;                                           \
    }                                                        \
    memcpy (file_descr->blk_sha1s +                          \
            file_descr->block_nr * CHECKSUM_LENGTH,          \
            chunk_descr.checksum, CHECKSUM_LENGTH);          \
    file_descr->blk_offsets[file_descr->block_nr] = offset;  \
    SHA1_Update (&file_ctx, chunk_descr.checksum, 20);       \
    file_descr->block_nr++;                                  \
    offset += _block_sz;                                     \
                                                             \
    memmove (buf, buf + _block_sz, tail - _block_sz);        \
    tail = tail - _block_sz;                                 \
    cur = 0;                                                 \
}while(0);

/* content-defined chunking */
int file_chunk_cdc(int fd_src,
                   CDCFileDescriptor *file_descr,
                   SeafileCrypt *crypt,
                   uint64_t expected_size,
                   gboolean write_data)
{
    char *buf;
    uint32_t buf_sz;
    SHA_CTX file_ctx;
    CDCDescriptor chunk_descr;
    int i;
    SHA1_Init (&file_ctx);

    gint64 tick;
    tick = g_get_monotonic_time();
    seaf_warning("About to chunk\n");
    // Get the running SHA1 from preexisting blocks.
    for (i = 0; i < file_descr->block_nr; i++) {
        SHA1_Update(&file_ctx, file_descr->blk_sha1s + i * CHECKSUM_LENGTH, 20);
    }

    uint32_t block_min_sz = file_descr->block_min_sz;
    uint32_t block_mask = file_descr->block_sz - 1;

    int fingerprint = 0;
    int offset = 0;
    int ret = 0;
    int tail, cur, rsize;

    if (file_descr->block_nr != 0) {
        offset = file_descr->blk_offsets[file_descr->block_nr - 1];
    }

    buf_sz = file_descr->block_max_sz;
    buf = chunk_descr.block_buf = malloc (buf_sz);
    if (!buf)
        return -1;

    /* buf: a fix-sized buffer.
     * cur: data behind (inclusive) this offset has been scanned.
     *      cur + 1 is the bytes that has been scanned.
     * tail: length of data loaded into memory. buf[tail] is invalid.
     */
    tail = cur = 0;
    while (1) {
        if (tail < block_min_sz) {
            rsize = block_min_sz - tail + READ_SIZE;
        } else {
            rsize = (buf_sz - tail < READ_SIZE) ? (buf_sz - tail) : READ_SIZE;
        }
        ret = readn (fd_src, buf + tail, rsize);
        if (ret < 0) {
            seaf_warning ("CDC: failed to read: %s.\n", strerror(errno));
            free (buf);
            return -1;
        }
        tail += ret;
        file_descr->file_size += ret;
        num_bytes_read_for_chunking += ret;

        if (file_descr->file_size > expected_size) {
            seaf_warning ("File size changed while chunking.\n");
            free (buf);
            return -1;
        }

        /* We've read all the data in this file. Output the block immediately
         * in two cases:
         * 1. The data left in the file is less than block_min_sz;
         * 2. We cannot find the break value until the end of this file.
         */
        if (tail < block_min_sz || cur >= tail) {
            if (tail > 0) {
                if (file_descr->block_nr == file_descr->max_block_nr) {
                    seaf_warning ("Block id array is not large enough, bail out.\n");
                    free (buf);
                    return -1;
                }
                WRITE_CDC_BLOCK (tail, write_data);
            }
            break;
        }

        /* 
         * A block is at least of size block_min_sz.
         */
        if (cur < block_min_sz - 1)
            cur = block_min_sz - 1;

        while (cur < tail) {
            fingerprint = (cur == block_min_sz - 1) ?
                finger(buf + cur - BLOCK_WIN_SZ + 1, BLOCK_WIN_SZ) :
                rolling_finger (fingerprint, BLOCK_WIN_SZ, 
                                *(buf+cur-BLOCK_WIN_SZ), *(buf + cur));

            /* get a chunk, write block info to chunk file */
            if (((fingerprint & block_mask) ==  ((BREAK_VALUE & block_mask)))
                || cur + 1 >= file_descr->block_max_sz)
            {
                if (file_descr->block_nr == file_descr->max_block_nr) {
                    seaf_warning ("Block id array is not large enough, bail out.\n");
                    free (buf);
                    return -1;
                }

                WRITE_CDC_BLOCK (cur + 1, write_data);
                break;
            } else {
                cur ++;
            }
        }
    }

    SHA1_Final (file_descr->file_sum, &file_ctx);

    free (buf);

    time_spent_chunking += (g_get_monotonic_time() - tick);
    seaf_warning("Time spent chunking %d", time_spent_chunking);
    return 0;
}

int filename_chunk_cdc(const char *filename,
                       CDCFileDescriptor *file_descr,
                       SeafileCrypt *crypt,
                       gboolean write_data)
{
    int fd_src = seaf_util_open (filename, O_RDONLY | O_BINARY);
    if (fd_src < 0) {
        seaf_warning ("CDC: failed to open %s.\n", filename);
        return -1;
    }

    int ret = file_chunk_cdc (fd_src, file_descr, crypt, 0, write_data);
    /* HACK: We currently need to flush all modified pages in order for Duet to
     * reliabily deliver modify events for now. This requirement will hopefully
     * be loosened later (perhaps with extensions to the duet interface.
     */
    fsync(fd_src);
    close (fd_src);
    return ret;
}

int incremental_filename_chunk_cdc(const char *filename,
                                   CDCFileDescriptor *file_descr,
                                   struct SeafileCrypt *crypt,
                                   uint64_t *offsets,
                                   uint64_t chunk_offset,
                                   char **existing_blocks,
                                   int num_unchanged,
                                   gboolean write_data) {

    gint64 seek_amount;
    int i;
    char buf[100];

    seaf_warning("CDC: Incremental chunking %s by %lu\n", filename, chunk_offset);
    int fd_src = seaf_util_open (filename, O_RDONLY | O_BINARY);
    if (fd_src < 0) {
        seaf_warning ("CDC: failed to open %s.\n", filename);
        return -1;
    }

    // Perform some intialization of the CDC struct.
    SeafStat sb;
    if (seaf_fstat (fd_src, &sb) < 0) {
        seaf_warning ("CDC: failed to stat: %s.\n", strerror(errno));
        return -1;
    }
    uint64_t expected_size = sb.st_size;
    init_cdc_file_descriptor (fd_src, expected_size, file_descr);

    for (i = 0; i < num_unchanged; i++) {
        hex_to_rawdata (existing_blocks[i],
                        file_descr->blk_sha1s + i * CHECKSUM_LENGTH, 20);
        file_descr->blk_offsets[i] = offsets[i];
    }
    file_descr->block_nr = num_unchanged;

    if (offsets != NULL) {
        file_descr->file_size = offsets[num_unchanged - 1];
    }

    seek_amount = seaf_util_lseek(fd_src, chunk_offset, SEEK_SET);
    if (seek_amount < 0) {
        seaf_warning("CDC: failed to seek %s\n", filename);
    } else if (seek_amount < chunk_offset) {
        seaf_warning("CDC: failed to seek %s by %d\n", filename, chunk_offset);
    }

    int ret = file_chunk_cdc (fd_src, file_descr, crypt, expected_size,  write_data);

    /*
    for (i = 0; i < file_descr->block_nr; i++) {
        rawdata_to_hex(file_descr->blk_sha1s + i * CHECKSUM_LENGTH, buf, CHECKSUM_LENGTH);
        buf[CHECKSUM_LENGTH] = '\0';
        seaf_warning("[CDCDUMP] %d, %s\n", i, buf);
    }
    */

    /* HACK: We currently need to flush all modified pages in order for Duet to
     * reliabily deliver modify events for now. This requirement will hopefully
     * be loosened later (perhaps with extensions to the duet interface.
     */
    fsync(fd_src);
    close (fd_src);
    return ret;
}


int meets_early_stop_criteria(uint64_t offset, uint64_t *offsets, int num_blocks) {
  seaf_warning("CDC-EARLY: >> meets_early_stop_criteria, num_blocks = %d, offset = %lu\n", num_blocks, offset);
  if (!offsets) {
    seaf_warning("CDC-EARLY: offsets are null\n");
    return 0;
  }
  int i;
  for (i = 0; i < num_blocks; i++) {
    seaf_warning("CDC-EARLY: looping to find existing offest to satisfy criteria\n");
    if (offsets[i] == offset) {
      seaf_warning("CDC-EARLY: << meets_early_stop_criteria (found offset)\n");
      return 1;
    }
  }

  seaf_warning("CDC-EARLY: << meets_early_stop_criteria (no offset found)\n");
  return 0;
}

int early_stop_file_chunk_cdc(int fd_src,
                   CDCFileDescriptor *file_descr,
                   SeafileCrypt *crypt,
                   uint64_t expected_size,
                   gboolean write_data,
                   uint64_t *offsets,
                   uint64_t num_blocks)
{
    seaf_warning("CDC-EARLY: >> early_stop_file_chunk from block %d\n", file_descr->block_nr);
    char *buf;
    uint32_t buf_sz;
    SHA_CTX file_ctx;
    CDCDescriptor chunk_descr;
    int i;
    int early_stop_offset;
    SHA1_Init (&file_ctx);

    gint64 tick;
    seaf_warning("CDC-EARLY: get sha1 from preexisting blocks. \n");
    // Get the running SHA1 from preexisting blocks.
    for (i = 0; i < file_descr->block_nr; i++) {
        SHA1_Update(&file_ctx, file_descr->blk_sha1s + i * CHECKSUM_LENGTH, 20);
    }
    seaf_warning("CDC-EARLY: segfault finder. \n");

    uint32_t block_min_sz = file_descr->block_min_sz;
    uint32_t block_mask = file_descr->block_sz - 1;

    seaf_warning("CDC-EARLY: segfault finder. file size %d\n", file_descr->file_size);
    int fingerprint = 0;
    int offset = file_descr->file_size;
    int ret = 0;
    int tail, cur, rsize;

    seaf_warning("CDC-EARLY: segfault finder. \n");

    seaf_warning("CDC-EARLY: segfault finder. \n");
    buf_sz = file_descr->block_max_sz;
    seaf_warning("CDC-EARLY: segfault finder. %d\n", buf_sz);
    seaf_warning("CDC-EARLY: segfault finder. %p\n", chunk_descr.block_buf);
    buf = chunk_descr.block_buf = malloc (buf_sz);
    seaf_warning("CDC-EARLY: segfault finder. %p\n", buf);
    if (!buf) {
        seaf_warning("CDC-EARLY: << early_stop_file_chunk\n");
        return -1;  
    }
    seaf_warning("CDC-EARLY: segfault finder. \n");
    seaf_warning("CDC-EARLY: entering loop. \n");
    /* buf: a fix-sized buffer.
     * cur: data behind (inclusive) this offset has been scanned.
     *      cur + 1 is the bytes that has been scanned.
     * tail: length of data loaded into memory. buf[tail] is invalid.
     */
    tail = cur = 0;
    while (1) {
        if (tail < block_min_sz) {
            rsize = block_min_sz - tail + READ_SIZE;
        } else {
            rsize = (buf_sz - tail < READ_SIZE) ? (buf_sz - tail) : READ_SIZE;
        }
        ret = readn (fd_src, buf + tail, rsize);
        if (ret < 0) {
            seaf_warning ("CDC: failed to read: %s.\n", strerror(errno));
            free (buf);
            seaf_warning("CDC-EARLY: << early_stop_file_chunk\n");
            return -1;
        }
        tail += ret;
        file_descr->file_size += ret;
        num_bytes_read_for_chunking += ret;

        if (file_descr->file_size > expected_size) {
            seaf_warning ("File size changed while chunking. %d > %d\n", file_descr->file_size, expected_size);
            free (buf);
            seaf_warning("CDC-EARLY: << early_stop_file_chunk\n");
            return -1;
        }

        /* We've read all the data in this file. Output the block immediately
         * in two cases:
         * 1. The data left in the file is less than block_min_sz;
         * 2. We cannot find the break value until the end of this file.
         */
        if (tail < block_min_sz || cur >= tail) {
            if (tail > 0) {
                if (file_descr->block_nr == file_descr->max_block_nr) {
                    seaf_warning ("Block id array is not large enough, bail out.\n");
                    free (buf);
                    seaf_warning("CDC-EARLY: << early_stop_file_chunk\n");
                    return -1;
                }
                WRITE_CDC_BLOCK (tail, write_data);
                if (meets_early_stop_criteria(offset, offsets, num_blocks)) {
                  seaf_warning("CDC-EARLY: << early_stop_file_chunk\n");
                  return expected_size;
                }

            }
            break;
        }

        /* 
         * A block is at least of size block_min_sz.
         */
        if (cur < block_min_sz - 1)
            cur = block_min_sz - 1;

        while (cur < tail) {
            fingerprint = (cur == block_min_sz - 1) ?
                finger(buf + cur - BLOCK_WIN_SZ + 1, BLOCK_WIN_SZ) :
                rolling_finger (fingerprint, BLOCK_WIN_SZ, 
                                *(buf+cur-BLOCK_WIN_SZ), *(buf + cur));

            /* get a chunk, write block info to chunk file */
            if (((fingerprint & block_mask) ==  ((BREAK_VALUE & block_mask)))
                || cur + 1 >= file_descr->block_max_sz)
            {
                if (file_descr->block_nr == file_descr->max_block_nr) {
                    seaf_warning ("Block id array is not large enough, bail out.\n");
                    free (buf);
                    seaf_warning("CDC-EARLY: << early_stop_file_chunk\n");
                    return -1;
                }

                WRITE_CDC_BLOCK (cur + 1, write_data);

                if (meets_early_stop_criteria(offset, offsets, num_blocks)) {
                    seaf_warning("CDC-EARLY: << early_stop_file_chunk\n");
                    return offset;
                }

                break;
            } else {
                cur ++;
            }
        }
    }

    SHA1_Final (file_descr->file_sum, &file_ctx);

    free (buf);

    seaf_warning("CDC-EARLY: << early_stop_file_chunk\n");
    return expected_size;
}

void write_out_intermediate_chunks(CDCFileDescriptor *file_descr, char **existing_blocks, int start_offset, int end_offset, uint64_t *offsets) {
  seaf_warning("CDC-EARLY: >> write out intermediate chunks from %d to %d\n", start_offset, end_offset);
  if (existing_blocks == NULL) {
      seaf_warning("CDC-EARLY: >> write out intermediate chunks - existing blocks is null\n");
  }
  int i;
  for (i = start_offset; i < end_offset; i++) {
    seaf_warning("CDC-EARLY: segfault detector existing blocks %s\n", existing_blocks[i]);
    hex_to_rawdata (existing_blocks[i],
                    file_descr->blk_sha1s + i * CHECKSUM_LENGTH, 20);
    seaf_warning("CDC-EARLY: segfault detector\n");
    // Shouldn't be 'i', should be block number
    file_descr->blk_offsets[i] = offsets[i];
    seaf_warning("CDC-EARLY: segfault detector\n");
  }
  seaf_warning("CDC-EARLY: << write out intermediate chunks\n");
}

void print_live_chunk_list(CDCFileDescriptor *file_descr, uint64_t num_chunks) {
  int i;
  char str[num_chunks];
  seaf_warning("CDC-EARLY: chunk list: \n");

  for (i = 0; i < num_chunks; i++) {
     if (file_descr->live_chunk_list[i]) {
       strcat(str, "1");
     } else {
       strcat(str, "0");
     }
  }

  seaf_warning("CDC-EARLY: chunk list: %s\n", str);
}

void populate_live_list(CDCFileDescriptor *file_descr, GArray *live_blocks, uint64_t *offsets, uint64_t num_chunks) {
  seaf_warning("CDC-EARLY: >> populate live list\n");
  seaf_warning("CDC-EARLY: max block nr %d\n", file_descr->max_block_nr);
  int i, j, chunk_index;
  uint64_t elem;
  if (live_blocks == NULL || offsets == NULL) {
    seaf_warning("CDC-EARLY: live blocks or offsets is null\n");
    for (chunk_index = 0; chunk_index < file_descr->max_block_nr; chunk_index++) {
      file_descr->live_chunk_list[chunk_index] = 1;
    }
    return;
  }

  for (i = 0; i < num_chunks; i++) {
    seaf_warning("Offset at %lu\n", offsets[i]);
  }

  for (i = 0; i < live_blocks->len; i++) {
    elem = g_array_index(live_blocks, uint64_t, i);
    for (chunk_index = num_chunks - 1; chunk_index > -1; chunk_index--) {
      if (offsets[chunk_index] <= elem) {
        file_descr->live_chunk_list[chunk_index] = 1;
        break;
      }
    }
  }

  file_descr->live_chunk_list[num_chunks - 1] = 1;
  
  print_live_block_list("", live_blocks);
  print_live_chunk_list(file_descr, num_chunks);
  seaf_warning("CDC-EARLY: << populate live list\n");
}

uint64_t get_chunk_nr(CDCFileDescriptor *file_descr, uint64_t old_offset, uint64_t *offsets, uint64_t num_chunks) {
  seaf_warning("CDC-EARLY: << get_chunk_nr, old offset = %d \n", old_offset);

  int nr;
  for (nr = 0; nr < num_chunks; nr++) {
    seaf_warning("CDC-EARLY: checking %d against %d \n", old_offset, offsets[nr]);
    if (old_offset == offsets[nr]) {
      return nr;
    }
  }
  return -1;
}


/**
  * 1. Seek to the first block of the file.
  * 2. Begin chunking.
  * 3. Once criteria met, stop chunking.
  * 4. Seek to next block of file.
  * 5. Return to step 2.
 **/
int early_stop_filename_chunk_cdc(const char *filename,
                                  CDCFileDescriptor *file_descr,
                                  struct SeafileCrypt *crypt,
                                  uint64_t *offsets,
                                  uint64_t chunk_offset,
                                  char **existing_blocks,
                                  GArray *live_blocks,
                                  int num_unchanged,
                                  gboolean write_data,
                                  uint64_t num_chunks) {
    seaf_warning("CDC-EARLY: Early-stop chunking %s by %lu\n", filename, chunk_offset);
    seaf_warning("CDC-EARLY: >> live_blocks = %p\n", live_blocks);
    gint64 seek_amount;
    int i;
    char buf[100];
    gint64 tick;
    uint64_t old_chunk_offset = 0;
    int fd_src = seaf_util_open (filename, O_RDONLY | O_BINARY);
    if (fd_src < 0) {
        seaf_warning ("CDC-EARLY: failed to open %s.\n", filename);
        return -1;
    }

    // Perform some intialization of the CDC struct.
    SeafStat sb;
    if (seaf_fstat (fd_src, &sb) < 0) {
        seaf_warning ("CDC-EARLY: failed to stat: %s.\n", strerror(errno));
        return -1;
    }
    uint64_t expected_size = sb.st_size;
    seaf_warning("CDC-EARLY: << init_cdc_file_descriptor\n");
    init_cdc_file_descriptor (fd_src, expected_size, file_descr);
    seaf_warning("CDC-EARLY: << init_cdc_file_descriptor\n");

    file_descr->block_nr = num_unchanged;
    seaf_warning("CDC-EARLY: num unchanged %d\n", num_unchanged);
    if (offsets != NULL && num_unchanged != 0) {
        file_descr->file_size = offsets[num_unchanged - 1];
        seaf_warning("CDC-EARLY: file_size is being set to: %d\n", file_descr->file_size);
    }
    
    populate_live_list(file_descr, live_blocks, offsets, num_chunks);

    int num_blocks = file_descr->max_block_nr;

    int old_chunk_nr = 0;
    int curr_chunk_nr = 0;
    seaf_warning("CDC-EARLY: File size is %lu bytes\n", expected_size);
    tick = g_get_monotonic_time();
    seaf_warning("CDC-EARLY: About to chunk %d chunks\n", num_chunks);

    // Chunk until the final offset that has been returned is larger than the expected
    // size of the file
    while (chunk_offset < expected_size) { /** TODO **/
        seaf_warning("CDC-EARLY: >> chunk iter\n");
        seaf_warning("CDC-EARLY: >> checking live list\n");
        while (file_descr->live_chunk_list[curr_chunk_nr] != 1 && curr_chunk_nr < num_chunks) {
          curr_chunk_nr++;
          file_descr->block_nr++;
        }
        seaf_warning("CDC-EARLY: << checking live list\n");
        if (offsets == NULL) {
          seaf_warning("CDC-EARLY: there are no offsets\n");
          chunk_offset = old_chunk_offset;
        } else {
          chunk_offset = offsets[curr_chunk_nr];
          seaf_warning("CDC-EARLY: setting chunk offset to %lu for chunk %d\n", chunk_offset, curr_chunk_nr);
        }
        file_descr->file_size = chunk_offset; 
        // Write out the chunks between the last live chunk and the next live chunk
        write_out_intermediate_chunks(file_descr, existing_blocks, old_chunk_nr, curr_chunk_nr, offsets);
        seaf_warning("CDC-EARLY: seeking to %lu in %s\n", chunk_offset, filename);
        seek_amount = seaf_util_lseek(fd_src, chunk_offset, SEEK_SET);

        if (seek_amount < 0) {
            seaf_warning("CDC-EARLY: failed to seek %s\n", filename);
        } else if (seek_amount < chunk_offset) {
            seaf_warning("CDC-EARLY: failed to seek %s by %d\n", filename, chunk_offset);
        }

        old_chunk_offset = early_stop_file_chunk_cdc (fd_src, file_descr, crypt, expected_size, write_data, offsets, num_chunks);
        seaf_warning("CDC-EARLY: segf detect %d \n", old_chunk_offset);
        if (old_chunk_offset == expected_size) {
          seaf_warning("CDC-EARLY: offset == expected size\n");
          goto cleanup;
        }
        seaf_warning("CDC-EARLY: segf detect\n");
        if (old_chunk_offset == -1) {
          seaf_warning("CDC-EARLY: early_stop_file_chunk_cdc failed (-1)\n");
          return -1;
        }
        seaf_warning("CDC-EARLY: segf detect\n");
        old_chunk_nr = curr_chunk_nr = get_chunk_nr(file_descr, old_chunk_offset, offsets, num_chunks);
        seaf_warning("CDC-EARLY: segf detect\n");
        if (old_chunk_nr == -1) {
            seaf_warning("CDC-EARLY: curr chunk nr is -1\n");
            old_chunk_nr = 0;
            curr_chunk_nr = 0;
        }

        seaf_warning("CDC-EARLY: << chunk iter\n");
    }
cleanup:
    time_spent_chunking += (g_get_monotonic_time() - tick);
    seaf_warning("Time spent chunking %d", time_spent_chunking);

    /* HACK: We currently need to flush all modified pages in order for Duet to
     * reliabily deliver modify events for now. This requirement will hopefully
     * be loosened later (perhaps with extensions to the duet interface.
     */
    fsync(fd_src);
    close (fd_src);
    seaf_warning("CDC-EARLY: << early_stop_filename\n");
    return 0;
}

void cdc_init ()
{
    rabin_init (BLOCK_WIN_SZ);
}
