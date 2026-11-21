/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

   Added to ld's default script for shared objects: drop the sections that
   only hold metadata for the kernel (exports, the bug table, boot-time
   alternatives, module information), as the kernel's own linker scripts
   do with most of them. The alternatives only patch the atomics in
   wg_noise_keypair_get, wg_noise_keypair_put and
   wg_noise_handshake_begin_session. */

SECTIONS
{
  /DISCARD/ : {
    *(.discard.*) *(.export_symbol) *(.modinfo) *(__bug_table)
    *(.altinstructions) *(.init.data) *(.exit.data) *(.comment)
  }
}
INSERT AFTER .text;
