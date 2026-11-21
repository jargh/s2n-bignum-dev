// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Kernel data that the WireGuard image refers to by PC-relative addressing.
// In the kernel these are variables of vmlinux; here they are part of the
// image's writable data, and the proofs state their contents as
// preconditions. Calls to kernel functions go through the PLT instead.
//
//   empty_zero_page   the zero page, read by the AEAD code for padding
//   kimage_voffset    the offset of the kernel image (for __pa_symbol)
//   memstart_addr     the physical start of memory (for __va)
//   kmalloc_caches    the slab caches indexed by kzalloc
// ----------------------------------------------------------------------------

        .data
        .balign 8
        .globl  kimage_voffset
        .type   kimage_voffset, %object
        .size   kimage_voffset, 8
kimage_voffset:
        .quad   0

        .globl  memstart_addr
        .type   memstart_addr, %object
        .size   memstart_addr, 8
memstart_addr:
        .quad   0

        .globl  kmalloc_caches
        .type   kmalloc_caches, %object
        .size   kmalloc_caches, 4096
kmalloc_caches:
        .zero   4096

        .bss
        .balign 4096
        .globl  empty_zero_page
        .type   empty_zero_page, %object
        .size   empty_zero_page, 4096
empty_zero_page:
        .zero   4096

        .section .note.GNU-stack,"",%progbits
