/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 */

/* Run puff on files, for diff_puff.py. Each line of the input is a file
   name and a size for the output buffer; for each, print the name, the
   return code of puff, the output and input lengths that it gives back,
   and an FNV-1a hash of the output if it succeeded. */

#include <stdio.h>
#include <stdlib.h>
#include "puff.h"

int main(void)
{
    static unsigned char in[1 << 20];
    char path[4096];
    unsigned long destsize;
    while (scanf("%4095s %lu", path, &destsize) == 2) {
        FILE *f = fopen(path, "rb");
        if (f == NULL) { printf("%s ERROR\n", path); continue; }
        unsigned long inlen = fread(in, 1, sizeof in, f);
        fclose(f);
        unsigned char *out = malloc(destsize ? destsize : 1);
        unsigned long destlen = destsize, sourcelen = inlen;
        int rc = puff(out, &destlen, in, &sourcelen);
        unsigned long h = 1469598103934665603UL;
        if (rc == 0)
            for (unsigned long i = 0; i < destlen; i++)
                h = (h ^ out[i]) * 1099511628211UL;
        printf("%s %d %lu %lu %016lx\n", path, rc, destlen, sourcelen, h);
        free(out);
    }
    return 0;
}
