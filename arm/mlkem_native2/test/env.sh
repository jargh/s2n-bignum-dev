# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

# The settings shared by the scripts here, which source this file. All
# that they download or build goes under WORK, and any of these can be
# set in the environment instead:
#
#   WORK          downloads, builds and results (default: work/ here)
#   MLKEM_NATIVE  a checkout of mlkem-native at MLKEM_NATIVE_COMMIT, the
#                 reference (default: WORK/mlkem-native, made by setup.sh)
#   VECTORS       the ACVP and Wycheproof vectors (default: WORK/vectors)
#   VALGRIND      a valgrind that can run the SHA3 instructions (default:
#                 WORK/valgrind/bin/valgrind if setup.sh built it); if it
#                 is empty, the steps under valgrind are skipped
#   CC            the C compiler for the tests (default: gcc)

T=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
REPO=$(cd "$T/../../.." && pwd)
WORK=${WORK:-$T/work}
MLKEM_NATIVE_COMMIT=9b96caa137514c82a097a4251783769657826f6c
MLKEM_NATIVE=${MLKEM_NATIVE:-$WORK/mlkem-native}
VECTORS=${VECTORS:-$WORK/vectors}
if [ -z "${VALGRIND+set}" ]; then
  VALGRIND=$WORK/valgrind/bin/valgrind
  [ -x "$VALGRIND" ] || VALGRIND=
fi
CC=${CC:-gcc}

# The objects of a build (see build.sh): the API, the middle layer and
# the constants in arm/mlkem_native2, the new leaves in arm/mlkem, and
# the existing functions they call (and mlkem_rej_uniform_VARIABLE_TIME,
# which test_leaf compares with the new sampler).

NATIVE2_OBJS="mlkem512 mlkem768 mlkem1024 mlkem_gen_matrix mlkem_getnoise
  mlkem_hash_h mlkem_hash_g mlkem_native2_constants"
LEAF_OBJS="add_reduce sub_reduce cbd2 cbd3 check_encoding compress_d4
  compress_d5 compress_d10 compress_d11 decompress_d4 decompress_d5
  decompress_d10 decompress_d11 frombytes frommsg tomsg
  rej_uniform_alt_VARIABLE_TIME ntt_alt intt_alt tobytes_alt
  basemul_k2_alt basemul_k3_alt basemul_k4_alt mulcache_compute reduce
  tomont rej_uniform_VARIABLE_TIME"
SHA3_OBJS="sha3_keccak_f1600 sha3_keccak4_f1600_alt2"

# The flags that make the kernel enforce BTI in a test program

BTI_FLAGS="-mbranch-protection=bti -Wl,-z,force-bti -Wl,-e,bti_start
  -Wl,-init,bti_init -Wl,-fini,bti_init $T/bti_start.S"

result() {
  if [ "$2" = 0 ]; then echo "  $1: OK"
  elif [ "$2" = skip ]; then echo "  $1: skipped"
  else echo "  $1: FAIL"; st=1; fi
}
