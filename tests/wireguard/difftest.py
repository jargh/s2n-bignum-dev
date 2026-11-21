#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

# Differential tests of the WireGuard image (the code that is verified)
# against the specification common/wireguard.ml, through its Python
# transcription wg_ref.py. Each case runs a complete handshake between two
# devices in the harness (harness/wg_harness.c, which loads wireguard.so),
# with chosen randomness, clocks and indices, and checks every message
# byte, the handshake state and the transport keys against the spec, plus
# rejections: tampered messages, replayed and too frequent initiations,
# and peers whose public key gives an all-zero Diffie-Hellman result.
#
# Usage: python3 -I difftest.py OUTDIR [SEED] [N]
#
#   OUTDIR  the build directory of arm/wireguard/build.sh, with test/ built
#           by harness/build.sh; on a host other than AArch64 the harness
#           runs under qemu-aarch64 -L /usr/aarch64-linux-gnu.

import os, platform, random, subprocess, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import wg_ref as R

out = os.path.abspath(sys.argv[1])
seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
count = int(sys.argv[3]) if len(sys.argv) > 3 else 20
rng = random.Random(seed)
rb = lambda n: bytes(rng.getrandbits(8) for _ in range(n))

HARNESS = [os.path.join(out, 'test', 'wg_harness'),
           os.path.join(out, 'wireguard.so')]
if platform.machine() not in ('aarch64', 'arm64'):
    HARNESS = ['qemu-aarch64', '-L', '/usr/aarch64-linux-gnu'] + HARNESS

failures = 0
def check(name, got, want):
    global failures
    if got != want:
        failures += 1
        print('FAIL', name)
        print('  got ', got.hex() if isinstance(got, bytes) else got)
        print('  want', want.hex() if isinstance(want, bytes) else want)

def run(cmds):
    r = subprocess.run(HARNESS, input='\n'.join(cmds) + '\n',
                       capture_output=True, text=True, timeout=600)
    if r.returncode != 0:
        print('harness failed:', r.stderr.strip())
        sys.exit(2)
    return r.stdout.splitlines()

def results(lines):
    """Split the output into the results of the commands that print."""
    groups, cur = [], None
    for l in lines:
        k, _, v = l.partition(' ')
        if k in ('has_identity', 'precomputed_static_static', 'ret', 'peer'):
            cur = {}; groups.append(cur)
        cur[k] = v
    return groups

def hexb(s): return bytes.fromhex(s)
def le32(x): return x.to_bytes(4, 'little')

# Points of small order (RFC 7748 Section 7): DH with them is all zero.
LOW_ORDER = [bytes(32), bytes([1]) + bytes(31),
             bytes.fromhex('e0eb7a7c3b41b8ae1656e3faf19fc46ada098deb9c32b1fd866205165f49b800')]

for case in range(count):
    si, sr = rb(32), rb(32)                      # raw static private keys
    si_pub, sr_pub = R.wg_dh_pubkey(si), R.wg_dh_pubkey(sr)
    psk = rb(32) if rng.random() < 0.7 else None
    q = psk if psk is not None else bytes(32)
    ri, rr = rb(32), rb(32)                      # ephemeral randomness
    sec, nsec = rng.getrandbits(34), rng.randrange(10 ** 9)
    ii, ir = rng.getrandbits(32), rng.getrandbits(32)
    t1 = rng.randrange(10 ** 8, 10 ** 12)        # coarse clock readings
    t2 = t1 + rng.randrange(0, 10 ** 6)
    t3, t4 = t2 + 1000, t2 + 2000
    pskarg = psk.hex() if psk is not None else '-'
    cmds = ['device ' + si.hex(), 'device ' + sr.hex(),
            'peer 0 %s %s' % (sr_pub.hex(), pskarg),
            'peer 1 %s %s' % (si_pub.hex(), pskarg),
            'rand ' + ri.hex(), 'realtime %d %d' % (sec, nsec),
            'index %d' % ii, 'create_init 0 0']
    lines = run(cmds)
    g = results(lines)
    msg1 = hexb(g[4]['msg'])
    # the spec of create_initiation
    ei = R.wg_clamp(ri)
    ts = R.wg_tai64n(sec, nsec)
    ss_i = R.wg_dh(R.wg_clamp(si), sr_pub)
    check('%d static_public I' % case, hexb(g[0]['static_public']), si_pub)
    check('%d precomputed I' % case, hexb(g[2]['precomputed_static_static']),
          ss_i)
    spec1 = R.wg_create_initiation(si_pub, sr_pub, ss_i, ei, ts, ii)
    check('%d create_init ret' % case, g[4]['ret'], '1')
    check('%d initiation' % case, msg1[:116], spec1[0])
    check('%d initiation macs untouched' % case, msg1[116:], b'\xee' * 32)
    check('%d initiator state' % case, g[4]['state'], '1')
    check('%d initiator hash' % case, hexb(g[4]['hash']), spec1[2])
    check('%d initiator ck' % case, hexb(g[4]['chaining_key']), spec1[1])
    check('%d initiator eph' % case, hexb(g[4]['ephemeral_private']), ei)

    # the responder consumes it, responds, and the initiator consumes that
    cmds += ['coarse %d' % t1, 'coarse %d' % t2,
             'consume_init 1 ' + msg1.hex(),
             'rand ' + rr.hex(), 'index %d' % ir, 'create_resp 1 0']
    g = results(run(cmds))
    st = R.wg_consume_initiation_static(R.wg_clamp(sr), sr_pub, msg1)
    e_i, s_i, ck, hh = st
    ss_r = R.wg_dh(R.wg_clamp(sr), s_i)
    t_i, ck_r, h_r = R.wg_consume_initiation_timestamp(ss_r, (ck, hh), msg1)
    check('%d consume_init peer' % case, g[5]['peer'], '0')
    check('%d responder state' % case, g[5]['state'], '2')
    check('%d responder hash' % case, hexb(g[5]['hash']), h_r)
    check('%d responder ck' % case, hexb(g[5]['chaining_key']), ck_r)
    check('%d responder remote eph' % case, hexb(g[5]['remote_ephemeral']),
          e_i)
    check('%d responder timestamp' % case, hexb(g[5]['latest_timestamp']), t_i)
    check('%d responder remote index' % case, hexb(g[5]['remote_index']),
          le32(ii))
    check('%d last consumption' % case,
          int(g[5]['last_initiation_consumption']), t2)
    er = R.wg_clamp(rr)
    spec2 = R.wg_create_response((ck_r, h_r), e_i, s_i, q, er, ir, ii)
    msg2 = hexb(g[6]['msg'])
    check('%d create_resp ret' % case, g[6]['ret'], '1')
    check('%d response' % case, msg2[:60], spec2[0])
    check('%d response macs untouched' % case, msg2[60:], b'\xee' * 32)
    check('%d responder state 2' % case, g[6]['state'], '3')
    check('%d responder hash 2' % case, hexb(g[6]['hash']), spec2[2])
    check('%d responder ck 2' % case, hexb(g[6]['chaining_key']), spec2[1])

    cmds += ['consume_resp 0 ' + msg2.hex(),
             'coarse %d' % t3, 'begin 0 0', 'coarse %d' % t4, 'begin 1 0']
    g = results(run(cmds))
    spec3 = R.wg_consume_response((spec1[1], spec1[2]), ei, R.wg_clamp(si),
                                  q, msg2)
    check('%d consume_resp peer' % case, g[7]['peer'], '0')
    check('%d initiator state 2' % case, g[7]['state'], '4')
    check('%d initiator hash 2' % case, hexb(g[7]['hash']), spec3[2])
    check('%d initiator ck 2' % case, hexb(g[7]['chaining_key']), spec3[1])
    check('%d initiator remote eph' % case, hexb(g[7]['remote_ephemeral']),
          spec3[0])
    check('%d initiator remote index' % case, hexb(g[7]['remote_index']),
          le32(ir))
    k1, k2 = R.wg_transport_keys(spec3[1])
    check('%d begin I' % case, (g[8]['ret'], g[8]['initiator']), ('1', '1'))
    check('%d keys I' % case, (hexb(g[8]['sending']), hexb(g[8]['receiving'])),
          (k1, k2))
    check('%d begin R' % case, (g[9]['ret'], g[9]['initiator']), ('1', '0'))
    check('%d keys R' % case, (hexb(g[9]['sending']), hexb(g[9]['receiving'])),
          (k2, k1))
    check('%d handshakes zeroed' % case, (g[8]['state'], g[9]['state']),
          ('0', '0'))

    # Rejections, each in a fresh run of the first part.
    base = cmds[:8] + ['coarse %d' % t1, 'coarse %d' % t2]
    # a tampered initiation
    j = rng.randrange(8, 116)
    bad = bytearray(msg1); bad[j] ^= 1 << rng.randrange(8)
    g = results(run(base + ['consume_init 1 ' + bytes(bad).hex(),
                            'show 1 0']))
    check('%d tampered initiation' % case, g[5]['peer'], '-1')
    # a replay, and an initiation too soon after the last one
    rep = base + ['consume_init 1 ' + msg1.hex(),
                  'coarse %d' % (t2 + 30000000), 'coarse %d' % (t2 + 30000001),
                  'consume_init 1 ' + msg1.hex()]
    g = results(run(rep))
    check('%d replay' % case, (g[5]['peer'], g[6]['peer']), ('0', '-1'))
    ri2 = rb(32)
    flood = cmds[:8] + ['coarse %d' % t1, 'coarse %d' % t2,
                        'consume_init 1 ' + msg1.hex(),
                        'rand ' + ri2.hex(), 'realtime %d %d' % (sec + 1, nsec),
                        'index %d' % (ii ^ 1), 'create_init 0 0']
    g = results(run(flood))
    msg1b = hexb(g[6]['msg'])
    soon = rng.randrange(0, 20000000)
    late = 20000000 + rng.randrange(0, 1000)
    g = results(run(flood + ['coarse %d' % (t2 + soon), 'coarse %d' % (t2 + soon),
                             'consume_init 1 ' + msg1b.hex()]))
    check('%d flood' % case, g[7]['peer'], '-1')
    g = results(run(flood + ['coarse %d' % (t2 + late), 'coarse %d' % (t2 + late),
                             'consume_init 1 ' + msg1b.hex()]))
    check('%d after flood window' % case, g[7]['peer'], '0')
    # a tampered response
    j = rng.randrange(12, 60)
    bad = bytearray(msg2); bad[j] ^= 1 << rng.randrange(8)
    g = results(run(cmds[:14] + ['consume_resp 0 ' + bytes(bad).hex()]))
    check('%d tampered response' % case, g[7]['peer'], '-1')
    # a peer with a low-order public key: no initiation
    lo = rng.choice(LOW_ORDER)
    g = results(run(['device ' + si.hex(), 'peer 0 %s -' % lo.hex(),
                     'rand ' + ri.hex(), 'realtime 1 2', 'index 7',
                     'create_init 0 0']))
    check('%d low-order peer' % case, (g[1]['precomputed_static_static'],
                                       g[2]['ret']), ('00' * 32, '0'))

print('%d cases, %d failures' % (count, failures))
sys.exit(1 if failures else 0)
