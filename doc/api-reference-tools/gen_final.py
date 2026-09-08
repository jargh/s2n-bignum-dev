#!/usr/bin/env python3
import os as _os
_WD = _os.environ.get('APIDOC_WORKDIR', '/tmp')
"""Generate the final flat A-Z API reference markdown."""
import json, re, importlib.util

hdr_list = json.load(open(_os.path.join(_WD, 'hdr.json')))
ban   = json.load(open(_os.path.join(_WD, 'banners.json')))
sigs  = json.load(open(_os.path.join(_WD, 'sigs.json')))
specs = json.load(open(_os.path.join(_WD, 'specs.json')))
deltas= json.load(open(_os.path.join(_WD, 'deltas.json')))
assum = json.load(open(_os.path.join(_WD, 'assumptions.json')))
stack = json.load(open(_os.path.join(_WD, 'stack.json')))

_spec = importlib.util.spec_from_file_location('al',_os.path.join(_WD, 'alias_logic.py'))
al = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(al)

hdr = {}
for r in hdr_list:
    hdr.setdefault(r['name'], r)

# ---- alt/base + arch-only sets -------------------------------------------
ALT = {h for h in hdr if h.endswith('_alt')}

def render_static(s):
    # S2N_BIGNUM_STATIC N  -> static N  (readable); keep const/pointer forms
    return s.replace('S2N_BIGNUM_STATIC ', 'static ')

def c_signature(rec):
    return render_static(f"{rec['ret']} {rec['name']}({rec['args']});")

def _base(fn):
    for suf in ('_VARIABLE_TIME_arm','_VARIABLE_TIME_x86','_VARIABLE_TIME','_arm','_x86'):
        if fn.endswith(suf): return fn[:-len(suf)]
    return fn

def get_sig(fn):
    return (sigs['arm'].get(fn) or sigs['x86'].get(fn)
            or sigs['arm'].get(_base(fn)) or sigs['x86'].get(_base(fn)))

UNIT = {'8':'', '1':' (bytes)', '4':' (32-bit words)', '2':' (16-bit words)'}
def fmt_bufs(bs):
    parts=[]
    for b in bs:
        parts.append(f"`{b['name']}`[{b['n']}]{UNIT.get(str(b['elem']),'')}")
    return ', '.join(parts)

SIZES_OVERRIDE = {
 'mlkem_rej_uniform_VARIABLE_TIME': "inputs `buf`[buflen] (bytes), `table`[4096] (bytes); output `r`[256] (16-bit words); returns count written (0..256)",
 'mldsa_rej_uniform_VARIABLE_TIME': "inputs `buf`[buflen] (bytes), `table`[4096] (bytes); output `r`[256] (32-bit words); returns count written (0..256)",
 'mldsa_rej_uniform_VARIABLE_TIME_x86': "inputs `buf`[840] (bytes), `table`[256] (64-bit words); output `r`[256] (32-bit words); returns count written (0..256)",
 'mldsa_rej_uniform_eta2_VARIABLE_TIME': "inputs `buf`[buflen] (bytes), `table`[4096] (bytes); output `r`[256] (32-bit words); returns count written (0..256)",
 'mldsa_rej_uniform_eta4_VARIABLE_TIME': "inputs `buf`[buflen] (bytes), `table`[4096] (bytes); output `r`[256] (32-bit words); returns count written (0..256)",
}

def banner_io_line(fn):
    """The banner's 'Inputs .../output ...' line — used as a Sizes fallback for
    functions (e.g. the scalar word_* ops) that have no buffer-based signature."""
    b=ban.get(fn,{})
    for arch in ('arm','x86'):
        for l in b.get(arch,{}).get('prose',[])[:3]:
            if re.match(r'^\s*(Inputs?|Input/output)\b', l.strip()):
                return l.strip()
    return None

def buffers_line(fn):
    if fn in SIZES_OVERRIDE:
        return SIZES_OVERRIDE[fn]
    s=get_sig(fn)
    if not s:
        return banner_io_line(fn)
    segs=[]
    if s['inputs']: segs.append('inputs '+fmt_bufs(s['inputs']))
    if s['outputs']: segs.append('output '+fmt_bufs(s['outputs']))
    if s['temps']: segs.append('temporary '+fmt_bufs(s['temps']))
    # no pointer buffers (pure word ops): fall back to the banner's I/O line
    return '; '.join(segs) if segs else banner_io_line(fn)

def summary_line(fn):
    b=ban.get(fn,{})
    for arch in ('arm','x86'):
        pr=b.get(arch,{}).get('prose',[])
        if pr: return pr[0].strip()
    return (hdr[fn]['desc'][0] if hdr[fn]['desc'] else '').strip()

def detail_paras(fn, arch_pref=('arm','x86')):
    b=ban.get(fn,{})
    for arch in arch_pref:
        pr=b.get(arch,{}).get('prose',[])
        if not pr: continue
        rest=pr[1:]
        while rest and (rest[0].strip()=='' or re.match(r'^\s*(Inputs?|Outputs?|Input/output)\b', rest[0])):
            rest.pop(0)
        paras=[]; cur=[]
        for l in rest:
            if l.strip()=='':
                if cur: paras.append(' '.join(x.strip() for x in cur)); cur=[]
            else: cur.append(l)
        if cur: paras.append(' '.join(x.strip() for x in cur))
        return paras
    return []

# ML-KEM / ML-DSA entries whose proof variable-names collide with C arg-names, or
# which transform in place: auto-derived aliasing is unreliable, hand-write these.
ALIAS_MANUAL = {
 'mldsa_ntt','mldsa_ntt_arm','mldsa_intt','mldsa_intt_arm','mlkem_ntt','mlkem_ntt_x86',
 'mlkem_intt','mlkem_intt_x86','mldsa_decompose_32','mldsa_decompose_88','mldsa_caddq',
 'mldsa_chknorm','mlkem_reduce','mlkem_tomont','mlkem_mulcache_compute','mlkem_mulcache_compute_x86',
 'mldsa_nttunpack','mldsa_reduce','mlkem_unpack','mlkem_frombytes','mlkem_tobytes',
 'mldsa_poly_use_hint_32','mldsa_poly_use_hint_88','mldsa_polyz_unpack_17','mldsa_polyz_unpack_19',
 'mldsa_polyz_unpack_17_arm','mldsa_polyz_unpack_19_arm',
 'mldsa_pointwise','mldsa_pointwise_x86','mldsa_pointwise_acc_l4','mldsa_pointwise_acc_l4_x86',
 'mldsa_pointwise_acc_l5','mldsa_pointwise_acc_l5_x86','mldsa_pointwise_acc_l7','mldsa_pointwise_acc_l7_x86',
 'mlkem_basemul_k2','mlkem_basemul_k3','mlkem_basemul_k4',
 'mldsa_rej_uniform_VARIABLE_TIME','mldsa_rej_uniform_VARIABLE_TIME_x86',
 'mldsa_rej_uniform_eta2_VARIABLE_TIME','mldsa_rej_uniform_eta4_VARIABLE_TIME',
 'mlkem_rej_uniform_VARIABLE_TIME',
}

# Hand-written aliasing for the ML-KEM / ML-DSA family, read directly off the
# SUBROUTINE_CORRECT preconditions (see notes in api-doc-task memory).
_inplace_poly = "Operates in place on `a`; the table argument(s) must not overlap `a`."
ALIAS_OVERRIDE = {
 'mldsa_ntt_arm': "Transforms the coefficient array `a` in place; the twiddle tables `z_012345`, `z_67` must not overlap `a`.",
 'mldsa_ntt':     "Transforms the coefficient array `a` in place; the `zetas` table must not overlap `a`.",
 'mldsa_intt_arm':"Transforms the coefficient array `a` in place; the twiddle tables `z_78`, `z_123456` must not overlap `a`.",
 'mldsa_intt':    "Transforms the coefficient array `a` in place; the `zetas` table must not overlap `a`.",
 'mlkem_ntt':     "Transforms the coefficient array `a` in place; the twiddle tables `z_01234`, `z_56` must not overlap `a`.",
 'mlkem_ntt_x86': "Transforms the coefficient array `a` in place; the `qdata` table must not overlap `a`.",
 'mlkem_intt':    "Transforms the coefficient array `a` in place; the twiddle tables `z_01234`, `z_56` must not overlap `a`.",
 'mlkem_intt_x86':"Transforms the coefficient array `a` in place; the `qdata` table must not overlap `a`.",
 'mldsa_nttunpack':"Operates in place on `a` (which must be 32-byte aligned).",
 'mldsa_reduce':  "Operates in place on `a` (which must be 32-byte aligned).",
 'mlkem_reduce':  "Operates in place on `a`.",
 'mlkem_tomont':  "Operates in place on `a`.",
 'mlkem_unpack':  "Operates in place on `a` (which must be 32-byte aligned).",
 'mldsa_caddq':   "Operates in place on `a`.",
 'mldsa_chknorm': "Reads `a` only (returns a flag); no output buffer.",
 'mldsa_pointwise':     "Output `r` must not overlap inputs `a`, `b`.",
 'mldsa_pointwise_x86': "Output `c` must not overlap inputs `a`, `b` (or the `qdata` table).",
 'mldsa_pointwise_acc_l4': "Output `r` must not overlap inputs `a`, `b`.",
 'mldsa_pointwise_acc_l4_x86': "Output `c` must not overlap inputs `a`, `b` (or the `qdata` table).",
 'mldsa_pointwise_acc_l5': "Output `r` must not overlap inputs `a`, `b`.",
 'mldsa_pointwise_acc_l5_x86': "Output `c` must not overlap inputs `a`, `b` (or the `qdata` table).",
 'mldsa_pointwise_acc_l7': "Output `r` must not overlap inputs `a`, `b`.",
 'mldsa_pointwise_acc_l7_x86': "Output `c` must not overlap inputs `a`, `b` (or the `qdata` table).",
 'mlkem_basemul_k2': "Output must not overlap any of its inputs.",
 'mlkem_basemul_k3': "Output must not overlap any of its inputs.",
 'mlkem_basemul_k4': "Output must not overlap any of its inputs.",
 'mlkem_mulcache_compute':     "Output (mulcache) must not overlap the input polynomial or the zeta tables.",
 'mlkem_mulcache_compute_x86': "Output (mulcache) must not overlap the input polynomial or the `qdata` table.",
 'mlkem_tobytes':  "Output byte array `r` must not overlap the input polynomial `a`.",
 'mlkem_frombytes':"Output polynomial `r` must not overlap the input byte array `a`; `r` must be 32-byte aligned.",
 'mldsa_decompose_32': "Writes high parts to `a1` and, in place, the low parts to `a0` (the input array); `a1` must not overlap `a0`.",
 'mldsa_decompose_88': "Writes high parts to `a1` and, in place, the low parts to `a0` (the input array); `a1` must not overlap `a0`.",
 'mldsa_poly_use_hint_32': "Output `b` must not overlap inputs `a`, `h`.",
 'mldsa_poly_use_hint_88': "Output `b` must not overlap inputs `a`, `h`.",
 'mldsa_polyz_unpack_17': "Output `r` must not overlap the packed input `b` or the shuffle table `t`.",
 'mldsa_polyz_unpack_19': "Output `r` must not overlap the packed input `b` or the shuffle table `t`.",
 'mldsa_polyz_unpack_17_arm': "Output `r` must not overlap the packed input `b` or the shuffle table `t`.",
 'mldsa_polyz_unpack_19_arm': "Output `r` must not overlap the packed input `b` or the shuffle table `t`.",
 'mldsa_rej_uniform_VARIABLE_TIME': "No restrictions (the spec imposes no disjointness between `r` and `buf` or `table`).",
 'mldsa_rej_uniform_VARIABLE_TIME_x86': "No restrictions (the spec imposes no disjointness between `r` and `buf` or `table`).",
 'mldsa_rej_uniform_eta2_VARIABLE_TIME': "No restrictions (the spec imposes no disjointness between `r` and `buf`).",
 'mldsa_rej_uniform_eta4_VARIABLE_TIME': "No restrictions (the spec imposes no disjointness between `r` and `buf`).",
 'mlkem_rej_uniform_VARIABLE_TIME': "No restrictions (the spec imposes no disjointness between `r` and `buf` or `table`).",
}

# Corrections where the auto-deriver mis-maps proof-variable names to C args, or
# where a co-present ALLPAIRS nonoverlapping(z,x) overrides an in-place disjunct.
# All verified by hand against the _SUBROUTINE_CORRECT preconditions.
ALIAS_CORRECTION = {
 # proof calls the sole input buffer `x`; C prototype calls it `y`. In-place OK.
 'bignum_cmul':    "Output `z` may be the same buffer as `y` (exact aliasing only — no partial overlap).",
 'bignum_cmadd':   "Output `z` may be the same buffer as `y` (exact aliasing only — no partial overlap).",
 'bignum_cmnegadd':"Output `z` may be the same buffer as `y` (exact aliasing only — no partial overlap).",
 # modinv proof vars x,y are C args a,b; ALLPAIRS forces z disjoint from both.
 'bignum_modinv':  "Output `z` must not overlap inputs `a`, `b`. Temporary buffer `t` (>= 3*k words) must be distinct from all other arguments.",
 # subroutine contract's stackframe ALLPAIRS forces z disjoint from x, overriding
 # the vestigial in-place disjunct — so as a called subroutine these need z, x, y distinct.
 'bignum_mul_6_12_alt': "Output `z` must not overlap `x`, `y`.",
 'bignum_mul_8_16_alt': "Output `z` must not overlap `x`, `y`.",
}

def aliasing_text(fn):
    if fn in ALIAS_CORRECTION:
        return ALIAS_CORRECTION[fn]
    if fn in ALIAS_OVERRIDE:
        return ALIAS_OVERRIDE[fn]
    if fn in ALIAS_MANUAL:
        return None
    a=al.analyze(fn,'arm') or al.analyze(fn,'x86')
    if not a: return None
    outs,ins,temps,verds=a['outs'],a['ins'],a['temps'],a['verdicts']
    if not outs or not ins:
        return None
    # pure in-place: the only input is the output buffer itself (z read and written)
    if outs==ins and len(outs)==1:
        return f"Operates in place on `{outs[0]}` (read and written in the same buffer)."
    def joinb(xs): return ', '.join(f"`{x}`" for x in xs)
    temp_note = (f"Temporary buffer {', '.join('`'+t+'`' for t in temps)} must be "
                 f"distinct from all other arguments." if temps else "")

    segs=[]
    any_restriction=False
    for O in outs:
        # ignore self-reference (in-place transforms where an arg is both in and out)
        inplace=[I for I in ins if I!=O and verds.get(f'{O}<-{I}')=='INPLACE']
        free=[I for I in ins if I!=O and verds.get(f'{O}<-{I}')=='FREE']
        disj=[I for I in ins if I!=O and verds.get(f'{O}<-{I}')=='DISJOINT']
        clause=[]
        if free: clause.append(f"may coincide with or overlap {joinb(free)} arbitrarily")
        if inplace:
            clause.append(f"may be the same buffer as {joinb(inplace)} (exact aliasing only — no partial overlap)")
            any_restriction=True
        if disj:
            clause.append(f"must not overlap {joinb(disj)}")
            any_restriction=True
        if clause:
            segs.append(f"output `{O}` " + '; '.join(clause))

    # No non-trivial input/output restriction (every pair FREE): say so tersely.
    # Code/stack disjointness is a global rule that goes without saying at C level.
    if not any_restriction:
        if temp_note:
            return "No restrictions on input/output overlap. " + temp_note
        return "No restrictions."

    txt='. '.join(s[0].upper()+s[1:] for s in segs)
    if txt and not txt.endswith('.'): txt+='.'
    if temp_note:
        txt += " " + temp_note
    return txt or None

def assumptions_text(fn):
    parts=[]
    if fn in assum:
        parts.extend(assum[fn])
    # light touch-ups for readability
    out=[]
    for p in parts:
        p=p.replace(' MOD 8 = 0',' is a multiple of 8')
        out.append(p)
    return out

# Curated per-function cross-arch notes (real, non-cosmetic deltas).
ARCH_NOTES = {
 'sha3_keccak4_f1600_alt': 'On x86 this takes two extra input arguments `rho8[4]` and `rho56[4]` (rotation-constant tables); on ARM the prototype is just `(a[100], rc[24])`.',
 'bignum_kmul_16_32': 'On x86 the temporary-buffer argument `t` is unused (retained only for API compatibility with ARM).',
 'bignum_ksqr_16_32': 'On x86 the temporary-buffer argument `t` is unused (retained only for API compatibility with ARM).',
 'bignum_kmul_32_64': 'On x86 the `t` buffer is used but the nominal size (96) overstates the real requirement (65 words); the size is kept for ARM compatibility.',
 'bignum_ksqr_32_64': 'On x86 the `t` buffer is used but the nominal size (72) overstates the real requirement (65 words); the size is kept for ARM compatibility.',
}
# base -> byte-variant cross reference
BYTE_SIBLING = {
 'curve25519_x25519':'curve25519_x25519_byte',
 'curve25519_x25519_alt':'curve25519_x25519_byte_alt',
 'curve25519_x25519base':'curve25519_x25519base_byte',
 'curve25519_x25519base_alt':'curve25519_x25519base_byte_alt',
}

def stack_text(fn):
    st=stack.get(fn,{})
    a,x=st.get('arm'),st.get('x86')
    d=deltas.get(fn,{}); avail=d.get('avail',['arm','x86'])
    def show(v): return 'none' if v==0 else f"{v} bytes"
    # only report for the architectures the function exists on
    parts=[]
    if 'arm' in avail and a is not None: parts.append(('ARM', a))
    if 'x86' in avail and x is not None: parts.append(('x86', x))
    if not parts: return None
    if all(v==0 for _,v in parts): return None   # leaf functions: omit
    if len(parts)==2 and parts[0][1]==parts[1][1]:
        return f"{show(parts[0][1])} (below the stack pointer)"
    return ', '.join(f"{arch} {show(v)}" for arch,v in parts) + " (below the stack pointer)"

def availability_text(fn):
    d=deltas.get(fn,{})
    avail=d.get('avail',['arm','x86'])
    if avail==['arm']: base='ARM only.'
    elif avail==['x86']: base='x86 only.'
    else: base='ARM and x86.'
    extra=[]
    if fn in ARCH_NOTES: extra.append(ARCH_NOTES[fn])
    if fn in BYTE_SIBLING:
        extra.append(f'See also [`{BYTE_SIBLING[fn]}`](#{BYTE_SIBLING[fn]}), an identical routine whose arguments are typed as 32-byte little-endian arrays instead of 4-word bignums.')
    return base + (' ' + ' '.join(extra) if extra else '')

def render(fn):
    rec=hdr[fn]
    L=[]
    L.append(f"### `{fn}`\n")
    L.append("```c")
    if fn=='sha3_keccak4_f1600_alt':
        # the one function with a genuinely different prototype per architecture
        recs={r['arch']:r for r in hdr_list if r['name']==fn}
        L.append("// ARM:")
        L.append(c_signature(recs['arm']))
        L.append("// x86:")
        L.append(c_signature(recs['x86']))
    else:
        L.append(c_signature(rec))
    L.append("```\n")
    L.append(f"**Operation.** {summary_line(fn)}\n")
    bl=buffers_line(fn)
    if bl: L.append(f"**Sizes.** {bl}\n")
    asm=assumptions_text(fn)
    if asm:
        L.append(f"**Assumptions.** "+'; '.join(asm)+".\n")
    at=aliasing_text(fn)
    if at: L.append(f"**Aliasing.** {at}\n")
    stk=stack_text(fn)
    if stk: L.append(f"**Stack use.** {stk}\n")
    L.append(f"**Availability.** {availability_text(fn)}\n")
    dp=detail_paras(fn)
    if dp:
        # keep it to the first 1-2 substantive paragraphs to stay digestible
        body=' '.join(dp[:2]) if len(' '.join(dp))<900 else dp[0]
        L.append(f"**Details.** {body}\n")
    return '\n'.join(L)

names=sorted(hdr.keys())
with open(_os.path.join(_WD, 'API_BODY.md'),'w') as f:
    for fn in names:
        f.write(render(fn)+'\n')
print("wrote API_BODY.md with", len(names), "entries")
