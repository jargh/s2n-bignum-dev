Initial draft:

Public key generation:
private_key : byte list (LENGTH = 32)
h = sha512_pad private_key : byte list (LENGTH = 64)
bytelist_s = [(HD h) && 0b11111000] ++ SUB_LIST (1, 30) h ++ [EL 31 h && 0b01111111 || 0b01000000]
secret_s = bignum_of_bytelist bytelist_s : num
sB = group_pow edwards25519_group E_25519 secret_s : int#int
enc_A = ed25519_encode sB : num
bytelist_A = bytelist_of_num 32 enc_A

Sign:
m : byte list (LENGTH m < 2 EXP 64)
alg : num (0 for Ed25519, 1 for Ed25519ctx, 2 for Ed25519ph, else invalid)
phflag = if alg = 2 then 1 else 0 : byte
ctxt = byte list (LENGTH < 256)
dom2_prefix : byte list (LENGTH = 32)
dom2 = if alg = 0 then []
    else dom2_prefix ++ [phflag] ++ [word (LENGTH ctxt)] ++ ctxt : byte list
prefix = SUB_LIST (32, 32) h
ph = if phflag == 0 then \x.x else sha512_pad : byte list -> byte list
bytelist_r = sha512_pad (dom2 ++ prefix ++ ph(m))
r = bignum_of_bytelist bytelist_r : num
rB = group_pow edwards25519_group E_25519 r
enc_R = ed25519_encode rB : num
bytelist_R = bytelist_of_num 32 enc_R
bytelist_k = sha512_pad (dom2 ++ bytelist_R ++ bytelist_A ++ ph m)
k = bignum_of_bytelist bytelist_k : num
sig_S = (r + k * secret_s) MOD n_25519
bytelist_S = bytelist_of_num 32 sig_S
signature = bytelist_R ++ bytelist_S

Verify:
signature : byte list (LENGTH 64)
bytelist_A : byte list (LENGTH 32)
m : byte list (LENGTH < 2 EXP 64)
bytelist_R = SUB_LIST (0, 32) signature
bytelist_S = SUB_LIST (32, 32) signature
enc_R = bignum_of_bytelist bytelist_R : num
dec_R = ed25519_decode enc_R : int#int (may fail)
sig_S = bignum_of_bytelist bytelist_S : num (sig_S < n_25519 else fail)
enc_A = bignum_of_bytelist bytelist_A : num
dec_A = ed25519_decode enc_A : int#int (may fail)
bytelist_k = sha512_pad (dom2 ++ bytelist_R ++ bytelist_A ++ ph m)
k = bignum_of_bytelist bytelist_k : num
sig_SB = group_pow edwards25519_group E_25519 sig_S : int#int
kA = group_pow edwards25519_group dec_A k : int#int
expect_R = group_mul edwards25519_group sig_SB (group_inv edwards25519_group kA) : int#int
enc_expect_R = ed25519_encode expect_R
bytelist_expect_R = bytelist_of_num 32 enc_expect_R

Need:
bytelist_of_num 32 (ed25519_encode R) = bytelist_of_num 32 (ed25519_encode R') ==> R = R'