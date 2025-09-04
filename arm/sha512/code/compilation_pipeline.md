gcc -O3 -fno-builtin -march=armv8-a+nosimd -fno-ipa-cp -c sha512.c -S -o sha512.S
replace .LANCHOR0 with K
remove the line: 	.set	.LANCHOR0,. + 0
Copy sha512.S and rename the copy sha512_asm.S
Manually write the assembly code for sha512_update and sha512_final
gcc -c -o sha512.o sha512.S

In test folder,
gcc test_sha512.c ../tweetnacl_sha512.c ../sha512_asm.S -o test.out
run test.out