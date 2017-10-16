cake: cake.S basis_ffi.c
	$(CC) $< basis_ffi.c -o $@

result: cake input.cml basis_ffi.c
	./$< <input.cml >result.S
	$(CC) result.S basis_ffi.c -o $@
