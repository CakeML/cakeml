cake: cake.o basis_ffi.o

result.S: input.cml cake
	./cake <$< >$@

result: result.o basis_ffi.o
