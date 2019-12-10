# Links the CakeML compiler and compiles all the .cml files in this directory
all: yes$(SUFF)

# Linking the CakeML compiler

yes$(SUFF): yes.o yes_ffi.o
	$(CC) $(LDFLAGS) $< yes_ffi.o $(LOADLIBES) $(LDLIBS) -o $@

clean:
	$(RM) yes_ffi.o yes.o yes$(SUFF)
