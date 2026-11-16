CC ?= cc
CFLAGS ?= -O2
LDLIBS += -lm

all: pancake

pancake: pancake.S basis_ffi.c
	$(CC) $(CFLAGS) $^ $(LDFLAGS) $(LDLIBS) -o $@

clean:
	$(RM) pancake

.PHONY: all clean
