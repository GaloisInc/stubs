CC=clang 
CFLAGS= -c --target=x86_64-unknown-linux-gnu 
LINKER=/usr/local/opt/llvm@16/bin/ld.lld 
all: $(patsubst %.c, %.out,$(wildcard *.c))
%.o: %.c
	$(CC) $(CFLAGS) $< -o $@ 
%.out: %.o 
	$(LINKER) $< -o $@
clean: 
	-rm *.o *.out