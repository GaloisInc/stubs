CC=clang 
CFLAGS= -c --target=x86_64-unknown-linux-gnu 
LINKER=/usr/local/opt/llvm@16/bin/ld.lld 
all: a.out mult.out mult_i.out two.out
a.out: malloc_test.o 
	$(LINKER) malloc_test.o
malloc_test.o: 
	$(CC) $(CFLAGS) malloc_test.c -o malloc_test.o 
mult.out: multiple_ov.o 
	$(LINKER) multiple_ov.o -o mult.out
multiple_ov.o: 
	$(CC) $(CFLAGS) multiple_ov.c -o multiple_ov.o 
mult_i.out: multiple_ov_i.o
	$(LINKER) multiple_ov_i.o -o mult_i.out
multiple_ov_i.o:
	$(CC) $(CFLAGS) multiple_ov_i.c -o multiple_ov_i.o
two_override.o:
	$(CC) $(CFLAGS) two_override.c -o two_override.o
two.out: two_override.o
	$(LINKER) two_override.o -o two.out
clean: 
	-rm *.o *.out