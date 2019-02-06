#Cleanup
make clean

mkdir -p temp
#No clos optimisations
make CAKEFLAGS="--multi=false --known=false --call=false --max_app=1"
for f in *.cake ; do mv -- "$f" "temp/noclos_$f" ; done

#No BVL optimisations
make CAKEFLAGS="--inline_size=0 --exp_cut=10000 --split=false"
for f in *.cake ; do mv -- "$f" "temp/nobvl_$f" ; done

#No register allocator
make CAKEFLAGS="--reg_alg=0"
for f in *.cake ; do mv -- "$f" "temp/noalloc_$f" ; done

#All default optimisations enabled
make
for f in *.cake ; do mv -- "$f" "temp/all_$f" ; done

#GC debug enabled
make CAKEFLAGS="--emit_empty_ffi=true" FLAGS='-g -D"DEBUG_FFI" -o'
for f in *.cake ; do mv -- "$f" "temp/gc_$f" ; done

mv temp/* .
rm -r temp/

#TODO: this needs to be updated:
#Compilation to different targets
#mkdir -p arm8
#SKIPGCC=T make CAKE_PREFIX=cake_ PATH_PREFIX=./arm8 CAKE_FLAGS="--target=arm8"

#mkdir -p riscv
#SKIPGCC=T make CAKE_PREFIX=cake_ PATH_PREFIX=./riscv CAKE_FLAGS="--target=riscv"

#mkdir -p mips
#SKIPGCC=T make CAKE_PREFIX=cake_ PATH_PREFIX=./mips CAKE_FLAGS="--target=mips --no_jump"

#mkdir -p x64
#SKIPGCC=T make CAKE_PREFIX=cake_ PATH_PREFIX=./x64 CAKE_FLAGS="--target=x64"

#For arm6, we need the 32-bit compiler
#make compiler32
#mkdir -p arm6
#CAKECC=cake32 SKIPGCC=T make CAKE_PREFIX=cake_ PATH_PREFIX=./arm6 CAKE_FLAGS="--target=arm6 --heap_size=500 --stack_size=500"
