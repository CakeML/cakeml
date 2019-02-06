#Cleanup
make clean
rm -rf noclos/ nobvl/ noalloc/ all/ gc/

#No clos optimizations
mkdir -p noclos
make CAKEFLAGS="--multi=false --known=false --call=false --max_app=1"
mv *.cake noclos/

#No BVL optimizations
mkdir -p nobvl
make CAKEFLAGS="--inline_size=0 --exp_cut=10000 --split=false"
mv *.cake nobvl/

#No register allocator
mkdir -p noalloc
make CAKEFLAGS="--reg_alg=0"
mv *.cake noalloc/

#All default optimizations enabled
mkdir -p all
make
mv *.cake all/

#GC debug enabled
mkdir -p gc
make CAKEFLAGS="--emit_empty_ffi=true" FLAGS='-g -D"DEBUG_FFI" -o'
make
mv *.cake gc/

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
