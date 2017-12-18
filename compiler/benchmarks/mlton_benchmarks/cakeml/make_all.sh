#Build the compiler
make compiler
#No clos optimizations
mkdir -p noclos
make CAKE_PREFIX=cake_ PATH_PREFIX=./noclos CAKE_FLAGS="--multi=false --known=false --call=false --max_app=1"
#No BVL optimizations
mkdir -p nobvl
make CAKE_PREFIX=cake_ PATH_PREFIX=./nobvl CAKE_FLAGS="--inline_size=0 --exp_cut=10000 --split=false"
#No register allocator
mkdir -p noalloc
make CAKE_PREFIX=cake_ PATH_PREFIX=./noalloc CAKE_FLAGS="--reg_alg=0"
#All optimizations enabled
mkdir -p all
make CAKE_PREFIX=cake_ PATH_PREFIX=./all

#GC debug enabled
#mkdir -p gc
#make CAKE_PREFIX=cake_ PATH_PREFIX=./gc CAKE_FLAGS="--emit_empty_ffi=true" FLAGS='-g -D"DEBUG_FFI" -o'

#Smaller heap size
#mkdir -p gc2
#make CAKE_PREFIX=cake_ PATH_PREFIX=./gc2 CAKE_FLAGS="--emit_empty_ffi=true --heap_size=100" FLAGS='-g -D"DEBUG_FFI" -o'

#Compilation to different targets
#mkdir -p arm8
#make CAKE_PREFIX=cake_ PATH_PREFIX=./arm8 CAKE_FLAGS="--target=arm8"

#mkdir -p riscv
#make CAKE_PREFIX=cake_ PATH_PREFIX=./riscv CAKE_FLAGS="--target=riscv"

#mkdir -p mips
#make CAKE_PREFIX=cake_ PATH_PREFIX=./mips CAKE_FLAGS="--target=mips --no_jump"

#mkdir -p x64
#make CAKE_PREFIX=cake_ PATH_PREFIX=./x64 CAKE_FLAGS="--target=x64"

