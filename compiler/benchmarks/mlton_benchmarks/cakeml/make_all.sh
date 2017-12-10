#Build the compilre
make compiler
#No clos optimizations
mkdir -p noclos
make CAKE_PREFIX=cake_ PATH_PREFIX=./noclos CAKE_FLAGS="--no_multi --no_known --no_call --max_app=1"
#No BVL optimizations
mkdir -p nobvl
make CAKE_PREFIX=cake_ PATH_PREFIX=./nobvl CAKE_FLAGS="--inline_size=0 --exp_cut=10000 --no_split"
#No register allocator
mkdir -p noalloc
make CAKE_PREFIX=cake_ PATH_PREFIX=./noalloc CAKE_FLAGS="--reg_alg=0"
#All optimizations enabled
mkdir -p all
make CAKE_PREFIX=cake_ PATH_PREFIX=./all
