#!/usr/bin/env python
import os
import time
import subprocess
import numpy as np
from os import system

#Our micro benchmarks
benchmarks = ["btree","fib","foldl","nqueens","qsortimp","qsort","queue","reverse"]
bm_iters = 20

#ML version to expected prefix
comp_mls = {
    "cakeO4": "./cakeml/cake_O4_",
    #"ocamlc": "./ocaml/ocamlc_",
    "ocamlopt": "./ocaml/ocamlopt_",
    "polyc": "./sml/polyc_",
    "mlton": "./sml/mlton_"
}

def timecmd(cmd,iters,bmin=None):
    print("Timing " +str(cmd))
    print(str(iters)+" Iterations")
    times = []
    for i in range(0,iters):
        start = time.time()
        system(cmd)
        end = time.time()
        print(end-start)
        times.append(end-start)
    return times

bmdict = {}
for bm in benchmarks:
    timings = {}
    #Time the compiled ones
    for mls in comp_mls:
        cmd = comp_mls[mls]+bm
        timings[mls] = timecmd(cmd,bm_iters)
    #SMLNJ is interpreted
    cmd = "sml @SMLalloc=100000k < ./sml/sml_"+bm+"> /dev/null"
    timings["smlnj"] = timecmd(cmd,bm_iters)
    bmdict[bm] = timings

#Plot CakeML vs other ML graph
p2 = open('bm2.dat', 'w')
for bm in bmdict:
  #All other numbers are normalised to this
  times = bmdict[bm]
  norm = np.mean(times["ocamlopt"])
  pstr=bm
  for ml in ["ocamlopt","mlton","smlnj","polyc","cakeO4"]:
      maxtime = max(times[ml])/norm
      mintime = min(times[ml])/norm
      meantime = np.mean(times[ml])/norm
      pstr+=","+str(meantime)+","+str(mintime)+","+str(maxtime)
  p2.write(pstr+"\n")

p2.close()

system('gnuplot plot_benchmarks2.gplot')

print('Graph plotted at compiler/benchmarks/benchmarks2.eps')
