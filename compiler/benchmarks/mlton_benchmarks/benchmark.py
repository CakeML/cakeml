#!/usr/bin/env python
import os
import time
import subprocess
import numpy as np
from os import system

#The benchmarks to test
benchmarks = [
    "even-odd",
    "fib",
    "flat-array",
    "imp-for",
    "knuth-bendix",
    "life",
    "logic",
    "merge",
    "mpuz",
    "pidigits",
    "ratio-regions",
    "smith-normal-form",
    "tailfib",
    "tak",
    "vector-concat",
    "vector-rev"
]
bm_iters = 20

#compiled MLs
comp_mls = {
    "mlton" : "./sml/mlton_",
    "mlton_intinf" : "./sml/mlton_intinf_",
    "cakeml_all" : "./cakeml/all/cake_",
    "cakeml_noclos" : "./cakeml/noclos/cake_",
    "cakeml_nobvl" : "./cakeml/nobvl/cake_",
    "cakeml_noalloc" : "./cakeml/noalloc/cake_"
}

#interpreted MLs,
interp_mls = {
   #This should be a path to PolyML without --enable-intinf-as-int
   #"poly" : ("poly","./sml/"),
   #This should be a path to PolyML with --enable-intinf-as-int
   "poly" : ("~/polyml2/poly","./sml/"),
   #"smlnj" : ("sml @SMLalloc=10000k","./sml/"),
   #This doesn't quite work:
   #"smlnj_intinf" : ("sml @SMLload=intinf.x86-linux","./sml/"),
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
    #Time the interpreted ones
    for mls in interp_mls:
        (execp,path) = interp_mls[mls]
        cmd = execp+" < "+path+bm+".sml > /dev/null"
        timings[mls] = timecmd(cmd,bm_iters)
    bmdict[bm] = timings

p2 = open('all.dat', 'w')
for bm in bmdict:
  #All other numbers are normalised to this
  times = bmdict[bm]
  pstr=bm+"\n"
  for ml in times.keys():
      maxtime = max(times[ml])
      mintime = min(times[ml])
      meantime = np.mean(times[ml])
      pstr+=ml+":"+str(meantime)+","+str(mintime)+","+str(maxtime)+"\n"
  p2.write(pstr+"\n")

p2.close()


