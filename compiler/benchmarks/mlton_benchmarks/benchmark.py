#!/usr/bin/env python
import os
import time
import subprocess
import numpy as np
from os import system

#The benchmarks to test
benchmarks = [
    #Small, pure benchmarks
    "even-odd",
    "fib",
    "merge",
    "tailfib",
    "tak",

    #Small, imperative benchmarks
    "flat-array",
    "imp-for",
    "vector-concat",
    "vector-rev",

    #Large, pure benchmarks
    "knuth-bendix",
    "life",
    "pidigits",

    #Large, imperative benchmarks
    "logic",
    "mpuz",
    "ratio-regions",
    "smith-normal-form",
]
bm_iters = 20

#compiled MLs
comp_mls = {
    # MLton with and without intinf
    "mlton" : "./sml/mlton_",
    "mlton_intinf" : "./sml/mlton_intinf_",

    ## MosML compiled
    "mosml" : "./sml/mosml_",

    ## CakeML compiled
    "cakeml_all" : "./cakeml/all/cake_",
    "cakeml_noclos" : "./cakeml/noclos/cake_",
    "cakeml_nobvl" : "./cakeml/nobvl/cake_",
    "cakeml_noalloc" : "./cakeml/noalloc/cake_"

    #GC tests
    #"cakeml_gc" : "./cakeml/gc/cake_",
    #"cakeml_gc2" : "./cakeml/gc2/cake_",
    #"cakeml_gc3" : "./cakeml/gc3/cake_",
}

#interpreted MLs,
interp_mls = {
   #This should be a path to PolyML without --enable-intinf-as-int
   "poly" : ("poly","./sml/"),

   ##This should be a path to PolyML with --enable-intinf-as-int
   "poly_intinf" : ("~/polyml2/poly","./sml/"),

   #Path to SMLNJ
   "smlnj" : ("~/sml/smlnj/bin/sml @SMLalloc=100000k","./sml/"),
}

#Exclude SML/NJ and MosML on the IntInf benchmarks because they either take
#forever (>200s) to run, or fail to compile entirely
exclude = [
  ("smlnj","smith-normal-form"),("smlnj","pidigits"),
  ("mosml","smith-normal-form"),("mosml","pidigits"),
]

def timecmd(cmd,iters,bmin=None):
    print("Timing " +str(cmd))
    print(str(iters)+" Iterations")
    times = []
    for i in range(0,iters):
        start = time.time()
        ret = system(cmd)
        end = time.time()
        if ret == 0:
            print(end-start)
            times.append(end-start)
        else:
            return None
    return times

bmdict = {}
for bm in benchmarks:
    timings = {}
    #Time the compiled ones
    for mls in comp_mls:
        cmd = comp_mls[mls]+bm
        if ((mls,bm) in exclude):
            timings[mls] = None
        else:
            timings[mls] = timecmd(cmd,bm_iters)
    #Time the interpreted ones
    for mls in interp_mls:
        if ((mls,bm) in exclude):
            timings[mls] = None
        else:
            (execp,path) = interp_mls[mls]
            cmd = execp+" < "+path+bm+".sml > /dev/null"
            timings[mls] = timecmd(cmd,bm_iters)
    bmdict[bm] = timings

#Invert the mapping
mls = comp_mls.keys() + interp_mls.keys()
mltimes = {}
for ml in mls:
    mltimes[ml] = {}
    for bm in benchmarks:
        tml = bmdict[bm][ml]
        if tml == None:
            mltimes[ml][bm] = None
        else:
            logtime = tml #map(np.log10,tml)
            meantime = np.mean(logtime)
            stdtime = np.std(logtime)
            mltimes[ml][bm] = (meantime,stdtime)

#Dump to log file
p2 = open('all.dat', 'w')
for bm in benchmarks:
  times = bmdict[bm]
  pstr=bm+"\n"
  for ml in times.keys():
      tml = times[ml]
      if tml == None:
          pstr+=ml+" : Failed\n"
      else:
          logtime = tml
          meantime = np.mean(logtime)
          stdtime = np.std(logtime)
          pstr+=ml+" : "+str(meantime)+" , "+str(stdtime)+"\n"
  p2.write(pstr+"\n")

p2.close()

#Plotting
import pandas
import matplotlib
import matplotlib.pyplot as plt
import numpy as np
matplotlib.rcParams['hatch.linewidth']=0.5
rbm = benchmarks[::-1]
ind = np.arange(len(rbm))*5
fs = (8,8)
ind[4::]+=2
ind[7::]+=2
ind[11::]+=2
width = 1.0

#First plot will be between polyml, mlton, cakeml all with intinfs
mls = ["mlton_intinf","poly_intinf","cakeml_all"]
normalizer = "cakeml_all"
mlnames = ["MLton (IntInf)","Poly/ML (IntInf)","CakeML"]
colors = ['red','green','blue']
hatches = ['||','///','\\\\\\']

fig, ax = plt.subplots(figsize=fs)
rects=[]
for (mli,(ml,c,h)) in enumerate(zip(mls,colors,hatches)):
    bmt = []
    for bm in rbm:
        (normavg,normstd) = mltimes[normalizer][bm]
        if (not(mltimes[ml].has_key(bm))):
            bmt += [(0.0,0.0)]
        else:
            if mltimes[ml][bm] == None:
                bmt += [(0.0,0.0)]
            else:
                (l,r) = mltimes[ml][bm]
                bmt+= [(l/normavg,r/normstd)]
    bmt1 = [i for (i,j) in bmt]
    bmt2 = [j for (i,j) in bmt]
    (bmt1,bmt2)
    rects+=[ax.barh(ind+mli*width,bmt1, width, fill=False, color=c, edgecolor=c, hatch=h)]
    ax.barh(ind+mli*width,bmt1, width, fill=False, color=c, edgecolor='black')

plt.xscale('log')
ax.set_yticks(ind+(len(mls)-1)*width/2)
ax.set_yticklabels(tuple(rbm))
lgd = ax.legend(rects,mlnames, loc='upper center', ncol=len(mls), bbox_to_anchor=(0.5,1.05))

plt.tight_layout()
plt.savefig('plot1noerr.svg',bbox_extra_artists=(lgd,),bbox_inches='tight')

#Second plot will be between all the MLs without intinfs
#Fill in solid bars for the 'intinf' ones
ind = np.arange(len(rbm))*8
fs = (8,8)
mls = ["smlnj","mosml","mlton","poly","cakeml_all"]
has_inf = [False,False,True,True,False]
inf_suffix = '_intinf'
normalizer = "cakeml_all"
mlnames = ["SML/NJ","Moscow ML","MLton","Poly/ML","CakeML"]
colors = ['0.1','0.5','red','green','blue']
hatches = ['********','xxxxxxxx','||','///','\\\\\\']

fig, ax = plt.subplots(figsize=fs)
rects=[]
for (mli,(ml,hi,c,h)) in enumerate(zip(mls,has_inf,colors,hatches)):
    bmt = []
    bmt3 = []
    for bm in rbm:
        (normavg,normstd) = mltimes[normalizer][bm]
        if (not(mltimes[ml].has_key(bm))):
            bmt += [(0.0,0.0)]
            bmt3 += [0.0]
        else:
            if mltimes[ml][bm] == None:
                bmt += [(0.0,0.0)]
                bmt3 += [0.0]
            else:
                (l,r) = mltimes[ml][bm]
                bmt+= [(l/normavg,r/normstd)]
                if hi:
                    (l,r) = mltimes[ml+inf_suffix][bm]
                    bmt3 += [l/normavg]
                else:
                    bmt3 +=[l/normavg]
    bmt1 = [i for (i,j) in bmt]
    bmt2 = [j for (i,j) in bmt]
    (bmt1,bmt2)
    sub = [j-i for (i,j) in zip(bmt1,bmt3)]
    rects+=[ax.barh(ind+mli*width,bmt1, width, fill=False, color=c, edgecolor=c, hatch=h)]
    ax.barh(ind+mli*width,sub, width, fill=True, color=c, edgecolor=c, hatch=h, left = bmt1)
    ax.barh(ind+mli*width,bmt3, width, fill=False, color=c, edgecolor='black')

plt.xscale('log')
ax.set_yticks(ind+(len(mls)-1)*width/2)
ax.set_yticklabels(tuple(rbm))
lgd = ax.legend(rects,mlnames, loc='upper center', ncol=len(mls), bbox_to_anchor=(0.5,1.05))

plt.tight_layout()
plt.savefig('plot2noerr.svg',bbox_extra_artists=(lgd,),bbox_inches='tight')

#Third plot will be CakeML vs CakeML plots
ind = np.arange(len(rbm))*6
fs = (8,8)
mls = ["cakeml_noclos","cakeml_nobvl","cakeml_noalloc","cakeml_all"]
mlnames = ["CO","BO","RA","All"]
colors = ['0.5','red','green','blue']
hatches = ['xxxxxxxx','||','///','\\\\\\']

fig, ax = plt.subplots(figsize=fs)
rects=[]
for (mli,(ml,c,h)) in enumerate(zip(mls,colors,hatches)):
    bmt = []
    for bm in rbm:
        (normavg,normstd) = mltimes[normalizer][bm]
        if (not(mltimes[ml].has_key(bm))):
            bmt += [(0.0,0.0)]
        else:
            if mltimes[ml][bm] == None:
                bmt += [(0.0,0.0)]
            else:
                (l,r) = mltimes[ml][bm]
                bmt+= [(l/normavg,r/normstd)]
    bmt1 = [i for (i,j) in bmt]
    bmt2 = [j for (i,j) in bmt]
    (bmt1,bmt2)
    rects+=[ax.barh(ind+mli*width,bmt1, width, fill=False, color=c, edgecolor=c, hatch=h)]
    ax.barh(ind+mli*width,bmt1, width, fill=False, color=c, edgecolor='black')

plt.xscale('log')
ax.set_yticks(ind+(len(mls)-1)*width/2)
ax.set_yticklabels(tuple(rbm))
lgd = ax.legend(rects,mlnames, loc='upper center', ncol=len(mls), bbox_to_anchor=(0.5,1.05))

plt.tight_layout()
plt.savefig('plot3noerr.svg',bbox_extra_artists=(lgd,),bbox_inches='tight')
