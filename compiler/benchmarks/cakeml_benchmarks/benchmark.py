#!/usr/bin/env python
import os
import time
import subprocess
import numpy as np
from os import system
from threading import Timer

#The benchmarks to test
benchmarks = [
  "fib",
  "foldl",
  "reverse",
  "nqueens",
  "queue",
  "btree",
  "qsort",
  "qsortimp",
  "array_contain",
  "dummy_contain",
  "bst_contain",
  "sptree_contain",
]

#Benchmark iterations
bm_iters = 5

#Benchmark timeouts (in seconds)
bm_timeout = 120

# Format: key -> (path,suffix)
#compiled MLs
comp_mls = {
  # MLton with and without intinf
  "mlton"          : ("./sml/mlton_",""),
  "mlton_intinf"   : ("./sml/mlton_intinf_",""),

  # MosML compiled
  "mosml"          : ("./sml/mosml_",""),

  # OCaml compiled
  "ocamlopt"       : ("./ocaml/ocamlopt_",""),
  "ocamlc"         : ("./ocaml/ocamlc_",""),

  # CakeML compiled
  "cakeml_all"     : ("./cakeml/all_",".cake"),
  "cakeml_noclos"  : ("./cakeml/noclos_",".cake"),
  "cakeml_nobvl"   : ("./cakeml/nobvl_",".cake"),
  "cakeml_noalloc" : ("./cakeml/noalloc_",".cake"),

  #GC tests
  #"cakeml_gc"      : ("./cakeml/gc_",".cake")
}

#Format: key -> (interpreter executable, extra arguments, path, suffix)
#interpreted MLs
interp_mls = {
  #This should be a path to PolyML without --enable-intinf-as-int
  "poly" : ("poly","--use","./sml/",".sml"),

  #This should be a path to PolyML with --enable-intinf-as-int
  #"poly_intinf" : ("~/polyml2/poly","--use","./sml/",".sml"),

  #Path to SMLNJ
  "smlnj" : ("sml","@SMLalloc=100000k", "./sml/",".sml"),
}

#Exclude benchmarks
exclude = [
]

kill = lambda process: process.kill()

def timecmd(cmd,iters):
  print("Timing " +str(cmd))
  print(str(iters)+" Iterations")
  times = []
  for i in range(0,iters):
    start = time.time()
    try:
      proc = subprocess.Popen(cmd,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    except:
      print("failed to execute benchmark")
      return None
    try:
      timer = Timer(bm_timeout, kill, [proc])
      timer.start()
      stdout, stderr = proc.communicate()
    finally:
      timer.cancel()

    end = time.time()
    ret = proc.returncode
    if ret == 0:
      print(end-start)
      times.append(end-start)
    else:
      print("benchmark timed out or did not return successfully")
      return None
  return times

bmdict = {}
for bm in benchmarks:
    timings = {}
    #Time the compiled ones
    for mls in comp_mls:
        if ((mls,bm) in exclude):
            timings[mls] = None
        else:
            (path,suffix) = comp_mls[mls]
            cmd = path+bm+suffix
            timings[mls] = timecmd(cmd,bm_iters)
    #Time the interpreted ones
    for mls in interp_mls:
        if ((mls,bm) in exclude):
            timings[mls] = None
        else:
            (execp,arg,path,suffix) = interp_mls[mls]
            cmd = [execp,arg,path+bm+suffix]
            timings[mls] = timecmd(cmd,bm_iters)
    bmdict[bm] = timings

import pickle
pickle.dump(bmdict,open("bmdict.pickle","w"))

#import pickle
#bmdict = pickle.load(open("bmdict.pickle","rb"))

#Invert the mapping
mls = list(comp_mls.keys()) + list(interp_mls.keys())
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
p2 = open('cakeml_all.dat', 'w')
for bm in benchmarks:
  times = bmdict[bm]
  pstr=bm+"\n"
  for ml in sorted(times.keys()):
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
import matplotlib
import matplotlib.pyplot as plt
import numpy as np
matplotlib.rcParams['hatch.linewidth']=0.5
rbm = benchmarks[::-1]
ind = np.arange(len(rbm))*5
fs = (12,12)
width = 1.0

#Configuration for annotations
label_size = 12
xoffset=-110
xoffsett=-130
heightmul = 31
offset = 19
axh = 1.55
lenB = 11.2

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
    if(not(mltimes[normalizer][bm]==None)):
      (normavg,normstd) = mltimes[normalizer][bm]
    else:
      print("normalizing "+bm+" against: "+normalizer+", but numbers not found. Setting to maximum value: "+ str(bm_timeout))
      (normavg,normstd) = (bm_timeout,0.0)
    if (ml not in mltimes or bm not in mltimes[ml] or mltimes[ml][bm] == None):
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
ax.set_yticklabels(tuple(rbm),fontsize=label_size)
lgd = ax.legend(rects,mlnames, loc='upper center', ncol=len(mls), bbox_to_anchor=(0.5,1.05), fontsize=label_size)

plt.tight_layout()
plt.savefig('cakeml_plot1noerr.svg',bbox_extra_artists=(lgd,),bbox_inches='tight')

#Second plot will be between all the MLs without intinfs
#Fill in solid bars for the 'intinf' ones
ind = np.arange(len(rbm))*10
fs = (12,16)
mls = ["smlnj","mosml","ocamlc","ocamlopt","mlton","poly","cakeml_all"]
has_inf = [False,False,False,False,True,True,False]
inf_suffix = '_intinf'
normalizer = "cakeml_all"
mlnames = ["SML/NJ","Moscow ML","OCaml","OCaml(Opt)","MLton","Poly/ML","CakeML"]
colors = ['0.1','0.5','0.5','0.5','red','green','blue']
hatches = ['********','xxxxxxxx','','\|\|','||','///','\\\\\\']

fig, ax = plt.subplots(figsize=fs)
rects=[]
for (mli,(ml,hi,c,h)) in enumerate(zip(mls,has_inf,colors,hatches)):
  bmt = []
  bmt3 = []
  for bm in rbm:
    if(not(mltimes[normalizer][bm]==None)):
      (normavg,normstd) = mltimes[normalizer][bm]
    else:
      print("normalizing "+bm+" against: "+normalizer+", but numbers not found. Setting to maximum value: "+ str(bm_timeout))
      (normavg,normstd) = (bm_timeout,0.0)
    if (ml not in mltimes or bm not in mltimes[ml] or mltimes[ml][bm] == None):
      bmt += [(0.0,0.0)]
      bmt3 += [0.0]
    else:
      (l,r) = mltimes[ml][bm]
      bmt+= [(l/normavg,r/normstd)]
      if hi and (ml+inf_suffix) in mltimes and not(mltimes[ml+inf_suffix][bm]==None) :
        (ll,rr) = mltimes[ml+inf_suffix][bm]
        if ll > l:
          bmt3 += [ll/normavg]
        else:
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
ax.set_yticklabels(tuple(rbm),fontsize=label_size)
lgd = ax.legend(rects,mlnames, loc='upper center', ncol=len(mls), bbox_to_anchor=(0.5,1.05), fontsize=label_size)

plt.tight_layout()
plt.savefig('cakeml_plot2noerr.svg',bbox_extra_artists=(lgd,),bbox_inches='tight')

#Third plot will be CakeML vs CakeML plots
ind = np.arange(len(rbm))*6
fs = (12,12)
mls = ["cakeml_noclos","cakeml_nobvl","cakeml_noalloc","cakeml_all"]
mlnames = ["CO","BO","RA","All"]
colors = ['0.5','red','green','blue']
hatches = ['xxxxxxxx','||','///','\\\\\\']

fig, ax = plt.subplots(figsize=fs)
rects=[]
for (mli,(ml,c,h)) in enumerate(zip(mls,colors,hatches)):
  bmt = []
  for bm in rbm:
    if(not(mltimes[normalizer][bm]==None)):
      (normavg,normstd) = mltimes[normalizer][bm]
    else:
      print("normalizing "+bm+" against: "+normalizer+", but numbers not found. Setting to maximum value: "+ str(bm_timeout))
      (normavg,normstd) = (bm_timeout,0.0)
    if (ml not in mltimes or bm not in mltimes[ml] or mltimes[ml][bm] == None):
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
ax.set_yticklabels(tuple(rbm),fontsize=label_size)
lgd = ax.legend(rects,mlnames, loc='upper center', ncol=len(mls), bbox_to_anchor=(0.5,1.05), fontsize=label_size)

plt.tight_layout()
plt.savefig('cakeml_plot3noerr.svg',bbox_extra_artists=(lgd,),bbox_inches='tight')
