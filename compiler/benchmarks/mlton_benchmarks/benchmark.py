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

    ##Large, imperative benchmarks
    "logic",
    "mpuz",
    "ratio-regions",
    "smith-normal-form",
]
bm_iters = 20

#compiled MLs
comp_mls = {
    # MLton with and without intinf
    #"mlton" : "./sml/mlton_",
    "mlton_intinf" : "./sml/mlton_intinf_",

    # MosML compiled
    #"mosml" : "./sml/mosml_",

    # CakeML compiled
    "cakeml_all" : "./cakeml/all/cake_",
    "cakeml_noclos" : "./cakeml/noclos/cake_",
    "cakeml_nobvl" : "./cakeml/nobvl/cake_",
    "cakeml_noalloc" : "./cakeml/noalloc/cake_"

    #GC tests
    #"cakeml_gc" : "./cakeml/gc/cake_",
    #"cakeml_gc2" : "./cakeml/gc2/cake_"
    #"cakeml_gc3" : "./cakeml/gc3/cake_",
    #"cakeml_gc4" : "./cakeml/gc4/cake_",
    #"cakeml_gc5" : "./cakeml/gc5/cake_"
}

#interpreted MLs,
interp_mls = {
   #This should be a path to PolyML without --enable-intinf-as-int
   #"poly" : ("poly","./sml/"),

   ##This should be a path to PolyML with --enable-intinf-as-int
   "poly_intinf" : ("~/polyml2/poly","./sml/"),

   #Path to SMLNJ
   #"smlnj" : ("~/sml/smlnj/bin/sml @SMLalloc=100000k","./sml/"),
}

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
        timings[mls] = timecmd(cmd,bm_iters)
    #Time the interpreted ones
    for mls in interp_mls:
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
          logtime = map(np.log10,tml)
          meantime = np.mean(logtime)
          stdtime = np.std(logtime)
          pstr+=ml+" : "+str(meantime)+" , "+str(stdtime)+"\n"
  p2.write(pstr+"\n")

p2.close()

#Plotting
import pandas
import matplotlib.pyplot as plt
import numpy as np
rbm = benchmarks[::-1]
ind = np.arange(len(rbm))
ind[4::]+=1
ind[7::]+=1
ind[11::]+=1
width = 0.2

#First plot will be between polyml, mlton, cakeml all with intinfs
mls = ["mlton_intinf","poly_intinf","cakeml_all"]
mlnames = ["MLton","Poly\ML","CakeML"]
colors = ['red','green','blue']

fig, ax = plt.subplots()
rects=[]
for (mli,(ml,c)) in enumerate(zip(mls,colors)):
    bmt = []
    for bm in rbm:
        if (not(mltimes[ml].has_key(bm))):
            bmt += [(0.0,0.0)]
        else:
            if mltimes[ml][bm] == None:
                bmt += [(0.0,0.0)]
            else:
                bmt+= [mltimes[ml][bm]]
    bmt1 = [i for (i,j) in bmt]
    bmt2 = [j for (i,j) in bmt]
    (bmt1,bmt2)
    #rects+=[ax.barh(ind+mli*width,bmt1, width, color=c, xerr=bmt2)]
    rects+=[ax.barh(ind+mli*width,bmt1, width, color=c)]

plt.xscale('log')
ax.set_yticks(ind+(len(mls)-1)*width/2)
ax.set_yticklabels(tuple(rbm))
#ax.set(yticks=ind + width, yticklabels=df.graph, ylim=[2*width - 1, len(df)])
lgd = ax.legend(rects,mlnames, loc='upper center', ncol=len(mls), bbox_to_anchor=(0.5,1.10))

plt.tight_layout()
plt.savefig('plot1noerr.svg',bbox_extra_artists=(lgd,),bbox_inches='tight')

fig, ax = plt.subplots()
rects=[]
for (mli,(ml,c)) in enumerate(zip(mls,colors)):
    bmt = []
    for bm in rbm:
        if (not(mltimes[ml].has_key(bm))):
            bmt += [(0.0,0.0)]
        else:
            if mltimes[ml][bm] == None:
                bmt += [(0.0,0.0)]
            else:
                bmt+= [mltimes[ml][bm]]
    bmt1 = [i for (i,j) in bmt]
    bmt2 = [j for (i,j) in bmt]
    (bmt1,bmt2)
    rects+=[ax.barh(ind+mli*width,bmt1, width, color=c, xerr=bmt2)]

plt.xscale('log')
ax.set_yticks(ind+(len(mls)-1)*width/2)
ax.set_yticklabels(tuple(rbm))
#ax.set(yticks=ind + width, yticklabels=df.graph, ylim=[2*width - 1, len(df)])
lgd = ax.legend(rects,mlnames, loc='upper center', ncol=len(mls), bbox_to_anchor=(0.5,1.10))

plt.tight_layout()
plt.savefig('plot1werr.svg',bbox_extra_artists=(lgd,),bbox_inches='tight')

#Second plot will be CakeML vs CakeML plots
mls = ["cakeml_noclos","cakeml_nobvl","cakeml_noalloc","cakeml_all"]
mlnames = ["CO","BO","RA","All"]
colors = ['0.5','red','green','blue']

fig, ax = plt.subplots()
rects=[]
for (mli,(ml,c)) in enumerate(zip(mls,colors)):
    bmt = []
    for bm in rbm:
        if (not(mltimes[ml].has_key(bm))):
            bmt += [(0.0,0.0)]
        else:
            if mltimes[ml][bm] == None:
                bmt += [(0.0,0.0)]
            else:
                bmt+= [mltimes[ml][bm]]
    bmt1 = [i for (i,j) in bmt]
    bmt2 = [j for (i,j) in bmt]
    (bmt1,bmt2)
    #rects+=[ax.barh(ind+mli*width,bmt1, width, color=c, xerr=bmt2)]
    rects+=[ax.barh(ind+mli*width,bmt1, width, color=c)]

plt.xscale('log')
ax.set_yticks(ind+(len(mls)-1)*width/2)
ax.set_yticklabels(tuple(rbm))
#ax.set(yticks=ind + width, yticklabels=df.graph, ylim=[2*width - 1, len(df)])
lgd = ax.legend(rects,mlnames, loc='upper center', ncol=len(mls), bbox_to_anchor=(0.5,1.10))

plt.tight_layout()
plt.savefig('plot2noerr.svg',bbox_extra_artists=(lgd,),bbox_inches='tight')


fig, ax = plt.subplots()
rects=[]
for (mli,(ml,c)) in enumerate(zip(mls,colors)):
    bmt = []
    for bm in rbm:
        if (not(mltimes[ml].has_key(bm))):
            bmt += [(0.0,0.0)]
        else:
            if mltimes[ml][bm] == None:
                bmt += [(0.0,0.0)]
            else:
                bmt+= [mltimes[ml][bm]]
    bmt1 = [i for (i,j) in bmt]
    bmt2 = [j for (i,j) in bmt]
    (bmt1,bmt2)
    rects+=[ax.barh(ind+mli*width,bmt1, width, color=c, xerr=bmt2)]

plt.xscale('log')
ax.set_yticks(ind+(len(mls)-1)*width/2)
ax.set_yticklabels(tuple(rbm))
#ax.set(yticks=ind + width, yticklabels=df.graph, ylim=[2*width - 1, len(df)])
lgd = ax.legend(rects,mlnames, loc='upper center', ncol=len(mls), bbox_to_anchor=(0.5,1.10))

plt.tight_layout()
plt.savefig('plot2werr.svg',bbox_extra_artists=(lgd,),bbox_inches='tight')


#import pickle
#pickle_out = open("dict.pickle","wb")
#pickle.dump(bmdict,pickle_out)
#pickle_out.close()

