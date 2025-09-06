import os
import string
import subprocess
import time
import random

##########################################################################
# Python script to evaluate efficiency of compression binary against zip #
##########################################################################

# CHANGE TO MATCH YOUR SETUP
os.chdir("/home/ericcur/git/chalmers/cakeml/examples/deflate/translation/compilation")

# CHANGE DEPENDING ON WHICH BINARY YOU WANT TO TEST
arg = "./deflateEncode"
#arg = "zip"

encoding = 'cp437'


res = []
check = []
os.chdir("./tests")
files = [f for f in os.listdir('.') if os.path.isfile(f)]
files.sort()
os.chdir("..")

# CHECKS WHETHER A TEXT HAS THE PREFIX "Compressed: "
def check_compressed(bytes):
    return bytes.decode(encoding).startswith("Compressed: ")


# COMPRESSES THE FILES IN ./tests
def test_files():
    for f in files:
        inp = open('tests/' + f)
        start_time = time.time_ns()
        li = os.stat('tests/' + f).st_size
        print(f"{f}  - {li/1000} kb:")
        p = subprocess.Popen(arg, stdout=subprocess.PIPE, stdin=inp)
        o, i = p.communicate()
        t = time.time_ns() - start_time
        t = t / 1000000
        lo = len(o) - 12
        ratio = round((lo/li)*100)
        c = check_compressed(o)
        res.append((f, c, t))
        print(f" {c}, in {t} ms - {ratio}%")
        check.append(c)


# GENERATES AND COMPRESSES RANDOM FILES
def test_random_text(n):
    for i in range(0,n):
        r = random.randint(100,21000)
        s = os.urandom(r)
        initlen = len(s)
        start_time = time.time_ns()
        p = subprocess.run(arg, stdout=subprocess.PIPE, input=s)
        t = time.time_ns() - start_time
        t = t / 1000000
        finlen = len(p.stdout)
        ratio = round(((finlen-12) / initlen) * 100)
        c = check_compressed(p.stdout)
        res.append(c)
        print(f"Random text of length {str(r)}: {c}, in {t} ms - {ratio}%")


test_files()
test_random_text(100)
print(f"{sum(check)}/{len(check)}")
