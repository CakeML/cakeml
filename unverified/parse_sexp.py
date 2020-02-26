
import re

paren_split_re = re.compile (r''' ( \( | \) ) ''', re.X)

def parse_sec (s, state):
  for bit in paren_split_re.split (s):
    if bit == '(':
      state.append ([])
    elif bit == ')':
      paren = state.pop ()
      state[-1].append (tuple (paren))
    else:
      for tok in bit.split ():
        state[-1].append (('tok', tok))

def tokens (ss):
  toks = []
  for s in ss:
    qs = [-1]
    bss = 0
    for (i, c) in enumerate (s):
      if c == '\\':
        bss += 1
        continue
      prev_bss = bss
      bss = 0
      if c != '"':
        continue
      if prev_bss % 2 != 0:
        continue
      qs.append (i)
      sec = s[qs[-2] + 1 : i]
      if len (qs) % 2 == 0:
        toks.extend (paren_split_re.split (sec))
      else:
        sec = '"'.join (sec.split ('\\"'))
        sec = '\\'.join (sec.split ('\\\\'))
        toks.append (('str', sec))
    assert len (qs) % 2 != 0, 'mismatched quotes'
    sec = s[qs[-1] + 1 :]
    toks.extend (paren_split_re.split (sec))
  return toks

atom_kinds = set (['str', 'tok'])

def is_atom (sexp):
  return len (sexp) == 2 and sexp[0] in atom_kinds

def parse (ss):
  toks = tokens (ss)
  state = [[]]
  for t in toks:
    if is_atom (t):
      state[-1].append (t)
    elif t == '(':
      state.append ([])
    elif t == ')':
      paren = state.pop ()
      state[-1].append (tuple (paren))
    else:
      for bit in t.split ():
        state[-1].append (('tok', bit))
  assert len (state) == 1, ("mismatched parens", len (state))
  return tuple (state[0])

def get_decs (sexp):
  if is_atom (sexp):
    return []
  if not sexp:
    return []
  xs = []
  if sexp[0] == ('tok', 'Dlet'):
    (_, _, nm, body) = sexp
    xs = [(nm, body)]
  elif sexp[0] == ('tok', 'Dletrec'):
    (_, _, bodies) = sexp
    xs = [(v[0], v[-1]) for v in bodies]
  for x in sexp:
    xs.extend (get_decs (x))
  return xs

def count_toks (sexp, toknames):
  if is_atom (sexp):
    if sexp[0] == 'tok' and sexp[1] in toknames:
      return 1
    return 0
  return sum ([count_toks (x, toknames) for x in sexp])

def sort_pcons (sexp):
  con_s = set (["Pcon"])
  data = [(count_toks (body, con_s), nm) for (nm, body) in get_decs (sexp)]
  data.sort ()
  return data

def print_pcons (data, n = None):
  if n == 0:
    return
  if n == None:
    n = 0
  for (count, nm_atom) in reversed (data[- n:]):
    print ('%s: %d' % (nm_atom[1], count))

import argparse

def main ():
  parser = argparse.ArgumentParser(description=
    'Parse and analyse a CakeML s-expression')
  parser.add_argument ('FILES', nargs='+', help='files to process')
  parser.add_argument ('--pcons', type=int, nargs='?', const='20', default=None,
    metavar='N', help='list N (=20) functions with most Pcon pattern-matches')
  args = parser.parse_args ()
  for fname in args.FILES:
    sexp = parse (open (fname))
    if args.pcons:
      print_pcons (sort_pcons (sexp), args.pcons)

if __name__ == '__main__':
  main ()








