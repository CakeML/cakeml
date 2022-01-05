
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

def count_toks (sexp, toknames):
  q = [sexp]
  count = 0
  while q:
    x = q.pop()
    if is_atom (x):
      if x[0] == 'tok' and x[1] in toknames:
        count += 1
    else:
      q.extend(x)
  return count

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

def scan_defined (sexp, context, hidden = False, quiet = False):
  tys = set ()
  vals = set ()
  if is_atom(sexp):
    # this is allowed, e.g. 'nil' can appear in either part of Dlocal
    return (tys, vals)
  for x in sexp:
    if x[0] == ('tok', 'Dtype'):
      (_, _, tydefs) = x
      for v in tydefs:
        (_, nm) = v[:2]
        tys.add (nm)
    elif x[0] == ('tok', 'Dlocal'):
      (_, loc, glob) = x
      scan_defined (loc, context + ['<local>'], hidden = True)
      (tys2, vals2) = scan_defined (glob, context, quiet = True)
      tys.update(tys2)
      vals.update(vals2)
    elif x[0] == ('tok', 'Dmod'):
      (_, nm, contents) = x
      scan_defined (contents, context + [nm])
    elif x[0] == ('tok', 'Dlet'):
      (_, _, nm, body) = x
      vals.add (nm)
    elif x[0] == ('tok', 'Dletrec'):
      (_, _, bodies) = x
      for v in bodies:
        vals.add (v[0])
  if not quiet:
    print ("types defined at %s: %s" % (context, tys))
    print ("vals defined at %s: %s" % (context, vals))
  return (tys, vals)

def print_defined (sexp):
  for x in sexp:
    scan_defined (x, [])

def printd (depth, s):
  print ((' ' * depth) + s)

def addh (hidden, s):
  if hidden:
    return '<hidden> ' + s
  else:
    return s

def printdh (depth, hidden, s):
  printd (depth, addh (hidden, s))

def atom_name (sexp):
  assert is_atom(sexp), ("atom_name", sexp)
  return sexp[1]

def format_defined (sexp, depth, hidden):
  if is_atom(sexp):
    return
  if not is_atom(sexp[0]):
    printd (depth, '%s (' % type(sexp))
    format_defined_list (sexp, depth + 2, hidden)
    printd (depth, ')')
    return
  xnm = atom_name(sexp[0])
  if xnm == 'Dtype':
    (_, _, tydefs) = sexp
    nms = [atom_name (v[1]) for v in tydefs]
    printd (depth, 'Dtype (%s)' % addh (hidden, ', '.join(nms)))
  elif xnm == 'Dlocal':
    (_, loc, glob) = sexp
    printd (depth, 'Dlocal ([')
    format_defined_list (loc, depth + 2, True)
    printd (depth, '], [')
    format_defined_list (glob, depth + 2, hidden)
    printd (depth, '])')
  elif xnm == 'Dmod':
    (_, nm, contents) = sexp
    printd (depth, 'Dmod (%s,' % atom_name (nm))
    format_defined_list (contents, depth + 2, hidden)
    printd (depth, ')')
  elif xnm == 'Dlet':
    (_, _, nm, body) = sexp
    dnm = atom_name(nm)
    printd (depth, 'Dlet (%s)' % addh (hidden, dnm))
  elif xnm == 'Dletrec':
    (_, _, bodies) = sexp
    nms = [atom_name(v[0]) for v in bodies]
    printd (depth, 'Dletrec (%s)' % addh(hidden, ', '.join(nms)))
  else:
    printd (depth, '<unknown>: ' + str(sexp[0]))

def format_defined_list (sexp, depth, hidden):
  if is_atom(sexp):
    printd (depth, atom_name (sexp))
  else:
    for x in sexp:
      format_defined (x, depth, hidden)

import argparse

def main ():
  parser = argparse.ArgumentParser(description=
    'Parse and analyse a CakeML s-expression')
  parser.add_argument ('FILES', nargs='+', help='files to process')
  parser.add_argument ('--pcons', type=int, nargs='?', const='20', default=None,
    metavar='N', help='list N (=20) functions with most Pcon pattern-matches')
  parser.add_argument ('--summary', action='store_true',
    help='print summary of decs in various scopes')
  parser.add_argument ('--defined', action='store_true',
    help='print what is defined in various scopes')
  args = parser.parse_args ()
  for fname in args.FILES:
    sexp = parse (open (fname))
    if args.pcons:
      print_pcons (sort_pcons (sexp), args.pcons)
    if args.defined:
      print_defined (sexp)
    if args.summary:
      format_defined_list (sexp, 0, False)

if __name__ == '__main__':
  main ()








