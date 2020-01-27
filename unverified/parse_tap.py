
import json

def json_to_display (j):
  if type (j) == list:
    return map (json_to_display, j)
  elif 'name' in j:
    return tuple ([j['name']] + json_to_display (j['args']))
  else:
    assert 'isTuple' in j
    return tuple ([None] + json_to_display (j['elements']))

def parse_output (fname, lang = 'clos'):
  f = open (fname)
  header = 'tap.' + lang
  while header not in f.readline ():
    pass
  for l in f:
    l = l.strip ()
    if l:
      break
  j = json.loads (l)
  return json_to_display (j['prog'])

def arrange_display (display, indent = 0, margin = 80):
  if type (display) == list:
    head = '['
    tail = '],'
    ds = display
  else:
    head = '%s (' % display[0]
    tail = '),'
    ds = display[1:]
  xs = [arrange_display (d, indent + 2, margin) for d in ds]
  multi = [x for x in xs if len (x) > 1]
  line_len = sum ([len (x[0][1]) + 1 for x in xs]
    + [indent, len (head), len (tail)])
  if multi or line_len > margin:
    return [(indent, head)] + [y for x in xs for y in x] + [(indent, tail)]
  else:
    return [(indent, head + ' '.join ([x[0][1] for x in xs]) + tail)]

def print_display (display, indent = 0, margin = 80):
  for (indent, s) in arrange_display (display):
    print (' ' * indent + s)

def main ():
  import sys
  fname = sys.argv[1]
  if len (sys.argv) > 2:
    lang = sys.argv[2]
  else:
    lang = 'clos'
  print_display (parse_output (fname, lang))

if __name__ == '__main__':
  main ()


