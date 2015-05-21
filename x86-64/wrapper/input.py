
print """
break wrapper.c:20
set disassembly-flavor intel
display /3i $pc
display $pc
display $r15
display $r14
display $r13
display $r12
display $r11
display $r10
display $r9
display $r8
display $rdi
display $rsi
display $rbp
display $rsp
display $rdx
display $rcx
display $rbx
display $rax
run
"""

while True:
  print "si\n"
