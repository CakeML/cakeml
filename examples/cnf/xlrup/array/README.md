Array-based implementation of the XLRUP checker

[compilation](compilation):
The CNF-XOR XLRUP proof checker, compiled.

[xlrup_arrayFullProgScript.sml](xlrup_arrayFullProgScript.sml):
This builds the cake_xlrup proof checker

[xlrup_arrayProgScript.sml](xlrup_arrayProgScript.sml):
This refines xlrup_list to use arrays

[xlrup_listScript.sml](xlrup_listScript.sml):
This refines the XLRUP checker to a list-based implementation.

[xor_listScript.sml](xor_listScript.sml):
A byte-list mirror of the XOR bitstring operations, which the array
implementation updates destructively. Each definition here is proved
equal to its string-based counterpart under
s ↦ implode (MAP fromByte s).
