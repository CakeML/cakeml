Improving the pseudo-boolean proof checker with arrays (manually).

[compilation](compilation):
Compiling the pseudo-boolean constraints checker.

[npbc_arrayProgScript.sml](npbc_arrayProgScript.sml):
Refine npbc_list to npbc_array

[npbc_fullProgScript.sml](npbc_fullProgScript.sml):
Add PBF parsing and wrap around the PBP parser

[npbc_listScript.sml](npbc_listScript.sml):
Refine PB proof checker to use arrays

[npbc_mo_arrayProgScript.sml](npbc_mo_arrayProgScript.sml):
Refine the multi-objective PB proof checker to CakeML

[npbc_mo_fullProgScript.sml](npbc_mo_fullProgScript.sml):
Multi-objective OPB frontend: parse an OPB file with several objectives,
then either print it back or check a PB proof of its nondominated set

[npbc_mo_listScript.sml](npbc_mo_listScript.sml):
Refine the multi-objective PB proof checker to use arrays

[npbc_parseProgScript.sml](npbc_parseProgScript.sml):
Add shared pbp parsing, normalization and other common stuff to npbc_arrayProg
