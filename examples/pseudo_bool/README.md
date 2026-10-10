A checker for pseudo-boolean constraints.

[array](array):
Improving the pseudo-boolean proof checker with arrays (manually).

[cnf_encoding](cnf_encoding):
Encoders for various CNF-based problems.

[cp_encoding](cp_encoding):
CP semantics and encoders

[graph_encoding](graph_encoding):
Encoders for various graph problems.

[npbcScript.sml](npbcScript.sml):
Formalisation of normalised pseudo-boolean constraints

[npbc_checkScript.sml](npbc_checkScript.sml):
Pseudo-boolean constraints proof format and checker

[npbc_check_stepScript.sml](npbc_check_stepScript.sml):
Structural facts about the individual core proof steps of the PB checker

[npbc_moScript.sml](npbc_moScript.sml):
Multi-objective semantics for npbc, the pbc to npbc bridge, and the
recognition of loaded orders that refine an objective ordering

[npbc_mo_checkScript.sml](npbc_mo_checkScript.sml):
Checker for the restricted (multi-objective) proof format

[pb_parseScript.sml](pb_parseScript.sml):
Parse and print for pbc, npbc_check

[pb_parse_moScript.sml](pb_parse_moScript.sml):
Parse and print for multi-objective pbc problems

[pbcScript.sml](pbcScript.sml):
Formalisation of a flexible surface syntax and semantics for
pseudo-boolean problems with 'a var type

[pbc_encodeScript.sml](pbc_encodeScript.sml):
Helper lemmas for developing PB encodings

[pbc_moScript.sml](pbc_moScript.sml):
Multi-objective semantics for pbc, under the Pareto or the Leximax
ordering. A front holds one vector per class of equivalent non-dominated
vectors; under Leximax that is a single vector, unique up to permutation
and not necessarily attained itself

[pbc_normaliseScript.sml](pbc_normaliseScript.sml):
Normalizes pbc into npbc

[spt_to_vecScript.sml](spt_to_vecScript.sml):
Converting sptree to vector
