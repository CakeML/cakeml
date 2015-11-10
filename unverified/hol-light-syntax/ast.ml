(*Internal AST definition*)

type ml_typ =
| Typ_var_anon
| Typ_var of string
| Typ_arrow of ml_typ * ml_typ
| Typ_tuple of ml_typ list
| Typ_constr of string * ml_typ list
| Typ_qual_constr of string * string * ml_typ list;;

type ml_exp =
| Exp_ident of string
| Exp_qual_ident of string * string
| Exp_int of int
| Exp_string of string
| Exp_construct of string * ml_texp list
| Exp_tuple of ml_texp list
| Exp_apply of ml_texp * ml_texp list
| Exp_function of (ml_tpat * ml_texp option * ml_texp) list
| Exp_match of ml_texp * (ml_tpat * ml_texp option * ml_texp) list
| Exp_try of ml_texp * (ml_tpat * ml_texp option * ml_texp) list
| Exp_let of bool * (ml_tpat * ml_texp) list * ml_texp
| Exp_sequence of ml_texp * ml_texp
| Exp_ifthenelse of ml_texp * ml_texp * ml_texp
|   Exp_constraint of ml_texp * ml_typ

and ml_pat =
| Pat_any
| Pat_var of string
| Pat_int of int
| Pat_string of string
| Pat_construct of string * ml_tpat list
| Pat_tuple of ml_tpat list
| Pat_constraint of ml_tpat * ml_typ
|   Pat_alias of ml_tpat * string
|   Pat_or of ml_tpat * ml_tpat

and ml_texp = ml_typ * ml_exp
and ml_tpat = ml_typ * ml_pat;;

type ml_type_decl =
| Type_abbrev of ml_typ
| Type_variant of (string * ml_typ list) list;;

type ml_sig_item =
| Sig_value of string * ml_typ
| Sig_type of string * ml_typ list * ml_type_decl option;;

type ml_str_item =
| Str_eval of ml_texp
| Str_value of bool * (ml_typ * ml_tpat * ml_texp) list
| Str_type of (string * ml_typ list * ml_type_decl) list
| Str_exception of string * ml_typ list
| Str_install_printer of string
| Str_modtype of string * ml_sig_item list
| Str_module of string * string * ml_str_item list
| Str_include of string;;
