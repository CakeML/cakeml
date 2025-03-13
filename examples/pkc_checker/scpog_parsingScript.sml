(*
   Parsing interface for CNF and SCPOG files
*)
open preamble miscTheory lpr_parsingTheory mlintTheory cnf_scpogTheory;

val _ = new_theory "scpog_parsing";

(* We'll reuse the existing DIMACS parser from lpr_parsing.
  TODO: some of this material ought to be refactored.

  For SCPOG files, we write a simple parser that is easy
  to inspect, since the parsing of POG is trusted for our
  checker. *)

(* parse natural numbers until zero as end-of-line *)
Definition parse_nat_until_zero_def:
  parse_nat_until_zero ls =
  case parse_until_nn ls [] of NONE => NONE
  | SOME (n,i0,rest) =>
    if n = 0 ∧ rest = [] then SOME i0
    else NONE
End

Definition opt_union_def:
  opt_union (t:num_set option) (s:num list) =
  let tt = case t of NONE => LN | SOME t => t in
  SOME (FOLDL (\t v. insert v () t) tt s)
End

(* For a line starting with c, checks for p show ... *)
Definition parse_show_def:
  (parse_show vs (c::p::show::rest) =
  if p = INL (strlit "p")
  then
    if show = INL (strlit "show")
    then
      (case parse_nat_until_zero rest of
        NONE => NONE
      | SOME ls => SOME (opt_union vs ls))
    else SOME vs
  else SOME vs) ∧
  (parse_show vs [] = SOME vs) ∧
  (parse_show vs _ = NONE)
End

(* Parses extended DIMACS including support for "c p show ... 0" lines. Produces the list of clauses in order they are read.
  Comments are filtered. *)
Definition parse_one_def:
  parse_one maxvar s (vs:sptree$num_set option) acc =
  (if nocomment_line s
  then
    case parse_clause maxvar s of
      NONE => NONE
    | SOME cl => SOME(INL cl)
  else
    case parse_show vs s of
      NONE => NONE
    | SOME vs => SOME (INR vs))
End

Definition parse_ext_dimacs_body_def:
  (parse_ext_dimacs_body maxvar [] vs acc =
    SOME (vs,REVERSE acc)) ∧
  (parse_ext_dimacs_body maxvar (s::ss) vs acc =
    case parse_one maxvar s vs acc of
      NONE => NONE
    | SOME (INL cl) =>
      parse_ext_dimacs_body maxvar ss vs (cl::acc)
    | SOME (INR vs) =>
      parse_ext_dimacs_body maxvar ss vs acc
  )
End

Definition parse_ext_header_def:
  (parse_ext_header [] vs = NONE) ∧
  (parse_ext_header (s::ss) vs =
    if nocomment_line s
    then
      case parse_header_line s of NONE => NONE
      | SOME (vars,clauses) => SOME(vars,clauses,vs,ss)
    else
      case parse_show vs s of
        NONE => NONE
      | SOME vs => parse_ext_header ss vs)
End

Definition opt_bound_vs_def:
  opt_bound_vs maxvar vs =
  case vs of NONE => T
  | SOME t => EVERY (λv. FST v ≤ maxvar) (toAList t)
End

(* Parse the tokenized DIMACS file as a list of clauses *)
Definition parse_ext_dimacs_toks_def:
  parse_ext_dimacs_toks tokss =
  case parse_ext_header tokss NONE of
    SOME (vars,clauses,vs,ss) =>
      (case parse_ext_dimacs_body vars ss vs [] of
        NONE => NONE
      | SOME (vs,acc) =>
        if
          LENGTH acc = clauses ∧
          opt_bound_vs vars vs
        then SOME (vars,clauses,vs,acc)
        else NONE)
  | NONE => NONE
End

Definition parse_root_def:
  (parse_root [INR i] = SOME (Root i)) ∧
  (parse_root _ = NONE)
End

(* Parses {clause} 0 {hints} 0 *)
Definition parse_rup_add_def:
  parse_rup_add b n ls =
  case parse_until_zero ls [] of NONE => NONE
  | SOME (C,rest) =>
  case parse_nat_until_zero rest of NONE => NONE
  | SOME i0 => SOME (RupAdd b n C i0)
End

(*
(* Parses clauseID {nat_until_zeros} 0 *)
Definition parse_rup_del_def:
  parse_rup_del ls =
  case ls of
  | INR i::ls =>
    if i > 0:int then
      case parse_nat_until_zero ls of NONE => NONE
      | SOME i0 => SOME (RupDel (Num (ABS i)) i0)
    else NONE
  | _ => NONE
End
*)

Definition parse_arb_del_def:
  parse_arb_del ls =
  case parse_nat_until_zero ls of NONE => NONE
  | SOME ls => SOME (ArbDel ls)
End

Definition parse_pro_aux_def:
  parse_pro_aux ls =
  case ls of
  | INR i::ls =>
    if i > 0:int then
      case parse_until_zero ls [] of
      | SOME (lits,[]) => SOME (Num (ABS i),lits)
      | _ => NONE
    else NONE
  | _ => NONE
End

Definition parse_pro_def:
  parse_pro id ls =
  case parse_pro_aux ls of
    SOME (v,lits) => SOME (DeclPro id v lits)
  | _ => NONE
End

Definition parse_sko_def:
  parse_sko id ls =
  case parse_pro_aux ls of
    SOME (v,lits) => SOME (DeclSko id v lits)
  | _ => NONE
End

Definition parse_sum_def:
  parse_sum id ls =
  case ls of
    (INR i::INR l1::INR l2::ls) =>
    if i > 0
    then
      case parse_nat_until_zero ls of NONE => NONE
      | SOME nat_until_zero => SOME (DeclSum id (Num (ABS i)) l1 l2 nat_until_zero)
    else NONE
  | _ => NONE
End

(* case on the headings *)
Definition parse_scpstep_def:
  parse_scpstep ls =
  case ls of
  | INL s::ls =>
    if s = strlit"c" then SOME Skip
    (* else if s = strlit "d" then parse_rup_del ls *)
    else if s = strlit "D" then parse_arb_del ls
    else if s = strlit"r" then parse_root ls
    else NONE
  | INR i::INL s::ls =>
    if i > 0 then
      let C = Num (ABS i) in
      if s = strlit"a" then parse_rup_add F C ls
      else if s = strlit "as" then parse_rup_add T C ls
      else if s = strlit "p" then parse_pro C ls
      else if s = strlit "s" then parse_sum C ls
      else if s = strlit "t" then parse_sko C ls
      else NONE
    else NONE
  | _ => NONE
End

(* Mostly semantic! *)
Definition parse_scpsteps_def:
  (parse_scpsteps [] = SOME []) ∧
  (parse_scpsteps (l::ls) =
    case parse_scpstep (toks l) of
      NONE => NONE
    | SOME s =>
      (case parse_scpsteps ls of
        NONE => NONE
      | SOME ss => SOME (s :: ss))
    )
End

val scpstepsraw = ``[
  strlit"29 a 18 0 1 27 0 ";
  strlit"30 a 14 0 29 19 0";
  strlit"31 a 10 0 30 11 0";
  strlit"r 100";
  strlit"83 s 40 32 39 61 80 0";
  strlit"86 p 41 30 40 0 ";
  strlit"89 t 42 -15 -19 0 ";
  strlit"92 p 43 4 41 42 0 ";
  strlit"c Operation T23";
  strlit"124 as -47 -45 -52 0 101 108 0";
  strlit"125 as -49 -45 -52 0 100 113 0";
  strlit"c Operation T23";
  strlit"D 6 406 35 40 49 53 54 87 94 135 148 159 185 238 243 249 256 300 308 317 324 348 357 0 ";]``

val scpsteps = rconc (EVAL ``THE (parse_scpsteps ^(scpstepsraw))``);

val _ = export_theory ();
