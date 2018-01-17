open preamble holSyntaxTheory mlstringTheory

val _ = new_theory "pretty";

(* ------------------------------------------------------------------------- *)
(* Printing blocks of strings                                                *)
(* ------------------------------------------------------------------------- *)

(* Based on the pretty printer from "ML from the working programmer". *)

val _ = Datatype `
  t = Block (t list) num num
    | String mlstring
    | Break num`;

val breakdist_def = Define `
  breakdist tt after =
    case tt of
      []                => after
    | Block _ _ len::es => len + breakdist es after
    | String s::es      => strlen s + breakdist es after
    | Break _::es       => 0`;

val blanks_def = Define `
  blanks space n = (space-n, concat (REPLICATE n (strlit" ")))`;

val newline_def = Define `newline = strlit"\n"`;

val printing_def = tDefine "printing" `
  (printing bs af sp mr []                     = (sp, strlit"")) /\
  (printing bs af sp mr (Block bes ind ln::es) =
     let (s1, r1) = printing (sp-ind) (breakdist es af) sp mr bes in
     let (s2, r2) = printing bs af s1 mr es in (s2, r1 ^ r2)) /\
  (printing bs af sp mr (String s::es) =
     let (s1, r1) = (sp - strlen s, s) in
     let (s2, r2) = printing bs af s1 mr es in (s2, r1 ^ r2)) /\
  (printing bs af sp mr (Break ln::es) =
     if ln + breakdist es af <= sp then
       let (s1, r1) = blanks sp ln in
       let (s2, r2) = printing bs af s1 mr es in (s2, r1 ^ r2)
     else
       let (s1, r1) = (mr, newline) in
       let (s2, r2) = blanks s1 (mr - bs) in
       let (s3, r3) = printing bs af s2 mr es in (s3, r1 ^ r2 ^ r3))`
  (WF_REL_TAC `measure (t1_size o SND o SND o SND o SND)`);

val pr_def = Define `pr e margin = SND (printing margin 0 margin margin [e])`

val tlength_def = Define `
  tlength t =
    case t of
      Block _ _ len => len
    | String s      => strlen s
    | Break len     => len`;

val mk_str_def = Define `mk_str x = String x`;
val mk_brk_def = Define `mk_brk x = Break x`;
val mk_blo_def = Define `
  mk_blo indent es = Block es indent (SUM (MAP tlength es))`

(* ------------------------------------------------------------------------- *)
(* Printing types, terms and theorems                                        *)
(* ------------------------------------------------------------------------- *)

val margin_tm = ``78n``;

(* type := Tyvar mlstring | Tyapp mlstring (type list) *)

(* TODO all types are written in postfix *)
val typ_def = Define `
  typ ty =
    case ty of
      Tyvar n => mk_str n
    | Tyapp n [] => mk_str n
    | Tyapp n [t1] => mk_blo 0 [typ t1; mk_str (strlit" " ^ n)]
    | Tyapp n (t1::ts) =>
        let t1 =
          case t1 of
            Tyvar m => mk_str m
          | tt => mk_blo 1 [mk_str (strlit"("); typ tt; mk_str (strlit")")]
        in
          mk_blo 0 [mk_str (strlit"("); t1; mk_brk 1; typ (Tyapp n ts); mk_str(strlit")")]`;

val ty_to_string_def = Define `ty_to_string ty = pr (typ ty) ^margin_tm`

(*
val A = ``Tyvar (strlit"A")``
val B = ``Tyvar (strlit"B")``
val AB = ``Tyapp (strlit"fun") [^A; ^B]``
val Alist = ``Tyapp (strlit"list") [^A]``

val test = EVAL ``ty_to_string ^AB``
val test = EVAL ``ty_to_string ^Alist``
*)

(* term := Var mlstring type
         | Const mlstring type
         | Comb term term
         | Abs term term *)

(* TODO Simplified to save time (avoid mutual recursion). It does not
 * handle abstractions or applications properly.
 *)
val term_def = Define `
   term tm =
    case tm of
      Var n ty => mk_blo 0 [mk_str n; mk_str (strlit" : "); mk_str (ty_to_string ty)]
    | Const n ty => mk_blo 0 [mk_str n; mk_str (strlit" : "); mk_str (ty_to_string ty)]
    | Abs s t => mk_blo 0 [mk_str (strlit"\\"); term s; mk_str (strlit"."); mk_brk 1; term t]
    | Comb s t =>
        let s1 = mk_blo 1 [mk_str (strlit"("); term s; mk_str (strlit")")]
        in
          mk_blo 0 [s1; mk_brk 1; term t]`;

val tm_to_string_def = Define `tm_to_string tm = pr (term tm) ^margin_tm`

(*
val Va = ``Var (strlit "a") (^A)``
val Vf = ``Var (strlit "f") (^AB)``
val AppVfVa = ``Comb (^Vf) (^Va)``
val Abs = ``Abs (^Va) (Var (strlit "b") (^B))``
val AbsApp = ``Comb (^Abs) (^Va)``
val AbsAppApp = ``Comb (^AbsApp) (^Vf)``

val test = EVAL ``tm_to_string ^Va``
val test = EVAL ``tm_to_string ^Vf``
val test = EVAL ``tm_to_string ^AppVfVa``
val test = EVAL ``tm_to_string ^Abs``
val test = EVAL ``tm_to_string ^AbsApp``
val test = EVAL ``tm_to_string ^AbsAppApp``
*)

val hyps_def = Define `
  hyps hs =
    case hs of
      []    => []
    | [h]   => [term h]
    | h::hs => term h :: mk_str (strlit",") :: mk_brk 1 :: hyps hs`

val thm_def = Define `
  thm (Sequent hs c) =
    mk_blo 0 (hyps hs ++ [mk_brk 1; mk_str (strlit" |-"); mk_brk 1; term c])`

val thm_to_string_def = Define `thm_to_string th = pr (thm th) ^margin_tm`

val _ = export_theory ();

