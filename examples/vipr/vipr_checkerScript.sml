(*
  A pure version of the VIPR checker
*)
Theory vipr_checker
Ancestors
  milp mllist
Libs
  preamble realLib

Datatype:
  conf = <| vars : mlstring list ;
            ints : num_set ;
            lcs : (linop # real sptree$num_map # real) list ;
            min : bool ;
            obj : real sptree$num_map ;
            rtp : result ;
            sols : real sptree$num_map list |>
End

Type acc_type =
  “:(num list # linop # real sptree$num_map # real) sptree$num_map # num”;

Datatype:
  reader_state = Init
               | Reading (mlstring list list)
               | Der conf acc_type num
               | Error mlstring
End

Definition empty_conf_def:
  empty_conf = <| vars := [] ;
                  ints := LN ;
                  lcs := [] ;
                  min := F ;
                  obj := LN ;
                  rtp := Infeasible ;
                  sols := [] |>
End

Definition init_state_def:
  init_state = Init
End

Definition is_white_space_def:
  is_white_space c = MEM c " \n\t\r"
End

Definition tokens_spaces_def:
  tokens_spaces s = mlstring$tokens is_white_space s
End

Definition str_to_real_def:
  str_to_real s =
    case tokens (λc. MEM c "/") s of
    | [x;y] =>
      (case fromString x, fromNatString y of
       | (SOME (i:int), SOME j) =>
           (if j = 0 then NONE else SOME (real_of_int i / & j :real))
       | _ => NONE)
    | [x] => (case fromString x of
              | (SOME (i:int)) => SOME (real_of_int i)
              | NONE => NONE)
    | _ => NONE
End

Definition read_real_def:
  read_real xs =
    case xs of
    | [] => NONE
    | (x::xs) => (case str_to_real x of
                  | NONE => NONE
                  | SOME r => SOME (r,xs))
End

Definition read_num_def:
  read_num ts =
    case ts of
    | [] => NONE
    | (x::ts) => (case fromNatString x of
                  | NONE => NONE
                  | SOME n => SOME (n,ts))
End

Definition read_lin_def:
  read_lin k xs m =
    if k = 0:num then SOME (m,xs) else
      case xs of
      | (v::x::xs) =>
          (case fromNatString v, str_to_real x of
           | (SOME n, SOME r) => read_lin (k-1) xs (insert n r m)
           | _ => NONE)
      | _ => NONE
End

Definition read_lin_term_simple_def:
  read_lin_term_simple ts =
    case ts of
    | [] => NONE
    | (x::ts) =>
      case fromNatString x of
      | NONE => NONE
      | SOME n => read_lin n ts LN
End

Definition read_lin_term_def:
  read_lin_term obj ts =
    case ts of
    | [] => NONE
    | (x::ts) =>
      if x = strlit "OBJ" then
        SOME (obj,ts)
      else
        case fromNatString x of
        | NONE => NONE
        | SOME n => read_lin n ts LN
End

Definition read_linop_def:
  read_linop ts =
    case ts of
    | [] => NONE
    | (x::xs) =>
      if x = strlit "G" then SOME (GreaterEqual,xs) else
      if x = strlit "E" then SOME (Equal,xs) else
      if x = strlit "L" then SOME (LessEqual,xs) else
        NONE
End

Definition read_lc_def:
  read_lc obj ts =
    case ts of
    | (name::xs) =>
       (case read_linop xs of
        | NONE => NONE
        | SOME (p,ys) =>
            case read_real ys of
            | NONE => NONE
            | SOME (r,zs) =>
                case read_lin_term obj zs of
                | NONE => NONE
                | SOME (l,ts1) => SOME ((name,((p,l,r):lc)),ts1))
    | _ => NONE
End

Definition read_n_strings_def:
  read_n_strings n xs acc =
    if n = 0 then SOME (REVERSE acc,xs) else
      case xs of
      | [] => NONE
      | (y::xs) => read_n_strings (n-1:num) xs (y::acc)
End

Definition read_n_nums_def:
  read_n_nums n xs acc =
    if n = 0 then SOME (acc,xs) else
      case xs of
      | [] => NONE
      | (y::xs) =>
        case fromNatString y of
        | NONE => NONE
        | SOME k => read_n_nums (n-1:num) xs (insert k () acc)
End

Definition read_n_constraints_def:
  read_n_constraints obj n xs acc =
    if n = 0 then SOME (REVERSE acc,xs) else
      case read_lc obj xs of
      | NONE => NONE
      | SOME (y,xs) => read_n_constraints obj (n-1:num) xs (y::acc)
End

Definition read_n_solutions_def:
  read_n_solutions n ts acc =
    if n = 0 then SOME (REVERSE acc,ts) else
      case ts of
      | (name::ts) =>
          (case read_lin_term_simple ts of
           | NONE => NONE
           | SOME (l,ts) => read_n_solutions (n-1:num) ts ((name,l)::acc))
      | _ => NONE
End

Definition read_bound_def:
  read_bound s none_str =
    if s = none_str then SOME NONE else
      case str_to_real s of
      | NONE => NONE
      | SOME r => SOME (SOME r)
End

Definition read_goal_def:
  read_goal ts =
    case ts of
    | [] => NONE
    | (x::ts) =>
      if x = strlit "infeas" then SOME (Infeasible, ts) else
      if x ≠ strlit "range" then NONE else
        case ts of
        | (b1::b2::ts) =>
            (case read_bound b1 (strlit "-inf"), read_bound b2 (strlit "inf") of
             | (SOME lb, SOME ub) => SOME (Range lb ub, ts)
             | _ => NONE)
        | _ => NONE
End

Overload var_error = “strlit "Unable to read VAR section."”
Overload int_error = “strlit "Unable to read INT section."”
Overload obj_error = “strlit "Unable to read OBJ section."”
Overload con_error = “strlit "Unable to read CON section."”
Overload rtp_error = “strlit "Unable to read RTP section."”
Overload sol_error = “strlit "Unable to read SOL section."”
Overload der_error = “strlit "Unable to read DER line: "”
Overload der_proof_fail = “strlit "Check failed at DER line: "”

Definition read_sol_def:
  read_sol c ts =
    case ts of
    | (x::y::ts) =>
        (if x ≠ strlit "SOL" then INL sol_error else
           case fromNatString y of
           | NONE => INL sol_error
           | SOME n =>
             case read_n_solutions n ts [] of
             | NONE => INL sol_error
             | SOME (sols,ts) =>
                 if NULL ts then
                   INR (c with sols := MAP SND sols)
                 else INL sol_error)
    | _ => INL sol_error
End

Definition read_rtp_def:
  read_rtp c ts =
    case ts of
    | (x::ts) =>
        (if x ≠ strlit "RTP" then INL con_error else
           case read_goal ts of
           | NONE => INL con_error
           | SOME (rtp,ts) => read_sol (c with rtp := rtp) ts)
    | _ => INL rtp_error
End

Definition read_con_def:
  read_con c ts =
    case ts of
    | (x::y::z::ts) =>
        (if x ≠ strlit "CON" then INL con_error else
           case fromNatString y, fromNatString z of
           | (SOME m, SOME b) =>
               (if m < b then INL con_error else
                  case read_n_constraints c.obj m ts [] of
                  | NONE => INL con_error
                  | SOME (cs,ts) => read_rtp (c with lcs := MAP SND cs) ts)
           | _ => INL con_error)
    | _ => INL con_error
End

Definition read_obj_def:
  read_obj c ts =
    case ts of
    | (x::y::ts) =>
        (if x ≠ strlit "OBJ" then INL obj_error else
         if ~MEM y [strlit "min"; strlit "max"] then INL obj_error else
         case read_lin_term_simple ts of
         | NONE => INL obj_error
         | SOME (t,ts) => read_con (c with <| min := (y = strlit "min") ;
                                              obj := t |>) ts)
    | _ => INL obj_error
End

Definition read_int_def:
  read_int c ts =
    case ts of
    | (x::y::ts) =>
        (if x ≠ strlit "INT" then INL int_error else
         case fromNatString y of
         | NONE => INL int_error
         | SOME n =>
           case read_n_nums n ts LN of
           | NONE => INL int_error
           | SOME (int_vars,ts) => read_obj (c with ints := int_vars) ts)
    | _ => INL int_error
End

Definition read_problem_def:
  read_problem ts =
    case ts of
    | (x::y::ts) =>
        (if x ≠ strlit "VAR" then INL var_error else
         case fromNatString y of
         | NONE => INL var_error
         | SOME n =>
           case read_n_strings n ts [] of
           | NONE => INL var_error
           | SOME (vars,ts) => read_int (empty_conf with vars := vars) ts)
    | _ => INL var_error
End

Definition read_end_def:
  read_end ret ts =
    (case ts of
     | [] => NONE
     | (t::ts) => if t = strlit "}" then SOME (ret,ts) else NONE)
End

Definition read_vipr_lin_aux_def:
  read_vipr_lin_aux c ts acc =
    if c = 0 then SOME (REVERSE acc,ts) else
      case read_num ts of NONE => NONE | SOME (n,ts) =>
      case read_real ts of NONE => NONE | SOME (r,ts) =>
        read_vipr_lin_aux (c-1:num) ts ((n,r)::acc)
End

Definition read_vipr_lin_def:
  read_vipr_lin ts =
    case read_num ts of
    | NONE => NONE
    | SOME (n,ts) => read_vipr_lin_aux n ts []
End

Definition read_vipr_def:
  read_vipr ts =
    case ts of
    | [] => NONE
    | (x::ts) =>
      if x ≠ strlit "{" then NONE else
        case ts of
        | [] => NONE
        | (y::ts) =>
          if y = strlit "asm" then
            read_end Assum ts
          else if y = strlit "lin" then
            (case read_vipr_lin ts of
             | NONE => NONE
             | SOME (ls,ts) => read_end (Lin ls) ts)
          else if y = strlit "rnd" then
            (case read_vipr_lin ts of
             | NONE => NONE
             | SOME (ls,ts) => read_end (Round ls) ts)
          else if y = strlit "uns" then
            (case read_num ts of | NONE => NONE | SOME (n1,ts) =>
             case read_num ts of | NONE => NONE | SOME (n2,ts) =>
             case read_num ts of | NONE => NONE | SOME (n3,ts) =>
             case read_num ts of | NONE => NONE | SOME (n4,ts) =>
               read_end (Unsplit n1 n2 n3 n4) ts)
          else NONE
End

Definition read_der_line_def:
  read_der_line obj ts =
    case read_lc obj ts of
    | NONE => NONE
    | SOME ((_,c),ts) =>
      case read_vipr ts of
      | NONE => NONE
      | SOME (vipr,ts) =>
        case ts of
        | [] => NONE
        | (i::ts) => if NULL ts then SOME (c,vipr,i) else NONE
End

Definition checker_step_def:
  checker_step (line:mlstring) (s:reader_state) =
    let ts = tokens_spaces line in
      case ts of
      | [] => s (* empty line, reader state unchanged *)
      | (x::xs) =>
        case s of
        | Init =>
            (if isPrefix (strlit "%") line then s else
             if ts = [strlit "VER"; strlit "1.0"] then Reading [] else
               Error (strlit "Unable to find VER 1.0 after initial comments."))
        | Reading acc =>
            (if x ≠ strlit "DER" then Reading (ts::acc) else
               let input = FLAT (REVERSE acc) in
                 case read_problem input of
                 | INL e => Error e
                 | INR c =>
                     if ~ EVERY (check_sol c.ints c.lcs) c.sols then
                       Error (strlit "EVERY check_sol failed.")
                     else if ~ check_rtp_bound c.min c.obj c.sols c.rtp then
                       Error (strlit "check_rtp_bound failed.")
                     else
                       case read_num xs of
                       | NONE => Error der_error
                       | SOME (der_count,ts) =>
                           if NULL ts then Der c (build_fml 0 c.lcs LN) der_count
                           else Error der_error)
        | Error err => Error err
        | Der c acc der_count =>
            case read_der_line c.obj ts of
            | NONE => Error (der_error ^ line)
            | SOME (lc,vipr,index) =>
                case check_vipr c.ints acc (lc,vipr) of
                | INL err => Error (der_proof_fail ^ line ^ strlit"Reason: " ^ err)
                | INR acc' => Der c acc' (der_count-1)
End

Definition print_outcome_def:
  print_outcome (s:reader_state) =
    case s of
    | Init                => strlit "Incomplete file"
    | Reading _           => strlit "Failure: Could not find DER section.\n"
    | Error error_msg     => strlit "Error: " ^ error_msg ^ strlit "\n"
    | Der c acc der_count => if der_count ≠ 0 then
                               strlit "Error: DER count incorrect.\n"
                             else if ~ check_last c.min c.obj c.rtp acc then
                               strlit "Error: check_last failed.\n"
                             else
                               strlit "PASSED ALL CHECKS.\n"
End

(* do not change this *)
Definition run_vipr_def:
  run_vipr lines =
    print_outcome (foldl checker_step init_state lines)
End

Theorem checker_step_Error:
  ∀lines e.
  foldl checker_step (Error e) lines =
    Error e
Proof
  Induct>>rw[foldl_def,checker_step_def]>>
  every_case_tac>>fs[]
QED

Theorem checker_step_Der:
  ∀lines c acc der_count c' acc' der_count'.
  foldl checker_step (Der c acc der_count) lines =
    Der c' acc' der_count' ⇒
  c = c' ∧
  ∃viprs.
    check_viprs c.ints acc viprs = INR acc'
Proof
  Induct>>simp[foldl_def,checker_step_def]
  >- (
    rw[]>>
    qexists_tac`[]`>>simp[check_viprs_def])>>
  ntac 8 strip_tac>>
  every_case_tac>>fs[checker_step_Error]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]>>
  first_x_assum drule>>rw[]>>
  rename1`check_vipr _ _ (a,b) = _`>>
  qexists_tac`(a,b)::viprs`>>
  simp[check_viprs_def]
QED

Theorem tokens_spaces_head:
  tokens_spaces h = ls ⇒
  FLAT (MAP tokens_spaces (h::prob_lines)) =
  ls ++ FLAT (MAP tokens_spaces prob_lines)
Proof
  rw[]
QED

Theorem checker_step_Reading:
  ∀lines acc c res b.
  foldl checker_step (Reading acc) lines = Der c res b ⇒
  ∃prob_lines der_lines.
    lines = prob_lines ++ der_lines ∧
    read_problem (FLAT (REVERSE acc ++ (MAP tokens_spaces prob_lines))) = INR c ∧
    EVERY (check_sol c.ints c.lcs) c.sols ∧
    check_rtp_bound c.min c.obj c.sols c.rtp ∧
    ∃viprs.
      check_viprs c.ints (build_fml 0 c.lcs LN) viprs = INR res
Proof
  Induct>>rw[foldl_def,checker_step_def]>>
  pop_assum mp_tac>>
  TOP_CASE_TAC>>fs[]
  >- (
    rw[]>>first_x_assum drule>>
    metis_tac[APPEND,tokens_spaces_head] )>>
  TOP_CASE_TAC>>fs[]
  >- (
    rw[]>>first_x_assum drule>>
    rw[]>>
    qexists_tac`h::prob_lines`>>
    simp[]>>
    metis_tac[APPEND_ASSOC,APPEND])>>
  every_case_tac>>fs[checker_step_Error]>>
  rw[]>>
  drule checker_step_Der>>rw[]>>
  fs[EVERY_MEM]>>
  qexists_tac`[]`>>fs[]>>
  metis_tac[]
QED

Theorem checker_step_Init:
  ∀lines c res b.
  foldl checker_step Init lines = Der c res b ⇒
  ∃init_lines prob_lines der_lines.
    lines = init_lines ++ prob_lines ++ der_lines ∧
    read_problem (FLAT (MAP tokens_spaces prob_lines)) = INR c ∧
    EVERY (check_sol c.ints c.lcs) c.sols ∧
    check_rtp_bound c.min c.obj c.sols c.rtp ∧
    ∃viprs.
      check_viprs c.ints (build_fml 0 c.lcs LN) viprs = INR res
Proof
  Induct>>rw[foldl_def,checker_step_def]
  >- (
    every_case_tac>>fs[]>>
    metis_tac[APPEND])
  >- (
    drule checker_step_Reading>>
    rw[]>>
    metis_tac[APPEND])>>
  every_case_tac>>gs[checker_step_Error]>>
  metis_tac[APPEND]
QED

Theorem run_vipr_satisfies_rtp:
  run_vipr lines = strlit "PASSED ALL CHECKS.\n" ⇒
  ∃init_lines prob_lines der_lines c.
    lines = init_lines ++ prob_lines ++ der_lines ∧
    read_problem (FLAT (MAP tokens_spaces prob_lines)) = INR c ∧
    satisfies_rtp (domain c.ints) (set c.lcs) c.min c.obj c.rtp
Proof
  rw[run_vipr_def,print_outcome_def]>>
  reverse (every_case_tac>>fs[])
  >- (
    pop_assum mp_tac>>
    EVAL_TAC)>>
  fs[init_state_def]>>
  drule checker_step_Init>>
  rw[]>>
  qexists_tac`init_lines`>>
  qexists_tac`prob_lines`>>
  qexists_tac`der_lines`>>
  simp[]>>
  match_mp_tac (GEN_ALL check_rtp_sound)>>
  fs[check_rtp_def]>>
  asm_exists_tac>>fs[]>>
  qexists_tac`viprs`>>simp[]
QED

(* ==================================================================== *
    Testing below this line
 * ==================================================================== *)

fun run_vipr expected_output q = let
  fun quote_to_lines (q: string Portable.quotation) = let
    val s = Portable.quote_to_string (fn _ => raise General.Bind) q
    val seps = explode "\n"
    val lines = String.tokens (fn c => mem c seps) s |> map (fn line => line ^ "\n")
    val tm = listSyntax.mk_list(map stringSyntax.fromMLstring lines,“:string”)
    in tm end
  val output_str =
    SPEC (quote_to_lines q) (Q.SPEC ‘MAP strlit s’ run_vipr_def |> GEN_ALL)
    |> concl |> rand |> EVAL |> concl |> dest_eq |> snd
    |> rand |> stringSyntax.fromHOLstring
  val _ = (output_str = expected_output) orelse
            (print "\n"; print output_str; print "\n\n";
             failwith "run_vipr gave wrong answer")
  in () end;

(* infeasbb.vipr *)

val _ = run_vipr "PASSED ALL CHECKS.\n" ‘
VER 1.0
VAR 2
x1 x2
INT 2
0 1
OBJ min
0
CON 3 0
C1 G 1  2  0 2  1 1
C2 G 0  2  0 -2  1 3
C3 L 2  2  0 -1  1 4
RTP infeas
SOL 0
DER 5
a3 L 0  1  1 1 { asm } 7
a4 G 1  1  1 1 { asm } 7
C5 G 1  0 { lin 3  0 1  1 1  3 -4 } 7
C6 G 1  0 { lin 3  1 1 2 -2  4 5 } 7
C7 G 1  0 { uns 5 3  6 4 } -1’

(* cg.vipr *)

val _ = run_vipr "PASSED ALL CHECKS.\n" ‘
%
%  min x + y
%  s.t.
%  C1: 4x + y >= 1
%  C2: 4x - y <= 2
%
%  Optimal value: 1
%  Optimal solution: (x, y) = (0, 1)
%
%  Pure cutting plane proof using CG cuts
%
VER 1.0
VAR 2
x
y
INT 2
 0 1
OBJ min
 2  0 1  1 1
CON 2 0
C1 G 1  2  0 4  1 1
C2 L 2  2  0 4  1 -1
RTP range 1 1
SOL 2
feas 2  0 1  1 2
opt 1  1 1
DER 4
C3 G -1/2  1  1 1 { lin 2  0 1/2  1 -1/2 } 3
C4 G 0     1  1 1 { rnd 1  2 1 } 4
C5 G 1/4   OBJ  { lin 2  0 1/4  3 3/4 } 5
C6 G 1     OBJ  { rnd 1  4 1 } 0’

(* ip.vipr *)

val _ = run_vipr "PASSED ALL CHECKS.\n" ‘
% min x2
% s.t. 2 x1 +   x2 >= 1
%      2 x1 - 3 x2 <= 1
%        x1, x2 integers
VER 1.0
VAR 2
x1 x2
INT 2
0 1
OBJ min
1  1 1
CON 2 0
C1 G 1  2  0 2  1 1
C2 L 1  2  0 2  1 -3
RTP range 1 inf
SOL 1
opt 1  1 1
DER 6
a1 L 0  1  0 1 { asm } -1
a2 G 1  1  0 1 { asm } -1
d3 G 1  OBJ { lin 2  0 1  2 -2 } 7
d4 G 1/3  OBJ { lin 2  1 -1/3 3 2/3 } 7
r5 G 1 OBJ { rnd 1 5 1 } 7
obj G 1  OBJ { uns 4 2  6 3 } -1’

