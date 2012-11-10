structure test_compilerLib = struct
open HolKernel stringLib bytecodeML compileML ml_translatorLib

fun bc_evaln 0 s = s
  | bc_evaln n s = let
    val SOME s = bc_eval1 s in
      bc_evaln (n-1) s
    end handle Bind => (print "Fail\n"; s)

fun bc_eval_limit l s = let
     val SOME s = bc_eval1 s
     val n = length (bc_state_stack s)
  in if n > l then NONE else bc_eval_limit l s
   end handle Bind => SOME s

fun dest_list f = map f o (fst o listSyntax.dest_list)
fun dest_pair f1 f2 = (f1 ## f2) o pairSyntax.dest_pair
fun term_to_int tm = intML.fromString((Parse.term_to_string tm)^"i")
fun term_to_bool tm = tm = boolSyntax.T
fun term_to_lit tm = let
  val (f,x) = dest_comb tm
in case fst(dest_const f) of
    "IntLit" => IntLit (term_to_int x)
  | "Bool" => Bool (term_to_bool x)
  | s => raise Fail s
end handle (Fail s) => raise Fail s | _ => raise Fail (Parse.term_to_string tm)
fun term_to_opb tm =
  case fst(dest_const tm) of
    "Geq" => Geq
  | "Gt" => Gt
  | "Lt" => Lt
  | "Leq" => Leq
  | s => raise Fail s
fun term_to_opn tm =
  case fst(dest_const tm) of
    "Minus" => Minus
  | "Plus" => Plus
  | "Times" => Times
  | s => raise Fail s
fun term_to_op_ tm = let
  val (f,x) = dest_comb tm
in case fst(dest_const f) of
    "Opn" => Opn (term_to_opn x)
  | "Opb" => Opb (term_to_opb x)
  | s => raise Fail s
end handle _ => (
case fst(dest_const tm) of
    "Opapp" => Opapp
  | "Equality" => Equality
  | s => raise Fail s )
handle (Fail s) => raise Fail s | _ => raise Fail (Parse.term_to_string tm)
fun term_to_pat tm = let
  val (f,xs) = strip_comb tm
in case fst(dest_const f) of
    "Pvar" => let val [x1] = xs in Pvar (fromHOLstring x1) end
  | "Plit" => let val [x1] = xs in Plit (term_to_lit x1) end
  | "Pcon" => let val [x1,x2] = xs in Pcon (fromHOLstring x1, dest_list term_to_pat x2) end
  | s => raise Fail s
end handle (Fail s) => raise Fail s | _ => raise Fail (Parse.term_to_string tm)
fun term_to_error tm =
  case fst(dest_const tm) of
    "Bind_error" => Bind_error
  | s => raise Fail s
fun term_to_v tm = let
  val (f,xs) = strip_comb tm
in case fst(dest_const f) of
    "Litv" => let val [x1] = xs in Litv (term_to_lit x1) end
  | "Closure" => let val [x1,x2,x3] = xs in Closure (dest_list (dest_pair fromHOLstring term_to_v) x1,fromHOLstring x2,term_to_exp x3) end
  | "Conv" => let val [x1,x2] = xs in Conv (fromHOLstring x1,dest_list term_to_v x2) end
  | s => raise Fail s
end handle (Fail s) => raise Fail s | _ => raise Fail (Parse.term_to_string tm)
and term_to_exp tm = let
  val (f,xs) = strip_comb tm
in case fst(dest_const f) of
    "Lit" => let val [x1] = xs in Lit (term_to_lit x1) end
  | "If"  => let val [x1,x2,x3] = xs in If (term_to_exp x1, term_to_exp x2, term_to_exp x3) end
  | "App" => let val [x1,x2,x3] = xs in App (term_to_op_ x1, term_to_exp x2, term_to_exp x3) end
  | "Fun" => let val [x1,x2] = xs in Fun (fromHOLstring x1, term_to_exp x2) end
  | "Var" => let val [x1] = xs in Var (fromHOLstring x1) end
  | "Let" => let val [x1,x2,x3] = xs in Let (fromHOLstring x1,term_to_exp x2,term_to_exp x3) end
  | "Mat" => let val [x1,x2] = xs in Mat (term_to_exp x1,dest_list (dest_pair term_to_pat term_to_exp) x2) end
  | "Con" => let val [x1,x2] = xs in Con (fromHOLstring x1,dest_list term_to_exp x2) end
  | "Letrec" => let val [x1,x2] = xs in Letrec (dest_list (dest_pair fromHOLstring (dest_pair fromHOLstring term_to_exp)) x1,term_to_exp x2) end
  | "Raise" => let val [x1] = xs in Raise (term_to_error x1) end
  | s => raise Fail s
end handle (Fail s) => raise Fail s | _ => raise Fail (Parse.term_to_string tm)
fun term_to_t tm = let
  val (f,xs) = strip_comb tm
in case fst(dest_const f) of
    "Tnum" => Tnum
  | "Tvar" => let val [x1] = xs in Tvar (fromHOLstring x1) end
  | "Tapp" => let val [x1,x2] = xs in Tapp (dest_list term_to_t x1, fromHOLstring x2) end
  | s => raise Fail s
end handle (Fail s) => raise Fail s | _ => raise Fail (Parse.term_to_string tm)
fun term_to_dec tm = let
  val (f,xs) = strip_comb tm
in case fst(dest_const f) of
    "Dlet" => let val [x1,x2] = xs in Dlet (term_to_pat x1, term_to_exp x2) end
  | "Dtype" => let val [x1] = xs in Dtype (dest_list (dest_pair (dest_list fromHOLstring) (dest_pair fromHOLstring (dest_list (dest_pair fromHOLstring (dest_list term_to_t))))) x1) end
  | "Dletrec" => let val [x1] = xs in Dletrec (dest_list (dest_pair fromHOLstring (dest_pair fromHOLstring term_to_exp)) x1) end
  | s => raise Fail s
end handle (Fail s) => raise Fail s | _ => raise Fail (Parse.term_to_string tm)
val term_to_ov = v_to_ov o term_to_v

fun add_code c bs = bc_state_code_fupd
  (compile_labels (bc_state_inst_length bs) o (C append c))
  bs

fun prep_decs (bs,rs) [] = (bs,rs)
  | prep_decs (bs,rs) (d::ds) = let
      val (rs,c) = repl_dec rs (term_to_dec d)
      val bs = add_code c bs
    in prep_decs (bs,rs) ds end

fun prep_exp (bs,rs) e = let
  val (rs,c) = repl_exp rs (term_to_exp e)
  val bs = add_code c bs
in (bs,rs) end

fun prep_decs_exp (bs,rs) (ds,e) = let
  val (bs,rs) = prep_decs (bs,rs) ds
  val (bs,rs) = prep_exp (bs,rs) e
in (bs,rs) end

val inits = (init_bc_state, init_repl_state)

fun cpam rs = let val (_,(w,_)) = repl_state_contab rs in w end

fun mst_run_decs_exp (ds,e) = let
  val (bs,rs) = prep_decs_exp inits (ds,e)
  val bs = bc_eval bs
in (cpam rs, bc_state_stack bs) end

val run_decs_exp = snd o mst_run_decs_exp
fun mst_run_exp e = mst_run_decs_exp ([],e)
fun run_exp e = run_decs_exp ([],e)
end
