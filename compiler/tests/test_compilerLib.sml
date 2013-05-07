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
fun term_to_num tm = numML.fromString(Parse.term_to_string tm)
fun term_to_bool tm = tm = boolSyntax.T
fun fromId tm = fromHOLstring(rand(tm))
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
  | "Pcon" => let val [x1,x2] = xs in Pcon (Short(fromId x1), dest_list term_to_pat x2) end
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
  | "Conv" => let val [x1,x2] = xs in Conv (Short(fromId x1),dest_list term_to_v x2) end
  | s => raise Fail s
end handle (Fail s) => raise Fail s | _ => raise Fail (Parse.term_to_string tm)
and term_to_exp tm = let
  val (f,xs) = strip_comb tm
in case fst(dest_const f) of
    "Lit" => let val [x1] = xs in Lit (term_to_lit x1) end
  | "If"  => let val [x1,x2,x3] = xs in If (term_to_exp x1, term_to_exp x2, term_to_exp x3) end
  | "App" => let val [x1,x2,x3] = xs in App (term_to_op_ x1, term_to_exp x2, term_to_exp x3) end
  | "Fun" => let val [x1,x3] = xs in Fun (fromHOLstring x1, term_to_exp x3) end
  | "Var" => let val [x1] = xs in Var (Short(fromId x1)) end
  | "Let" => let val [x2,x4,x5] = xs in Let (fromHOLstring x2,term_to_exp x4,term_to_exp x5) end
  | "Mat" => let val [x1,x2] = xs in Mat (term_to_exp x1,dest_list (dest_pair term_to_pat term_to_exp) x2) end
  | "Con" => let val [x1,x2] = xs in Con (Short(fromId x1),dest_list term_to_exp x2) end
  | "Letrec" => let val [x1,x2] = xs in Letrec (dest_list (dest_pair fromHOLstring (dest_pair fromHOLstring term_to_exp)) x1,term_to_exp x2) end
  | "Raise" => let val [x1] = xs in compileML.Raise (term_to_error x1) end
  | s => raise Fail (s^"1")
end handle (Fail s) => raise Fail s | _ => raise Fail ((Parse.term_to_string tm)^"2")
fun term_to_tc tm = let
  val (f,xs) = strip_comb tm
in case fst(dest_const f) of
    "TC_name" => let val [x1] = xs in TC_name (Short(fromId x1)) end
  | "TC_int" => TC_int
  | "TC_bool" => TC_bool
  | "TC_unit" => TC_unit
  | "TC_ref" => TC_ref
  | "TC_fn" => TC_fn
end handle (Fail s) => raise Fail s | _ => raise Fail (Parse.term_to_string tm)
fun term_to_t tm = let
  val (f,xs) = strip_comb tm
in case fst(dest_const f) of
    "Tvar" => let val [x1] = xs in Tvar (fromHOLstring x1) end
  | "Tvar_db" => let val [x1] = xs in Tvar_db (term_to_num x1) end
  | "Tapp" => let val [x1,x2] = xs in Tapp (dest_list term_to_t x1, term_to_tc x2) end
  | s => raise Fail s
end handle (Fail s) => raise Fail s | _ => raise Fail (Parse.term_to_string tm)
fun term_to_dec tm = let
  val (f,xs) = strip_comb tm
in case fst(dest_const f) of
    "Dlet" => let val [x2,x3] = xs in Dlet (term_to_pat x2, term_to_exp x3) end
  | "Dtype" => let val [x1] = xs in Dtype (dest_list (dest_pair (dest_list fromHOLstring) (dest_pair fromHOLstring (dest_list (dest_pair fromHOLstring (dest_list term_to_t))))) x1) end
  | "Dletrec" => let val [x1] = xs in Dletrec (dest_list (dest_pair fromHOLstring (dest_pair fromHOLstring term_to_exp)) x1) end
  | s => raise Fail s
end handle (Fail s) => raise Fail s | _ => raise Fail (Parse.term_to_string tm)
val term_to_ov = v_to_ov [] o term_to_v

fun add_code c bs = bc_state_code_fupd
  (compile_labels (bc_state_inst_length bs) o (C append c))
  bs

fun prep_decs (bs,rs) [] = (bs,rs)
  | prep_decs (bs,rs) (d::ds) = let
      val (rs,c) = compile_dec rs (term_to_dec d)
      val bs = add_code c bs
    in prep_decs (bs,rs) ds end

fun prep_exp (bs,rs) e = prep_decs (bs,rs) [``Dlet (Pvar "it") ^e``]

fun prep_decs_exp (bs,rs) (ds,e) = let
  val (bs,rs) = prep_decs (bs,rs) ds
  val (bs,rs) = prep_exp (bs,rs) e
in (bs,rs) end

val inits = (init_bc_state, init_compiler_state)

fun mst_run_decs_exp (ds,e) = let
  val (bs,rs) = prep_decs_exp inits (ds,e)
  val (SOME bs) = bc_eval bs
in (cpam rs, bc_state_stack bs) end

val run_decs_exp = snd o mst_run_decs_exp
fun mst_run_exp e = mst_run_decs_exp ([],e)
fun run_exp e = run_decs_exp ([],e)

val int_toString = Int.toString o valOf o intML.toInt

fun print_prim2 CSub = "-"
| print_prim2 CEq = "="
| print_prim2 x =  (PolyML.print x; raise Match)
fun sp d = String.implode(List.tabulate (d,(K #" ")))
val print_Cexp = let fun
  f d (CLet (e1,e2)) = (sp d)^"let _ =\n"^(f (d+2) e1)^"\n"^(sp d)^"in\n"^(f (d+2) e2)
| f d (CFun (_,(n,e))) = (sp d)^"fn"^(numML.toString n)^" =>\n"^(f (d+2) e)
| f d (CLit (IntLit n)) = (sp d)^(int_toString n)
| f d (CLit (Bool true)) = (sp d)^"true"
| f d (CLit (Bool false)) = (sp d)^"false"
| f d (CCall (e,es)) = (sp d)^(f 0 e)^"("^(fs es)^")"
| f d (CPrim2 (p2,e1,e2)) = (f d e1)^"\n"^sp(d+2)^(print_prim2 p2)^"\n"^(f d e2)
| f d (CIf (e1,e2,e3)) = (sp d)^"if\n"^(f (d+2) e1)^"\n"^(sp d)^"then\n"^(f (d+2) e2)^"\n"^(sp d)^"else\n"^(f (d+2) e3)
| f d (CVar n) = (sp d)^"v"^(numML.toString n)
| f d (CRaise err) = (sp d)^"raise "^(PolyML.makestring err)
| f d x = (PolyML.print x; raise Match)
and
  fs [] = ""
| fs [e] =  f 0 e
| fs (e::es) = (f 0 e)^","^(fs es)
in f end
fun loc_to_string (Addr n) = "Addr "^(numML.toString n)
  | loc_to_string (Lab l) = "Lab "^(numML.toString l)
val print_bc_stack_op = let fun
  f (Load n) = "Load "^(numML.toString n)
| f (El n) = "El "^(numML.toString n)
| f (Pops n) = "Pops "^(numML.toString n)
| f (PushInt n) = "PushInt "^(int_toString n)
| f (TagEq n) = "TagEq "^(numML.toString n)
| f Equal = "Equal"
| f (Cons (n,m)) = "Cons "^(numML.toString n)^" "^(numML.toString m)
| f (Shift (n,m)) = "Shift "^(numML.toString n)^" "^(numML.toString m)
| f (Store n) = "Store "^(numML.toString n)
| f Pop = "Pop"
| f Sub = "Sub"
| f x = (PolyML.print x; raise Match)
in f end
val print_bc_inst = let fun
  f (Stack sop) = "Stack "^(print_bc_stack_op sop)
| f CallPtr = "CallPtr"
| f JumpPtr = "JumpPtr"
| f Return = "Return"
| f Deref = "Deref"
| f Ref = "Ref"
| f PopExc = "PopExc"
| f Update = "Update"
| f (Jump n) = "Jump "^(loc_to_string n)
| f (JumpIf n) = "JumpIf "^(loc_to_string n)
| f (PushPtr n) = "PushPtr "^(loc_to_string n)
| f x = (PolyML.print x; raise Match)
in f end
fun
  print_bv (Block (t,vs)) = "Block "^(numML.toString t)^" ["^(print_bvs vs)
| print_bv (CodePtr n) = "CodePtr "^(numML.toString n)
| print_bv (RefPtr n) = "RefPtr "^(numML.toString n)
| print_bv (Number n) = "Number "^(Int.toString (valOf (intML.toInt n)))
and print_bvs [] = "]" | print_bvs [bv] = (print_bv bv)^"]" | print_bvs (bv::bvs) = (print_bv bv)^", "^(print_bvs bvs)
fun print_bs bs =
(("stack", map print_bv (bc_state_stack bs)),
 ("pc", numML.toString(bc_state_pc bs)),
 ("code", rev(snd(foldl (fn (i,(n,ls)) => (n+1,((Int.toString n)^": "^print_bc_inst i)::ls)) (0,[]) (bc_state_code bs)))),
 ("refs", let val f = bc_state_refs bs in map (fn k => (numML.toString k,print_bv(fmapML.FAPPLY f k))) (sort (numML.<) (mk_set (setML.toList (fmapML.FDOM f)))) end))

end
