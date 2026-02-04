(*
  Shuhan's misc utilities
*)
structure shLib = struct
local open HolKernel boolLib bossLib in

val ERR = mk_HOL_ERR "shLib"

(*
fun component_equality_of ty = let
  val accfn_terms = map (fn (_, rcd) => #accessor rcd) (TypeBase.fields_of ty)
  val cases_thm =  TypeBase.nchotomy_of ty
  val oneone_thm = TypeBase.one_one_of ty
  val accessor_thms = TypeBase.accessors_of ty
  val var1 = mk_var("a", ty)
  val var2 = mk_var("b", ty)
  val lhs = mk_eq(var1, var2)
  val rhs_tms =
    map (fn tm => mk_eq(mk_comb(tm, var1), mk_comb(tm, var2)))
    accfn_terms
  val rhs = list_mk_conj rhs_tms
  val goal = mk_eq(lhs, rhs)
  val tactic =
    REPEAT GEN_TAC THEN
    MAP_EVERY (STRUCT_CASES_TAC o C SPEC cases_thm) [var1, var2] THEN
    REWRITE_TAC (oneone_thm::accessor_thms)
  in prove(goal, tactic) end
*)

fun trivial_simps ty = let
  val {Thy, Tyop, ...} = dest_thy_type ty
  val t = mk_var ("t", ty)
  fun mk_eqn {accessor, fupd, ty=fty} = let
    (* fupd (K (accessor t)) *)
    val lhs = mk_comb (mk_comb (fupd, mk_comb (mk_const("K",fty-->fty-->fty), mk_comb (accessor, t))), t)
    in mk_eq (lhs, t) end
  val thm_tm = list_mk_conj (map (fn (_, fld) => mk_eqn fld) (TypeBase.fields_of ty))
  in prove (thm_tm, REWRITE_TAC[fetch Thy (Tyop^"_component_equality"), fetch Thy (Tyop^"_accfupds"), combinTheory.K_THM]) end

fun index_opt x L = let
  fun aux i L =
    case L of
      [] => NONE
    | y::L' =>
      if x=y then SOME i else aux (i+1) L'
  in aux 0 L end

fun array_index_opt x A = let
  val n = Array.length A
  fun aux i =
    if i<n then
      if Array.sub(A,i)=x then SOME i else aux (i+1)
    else NONE
  in aux 0 end

fun inplace_map f A = let
  val n = Array.length A
  fun loop i =
    if i<n then (Array.update (A, i, f(Array.sub(A,i))); loop (i+1))
    else ()
  in loop 0 end

fun const_thy_name tm = let
  val {Name, Thy, ...} = dest_thy_const tm
  in (Name, Thy) end

fun dest_fupd tm = let
  val ty = type_of tm
  val fupds = map (fn (_,{fupd,...}) => const_thy_name fupd) (TypeBase.fields_of ty) |> Array.fromList
  fun fupd_field_index t : int option =
    if is_const t then let
      val {Name, Thy, ...} = dest_thy_const t
      in array_index_opt (Name, Thy) fupds end
    else NONE
  val nf = Array.length fupds
  val updated_by: term list array =
    Array.array (nf, [])
  fun recurse t =
    if is_comb t then let
      val (r,dd) = strip_comb t
      in
        case fupd_field_index r of
          NONE => t
        | SOME i => let
          val [f,t'] = dd
          in
            Array.update (updated_by, i, f :: Array.sub (updated_by, i));
            recurse t'
          end
      end
    else t
  val inner_tm = recurse tm
  val _ = inplace_map rev updated_by
  in (inner_tm, updated_by) end;

(*
dest_fupd  ``a_fupd f (b_fupd g (a_fupd f' t))`` |> mk_fupd;
*)

fun is_thy_const (name, thy) tm =
  is_const tm andalso let
  val {Thy, Name, ...} = dest_thy_const tm
  in Name=name andalso Thy=thy end

fun mk_thy_const' ((name, thy), ty) =
  mk_thy_const {Thy=thy, Name=name, Ty=ty}

fun dest_K tm : term option =
  if is_comb tm then let
    val (r,d) = dest_comb tm
    in if is_thy_const ("K","combin") r then SOME d else NONE end
  else NONE

fun mk_fupd (tm, updated_by) = let
  val ty = type_of tm
  val fields = TypeBase.fields_of ty
  val fupds: (string*string) array =
    map (fn (_,{fupd,...}) => const_thy_name fupd) fields
    |> Array.fromList
  fun f (i,ff,a) = let
    fun g(f,a) = let
      val fupd = mk_thy_const' (Array.sub (fupds, i), type_of f --> type_of a --> ty)
      in list_mk_comb(fupd,[f,a]) end
    in foldr g a ff end
  in Array.foldri f tm updated_by end

fun record_canon_simp_conv tm = let
  val ty = type_of tm
  val _ = if TypeBase.is_record_type ty then () else raise UNCHANGED
  val fields = TypeBase.fields_of ty
  val accessors: (string*string) array =
    map (fn (_,{accessor,...}) => const_thy_name accessor) fields
    |> Array.fromList
  val fupds: (string*string) array =
    map (fn (_,{fupd,...}) => const_thy_name fupd) fields
    |> Array.fromList
  val {Thy, Tyop, ...} = dest_thy_type ty
  val fupdcanon = fetch Thy (Tyop^"_fupdcanon")
  val fupdfupds = fetch Thy (Tyop^"_fupdfupds")
  val (inner_tm, updated_by) = dest_fupd tm
  val nf = Array.length updated_by
  val fupds_deleted = ref false
  fun loop i a =
    if i<nf then
      case Array.sub (updated_by, i) of
        [] => loop (i+1) a
      | ff as (f::ff') =>
        ( case dest_K f of
          NONE => loop (i+1) a
        | SOME x (* new value of field *) =>
          (
            (* the rest of the updates, ff', are rendered useless by f = K x *)
            if null ff' then () else (Array.update (updated_by, i, [f]); fupds_deleted:=true);
            (* is x an application of the accessor fn on inner_tm? *)
            if is_comb x then let
              val (r,d) = dest_comb x
              in
                if is_thy_const (Array.sub (accessors, i)) r andalso term_eq d inner_tm then let
                  val fupd = mk_thy_const' (Array.sub (fupds, i), type_of f --> type_of a --> ty)
                  in
                    Array.update (updated_by, i, []);
                    fupds_deleted:=true;
                    loop (i+1) (list_mk_comb (fupd,[f,a]))
                  end
                else loop (i+1) a
              end
            else loop (i+1) a
          )
        )
    else a
  val inner_tm' = loop 0 inner_tm
  val tm1 = mk_fupd (inner_tm', updated_by) (* redundant fupds at the end *)
  val _ = if not(!fupds_deleted) andalso term_eq tm tm1 then raise UNCHANGED else ()
  val eq1 = prove (mk_eq (tm, tm1), REWRITE_TAC[fupdcanon,fupdfupds,combinTheory.K_o_THM])
  val eq2 = prove (mk_eq (inner_tm', inner_tm), REWRITE_TAC[trivial_simps ty])
  in TRANS eq1 (PURE_REWRITE_CONV [eq2] tm1) end

(* the rw1 tactic *)

fun term_set tms = HOLset.addList (empty_tmset, tms)

fun try_match_term M N =
  SOME (match_term M N) handle HOL_ERR _ => NONE

fun print_thm' name thm =
  (print name; print": "; print_thm thm; print"\n")

fun print_term' name tm =
  (print name; print": "; print_term tm; print"\n")

(*
fun disch_as_conj (a, thm) = let
  val (p,q) = dest_imp $ concl thm
  in EQ_MP (SPECL [a,p,q] boolTheory.AND_IMP_INTRO) (DISCH a thm) end
*)

fun dest_imp_n n tm = let
  fun f n a tm =
    if n>0 then let
      val (p,q) = dest_imp tm
      in f (n-1) (p::a) q end
    else (rev a, tm)
  in f n [] tm end

(* thm: Γ |- P ==> Q *)
fun simple_irule n_prem thm (asl,c) = let
  val (pp, q) = dest_imp_n n_prem $ concl thm
  val _ = if aconv q c then () else raise ERR "simple_irule" "concl of thm is not aconv to goal"
  val new_goals = map (fn p => (asl, p)) pp
  val vldn = foldl (fn(th,imp)=> MP imp th) thm
(*
  val vldn = fn thms => let
    val goal_thm = foldl (fn(th,imp)=> MP imp th) thm thms
    val extra_assums = HOLset.difference (HOLset.addList (empty_tmset, hyp goal_thm), HOLset.addList (empty_tmset, asl))
    in
      if HOLset.isEmpty extra_assums
      then () else (print"EXTRA ASSUMPTIONS!\n"; HOLset.listItems extra_assums |> app (print_term'"o"));
      goal_thm
    end
*)
  in (new_goals, vldn(*K(mk_thm(asl,c))*)) end

(*
  in UNDISCH $ prove_goal ((hyp thm, mk_imp (list_mk_exists (yy, p), q)), rw[]) end
*)

fun undisch_ex_all concl_fv thm = let
  val excluded_fv = HOLset.union (concl_fv, FVL (hyp thm) empty_tmset)
  fun undisch_ex thm = let
    val (p,q) = dest_imp $ concl thm
    val yy = HOLset.listItems $ HOLset.difference (FVL [p] empty_tmset, excluded_fv)
    val thm' = foldr (fn(y,thm) => CONV_RULE FORALL_IMP_CONV $ GEN y thm) thm yy
    val (p',_) = dest_imp $ concl thm'
    in (UNDISCH thm', p') end
  fun f a thm =
    if is_imp $ concl thm then let
      val (thm',p) = undisch_ex thm
      in f (p::a) thm' end
    else (thm, a)
  in f [] thm end

(* thm: Γ, R y ==> P x = Q x *)
fun rw1 thm = fn (asl,c) => let
  val spec_thm = SPEC_ALL $ GEN_ALL thm
  val (lhs, rhs) = dest_eq $ snd $ strip_imp $ concl spec_thm
  fun f ctx tm =
    case try_match_term lhs tm of
      SOME m => SOME (tm, ctx, m)
    | NONE =>
      case dest_term tm of
        VAR _ => NONE | CONST _ => NONE
      | COMB (tm1,tm2) =>
        (
          case f (fn tm => ctx $ mk_comb (tm,tm2)) tm1 of SOME x => SOME x | NONE =>
          f (fn tm => ctx $ mk_comb (tm1,tm)) tm2
        )
      | LAMB (x,tm1) =>
        f (fn tm => ctx $ mk_abs (x,tm)) tm1
  in
    case f I c of
      SOME (lhs', ctx, (sub, tysub)) => let
      val rhs' = subst sub $ inst tysub rhs
      val eq_fv = FVL [lhs',rhs'] empty_tmset
      val x(*placeholder*) = genvar (type_of lhs')
      val inst_spec_thm = INST sub $ INST_TYPE tysub spec_thm
      (* Γ, ∃y. R y |- P x = Q x *)
      val (eq, eq_assums) = undisch_ex_all eq_fv inst_spec_thm
      (* Γ, ∃y. R y |- C (Q x) ==> C (P x) *)
      val th1 = SUBST [x|->eq] (mk_imp (ctx x, c)) (DISCH c $ ASSUME c)
      val n_eq_assums = length eq_assums
      (* irule: Γ |- ∃y. R y ==> C (Q x) ==> C (P x) *)
      (* note that “C (P x)” itself may be an implication *)
      val th2 = foldl (uncurry DISCH) th1 eq_assums
(*
      val _ = print_thm' "irule" th2
*)
      in simple_irule (n_eq_assums+1) th2 (asl,c) end

    | NONE => raise ERR "rw1" "no match"
  end

end (*local*)

end (*struct*)
