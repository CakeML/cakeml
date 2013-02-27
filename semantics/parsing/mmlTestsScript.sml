open HolKernel Parse boolLib bossLib

open mmlPEGTheory mmlGrammarTheory grammarTheory

val _ = new_theory "mmlTests"

val distinct_ths = let
  val ntlist = TypeBase.constructors_of ``:MMLnonT``
  fun recurse [] = []
    | recurse (t::ts) = let
      val eqns = map (fn t' => mk_eq(t,t')) ts
      val ths0 = map (SIMP_CONV (srw_ss()) []) eqns
      val ths1 = map (CONV_RULE (LAND_CONV (REWR_CONV EQ_SYM_EQ))) ths0
    in
      ths0 @ ths1 @ recurse ts
    end
in
  recurse ntlist
end

val _ = computeLib.add_thms distinct_ths computeLib.the_compset

val result_t = ``Result``
fun tytest s t = let
  val ttoks = rhs (concl (EVAL ``MAP TK ^t``))
  val _ = print ("Evaluating "^s^"\n")
  val evalth = time EVAL
                    ``peg_exec mmltyPEG (nt (mkNT nType) I) ^t [] done failed``
  val r = rhs (concl evalth)
  fun diag(s,t) = let
    fun pp pps (s,t) =
        (PP.begin_block pps PP.CONSISTENT 0;
         PP.add_string pps s;
         PP.add_break pps (1,2);
         pp_term pps t;
         PP.end_block pps)
  in
    print (PP.pp_to_string 79 pp (s,t) ^ "\n")
  end
  fun die (s,t) = (diag (s,t); raise Fail "Failed")

in
  if same_const (rator r) result_t then
    if optionSyntax.is_some (rand r) then let
      val pair = rand (rand r)
      val remaining_input = pair |> rator |> rand
      val res = pair |> rand |> rator |> rand
    in
      if listSyntax.is_nil remaining_input then let
        val _ = diag ("EVAL to: ", res)
        val fringe_th = EVAL ``ptree_fringe ^res``
        val fringe_t = rhs (concl fringe_th)
        val _ = diag ("fringe = ", fringe_t)
      in
        if aconv fringe_t ttoks then let
          val ptree_res = time EVAL ``ptree_Type ^res``
          val _ = diag ("ptree_Type to ", rhs (concl ptree_res))
          val valid_t = ``valid_ptree mmlG ^res``
          val vth = SIMP_CONV (srw_ss())
                              [grammarTheory.valid_ptree_def, mmlG_def,
                               DISJ_IMP_THM, FORALL_AND_THM]
                              valid_t
          val vres = rhs (concl vth)
        in
          if aconv boolSyntax.T vres then print "Valid\n"
          else die ("Invalid parse-tree: ", vres)
        end
        else die ("Fringe not preserved!", ttoks)
      end
      else die ("REMANING INPUT:", pair)
    end
    else die ("FAILED:", r)
  else die ("NO RESULT:", r)
end

val _ = tytest "'a" ``[TyvarT "'a"]``
val _ = tytest "'a -> bool" ``[TyvarT "'a"; ArrowT; AlphaT "bool"]``
val _ = tytest "'a -> bool -> foo"
                     ``[TyvarT "'a"; ArrowT; AlphaT "bool"; ArrowT;
                        AlphaT "foo"]``
val _ = tytest "('a)" ``[LparT; TyvarT "'a"; RparT]``
val _ = tytest "('a)list" ``[LparT; TyvarT "'a"; RparT; AlphaT "list"]``
val _ = tytest "('a->bool)list"
               ``[LparT; TyvarT "'a"; ArrowT; AlphaT "bool"; RparT;
                  AlphaT "list"]``
val _ = tytest "'a->bool list"
               ``[TyvarT "'a"; ArrowT; AlphaT "bool"; AlphaT "list"]``
val _ = tytest "('a->bool)->bool"
                     ``[LparT; TyvarT "'a"; ArrowT; AlphaT "bool"; RparT;
                        ArrowT; AlphaT "bool"]``
val _ = tytest "('a,foo)bar"
                     ``[LparT; TyvarT "'a";CommaT;AlphaT"foo";
                        RparT;AlphaT"bar"]``
val _ = tytest "('a) list list" ``[LparT; TyvarT "'a"; RparT; AlphaT"list";
                                   AlphaT"list"]``
val _ = tytest "('a,'b) foo list"
               ``[LparT; TyvarT "'a"; CommaT; TyvarT"'b"; RparT; AlphaT"foo";
                  AlphaT"list"]``
val _ = tytest "'a list" ``[TyvarT "'a"; AlphaT "list"]``
val _ = tytest "'a list list" ``[TyvarT "'a"; AlphaT "list"; AlphaT "list"]``
val _ = tytest "bool list list" ``[AlphaT "bool"; AlphaT "list"; AlphaT "list"]``
val _ = tytest "('a,bool list)++"
               ``[LparT; TyvarT "'a"; CommaT; AlphaT "bool"; AlphaT "list";
                  RparT; SymbolT"++"]``

val _ = export_theory()
