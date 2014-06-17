open HolKernel boolLib bossLib Parse astTheory terminationTheory sptreeTheory conLangProofTheory
open cakeml_computeLib progToBytecodeTheory
open smpp Portable

set_trace"pp_avoids_symbol_merges"0;

fun fullEval p =
  let val asts = eval ``get_all_asts ^(p)``
      val elab = eval ``elab_all_asts ^(asts |> concl |> rhs)``
      in
        rhs(concl elab) |>rand 
      end;
(*RHS of theorem to term*)
val rhsThm = rhs o concl;

val compile_primitives_def = Define`
  compile_primitives =
    FST(compile_top NONE init_compiler_state
    (Tdec initial_program))`;

val cs = cakeml_compset();
val _ = computeLib.add_thms [compile_primitives_def,compilerTheory.compile_top_def] cs
val eval = computeLib.CBV_CONV cs
val compile_primitives_full = eval ``compile_primitives``

val cs = cakeml_compset();
val _ = computeLib.add_thms [compile_primitives_full] cs
val eval = computeLib.CBV_CONV cs
val compile_primitives_pieces =
  LIST_CONJ[
  eval ``compile_primitives.globals_env``
  ,eval ``compile_primitives.next_global``
  ,eval ``compile_primitives.exh``
  ,eval ``compile_primitives.contags_env``
  ,eval ``compile_primitives.rnext_label``];
val cs = cakeml_compset();
val _ = computeLib.add_thms [compile_primitives_pieces] cs
val eval = computeLib.CBV_CONV cs

(*Return all intermediates during compilation in a record*)
fun allIntermediates prog =
  let val t1 = eval ``get_all_asts ^(prog)``
      val t2 = eval ``elab_all_asts ^(rhsThm t1)``
      val ast = rand (rhsThm t2)
      
      (*i1 translation*)
      val n = rhsThm (eval ``compile_primitives.next_global``)
      val (m1,m2) = pairSyntax.dest_pair( rhsThm( eval ``compile_primitives.globals_env``))
      val l1 = eval ``prog_to_i1 ^(n) ^(m1) ^(m2) ^(ast)``
      val [v1,v2,m2,p1] = pairSyntax.strip_pair(rhsThm l1)    

      (*Assume start from fempty*)
      val (_,modMap) = finite_mapSyntax.strip_fupdate v2
      val (_,globMap) = finite_mapSyntax.strip_fupdate m2

      (*i2 translation*)
      val l2 = eval ``prog_to_i2 compile_primitives.contags_env ^(p1) ``
      val (v,rest) = pairSyntax.dest_pair (rhsThm l2)
      val (exh,p2) = pairSyntax.dest_pair rest

      val p2' = (v,exh,p2)
      (*print the CTORS (num,name,typeid)*)
      val [_,_,_,ct] =pairSyntax.strip_pair v 

      val (_,ctors) = finite_mapSyntax.strip_fupdate ct;
      (*i3 translation*)
      val arg1 = rhsThm( eval ``(none_tag,SOME(TypeId (Short "option")))``)
      val arg2 = rhsThm( eval ``(some_tag,SOME(TypeId (Short "option")))``)
      val l3 = eval ``prog_to_i3 ^(arg1) ^(arg2) ^(n) ^(p2)``
      val (v,p3) = pairSyntax.dest_pair(rhsThm l3)

      (*exp to exh trans*)
      val exp_to_exh = eval ``exp_to_exh (^(exh) ⊌ compile_primitives.exh) ^(p3)``
      val p4 = rhsThm exp_to_exh

      (*exp_to_pat trans*)
      val exp_to_pat = eval ``exp_to_pat [] ^(p4)``
      val p5 = rhsThm exp_to_pat
      
      (*exp_to_cexp*)
      val exp_to_Cexp = eval ``exp_to_Cexp ^(p5)``
      val p6 = rhsThm exp_to_Cexp

      (*compileCexp*)
      val compile_Cexp = eval ``compile_Cexp [] 0 <|out:=[];next_label:=compile_primitives.rnext_label|> ^(p6)``
      val p7 = rhsThm compile_Cexp
  in
     {ast=ast,i1=p1,i2=p2,i3=p3,i4=p4,i5=p5,i6=p6,i7=p7,ctors = ctors,globMap=globMap,modMap=modMap}
  end;

(*Not included yet*)
val compile_print_err = eval ``compile_print_err ^(r)``
val r = rhs(concl compile_print_err)

val addIt = eval ``case FLOOKUP ^(m2) "it" of
                             NONE => ^(r)
                           | SOME n =>
                               (let r = emit ^(r) [Gread n; Print]
                                in
                                  emit r (MAP PrintC (EXPLODE "\n")))``
val r = rhs(concl addIt)
val emit = eval ``emit ^(r) [Stop T]``
val rev = eval ``REVERSE (^(rhs(concl emit))).out``

(*Nested ifs*)
val ex1 = allIntermediates ``"exception Fail; val x = 5+4; if( (if(x>4 andalso x>5) then 5 else 4) > 3 ) then (if x>5 then 4 else 5) else (if x<2 orelse x>100 then 3 else raise Fail);"``;

(*Top lvl mutually recursive functions and function calls*)
val ex2 = allIntermediates ``"fun f x y = (g x) + (g y) and g x = x+1; f 5 4; g it;"``;

(*raise, handle and case*)
val ex3 = allIntermediates ``"exception Fail of int; exception Odd; exception Even; val x = 1; (case x of 1 => 2 | 2 => raise Even | 3 => raise Odd | _ => raise Fail 4) handle Odd => 1 | Even => 0 | Fail n => n;"``;

(*Parse error*)
val ex4 = allIntermediates ``"structure Nat :> sig type nat val zero:nat val succ:nat-> nat end = struct datatype nat = Int of int val zero = Int 0 fun succ (Int x) = (Int (x+1)) end;"``;

(*HANGS Structs, using members of modules*)
val prog = ``"structure Nat = struct val zero = 0 fun succ x = x+1 end; val x = Nat.zero;"``;
val ex5 = allIntermediates ``"structure Nat = struct val zero = 0 fun succ x = x+1 end; val x = Nat.succ(Nat.zero);"``;
(*Ok*)
val ex5b = allIntermediates ``"structure Nat = struct val zero = 0 fun succ x = x+1 end;"``;

(*Top lvl val, ref/deref*)
val ex6 = allIntermediates ``"val x = ref 5; x:= 1+!x;"``;

val ex6= allIntermediates ``"fun f y = let val x = ref y in x:= !x+1 end;"``;
(*
val prog = #ast ex6
val tm = prog
val [tm] = tops
datatype top_result = Tdec of ...
datatype exp_view = 

fun dest_top tm =
  case total (match_term  ``Tdec dec``) tm
   of NONE =>
         case total (match_term ``Tmod ...``) tm of...
   | SOME [s] =>
     Tdec (#residue s)
    val s = match_term ``Tdec dec`` tm
   

fun pp_top tm acc =
  case dest_top tm of

fun pp_prog tm acc =
  let
    val (tops,_) = listSyntax.dest_list tm
  in
    List.foldr (uncurry pp_top) acc tops
  end
*)
(*datatypes, non exhausive pattern matching*)
val ex7 = allIntermediates ``"datatype 'a foo = Br of 'a * 'a foo * 'a foo | Lf of 'a | Nil; fun f x = case x of Br(v,l,r) => v + (f l) + (f r) | Lf v => v ; f (Br (1, Br(2,Lf 1, Lf 2), (Lf 1)));"``;

(*Pattern matching vals*)
val ex8 = allIntermediates ``"fun f x y z= x+y+z; val (x,y,z) = (f 1 1 1,f 2 2 2,f (f (f 3 3 3) 1 2));"``;

(*Coercion, parse error*)
val ex9 = allIntermediates ``"val x:int = 5;"`` 

(*complex datatypes*)

val ex10 = allIntermediates ``"datatype ('a,'b,'c) foo2 = Foo of 'a * 'b | Foo2 of 'b * 'c | Foo3 of 'a*'b*'c*('a,'a,'a) foo2;"``

(*Nested let vals*)

(*Inner lets*)

val ex11 = allIntermediates ``"val x = let fun f x = x + 1 val y = f 5 fun g z = y+1 and k y = g 1 val h = g 4 in let val k = 2 in k + f (f y) end end;"``;

val ex12 = allIntermediates ``"val x = let val y = (let val k = 4 in k+5 end) val z = 2 in let val k = 3 in k+z+y end end;"``;

(*Closures*)

val ex13 = allIntermediates ``"fun f x = (fn y => x+y); (if true then (f 2) else (f 3)) 3;"``

(*Nested letrec*)
val ex14 = allIntermediates ``"val it = let fun f x = g (x-1) and g x = if x = 0 then 1 else f (x-1) in f end 3;"``

(*top level letrec*)
val ex15 = allIntermediates ``"fun fabracadabra x = gabracadabra (x-1) and gabracadabra x = if x = 0 then 1 else fabracadabra (x-1); fabracadabra 3;"``

(*Exceptions*)
val ex16 = allIntermediates ``"exception E of int*int->string*unit;"``

(*Datatypes*)
val ex17 = allIntermediates ``"datatype tree = Br of int * tree * tree | Lf;"``

(*Lists*)
val ex18 = allIntermediates ``"fun append xs ys = case xs of [] => ys | (x::xs) => x :: append xs ys; fun reverse xs = case xs of [] => [] | x::xs => append (reverse xs) [x];"``

val ex19 = allIntermediates ``"val x = \"hello\";"``;

val ex20 = allIntermediates ``"structure Nat = struct val zero = 0 fun succ x = x+1 fun iter f n = if n = 0 then (fn x=> x) else f o (iter f n) end; (Nat.iter Nat.succ 5) Nat.zero;"``;
