open HolKernel boolLib bossLib Parse astTheory terminationTheory
open cakeml_computeLib progToBytecodeTheory
open smpp Portable

fun fullEval p =
  let val asts = eval ``get_all_asts ^(p)``
      val elab = eval ``elab_all_asts ^(asts |> concl |> rhs)``
      in
        rhs(concl elab) |>rand 
      end;
(*RHS of theorem to term*)
val rhsThm = rhs o concl;

(*Return all intermediates during compilation in a record*)
fun allIntermediates prog =
  let val t1 = eval ``get_all_asts ^(prog)``
      val t2 = eval ``elab_all_asts ^(rhsThm t1)``
      val ast = rand (rhsThm t2)

      (*i1 translation*)
      val n = rhsThm (eval ``init_compiler_state.next_global``)
      val (m1,m2) = pairSyntax.dest_pair( rhsThm( eval ``init_compiler_state.globals_env``))
      val l1 = eval ``prog_to_i1 ^(n) ^(m1) ^(m2) ^(ast)``;
      val [v1,v2,m2,p1] = pairSyntax.strip_pair(rhsThm l1)    

      (*i2 translation*)
      val l2 = eval ``prog_to_i2 init_compiler_state.contags_env ^(p1) ``
      val (v,rest) = pairSyntax.dest_pair (rhsThm l2)
      val (exh,p2) = pairSyntax.dest_pair rest

      (*i3 translation*)
      val arg1 = rhsThm( eval ``(none_tag,SOME(TypeId (Short "option")))``)
      val arg2 = rhsThm( eval ``(some_tag,SOME(TypeId (Short "option")))``)
      val l3 = eval ``prog_to_i3 ^(arg1) ^(arg2) ^(n) ^(p2)``
      val (v,p3) = pairSyntax.dest_pair(rhsThm l3)

      (*exp to exh trans*)
      val exp_to_exh = eval ``exp_to_exh (^(exh) ⊌ init_compiler_state.exh) ^(p3)``
      val p4 = rhsThm exp_to_exh

      (*exp_to_pat trans*)
      val exp_to_pat = eval ``exp_to_pat [] ^(p4)``
      val p5 = rhsThm exp_to_pat
      
      (*exp_to_cexp*)
      val exp_to_Cexp = eval ``exp_to_Cexp ^(p5)``
      val p6 = rhsThm exp_to_Cexp

      (*compileCexp*)
      val compile_Cexp = eval ``compile_Cexp [] 0 <|out:=[];next_label:=init_compiler_state.rnext_label|> ^(p6)``
      val p7 = rhsThm compile_Cexp
  in
     {ast=ast,i1=p1,i2=p2,i3=p3,i4=p4,i5=p5,i6=p6,i7=p7,v1=v1,v2=v2,m2=m2}
  end;


(*Nested ifs*)
val ex1 = allIntermediates ``"exception Fail; if (if f x then veryyyyyyyyyyloooooooonggggggggg else z) then if(g z) then 5 else 4 else if abraasdasdabraahssdfaraser yasdafasdasdfasd then 4 else raise Fail;"``;

(*Top lvl mutually recursive functions and function calls*)
val ex2 = allIntermediates ``"fun f x y = (g x) + (g y) and g x = x+1; f 5 4; g it;"``;

(*raise, handle and case*)
val ex3 = allIntermediates ``"exception Fail of int; exception Odd; exception Even; val x = 1; (case x of 1 => 2 | 2 => raise Even | 3 => raise Odd | _ => raise Fail 4) handle Odd => 1 | Even => 0 | Fail n => n;"``;

(*Parse error*)
val ex4 = allIntermediates ``"structure Nat :> sig type nat val zero:nat val succ:nat-> nat end = struct type nat = int val zero = 0 fun succ x = x+1 end;"``;

(*HANGS Structs, using members of modules*)
val ex5 = allIntermediates ``"structure Nat = struct val zero = 0 fun succ x = x+1 end; val x = Nat.zero;"``;
(*Ok*)
val ex5b = allIntermediates ``"structure Nat = struct val zero = 0 fun succ x = x+1 end;"``;

(*Top lvl val, ref/deref*)
val ex6 = allIntermediates ``"val x = ref 5; x:= !x+1; x;"``;

(*datatypes, non exhausive pattern matching*)
val ex7 = allIntermediates ``"datatype 'a foo = Br of 'a * 'a foo * 'a foo | Lf of 'a | Nil; fun f x = case x of Br(v,l,r) => v + (f l) + (f r) | Lf v => v ; f (Br (1, Br(2,Lf 1, Lf 2), (Lf 1)));"``;

(*Pattern matching vals*)
val ex8 = allIntermediates ``"fun f x y z= x+y+z; val (x,y,z) = (f 1 1 1,f 2 2 2,f (f (f 3 3 3) 1 2));"``;

(*Coercion, parse error*)
val ex9 = allIntermediates ``"val x:int = 5;"`` 

(*complex datatypes*)

val ex10 = allIntermediates ``"datatype ('a,'b,'c) foo2 = Foo of 'a * 'b | Foo2 of 'b * 'c | Foo3 of 'a*'b*'c*('a,'a,'a) foo2;"``

(*Nested let vals*)

val ex12 = allIntermediates ``"val x = let val y = 1 val z = 2 in let val k = 3 in k+z+y end end;"``;
(*Inner lets*)
val ex11 = allIntermediates ``"val x = let fun f x = x + 1 val y = f 5 fun g z = y+1 and k y = g 1 val h = g 4 in let val k = 2 in k + f (f y) end end;"``;
