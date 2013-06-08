(*Generated by Lem from compiler.lem.*)
open bossLib Theory Parse res_quanTheory
open fixedPointTheory finite_mapTheory listTheory pairTheory pred_setTheory
open integerTheory set_relationTheory sortingTheory stringTheory wordsTheory

val _ = numLib.prefer_num();



open ToBytecodeTheory ToIntLangTheory IntLangTheory CompilerPrimitivesTheory BytecodeTheory CompilerLibTheory SemanticPrimitivesTheory AstTheory LibTheory

val _ = new_theory "Compiler"

(*open Ast*)
(*open CompilerLib*)
(*open IntLang*)
(*open ToIntLang*)
(*open ToBytecode*)
(*open Bytecode*)

val _ = type_abbrev( "contab" , ``: (( conN id), num)fmap # (num # string) list # num``);
(*val cmap : contab -> Pmap.map (id conN) num*)
 val cmap_def = Define `
 (cmap (m,_,_) = m)`;


val _ = Hol_datatype `
 compiler_state =
  <| contab : contab
   ; rbvars : ( string id) list
   ; rnext_label : num
   |>`;


(*val cpam : compiler_state -> list (num * string)*)
 val cpam_def = Define `
 (cpam s = ((case s.contab of (_,w,_) => w )))`;


val _ = Define `
 (menv_cons mv mn s =  
((case FLOOKUP mv mn of
    NONE => FUPDATE  mv ( mn, [s])
  | SOME ls => FUPDATE  mv ( mn, (s ::ls))
  )))`;


(*val etC : compiler_state -> exp_to_Cexp_state * num * Pmap.map string (list num) * list ctbind*)
val _ = Define `
 (etC rs =  
(let (rsz,mvars,menv,bvars,env) = ( FOLDL
    (\ (i,mvars,menv,bvars,env) id .
      (case id of
        Short s => ((i +1),mvars,menv,(s ::bvars),((CTDec i) ::env))
      | Long mn s => ((i +1),menv_cons mvars mn s,menv_cons menv mn i,bvars,env)
      ))
    (0, FEMPTY, FEMPTY,[],[]) ( REVERSE rs.rbvars)) in
  (<| bvars := bvars ; mvars := mvars ; cnmap := ( cmap rs.contab) |>
  ,rsz,menv,env)))`;


val _ = Define `
 init_compiler_state =  
(<| contab := ( FUPDATE 
               ( FUPDATE 
                ( FUPDATE FEMPTY ( (Short ""), tuple_cn)) ( (Short "Bind"), bind_exc_cn)) ( (Short "Div"), div_exc_cn)
              (* TODO: don't need to store n, use length of list? *)
              ,[(tuple_cn,"");(bind_exc_cn,"Bind");(div_exc_cn,"Div")]
              ,3)
   ; rbvars := []
   ; rnext_label := 0
   |>)`;


val _ = Define `
 (compile_Cexp rsz menv env nl Ce =  
(let (Ce,n) = ( label_closures rsz nl Ce) in
  let cs = (<| out := []; next_label := n |>) in
  let (cs,l) = ( get_label cs) in
  let cs = ( emit cs [PushPtr (Lab l); PushExc]) in
  let cs = ( compile_code_env menv cs Ce) in
  (l, compile menv env TCNonTail (rsz +2) cs Ce)))`;


 val number_constructors_defn = Hol_defn "number_constructors" `

(number_constructors [] ct = ct)
/\
(number_constructors ((c,_)::cs) (m,w,n) =  
(number_constructors cs ( FUPDATE  m ( (Short c), n), ((n,c) ::w), (n +1))))`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) Defn.save_defn number_constructors_defn;

 val compile_news_defn = Hol_defn "compile_news" `

(compile_news cs i [] = cs)
/\
(compile_news cs i (_::vs) =  
(let cs = ( emit cs ( MAP Stack [Load 0; Load 0; El i; Store 1])) in
  compile_news cs (i +1) vs))`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) Defn.save_defn compile_news_defn;

val _ = Define `
 (compile_fake_exp rs vs e =  
(let (m,rsz,menv,env) = ( etC rs) in
  let Ce = ( exp_to_Cexp m (e (Con (Short "") ( MAP (\ v . Var (Short v)) vs)))) in
  let (l1,cs) = ( compile_Cexp rsz menv env rs.rnext_label Ce) in
  let cs = ( emit cs [PopExc; Stack (Pops 1)]) in
  let cs = ( compile_news cs 0 vs) in
  let (cs,l2) = ( get_label cs) in
  let cs = ( emit cs [Stack Pop; Stack (PushInt i0); Jump (Lab l2)
                   ; Label l1; Stack (PushInt i1); Label l2; Stop]) in
  (( rs with<| rbvars := ( REVERSE ( MAP Short vs)) ++rs.rbvars
    ; rnext_label := cs.next_label |>)
  ,( rs with<| rnext_label := cs.next_label |>)
  , REVERSE cs.out)))`;


 val compile_dec_def = Define `

(compile_dec rs (Dtype ts) =  
(let rs =    
(( rs with<| contab := FOLDL
         (\ct p . (case (ct ,p ) of ( ct , (_,_,cs) ) => number_constructors cs ct ))
         rs.contab ts |>)) in
  (rs,rs,[Stack (PushInt i0); Stop])))
/\
(compile_dec rs (Dletrec defs) =  
(let vs = ( MAP (\p . 
  (case (p ) of ( (n,_,_) ) => n )) defs) in
  compile_fake_exp rs vs (\ b . Letrec defs b)))
/\
(compile_dec rs (Dlet p e) =  
(let vs = ( pat_bindings p []) in
  compile_fake_exp rs vs (\ b . Mat e [(p,b)])))`;

val _ = export_theory()

