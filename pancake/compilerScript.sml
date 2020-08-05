(*
  Composes all of the compiler phases into
  a single compiler function
*)

open pan_to_crepTheory
     crep_to_loopTheory
     loop_to_loopliveTheory
     loop_to_loopremoveTheory
     loop_to_wordTheory
     backendTheory;

val _ = new_theory "compiler"


Datatype:
  clconfig =
  <| cl : num_set;
     cctxt : 'a crep_to_loop$context|>
End

Datatype:
  lwconfig =
  <| name : num
   ; params : num list
   ; p : 'a loopLang$prog # 'a loopLang$prog
   ; cont : 'a loopLang$prog
   ; s : num # (num # num list # 'a loopLang$prog) list
   |>
End

Datatype:
  context =
  <| pan_conf  : 'a pan_to_crep$context
   ; crep_conf : 'a clconfig
   ; loop_conf : 'a lwconfig
   |>
End

Definition from_loop_def:
 from_loop (ct:'a context) (conf:'a config) p =
   let ct = ct.loop_conf in
   let p = loop_to_word$compile ct.name ct.params ct.p ct.cont ct.s p in
    from_word conf [(ARB, ARB, p)]
End

Definition from_crep_def:
 from_crep (ctxt:'a context) (conf:'a config) p =
   let ct = ctxt.crep_conf in
   let p = crep_to_loop$compile ct.cctxt ct.cl p in
    from_loop ctxt conf p
End

Definition from_pan_def:
 from_pan (ct:'a context) (conf:'a config) p =
  let p = pan_to_crep$compile ct.pan_conf p in
  from_crep ct conf p
End


(* compile in x_to_y format *)


(*
Theorem compile_eq_from_source:
   compile = from_source
Proof
QED
*)

(* look for from_source *)



val _ = export_theory();
