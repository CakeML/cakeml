open preamble
open set_sepTheory helperLib ml_translatorTheory
open ml_translatorTheory semanticPrimitivesTheory
open cfHeapsBaseTheory cfHeapsTheory cfHeapsBaseLib cfStoreTheory
open cfNormaliseTheory cfAppTheory
open cfTacticsBaseLib cfTheory

val _ = new_theory "cfDiv";

val app_POSTd = store_thm("app_POSTd",
  ``!p f xvs H Q.
      (?io events (Hs: num -> hprop).
        Q io /\
        H ==>> Hs 0 /\
        (!i. ?P. Hs i = P * one (FFI_full (events i))) /\
        (!i. LENGTH (events i) < LENGTH (events (i+1))) /\
        (!i. app p f xvs (Hs (SUC i)) (POSTd Q) ==>
             app p f xvs (Hs i) (POSTd Q)) /\
        (!i. LPREFIX (fromList (THE(events_of (Hs i)))) io))
      ==>
      app p f xvs H (POSTd Q)``,
  cheat);

val _ = export_theory();
