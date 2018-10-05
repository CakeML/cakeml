open preamble
open set_sepTheory helperLib ml_translatorTheory
open ml_translatorTheory semanticPrimitivesTheory
open cfHeapsBaseTheory cfHeapsTheory cfHeapsBaseLib cfStoreTheory
open cfNormaliseTheory cfAppTheory
open cfTacticsBaseLib cfTheory

val _ = new_theory "cfDiv";

val events_of_def = Define`
  events_of H = some events. ?Q. H = Q * one(FFI_full events)`

val imp_app_POSTd = store_thm("imp_app_POSTd",
  ``!p f xvs H Q.
      (?io (Hs: num -> hprop).
        Q io /\
        Hs 0 = H /\
        (!i. IS_SOME(events_of(Hs i))) /\
        (!i. LENGTH(THE(events_of(Hs i))) <
             LENGTH(THE(events_of(Hs (SUC i))))) /\
        (!i. app p f xvs (Hs (SUC i)) (POSTd Q) ==>
             app p f xvs (Hs i) (POSTd Q)) /\
        (!i. LPREFIX (fromList (THE(events_of (Hs i)))) io))
      ==>
      app p f xvs H (POSTd Q)``,
  cheat);

val _ = export_theory();
