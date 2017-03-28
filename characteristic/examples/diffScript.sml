open preamble lcsTheory mlintTheory mlstringTheory;

val _ = new_theory "diff";

val line_numbers_def = Define `
  (line_numbers l n =
   if LENGTH l <= 1 then
     toString(int_of_num n)
   else
      strcat (toString(int_of_num n)) (strcat(implode ",") (toString(int_of_num (n+LENGTH l)))))`

val acd_def = Define `
  (acd [] [] = #" ")
  /\ (acd l [] = #"d")
  /\ (acd [] l = #"a")
  /\ (acd l l' = #"c")`

val diff_single_header_def = Define `
  (diff_single_header l n l' n' =
    strcat (line_numbers  l n) (strcat (implode [acd l l']) (line_numbers l' n')))`

val diff_add_prefix_def = Define `
  diff_add_prefix l h = MAP (strcat h) l `

val diff_single_def = Define `
  diff_single l n l' n' =
    diff_single_header l n l' n'::
    if l = [] then (* add *)
      diff_add_prefix l' (strlit "> ")
    else if l' = [] then (* delete *)
      diff_add_prefix l (strlit "< ")
    else (* change *)
      diff_add_prefix l (strlit "< ")
      ++ (strlit "---")::diff_add_prefix l' (strlit "> ")`

val diff_with_lcs_def = Define `
  (diff_with_lcs [] l n l' n' =
      if l = [] /\ l' = [] then
        []
      else
        diff_single l n l' n') /\
  (diff_with_lcs (f::r) l n l' n' =
      let (ll,lr) = SPLITP ($= f) l in
        let (l'l,l'r) = SPLITP ($= f) l' in
          if ll = [] /\ l'l = [] then
            diff_with_lcs r (TL lr) (n+1) (TL l'r) (n+1)
          else
            diff_single ll n l'l n' ++ diff_with_lcs r (TL lr) (n+LENGTH ll+1) (TL l'r) (n'+LENGTH l'l+1))`

val diff_def = Define `
  diff l l' = diff_with_lcs (optimised_lcs l l') l 0 l' 0`

val _ = export_theory ();
