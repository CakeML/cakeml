(*Shared utility functions between printers*)

let check_extras = ref true;;

let unbaked s =
  if !check_extras then failwith ("unbaked "^s) else ();;

let rec is_exp_list l =
  match l with
  | Exp_construct ("[]",[]) -> true
  | Exp_construct ("::",[_; (_,l')]) -> is_exp_list l'
  | _ -> false;;

let rec is_pat_list l =
  match l with
  | Pat_construct ("[]",[]) -> true
  | Pat_construct ("::",[_; (_,l')]) -> is_pat_list l'
  | _ -> false;;

let nontrivial b p =
  match p with
  | (Typ_arrow (_,_),Pat_var "v__") -> true
  | (_,Pat_var _) -> false
  | (_,Pat_constraint ((_,Pat_var _),_)) -> b
  | _ -> true;;

let rec collect_args sl e =
  match snd e with
  | Exp_function [(_,Pat_var s),None,e'] -> collect_args (s::sl) e'
  | Exp_function [(_,Pat_constraint ((_,Pat_var s),_)),None,e'] ->
      (rev sl,e)
  | Exp_function _ -> unbaked "Exp_function"; (rev sl,e)
  | _ -> (rev sl,e);;

let rec extra_args n t sl =
  match t with
  | Typ_arrow (_,t') -> extra_args (n + 1) t' (("v__"^string_of_int n)::sl)
  | _ -> rev sl;;
