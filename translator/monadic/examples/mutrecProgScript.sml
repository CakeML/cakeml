open preamble ml_translatorLib ml_translatorTheory

val _ = new_theory "mutrecProg";

val _ = Hol_datatype `
data = C1 of num | C2 of data list`;

val data_length_def = Define `data_length1 (C1 x) = x /\
        data_length1 (C2 x) = data_length2 x /\
        data_length2 (x::xl) = data_length1 x + data_length2 xl /\
        data_length2 [] = 0`;
val def = data_length_def;

val return_x_def = Define `return_x x = x`;
val def = return_x_def;

(* Precondition *)
val test1_def = Define `test1 (x:num) = x`;
val res = translate test1_def;

val test6_def = Define `
test6 (x::l) = (let (y : num) = test6 l in
(let z = test1 (x : num) in (x + y + z))) /\
test6 [] = (0 : num)`;
val def = test6_def;
val test6_v_th = translate test6_def;

val _ = export_theory();
