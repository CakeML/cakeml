open preamble labLangTheory;

val _ = new_theory "lab_simp";

val lab_simp_lines_def = Define `
(lab_simp_lines (a :: b :: xs) =
 case (a, b) of
   | ((LabAsm (Jump (Lab n11 n21)) w wl n), (Label n12 n22 k))
     => if (n11 = n12 /\ n21 = n22) then (Asm (Inst Skip) wl n :: Label n12 n22 k :: lab_simp_lines xs) else (a :: b :: lab_simp_lines xs)
   | _ => a :: b :: lab_simp_lines xs) /\
(lab_simp_lines x = x)`;

val lab_simp_sec_def = Define`
  lab_simp_sec (Section k ls) = Section k (lab_simp_lines ls)`;
val _ = export_rewrites["lab_simp_sec_def"];

val has_last_jump_def = Define`
  (has_last_jump k i [] ⇔ NONE) ∧
  (has_last_jump k i (x::xs) ⇔
    case x of
    | (LabAsm (Jump k') _ wl n) =>
      if k = k' ∧ EVERY (λx. is_Label x ∨ is_Skip x) xs then SOME (i,wl,n)
      else has_last_jump k (i+1n) xs
    | _ => has_last_jump k (i+1n) xs)`;

val replace_last_jump_def = Define`
  replace_last_jump k ls =
    case has_last_jump (Lab k 0) 0 ls of NONE => ls
    | SOME (i,wl,n) => LUPDATE (Asm (Inst Skip) wl n) i ls`;

val remove_tail_jumps_def = Define`
  (remove_tail_jumps [] = []) ∧
  (remove_tail_jumps [s] = [s]) ∧
  (remove_tail_jumps (Section k1 l1::(Section k2 l2::ss)) =
   Section k1 (replace_last_jump k2 l1)::remove_tail_jumps (Section k2 l2::ss))`;

val lab_simp_def = Define `
  lab_simp ss = remove_tail_jumps (MAP lab_simp_sec ss)`;

val _ = export_theory ();
