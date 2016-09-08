open preamble labLangTheory;

val _ = new_theory "lab_simp";

val lab_simp_sec_def = Define `
(lab_simp_sec (a :: b :: xs) =
 case (a, b) of
   | ((LabAsm (Jump (Lab n11 n21)) w wl n), (Label n12 n22 k))
     => if (n11 = n12 /\ n21 = n22) then (Asm (Inst Skip) wl n :: Label n12 n22 k :: lab_simp_sec xs) else (a :: b :: lab_simp_sec xs)
   | _ => a :: b :: lab_simp_sec xs) /\
(lab_simp_sec x = x)
`;

val lab_simp_def = Define `
(lab_simp ((Section k lines) :: sections) =
 let simpd = lab_simp_sec lines in
     if NULL simpd
     then lab_simp sections
     else (Section k simpd) :: lab_simp sections) /\
(lab_simp [] = [])`;

val _ = export_theory ();
