open preamble


val _ = new_theory "catfileSystem";

val _ = Datatype`
  RO_fs = <| files : (string # string) list ;
             infds : (num # (string # num)) list
  |>
`

val encode_files_def = Define`
  (encode_files [] = Num 0) ∧
  (encode_files ((s1,s2) :: t) =
     Cons (Cons (Str s1) (Str s2)) (encode_files t))
`;
val _ = export_rewrites ["encode_files_def"]

val encode_fds_def = Define`
  (encode_fds [] = Num 0) ∧
  (encode_fds ((n, (fname, offset)) :: t) =
    Cons (Cons (Num n) (Cons (Str fname) (Num offset))) (encode_fds t))
`;

val encode_def = Define`
  encode fs = cfHeapsBase$Cons (encode_files fs.files) (encode_fds fs.infds)
`

val decode_files_def = Define‘
  (decode_files (Cons (Cons (Str s1) (Str s2)) t) = (s1,s2) :: decode_files t) ∧
  (decode_files _ = [])
’
val _ = export_rewrites ["decode_files_def"]

val decode_encode_files = store_thm(
  "decode_encode_files",
  “∀l. decode_files (encode_files l) = l”,
  Induct >> simp[FORALL_PROD]);
(*
val decode_def = Define`
  decode (Cons files fds) = <|
    files := decode_files files ; infds := decode_fds fds
  |>
`;
*)

val _ = export_theory();
