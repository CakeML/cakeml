(*
  Module for text-based I/O with the underlying file system.
*)
Theory TextIOProg
Ancestors
  ml_translator CommandLineProg MarshallingProg
Libs
  preamble ml_translatorLib ml_progLib basisFunctionsLib
  semanticPrimitivesSyntax

val _ = translation_extends "MarshallingProg";

val cakeml = append_prog o process_topdecs;

val _ = ml_prog_update (open_module "TextIO");

val _ = ml_prog_update open_local_block;

(*
Definition get_buffered_in_def:
  get_out (InstreamBuffered)
End
*)

Datatype:
  instream = Instream mlstring
End

Datatype:
  outstream = Outstream mlstring
End

Definition get_out_def:
  get_out (Outstream s) = s
End

Definition get_in_def:
  get_in (Instream s) = s
End

val _ = (use_full_type_names := false);
val _ = register_type ``:instream``;
val _ = register_type ``:outstream``;
val _ = (use_full_type_names := true);

Quote cakeml:
  datatype instreambuffered =
  InstreamBuffered
    instream     (* stream name *)
    (int ref)    (* read index *)
    (int ref)    (* write index *)
    byte_array
End

val cur_env = get_env (get_ml_prog_state());
val stamp_eval = EVAL ``nsLookup (^cur_env).c (Short "InstreamBuffered")``
val instreambuffered_con_stamp = rhs (concl stamp_eval)

Definition instreambuffered_con_stamp_def[simp]:
  instreambuffered_con_stamp = OPTION_MAP SND ^instreambuffered_con_stamp
End

val _ = (next_ml_names := ["get_out"]);
val _ = translate get_out_def;
val _ = (next_ml_names := ["get_in"]);
val _ = translate get_in_def;

val _ = ml_prog_update open_local_in_block;

val _ = ml_prog_update (add_dec
  ``Dtabbrev unknown_loc [] "instream" (Atapp [] (Short "instream"))`` I);
val _ = ml_prog_update (add_dec
  ``Dtabbrev unknown_loc [] "outstream" (Atapp [] (Short "outstream"))`` I);
(* provides the TextIO.instreambuffered name for the instreambuffered type *)
val _ = ml_prog_update (add_dec
  ``Dtabbrev unknown_loc [] "b_instream" (Atapp [] (Short "instreambuffered"))`` I);

Quote cakeml:
  exception BadFileName;
  exception InvalidFD;
  exception EndOfFile;
  exception IllegalArgument
End

val _ = ml_prog_update open_local_block;

fun get_exn_conv name =
  EVAL ``lookup_cons (Short ^name) ^(get_env (get_ml_prog_state ()))``
  |> concl |> rand |> rand |> rand

val BadFileName = get_exn_conv ``"BadFileName"``
val InvalidFD = get_exn_conv ``"InvalidFD"``
val EndOfFile = get_exn_conv ``"EndOfFile"``
val IllegalArgument = get_exn_conv ``"IllegalArgument"``

Definition BadFileName_exn_def:
  BadFileName_exn v = (v = Conv (SOME ^BadFileName) [])
End

Definition InvalidFD_exn_def:
  InvalidFD_exn v = (v = Conv (SOME ^InvalidFD) [])
End

Definition EndOfFile_exn_def:
  EndOfFile_exn v = (v = Conv (SOME ^EndOfFile) [])
End

Definition IllegalArgument_exn_def:
  IllegalArgument_exn v = (v = Conv (SOME ^IllegalArgument) [])
End

val iobuff_e = ``(App Aw8alloc [Lit (IntLit 2052); Lit (Word8 0w)])``
val eval_thm = let
  val env = get_ml_prog_state () |> ml_progLib.get_env
  val st = get_ml_prog_state () |> ml_progLib.get_state
  val new_st = ``^st with refs := ^st.refs ++ [W8array (REPLICATE 2052 0w)]``
  val goal = list_mk_icomb (prim_mk_const {Thy="ml_prog", Name="eval_rel"},
    [st, env, iobuff_e, new_st, mk_var ("x", semanticPrimitivesSyntax.v_ty)])
  val lemma = goal |> (EVAL THENC SIMP_CONV(srw_ss())[semanticPrimitivesTheory.state_component_equality])
  val v_thm = prove(mk_imp(lemma |> concl |> rand, goal),
    rpt strip_tac \\ rveq \\ match_mp_tac(#2(EQ_IMP_RULE lemma))
    \\ asm_simp_tac bool_ss [])
    |> GEN_ALL |> SIMP_RULE std_ss [] |> SPEC_ALL;
  val v_tm = v_thm |> concl |> strip_comb |> #2 |> last
  val v_def = define_abbrev false "iobuff_loc" v_tm
  in v_thm |> REWRITE_RULE [GSYM v_def] end

val _ = ml_prog_update (add_Dlet eval_thm "iobuff");

val _ = ml_prog_update open_local_in_block;

(* stdin, stdout, stderr *)
Definition stdIn_def:
  stdIn = Instream (strlit (MAP (CHR o w2n) (n2w8 0)))
End

Definition stdOut_def:
  stdOut = Outstream (strlit (MAP (CHR o w2n) (n2w8 1)))
End

Definition stdErr_def:
  stdErr = Outstream (strlit (MAP (CHR o w2n) (n2w8 2)))
End

val _ = next_ml_names := ["stdIn","stdOut","stdErr"];

val r = stdIn_def
          |> SIMP_RULE (srw_ss()) [MarshallingTheory.n2w8_def]
          |> translate;

val r = stdOut_def
          |> SIMP_RULE (srw_ss()) [MarshallingTheory.n2w8_def]
          |> translate;

val r = stdErr_def
          |> SIMP_RULE (srw_ss()) [MarshallingTheory.n2w8_def]
          |> translate ;

val _ = ml_prog_update open_local_block;

(* writei: higher-lever write function which calls #write until something is written or
* a filesystem error is raised and outputs the number of bytes written.
* It assumes that iobuff is initialised
* write: idem, but keeps writing until the whole (specified part of the) buffer
* is written *)

Quote cakeml:
  fun writei fd n i =
    let val a = Marshalling.n2w2 n iobuff 0
        val a = Marshalling.n2w2 i iobuff 2
        val a = #(write) fd iobuff in
        if Word8Array.sub iobuff 0 = Word8.fromInt 1
        then raise InvalidFD
        else
          let val nw = Marshalling.w22n iobuff 1 in
            if nw = 0 then writei fd n i
            else nw
          end
    end
    fun write fd n i =
      if n = 0 then () else
        let val nw = writei fd n i in
          if nw < n then write fd (n-nw) (i+nw) else () end
End

val _ = ml_prog_update open_local_in_block;

(* Output functions on given file descriptor *)
Quote cakeml:
  fun output1 fd c =
    (Word8Array.update iobuff 4 (Word8.fromInt(Char.ord c)); write (get_out fd) 1 0; ())
End

(* writes a string into a file *)
Quote cakeml:
  fun output fd s =
  if s = "" then () else
  let val z = String.size s
      val n = if z <= 2048 then z else 2048
      val fl = Word8Array.copyVec s 0 n iobuff 4
      val a = write (get_out fd) n 0 in
         output fd (String.substring s n (z-n))
  end;
  fun print s = output stdOut s
  fun print_err s = output stdErr s
End

Quote cakeml:
  fun print_list ls =
    case ls of [] => () | (x::xs) => (print x; print_list xs)
End

Quote cakeml:
  fun openIn fname =
    let val b = Word8Array.array 9 (Word8.fromInt 0)
        val a = #(open_in) (fname ^ (String.str (Char.chr 0))) b in
          if Word8Array.sub b 0 = Word8.fromInt 0
          then Instream (Word8Array.substring b 1 8)
          else raise BadFileName
    end
  fun openOut fname =
    let val b = Word8Array.array 9 (Word8.fromInt 0)
        val a = #(open_out) (fname ^ (String.str (Char.chr 0))) b in
          if Word8Array.sub b 0 = Word8.fromInt 0
          then Outstream (Word8Array.substring b 1 8)
          else raise BadFileName
    end
End

Quote cakeml:
  fun closeOut fd =
    let val a = #(close) (get_out fd) iobuff in
          if Word8Array.sub iobuff 0 = Word8.fromInt 0
          then () else raise InvalidFD
    end
End

Quote cakeml:
  fun closeIn fd =
    let val a = #(close) (get_in fd) iobuff in
          if Word8Array.sub iobuff 0 = Word8.fromInt 0
          then () else raise InvalidFD
    end
End

val _ = ml_prog_update open_local_block;

(* wrapper for ffi call *)
Quote cakeml:
  fun read fd n =
    let val a = Marshalling.n2w2 n iobuff 0 in
          (#(read) fd iobuff;
          if Word8.toInt (Word8Array.sub iobuff 0) <> 1
          then Marshalling.w22n iobuff 1
          else raise InvalidFD)
    end
End

(* reads 1 char *)
Quote cakeml:
  fun read_byte fd =
      if read fd 1 = 0 then raise EndOfFile
      else Word8Array.sub iobuff 4
End

(* val input : in_channel -> bytes -> int -> int -> int
* input ic buf pos len reads up to len characters from the given channel ic,
* storing them in byte sequence buf, starting at character number pos. *)
(* TODO: input0 as local fun *)
Quote cakeml:
  fun input fd buff off len =
  let fun input0 off len count =
      let val nread = read (get_in fd) (min len 2048) in
          if nread = 0 then count else
            (Word8Array.copy iobuff 4 nread buff off;
             input0 (off + nread) (len - nread) (count + nread))
      end
  in input0 off len 0 end
End

val _ = ml_prog_update open_local_in_block;

Quote cakeml:
  fun input1 fd = Char.some(Char.fromByte(read_byte (get_in fd))) handle EndOfFile => None
End

val _ = ml_prog_update open_local_block;

(* helper function:
   extend a byte array, or, more accurately
   copy a byte array into a new one twice the size *)
Quote cakeml:
  fun extend_array arr =
    let
      val len = Word8Array.length arr
      val arr' = Word8Array.array (2*len) (Word8.fromInt 0)
    in (Word8Array.copy arr 0 len arr' 0; arr') end
End

val _ = ml_prog_update open_local_in_block;

(* read a line (same semantics as SML's TextIO.inputLine) *)
(* simple, inefficient version that reads 1 char at a time *)
Quote cakeml:
  fun inputLine fd =
    let
      val nl = Word8.fromInt (Char.ord #"\n")
      fun inputLine_aux arr i =
        if i < Word8Array.length arr then
          let
            val c = read_byte (get_in fd)
            val u = Word8Array.update arr i c
          in
            if c = nl then Some (Word8Array.substring arr 0 (i+1))
            else inputLine_aux arr (i+1)
          end
          handle EndOfFile =>
            if i = 0 then None
            else (Word8Array.update arr i nl;
                  Some (Word8Array.substring arr 0 (i+1)))
        else inputLine_aux (extend_array arr) i
      in inputLine_aux (Word8Array.array 127 (Word8.fromInt 0)) 0 end
End

(* This version doesn't work because CF makes it difficult (impossible?) to
   work with references/arrays inside data structures (here inside a pair)
Quote cakeml:
  fun inputLine fd =
    let
      fun realloc arr =
        let
          val len = Word8Array.length arr
          val arr' = Word8Array.array (2*len) (Word8.fromInt 0)
        in (Word8Array.copy arr 0 len arr' 0; arr') end
      val nl = Word8.fromInt (Char.ord #"\n")
      fun inputLine_aux arr i =
        if i < Word8Array.length arr then
          let val c = read_byte fd
          in if c = nl then (arr,i+1) else
            (Word8Array.update arr i c;
             inputLine_aux arr (i+1))
          end handle EndOfFile => (arr,i)
        else inputLine_aux (realloc arr) i
      val res = inputLine_aux (Word8Array.array 127 (Word8.fromInt 0)) 0
      val arr = fst res val nr = snd res
    in if nr = 0 then NONE else
      (Word8Array.update arr (nr-1) nl;
       SOME (Word8Array.substring arr 0 nr))
    end
End
*)

(*

Version of inputLine that reads chunks at a time, but has to return
the unused part of the last chunk. I expect this will not end up being
used, because something like the above simpler version becomes
efficient if we switch to buffered streams.  I.e., the buffering
shouldn't be inputLine-specific.

(* generalisable to splitl *)
Quote cakeml:
fun find_newline s i l =
  if i >= l then l else
  if String.sub s i = #"\n" then i
  else find_newline s (i+1) l
fun split_newline s =
  let val l = String.size s
      val i = find_newline s 0 l in
        (String.substring s 0 i, String.substring s i (l-i))
  end
End

(* using lets/ifs as case take a while in xlet *)
(* if/if take a while in xcf *)

fun inputLine fd lbuf =
  let fun inputLine_aux lacc =
    let val nr = read fd (Word8.fromInt 255) in
      if nr = 0 then (String.concat (List.rev lacc), "") else
        let val lread = Word8Array.substring iobuff 3 nr
            val split = split_newline lread
            val line = fst split
            val lrest = snd split in
              if lrest = "" then inputLine_aux (line :: lacc)
              else (String.concat (List.rev("\n" :: line :: lacc)),
                    String.extract lrest 1 NONE)
        end
    end
  val split = split_newline lbuf
  val line = fst split
  val lrest = snd split in
    if lrest = "" then
      let val split' = inputLine_aux [] in
        (String.concat (line :: fst split' :: []), snd split') end
    else (String.concat (line :: "\n" :: []), String.extract lrest 1 NONE)
  end` |> append_prog
*)

Quote cakeml:
  fun inputLines fd =
    case inputLine fd of
        None => []
      | Some l => l::inputLines fd
End

Quote cakeml:
  fun inputLinesFrom fname =
    let
      val fd = openIn fname
      val lines = inputLines fd
    in
      closeIn fd; Some lines
    end handle BadFileName => None
End

(* read everything (same semantics as SML's TextIO.inputAll) *)
Quote cakeml:
  fun inputAll fd =
    let
      fun inputAll_aux arr i =
        let val len = Word8Array.length arr in
          if i < len then
            let
              val n = input fd arr i (len - i)
            in
              if n = 0 then Word8Array.substring arr 0 i
              else inputAll_aux arr (i + n)
            end
          else inputAll_aux (extend_array arr) i
        end
      in inputAll_aux (Word8Array.array 127 (Word8.fromInt 0)) 0 end
End

(* copies all of an input stream to an output stream by chunks of 2048 bytes *)
(* similar to ocaml batteries included batIO.copy *)
Quote cakeml:
    fun copy inp out =
    let val nr = read (get_in inp) 2048 in
      if nr = 0 then () else (write (get_out out) nr 0; copy inp out)
    end
End

(*Buffered IO section*)

(*Open a buffered stdin with a buffer size of bsize.
  Force 1028 <= size < 256^2*)
Quote cakeml:
  fun b_openStdInSetBufferSize bsize =
      InstreamBuffered stdIn (Ref 4) (Ref 4)
        (Word8Array.array (min 65535 (max (bsize+4) 1028))
          (Word8.fromInt 48))
End

Quote cakeml:
  fun b_openStdIn () = b_openStdInSetBufferSize 4096
End

(*Open a buffered instream with a buffer size of bsize.
  Force 1028 <= size < 256^2*)
Quote cakeml:
  fun b_openInSetBufferSize fname bsize =
    let
      val is = openIn fname
    in
        InstreamBuffered is (Ref 4) (Ref 4)
          (Word8Array.array (min 65535 (max (bsize+4) 1028))
            (Word8.fromInt 48))
    end
End

Quote cakeml:
  fun b_openIn fname = b_openInSetBufferSize fname 4096
End

Quote cakeml:
  fun b_closeIn is =
    case is of InstreamBuffered fd rref wref surplus =>
      closeIn fd
End

val _ = ml_prog_update open_local_block;
(*b_input helper function for the case when there are
  enough bytes in instream buffer*)
Quote cakeml:
  fun b_input_aux is buff off len =
    case is of InstreamBuffered fd rref wref surplus =>
      let
        val readat = (!rref)
      in
        Word8Array.copy surplus readat len buff off;
        rref := readat + len;
        len
      end
End

val _ = ml_prog_update open_local_in_block;

Quote cakeml:
 fun b_input is buff off len =
   case is of InstreamBuffered fd rref wref surplus =>
     let
       val nBuffered = (!wref) - (!rref)
     in
       if Word8Array.length buff < len + off then raise IllegalArgument
       else
         if (Word8Array.length surplus - 4) < len then
           (b_input_aux is buff off nBuffered;
           input fd buff (off+nBuffered) (len - nBuffered) + nBuffered)
         else
           (*If there arent enough bytes in the buffer: copy all of the bytes
           in the buffer and then refill it, and copy the remaining bytes *)
           if len > nBuffered then
             (b_input_aux is buff off nBuffered;
             wref := 4 + input fd surplus 4 ((Word8Array.length surplus)-4);
             rref := 4;
             (b_input_aux is buff (off+nBuffered) (min ((!wref) - 4) (len-nBuffered))) + nBuffered)
           (*If there are enough bytes in the buffer, just copy them*)
           else
             b_input_aux is buff off len
     end
End

val _ = ml_prog_update open_local_block;

(* wrapper for ffi call *)
Quote cakeml:
  fun read_into fd buff n =
    let val a = Marshalling.n2w2 n buff 0 in
          (#(read) fd buff;
          if Word8.toInt (Word8Array.sub buff 0) <> 1
          then Marshalling.w22n buff 1
          else raise InvalidFD)
    end
End

val _ = ml_prog_update open_local_in_block;
val _ = ml_prog_update open_local_block;

Quote cakeml:
 fun b_refillBuffer_with_read is =
   case is of InstreamBuffered fd rref wref surplus =>
       (wref := 4 + (read_into (get_in fd) surplus ((Word8Array.length surplus)-4));
       rref := 4;
       (!wref) - 4)
End

Quote cakeml:
 fun b_peekChar_aux is =
   case is of InstreamBuffered fd rref wref surplus =>
          if (!wref) = (!rref) then None
          else
            let val readat = (!rref) in
              Char.some (Char.fromByte (Word8Array.sub surplus readat))
            end
End

Quote cakeml:
 fun b_input1_aux is =
   case is of InstreamBuffered fd rref wref surplus =>
          let val readat = (!rref) in
            if (!wref) = readat then None
            else
              (rref := readat + 1;
              Char.some (Char.fromByte (Word8Array.sub surplus readat)))
          end
End

val _ = ml_prog_update open_local_in_block;

Quote cakeml:
  fun b_peekChar is =
    case is of InstreamBuffered fd rref wref surplus =>
        if (!wref) = (!rref)
        then (b_refillBuffer_with_read is; b_peekChar_aux is)
        else b_peekChar_aux is
End

Quote cakeml:
  fun b_input1 is =
    case is of InstreamBuffered fd rref wref surplus =>
        if (!wref) = (!rref)
        then (b_refillBuffer_with_read is; b_input1_aux is)
        else b_input1_aux is
End

val _ = ml_prog_update open_local_block;

Quote cakeml:
  fun find_surplus c surplus readat writeat =
  if readat = writeat then None
  else
    if Char.fromByte (Word8Array.sub surplus readat) = c
    then Some (readat)
    else find_surplus c surplus (readat + 1) writeat;
End

Quote cakeml:
  fun b_inputUntil_1 is chr =
  case is of InstreamBuffered fd rref wref surplus =>
  let
    val readat = (!rref)
    val writeat = (!wref)
  in
    case find_surplus chr surplus readat writeat of
      None =>
      (rref := writeat;
        Inl (Word8Array.substring surplus readat (writeat-readat)))
    | Some i =>
      (rref := i+1;
        Inr (Word8Array.substring surplus readat (i+1-readat)))
  end;
End

Quote cakeml:
  fun b_refillBuffer_with_read_guard is =
    (b_refillBuffer_with_read is;
     case is of InstreamBuffered fd rref wref surplus =>
     (!wref) = (!rref));
End

Quote cakeml:
  fun b_inputUntil_2 is chr acc =
  case b_inputUntil_1 is chr of
    Inr s => Some (case acc of [] => s | _ => String.concat (List.rev (s :: acc)))
  | Inl s =>
      if b_refillBuffer_with_read_guard is
      then
        let
          val res = String.concat (List.rev (String.str chr :: s :: acc))
        in if String.size res = 1 then None else Some res end
      else
        b_inputUntil_2 is chr (s :: acc);
End

val _ = ml_prog_update open_local_in_block;

Quote cakeml:
  fun b_inputLine c0 is = b_inputUntil_2 is c0 []
End

Quote cakeml:
  fun b_inputLineTokens c0 is tokP mp =
    case b_inputLine c0 is of
      None => None
    | Some l =>
      Some (List.map mp (String.tokens tokP l))
End

val _ = ml_prog_update open_local_block;

Quote cakeml:
  fun b_inputLines_aux c0 is acc =
     case b_inputLine c0 is of
       None => List.rev acc
     | Some l => b_inputLines_aux c0 is (l::acc)
End

Quote cakeml:
  fun b_inputAllTokens_aux c0 is f g acc =
     case b_inputLineTokens c0 is f g of
       None => List.rev acc
     | Some l => b_inputAllTokens_aux c0 is f g (l::acc)
End

Quote cakeml:
  fun b_consume_rest is =
    case b_input1 is of
      None => ()
    | Some c => b_consume_rest is;
End

Quote cakeml:
  fun b_open_option stdin_or_fname =
    case stdin_or_fname of
      None (* stdin *) =>
                    (let
                       val is = b_openStdIn ()
                     in Some (is, (fn () => b_consume_rest is)) end)
    | Some fname => (let
                       val is = b_openIn fname
                     in Some (is, (fn () => b_closeIn is)) end
                     handle BadFileName => None)
End

Quote cakeml:
  fun fold_chars_loop f is y =
    case b_input1 is of
      None => y
    | Some c => fold_chars_loop f is (f c y);
  fun fold_lines_loop c0 f is y =
    case b_inputLine c0 is of
      None => y
    | Some c => fold_lines_loop c0 f is (f c y);
  fun fold_tokens_loop c0 tokP mp fld is y =
    case b_inputLineTokens c0 is tokP mp of
      None => y
    | Some c => fold_tokens_loop c0 tokP mp fld is (fld c y);
End

val _ = ml_prog_update open_local_in_block;

Quote cakeml:
  fun b_inputLines c0 is =
    b_inputLines_aux c0 is []
End

Quote cakeml:
  fun b_inputLinesFrom c0 fname =
    let
      val is = b_openIn fname
      val lines = b_inputLines c0 is
    in
      b_closeIn is; Some lines
    end handle BadFileName => None
End

Quote cakeml:
  fun b_inputLinesStdIn c0 =
    let
      val is = b_openStdIn ()
    in
      b_inputLines c0 is
    end
End

Quote cakeml:
  fun b_inputAllTokens c0 is f g =
    b_inputAllTokens_aux c0 is f g []
End

Quote cakeml:
  fun b_inputAllTokensFrom c0 fname f g =
    let
      val is = b_openIn fname
      val lines = b_inputAllTokens c0 is f g
    in
      b_closeIn is; Some lines
    end handle BadFileName => None
End

Quote cakeml:
  fun b_inputAllTokensStdIn c0 f g =
    let
      val is = b_openStdIn ()
      val lines = b_inputAllTokens c0 is f g
    in
      Some lines (* TODO: remove the OPTION on the return value *)
    end
End

Quote cakeml:
  fun foldChars f x stdin_or_fname =
    case b_open_option stdin_or_fname of
      None => None
    | Some (is,close) =>
      (let
         val res = fold_chars_loop f is x
         val _ = close ()
       in Some res end
       handle e => (close (); raise e))
End

Quote cakeml:
  fun foldLines c0 f x stdin_or_fname =
    case b_open_option stdin_or_fname of
      None => None
    | Some (is,close) =>
      (let
         val res = fold_lines_loop c0 f is x
         val _ = close ()
       in Some res end
       handle e => (close (); raise e))
End

Quote cakeml:
  fun foldTokens c0 tokP mp fld x stdin_or_fname =
    case b_open_option stdin_or_fname of
      None => None
    | Some (is,close) =>
      (let
         val res = fold_tokens_loop c0 tokP mp fld is x
         val _ = close ()
       in Some res end
       handle e => (close (); raise e))
End

val _ = ml_prog_update close_local_blocks;
val _ = ml_prog_update (close_module NONE);

