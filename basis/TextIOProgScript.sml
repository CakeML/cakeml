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

val _ = ml_prog_update (open_module "TextIO");

val _ = ml_prog_update open_local_block;

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

Quote add_cakeml:
  datatype instreambuffered =
  InstreamBuffered
    instream     (* stream name *)
    (int ref)    (* read index *)
    (int ref)    (* write index *)
    byte_array
End

val cur_env = get_env (get_ml_prog_state());
val stamp_eval = EVAL ``nsLookup (^cur_env).c (Short «InstreamBuffered»)``
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
  ``Dtabbrev unknown_loc [] «raw_instream» (Atapp [] (Short «instream»))`` I);
val _ = ml_prog_update (add_dec
  ``Dtabbrev unknown_loc [] «outstream» (Atapp [] (Short «outstream»))`` I);
val _ = ml_prog_update (add_dec
  ``Dtabbrev unknown_loc [] «instream» (Atapp [] (Short «instreambuffered»))`` I);

Quote add_cakeml:
  exception BadFileName;
  exception InvalidFD;
  exception EndOfFile;
  exception IllegalArgument
End

val _ = ml_prog_update open_local_block;

val BadFileName = get_exn_conv ``«BadFileName»``
val InvalidFD = get_exn_conv ``«InvalidFD»``
val EndOfFile = get_exn_conv ``«EndOfFile»``
val IllegalArgument = get_exn_conv ``«IllegalArgument»``

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

(* stdout, stderr *)

Definition stdOut_def:
  stdOut = Outstream (implode (MAP (CHR o w2n) (n2w8 1)))
End

Definition stdErr_def:
  stdErr = Outstream (implode (MAP (CHR o w2n) (n2w8 2)))
End

val _ = next_ml_names := ["stdOut","stdErr"];

val r = stdOut_def
          |> SIMP_RULE (srw_ss()) [MarshallingTheory.n2w8_def]
          |> translate;

val r = stdErr_def
          |> SIMP_RULE (srw_ss()) [MarshallingTheory.n2w8_def]
          |> translate ;


val _ = ml_prog_update open_local_block;

(* Note how we are in a local block: declarations are not exported. This is
   because we want to only expose the more efficient, buffered input to users. *)

Definition raw_stdIn_def:
  raw_stdIn = Instream (implode (MAP (CHR o w2n) (n2w8 0)))
End

val _ = next_ml_names := ["raw_stdIn"];

val r = raw_stdIn_def
          |> SIMP_RULE (srw_ss()) [MarshallingTheory.n2w8_def]
          |> translate;

Quote add_cakeml:
  fun raw_openIn fname =
    let val b = Word8Array.array 9 (Word8.fromInt 0)
        val a = #(open_in) (fname ^ (String.str (Char.chr 0))) b in
          if Word8Array.sub b 0 = Word8.fromInt 0
          then Instream (Word8Array.substring b 1 8)
          else raise BadFileName
    end
End

Quote add_cakeml:
  fun raw_closeIn fd =
    let val a = #(close) (get_in fd) iobuff in
          if Word8Array.sub iobuff 0 = Word8.fromInt 0
          then () else raise InvalidFD
    end
End

(* writei: higher-lever write function which calls #write until something is written or
* a filesystem error is raised and outputs the number of bytes written.
* It assumes that iobuff is initialised
* write: idem, but keeps writing until the whole (specified part of the) buffer
* is written *)
Quote add_cakeml:
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
Quote add_cakeml:
  fun output1 fd c =
    (Word8Array.update iobuff 4 (Word8.fromInt(Char.ord c)); write (get_out fd) 1 0; ())
End

(* writes a string into a file *)
Quote add_cakeml:
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

Quote add_cakeml:
  fun print_list ls =
    case ls of [] => () | (x::xs) => (print x; print_list xs)
End

Quote add_cakeml:
  fun openOut fname =
    let val b = Word8Array.array 9 (Word8.fromInt 0)
        val a = #(open_out) (fname ^ (String.str (Char.chr 0))) b in
          if Word8Array.sub b 0 = Word8.fromInt 0
          then Outstream (Word8Array.substring b 1 8)
          else raise BadFileName
    end
End

Quote add_cakeml:
  fun closeOut fd =
    let val a = #(close) (get_out fd) iobuff in
          if Word8Array.sub iobuff 0 = Word8.fromInt 0
          then () else raise InvalidFD
    end
End

val _ = ml_prog_update open_local_block;

(* wrapper for ffi call *)
Quote add_cakeml:
  fun read fd n =
    let val a = Marshalling.n2w2 n iobuff 0 in
          (#(read) fd iobuff;
          if Word8.toInt (Word8Array.sub iobuff 0) <> 1
          then Marshalling.w22n iobuff 1
          else raise InvalidFD)
    end
End

(* val raw_input : in_channel -> bytes -> int -> int -> int
* input ic buf pos len reads up to len characters from the given channel ic,
* storing them in byte sequence buf, starting at character number pos. *)
(* TODO: input0 as local fun *)
Quote add_cakeml:
  fun raw_input fd buff off len =
  let fun input0 off len count =
      let val nread = read (get_in fd) (min len 2048) in
          if nread = 0 then count else
            (Word8Array.copy iobuff 4 nread buff off;
             input0 (off + nread) (len - nread) (count + nread))
      end
  in input0 off len 0 end
End

(* helper function:
   extend a byte array, or, more accurately
   copy a byte array into a new one twice the size *)
Quote add_cakeml:
  fun extend_array arr =
    let
      val len = Word8Array.length arr
      val arr' = Word8Array.array (2*len) (Word8.fromInt 0)
    in (Word8Array.copy arr 0 len arr' 0; arr') end
End

val _ = ml_prog_update open_local_in_block;

(*Buffered IO section*)

(*Open a buffered stdin with a buffer size of bsize.
  Force 1028 <= size < 256^2*)
Quote add_cakeml:
  fun openStdInSetBufferSize bsize =
      InstreamBuffered raw_stdIn (Ref 4) (Ref 4)
        (Word8Array.array (min 65535 (max (bsize+4) 1028))
          (Word8.fromInt 48))
End

Quote add_cakeml:
  fun openStdIn () = openStdInSetBufferSize 4096
End

(*Open a buffered instream with a buffer size of bsize.
  Force 1028 <= size < 256^2*)
Quote add_cakeml:
  fun openInSetBufferSize fname bsize =
    let
      val is = raw_openIn fname
    in
        InstreamBuffered is (Ref 4) (Ref 4)
          (Word8Array.array (min 65535 (max (bsize+4) 1028))
            (Word8.fromInt 48))
    end
End

Quote add_cakeml:
  fun openIn fname = openInSetBufferSize fname 4096
End

Quote add_cakeml:
  fun closeIn is =
    case is of InstreamBuffered fd rref wref surplus =>
      raw_closeIn fd
End

val _ = ml_prog_update open_local_block;
(*input helper function for the case when there are
  enough bytes in instream buffer*)
Quote add_cakeml:
  fun input_aux is buff off len =
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

Quote add_cakeml:
 fun input is buff off len =
   case is of InstreamBuffered fd rref wref surplus =>
     let
       val nBuffered = (!wref) - (!rref)
     in
       if Word8Array.length buff < len + off then raise IllegalArgument
       else
         if (Word8Array.length surplus - 4) < len then
           (input_aux is buff off nBuffered;
           raw_input fd buff (off+nBuffered) (len - nBuffered) + nBuffered)
         else
           (*If there arent enough bytes in the buffer: copy all of the bytes
           in the buffer and then refill it, and copy the remaining bytes *)
           if len > nBuffered then
             (input_aux is buff off nBuffered;
             wref := 4 + raw_input fd surplus 4 ((Word8Array.length surplus)-4);
             rref := 4;
             (input_aux is buff (off+nBuffered) (min ((!wref) - 4) (len-nBuffered))) + nBuffered)
           (*If there are enough bytes in the buffer, just copy them*)
           else
             input_aux is buff off len
     end
End

val _ = ml_prog_update open_local_block;

(* wrapper for ffi call *)
Quote add_cakeml:
  fun read_into fd buff n =
    let val a = Marshalling.n2w2 n buff 0 in
          (#(read) fd buff;
          if Word8.toInt (Word8Array.sub buff 0) <> 1
          then Marshalling.w22n buff 1
          else raise InvalidFD)
    end
End

Quote add_cakeml:
 fun refillBuffer_with_read is =
   case is of InstreamBuffered fd rref wref surplus =>
       (wref := 4 + (read_into (get_in fd) surplus ((Word8Array.length surplus)-4));
       rref := 4;
       (!wref) - 4)
End

Quote add_cakeml:
 fun peekChar_aux is =
   case is of InstreamBuffered fd rref wref surplus =>
          if (!wref) = (!rref) then None
          else
            let val readat = (!rref) in
              Char.some (Char.fromByte (Word8Array.sub surplus readat))
            end
End

Quote add_cakeml:
 fun input1_aux is =
   case is of InstreamBuffered fd rref wref surplus =>
          let val readat = (!rref) in
            if (!wref) = readat then None
            else
              (rref := readat + 1;
              Char.some (Char.fromByte (Word8Array.sub surplus readat)))
          end
End

val _ = ml_prog_update open_local_in_block;

Quote add_cakeml:
  fun peekChar is =
    case is of InstreamBuffered fd rref wref surplus =>
        if (!wref) = (!rref)
        then (refillBuffer_with_read is; peekChar_aux is)
        else peekChar_aux is
End

Quote add_cakeml:
  fun input1 is =
    case is of InstreamBuffered fd rref wref surplus =>
        if (!wref) = (!rref)
        then (refillBuffer_with_read is; input1_aux is)
        else input1_aux is
End

val _ = ml_prog_update open_local_block;

Quote add_cakeml:
  fun find_surplus c surplus readat writeat =
  if readat = writeat then None
  else
    if Char.fromByte (Word8Array.sub surplus readat) = c
    then Some (readat)
    else find_surplus c surplus (readat + 1) writeat;
End

Quote add_cakeml:
  fun inputUntil_1 is chr =
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

Quote add_cakeml:
  fun refillBuffer_with_read_guard is =
    (refillBuffer_with_read is;
     case is of InstreamBuffered fd rref wref surplus =>
     (!wref) = (!rref));
End

Quote add_cakeml:
  fun inputUntil_2 is chr acc =
  case inputUntil_1 is chr of
    Inr s => Some (case acc of [] => s | _ => String.concat (List.rev (s :: acc)))
  | Inl s =>
      if refillBuffer_with_read_guard is
      then
        let
          val res = String.concat (List.rev (String.str chr :: s :: acc))
        in if String.size res = 1 then None else Some res end
      else
        inputUntil_2 is chr (s :: acc);
End

val _ = ml_prog_update open_local_in_block;

Quote add_cakeml:
  fun inputLine c0 is = inputUntil_2 is c0 []
End

Quote add_cakeml:
  fun inputLineTokens c0 is tokP mp =
    case inputLine c0 is of
      None => None
    | Some l =>
      Some (List.map mp (String.tokens tokP l))
End

val _ = ml_prog_update open_local_block;

Quote add_cakeml:
  fun inputLines_aux c0 is acc =
     case inputLine c0 is of
       None => List.rev acc
     | Some l => inputLines_aux c0 is (l::acc)
End

Quote add_cakeml:
  fun inputAllTokens_aux c0 is f g acc =
     case inputLineTokens c0 is f g of
       None => List.rev acc
     | Some l => inputAllTokens_aux c0 is f g (l::acc)
End

Quote add_cakeml:
  fun consume_rest is =
    case input1 is of
      None => ()
    | Some c => consume_rest is;
End

Quote add_cakeml:
  fun open_option stdin_or_fname =
    case stdin_or_fname of
      None (* stdin *) =>
                    (let
                       val is = openStdIn ()
                     in Some (is, (fn () => consume_rest is)) end)
    | Some fname => (let
                       val is = openIn fname
                     in Some (is, (fn () => closeIn is)) end
                     handle BadFileName => None)
End

Quote add_cakeml:
  fun fold_chars_loop f is y =
    case input1 is of
      None => y
    | Some c => fold_chars_loop f is (f c y);
  fun fold_lines_loop c0 f is y =
    case inputLine c0 is of
      None => y
    | Some c => fold_lines_loop c0 f is (f c y);
  fun fold_tokens_loop c0 tokP mp fld is y =
    case inputLineTokens c0 is tokP mp of
      None => y
    | Some c => fold_tokens_loop c0 tokP mp fld is (fld c y);
End

val _ = ml_prog_update open_local_in_block;

Quote add_cakeml:
  fun inputLines c0 is =
    inputLines_aux c0 is []
End

Quote add_cakeml:
  fun inputLinesFile c0 fname =
    let
      val is = openIn fname
      val lines = inputLines c0 is
    in
      closeIn is; Some lines
    end handle BadFileName => None
End

Quote add_cakeml:
  fun inputLinesStdIn c0 =
    let
      val is = openStdIn ()
    in
      inputLines c0 is
    end
End

Quote add_cakeml:
  fun inputAll is = case is of InstreamBuffered fd rref wref surplus =>
    let
      fun inputAll_aux arr i =
        let val len = Word8Array.length arr in
          if i < len then
            let
              val n = raw_input fd arr i (len - i)
            in
              if n = 0 then Word8Array.substring arr 0 i
              else inputAll_aux arr (i + n)
            end
          else inputAll_aux (extend_array arr) i
        end
      in inputAll_aux surplus 0 end
End

Quote add_cakeml:
  fun inputAllTokens c0 is f g =
    inputAllTokens_aux c0 is f g []
End

(* TODO Maybe should be removed in favor of inputAllTokensFrom? *)
Quote add_cakeml:
  fun inputAllTokensFile c0 fname f g =
    let
      val is = openIn fname
      val lines = inputAllTokens c0 is f g
    in
      closeIn is; Some lines
    end handle BadFileName => None
End

Quote add_cakeml:
  fun inputAllTokensFrom c0 stdin_or_fname f g =
    case open_option stdin_or_fname of
      None => None
    | Some (is,close) => let
        val lines = inputAllTokens c0 is f g
      in close (); Some lines end
      handle e => (close (); raise e)
End

Quote add_cakeml:
  fun foldChars f x stdin_or_fname =
    case open_option stdin_or_fname of
      None => None
    | Some (is,close) =>
      (let
         val res = fold_chars_loop f is x
         val _ = close ()
       in Some res end
       handle e => (close (); raise e))
End

Quote add_cakeml:
  fun foldLines c0 f x stdin_or_fname =
    case open_option stdin_or_fname of
      None => None
    | Some (is,close) =>
      (let
         val res = fold_lines_loop c0 f is x
         val _ = close ()
       in Some res end
       handle e => (close (); raise e))
End

Quote add_cakeml:
  fun foldTokens c0 tokP mp fld x stdin_or_fname =
    case open_option stdin_or_fname of
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
