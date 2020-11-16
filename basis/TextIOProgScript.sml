(*
  Module for text-based I/O with the underlying file system.
*)
open preamble
     ml_translatorTheory ml_translatorLib ml_progLib basisFunctionsLib
     CommandLineProgTheory MarshallingProgTheory
     semanticPrimitivesSyntax

val _ = new_theory"TextIOProg";

val _ = translation_extends "MarshallingProg";

val _ = ml_prog_update (open_module "TextIO");

val _ = ml_prog_update open_local_block;


(* val get_buffered_in_def = Define `get_out (InstreamBuffered)` *)


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

val instreamBuffered_def = (append_prog o process_topdecs)
  `datatype instreambuffered =
  InstreamBuffered
    instream     (* stream name *)
    (int ref)    (* read index *)
    (int ref)   (* write index *)
    byte_array`;


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

val _ = process_topdecs `
  exception BadFileName;
  exception InvalidFD;
  exception EndOfFile;
  exception IllegalArgument
` |> append_prog

val _ = ml_prog_update open_local_block;

fun get_exn_conv name =
  EVAL ``lookup_cons (Short ^name) ^(get_env (get_ml_prog_state ()))``
  |> concl |> rand |> rand |> rand

val BadFileName = get_exn_conv ``"BadFileName"``
val InvalidFD = get_exn_conv ``"InvalidFD"``
val EndOfFile = get_exn_conv ``"EndOfFile"``
val IllegalArgument = get_exn_conv ``"IllegalArgument"``

val BadFileName_exn_def = Define `
  BadFileName_exn v = (v = Conv (SOME ^BadFileName) [])`

val InvalidFD_exn_def = Define `
  InvalidFD_exn v = (v = Conv (SOME ^InvalidFD) [])`

val EndOfFile_exn_def = Define `
  EndOfFile_exn v = (v = Conv (SOME ^EndOfFile) [])`

val IllegalArgument_exn_def = Define `
  IllegalArgument_exn v = (v = Conv (SOME ^IllegalArgument) [])`

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

val _ = ml_prog_update (add_Dlet eval_thm "iobuff" []);

val _ = ml_prog_update open_local_in_block;

(* stdin, stdout, stderr *)
val stdIn_def = Define`
  stdIn = Instream (strlit (MAP (CHR o w2n) (n2w8 0)))`
  |> SIMP_RULE (srw_ss()) [MarshallingTheory.n2w8_def]
val stdOut_def = Define`
  stdOut = Outstream (strlit (MAP (CHR o w2n) (n2w8 1)))`
  |> SIMP_RULE (srw_ss()) [MarshallingTheory.n2w8_def]
val stdErr_def = Define`
  stdErr = Outstream (strlit (MAP (CHR o w2n) (n2w8 2)))`
  |> SIMP_RULE (srw_ss()) [MarshallingTheory.n2w8_def];
val _ = next_ml_names := ["stdIn","stdOut","stdErr"];
val r = translate stdIn_def;
val r = translate stdOut_def;
val r = translate stdErr_def;

val _ = ml_prog_update open_local_block;

(* writei: higher-lever write function which calls #write until something is written or
* a filesystem error is raised and outputs the number of bytes written.
* It assumes that iobuff is initialised
* write: idem, but keeps writing until the whole (specified part of the) buffer
* is written *)

val _ =
  process_topdecs`fun writei fd n i =
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
          if nw < n then write fd (n-nw) (i+nw) else () end` |> append_prog

val _ = ml_prog_update open_local_in_block;

(* Output functions on given file descriptor *)
val _ =
  process_topdecs` fun output1 fd c =
    (Word8Array.update iobuff 4 (Word8.fromInt(Char.ord c)); write (get_out fd) 1 0; ())
    ` |> append_prog

(* writes a string into a file *)
val _ =
  process_topdecs` fun output fd s =
  if s = "" then () else
  let val z = String.size s
      val n = if z <= 2048 then z else 2048
      val fl = Word8Array.copyVec s 0 n iobuff 4
      val a = write (get_out fd) n 0 in
         output fd (String.substring s n (z-n))
  end;
  fun print s = output stdOut s
  fun print_err s = output stdErr s
    ` |> append_prog

val _ = process_topdecs`
  fun print_list ls =
    case ls of [] => () | (x::xs) => (print x; print_list xs)`
       |> append_prog ;

val _ = process_topdecs`
fun openIn fname =
  let val b = Word8Array.array 9 (Word8.fromInt 0)
      val a = #(open_in) (fname^^(String.str (Char.chr 0))) b in
        if Word8Array.sub b 0 = Word8.fromInt 0
        then Instream (Word8Array.substring b 1 8)
        else raise BadFileName
  end
fun openOut fname =
  let val b = Word8Array.array 9 (Word8.fromInt 0)
      val a = #(open_out) (fname^^(String.str (Char.chr 0))) b in
        if Word8Array.sub b 0 = Word8.fromInt 0
        then Outstream (Word8Array.substring b 1 8)
        else raise BadFileName
  end` |> append_prog
val _ = process_topdecs`

fun closeOut fd =
  let val a = #(close) (get_out fd) iobuff in
        if Word8Array.sub iobuff 0 = Word8.fromInt 0
        then () else raise InvalidFD
  end` |> append_prog

val _ = process_topdecs`

fun closeIn fd =
  let val a = #(close) (get_in fd) iobuff in
        if Word8Array.sub iobuff 0 = Word8.fromInt 0
        then () else raise InvalidFD
  end` |> append_prog

val _ = ml_prog_update open_local_block;

(* wrapper for ffi call *)
val _ = process_topdecs`
  fun read fd n =
    let val a = Marshalling.n2w2 n iobuff 0 in
          (#(read) fd iobuff;
          if Word8.toInt (Word8Array.sub iobuff 0) <> 1
          then Marshalling.w22n iobuff 1
          else raise InvalidFD)
    end` |> append_prog

(* reads 1 char *)
val _ = process_topdecs`
fun read_byte fd =
    if read fd 1 = 0 then raise EndOfFile
    else Word8Array.sub iobuff 4
` |> append_prog


(* val input : in_channel -> bytes -> int -> int -> int
* input ic buf pos len reads up to len characters from the given channel ic,
* storing them in byte sequence buf, starting at character number pos. *)
(* TODO: input0 as local fun *)
val _ =
  process_topdecs`
fun input fd buff off len =
let fun input0 off len count =
    let val nread = read (get_in fd) (min len 2048) in
        if nread = 0 then count else
          (Word8Array.copy iobuff 4 nread buff off;
           input0 (off + nread) (len - nread) (count + nread))
    end
in input0 off len 0 end
` |> append_prog

val _ = ml_prog_update open_local_in_block;

val _ = (append_prog o process_topdecs)`
  fun input1 fd = Char.some(Char.fromByte(read_byte (get_in fd))) handle EndOfFile => None`

val _ = ml_prog_update open_local_block;

(* helper function:
   extend a byte array, or, more accurately
   copy a byte array into a new one twice the size *)
val () = (append_prog o process_topdecs)`
  fun extend_array arr =
    let
      val len = Word8Array.length arr
      val arr' = Word8Array.array (2*len) (Word8.fromInt 0)
    in (Word8Array.copy arr 0 len arr' 0; arr') end`;

val _ = ml_prog_update open_local_in_block;

(* read a line (same semantics as SML's TextIO.inputLine) *)
(* simple, inefficient version that reads 1 char at a time *)
val () = (append_prog o process_topdecs)`
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
      in inputLine_aux (Word8Array.array 127 (Word8.fromInt 0)) 0 end`;

(* This version doesn't work because CF makes it difficult (impossible?) to
   work with references/arrays inside data structures (here inside a pair)
val () = (append_prog o process_topdecs)`
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
    end`;
*)

(*

Version of inputLine that reads chunks at a time, but has to return
the unused part of the last chunk. I expect this will not end up being
used, because something like the above simpler version becomes
efficient if we switch to buffered streams.  I.e., the buffering
shouldn't be inputLine-specific.

(* generalisable to splitl *)
val _ = process_topdecs`
fun find_newline s i l =
  if i >= l then l else
  if String.sub s i = #"\n" then i
  else find_newline s (i+1) l
fun split_newline s =
  let val l = String.size s
      val i = find_newline s 0 l in
        (String.substring s 0 i, String.substring s i (l-i))
  end
` |> append_prog

(* using lets/ifs as case take a while in xlet *)
(* if/if take a while in xcf *)
val _ = process_topdecs`
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

val _ = (append_prog o process_topdecs) `
  fun inputLines fd =
    case inputLine fd of
        None => []
      | Some l => l::inputLines fd`;

val _ = (append_prog o process_topdecs) `
  fun inputLinesFrom fname =
    let
      val fd = openIn fname
      val lines = inputLines fd
    in
      closeIn fd; Some lines
    end handle BadFileName => None`;

(* read everything (same semantics as SML's TextIO.inputAll) *)
val () = (append_prog o process_topdecs)`
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
      in inputAll_aux (Word8Array.array 127 (Word8.fromInt 0)) 0 end`;

(* copies all of an input stream to an output stream by chunks of 2048 bytes *)
(* similar to ocaml batteries included batIO.copy *)
val _ = (append_prog o process_topdecs)`
    fun copy inp out =
    let val nr = read (get_in inp) 2048 in
      if nr = 0 then () else (write (get_out out) nr 0; copy inp out)
    end`

(*Buffered IO section*)

(*Open a buffered instream with a buffer size of bsize.
  Force 1028 <= size < 256^2*)
val _ =
  process_topdecs`
fun b_openInSetBufferSize fname bsize =
  let
    val is = openIn fname
  in
      InstreamBuffered is (Ref 4) (Ref 4)
        (Word8Array.array (min 65535 (max (bsize+4) 1028))
          (Word8.fromInt 48))
  end
` |> append_prog

val _ =
  process_topdecs`
fun b_openIn fname = b_openInSetBufferSize fname 4096
` |> append_prog

val _ = (append_prog o process_topdecs)`
  fun b_closeIn is =
    case is of InstreamBuffered fd rref wref surplus =>
      closeIn fd`;

val _ = ml_prog_update open_local_block;
(*b_input helper function for the case when there are
  enough bytes in instream buffer*)
val _ = (append_prog o process_topdecs)`
  fun b_input_aux is buff off len =
    case is of InstreamBuffered fd rref wref surplus =>
      let
        val readat = (!rref)
      in
        Word8Array.copy surplus readat len buff off;
        rref := readat + len;
        len
      end`;

val _ = ml_prog_update open_local_in_block;

val _ = (append_prog o process_topdecs)`
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
     end`;

val _ = ml_prog_update open_local_block;

(* wrapper for ffi call *)
val _ = process_topdecs`
  fun read_into fd buff n =
    let val a = Marshalling.n2w2 n buff 0 in
          (#(read) fd buff;
          if Word8.toInt (Word8Array.sub buff 0) <> 1
          then Marshalling.w22n buff 1
          else raise InvalidFD)
    end` |> append_prog

val _ = ml_prog_update open_local_in_block;
val _ = ml_prog_update open_local_block;

val _ = (append_prog o process_topdecs)`
 fun b_refillBuffer_with_read is =
   case is of InstreamBuffered fd rref wref surplus =>
       (wref := 4 + (read_into (get_in fd) surplus ((Word8Array.length surplus)-4));
       rref := 4;
       (!wref) - 4)`;

val _ = (append_prog o process_topdecs)`
 fun b_input1_aux is =
   case is of InstreamBuffered fd rref wref surplus =>
          if (!wref) = (!rref) then None
          else
            let val readat = (!rref) in
              rref := (!rref) + 1;
              Char.some (Char.fromByte (Word8Array.sub surplus readat))
            end`;

val _ = ml_prog_update open_local_in_block;

val _ = (append_prog o process_topdecs)`
  fun b_input1 is =
    case is of InstreamBuffered fd rref wref surplus =>
        if (!wref) = (!rref)
        then (b_refillBuffer_with_read is; b_input1_aux is)
        else b_input1_aux is`;

val _ = ml_prog_update open_local_block;

val _ = (append_prog o process_topdecs)`
  fun b_inputUntil_aux is (chr:char) =
    case b_input1 is of
      Some c =>  (if c <> chr then (c::b_inputUntil_aux is chr) else (c::[]))
    | None => []`;

Definition compress_def:
  compress chrs = mlstring$implode (REVERSE chrs)
End

val _ = translate compress_def;

val _ = (append_prog o process_topdecs)`
  fun b_inputLine_aux is k chrs strs =
    case b_input1 is of
      None =>
        if List.null chrs andalso List.null strs
        then None
        else Some (String.concat (List.rev (compress (#"\n"::chrs) :: strs)))
    | Some c =>
        if c = #"\n"
        then Some (String.concat (List.rev (compress (c::chrs) :: strs)))
        else if k = 0
             then b_inputLine_aux is 500 [] (compress (c::chrs) :: strs)
             else b_inputLine_aux is (k-1) (c::chrs) strs`;

Definition some_compress_def:
  some_compress g is_emp chrs acc =
    if is_emp then NONE else
      SOME (REVERSE (if NULL chrs then acc else g (compress chrs) :: acc))
End

val _ = translate some_compress_def;

val _ = (append_prog o process_topdecs)`
  fun b_inputLineTokens_aux is f g is_emp chrs acc =
    case b_input1 is of
      None => some_compress g is_emp chrs acc
    | Some c =>
        if c = #"\n"
        then some_compress g False chrs acc
        else if f c
             then if List.null chrs
                  then b_inputLineTokens_aux is f g False [] acc
                  else b_inputLineTokens_aux is f g False [] (g (compress chrs) :: acc)
             else b_inputLineTokens_aux is f g False (c::chrs) acc`;

val _ = ml_prog_update open_local_in_block;

val _ = (append_prog o process_topdecs)`
  fun b_inputUntil is chr = String.implode (b_inputUntil_aux is chr)`;

val _ = (append_prog o process_topdecs)`
  fun b_inputLine is = b_inputLine_aux is 500 [] []`;

val _ = (append_prog o process_topdecs)`
  fun b_inputLineTokens is f g = b_inputLineTokens_aux is f g True [] []`;

val _ = ml_prog_update open_local_block;

val _ = (append_prog o process_topdecs)`
  fun b_inputLines_aux is acc =
     case b_inputLine is of
       None => List.rev acc
     | Some l => b_inputLines_aux is (l::acc)`;

val _ = (append_prog o process_topdecs)`
  fun b_inputAllTokens_aux is f g acc =
     case b_inputLineTokens is f g of
       None => List.rev acc
     | Some l => b_inputAllTokens_aux is f g (l::acc)`;

val _ = ml_prog_update open_local_in_block;

val _ = (append_prog o process_topdecs)`
  fun b_inputLines is =
    b_inputLines_aux is []`;

val _ = (append_prog o process_topdecs) `
  fun b_inputLinesFrom fname =
    let
      val is = b_openIn fname
      val lines = b_inputLines is
    in
      b_closeIn is; Some lines
    end handle BadFileName => None`;

val _ = (append_prog o process_topdecs)`
  fun b_inputAllTokens is f g =
    b_inputAllTokens_aux is f g []`;

val _ = (append_prog o process_topdecs) `
  fun b_inputAllTokensFrom fname f g =
    let
      val is = b_openIn fname
      val lines = b_inputAllTokens is f g
    in
      b_closeIn is; Some lines
    end handle BadFileName => None`;

val _ = ml_prog_update close_local_blocks;
val _ = ml_prog_update (close_module NONE);

val _ = export_theory();
