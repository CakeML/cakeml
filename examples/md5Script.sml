(*
   Functional definition of md5 hash based on HOL/src/portableML/poly/MD5.sml
*)
open preamble wordsTheory;

val _ = new_theory "md5";

val _ = set_grammar_ancestry ["list", "words"];

(*
    type word64  = {hi:W32.word,lo:W32.word}
    type word128 = {A:W32.word, B:W32.word, C:W32.word,  D:W32.word}
    type md5state = {digest:word128,
                       mlen:word64,
                        buf:Word8Vector.vector}
*)

Datatype:
  w64 = <| hi : word32; lo : word32 |>
End

Datatype:
  w128 = <| A : word32; B : word32; C : word32; D : word32 |>
End

Datatype:
  md5state = <| digest : w128 ; mlen : w64 ;
                buf : word8 list ; (* kept in reverse order *)
                buf_len : num (* LENGTH of buf *) |>
End

(*
    val w64_zero = ({hi=0w0,lo=0w0}:word64)
    fun mul8add ({hi,lo},n) = let
      val mul8lo = W32.<< (W32.fromInt (n),0w3)
      val mul8hi = W32.>> (W32.fromInt (n),0w29)
      val lo = W32.+ (lo,mul8lo)
      val cout = if W32.< (lo,mul8lo) then 0w1 else 0w0
      val hi = W32.+ (mul8hi,W32.+ (hi,cout))
    in {hi=hi,lo=lo}
    end
*)

Definition w64_zero_def:
  w64_zero = <| hi := 0w; lo := 0w |>
End

Definition mul8add_def:
  mul8add w n =
    let hi = w.hi in
    let lo = w.lo in
    let mul8lo = (n2w n << 3):word32 in
    let mul8hi = (n2w n >>> 29):word32 in
    let lo = lo + mul8lo in
    let cout = (if lo <+ mul8lo then 1w else 0w) in
    let hi = mul8hi + hi + cout in
      <| hi:=hi ; lo:=lo|>
End

(*
    fun packLittle wrds = let
      fun loop [] = []
        | loop (w::ws) = let
            val b0 = Word8.fromLargeWord (W32.toLargeWord w)
            val b1 = Word8.fromLargeWord (W32.toLargeWord (W32.>> (w,0w8)))
            val b2 = Word8.fromLargeWord (W32.toLargeWord (W32.>> (w,0w16)))
            val b3 = Word8.fromLargeWord (W32.toLargeWord (W32.>> (w,0w24)))
          in b0::b1::b2::b3:: (loop ws)
          end
    in W8V.fromList (loop wrds)
    end
*)

Definition packLittle_def:
  packLittle [] = ([]:word8 list) ∧
  packLittle ((w:word32)::ws) =
    w2w w ::
    w2w (w >>> 8) ::
    w2w (w >>> 16) ::
    w2w (w >>> 24) :: packLittle ws
End

(*
    val S11 = 0w7
    val S12 = 0w12
    val S13 = 0w17
    val S14 = 0w22
    val S21 = 0w5
    val S22 = 0w9
    val S23 = 0w14
    val S24 = 0w20
    val S31 = 0w4
    val S32 = 0w11
    val S33 = 0w16
    val S34 = 0w23
    val S41 = 0w6
    val S42 = 0w10
    val S43 = 0w15
    val S44 = 0w21
*)

Overload S11[local] = “7:num”
Overload S12[local] = “12:num”
Overload S13[local] = “17:num”
Overload S14[local] = “22:num”
Overload S21[local] = “5:num”
Overload S22[local] = “9:num”
Overload S23[local] = “14:num”
Overload S24[local] = “20:num”
Overload S31[local] = “4:num”
Overload S32[local] = “11:num”
Overload S33[local] = “16:num”
Overload S34[local] = “23:num”
Overload S41[local] = “6:num”
Overload S42[local] = “10:num”
Overload S43[local] = “15:num”
Overload S44[local] = “21:num”

(*
    fun PADDING i =  W8V.tabulate (i,(fn 0 => 0wx80 | _ => 0wx0))
*)

Definition PADDING_def:
  PADDING i = GENLIST (λn. if n = 0 then 0x80w else 0w:word8) i
End

(*
    fun F (x,y,z) = W32.orb (W32.andb (x,y),
                           W32.andb (W32.notb x,z))
    fun G (x,y,z) = W32.orb (W32.andb (x,z),
                           W32.andb (y,W32.notb z))
    fun H (x,y,z) = W32.xorb (x,W32.xorb (y,z))
    fun I (x,y,z) = W32.xorb (y,W32.orb (x,W32.notb z))
    fun ROTATE_LEFT (x,n) =
      W32.orb (W32.<< (x,n), W32.>> (x,0w32 - n))
*)

Definition F'_def:
  F' x y z = ((x && y) || ((~x) && z)) :word32
End

Definition G'_def:
  G' x y z = ((x && z) || (y && (~z))) :word32
End

Definition H'_def:
  H' x y z = word_xor x (word_xor y z) :word32
End

Definition I'_def:
  I' x y z = word_xor y (x || (~z)) :word32
End

Definition ROTATE_LEFT_def:
  ROTATE_LEFT x n = ((x << n) || (x >>> (32 - n))) :word32
End

(*
    fun XX f (a,b,c,d,x,s,ac) = let
      val a = W32.+ (a,W32.+ (W32.+ (f (b,c,d),x),ac))
      val a = ROTATE_LEFT (a,s)
    in W32.+ (a,b)
    end
*)

Definition XX_def:
  XX f a b c d x s ac =
    let a = a + f b c d + x + ac in
    let a = ROTATE_LEFT a s in
      a + b :word32
End

(*
    val FF = XX F
    val GG = XX G
    val HH = XX H
    val II = XX I
*)

Overload FF = “XX F'”;
Overload GG = “XX G'”;
Overload HH = “XX H'”;
Overload II = “XX I'”;

(*
    val empty_buf = W8V.tabulate (0,(fn x => raise (Fail "buf")))
    val init = {digest= {A=0wx67452301,
                        B=0wxefcdab89,
                        C=0wx98badcfe,
                        D=0wx10325476},
                mlen=w64_zero,
                buf=empty_buf} : md5state
*)

Definition init_def:
  init = <| digest := <| A := 0x67452301w ;
                         B := 0xefcdab89w ;
                         C := 0x98badcfew ;
                         D := 0x10325476w |> ;
            mlen := <| hi := 0w ; lo := 0w |>;
            buf := [] ;
            buf_len := 0 |>
End

(*
    fun transform ({A,B,C,D},i,buf) = let
      val off = i div PackWord32Little.bytesPerElem
      fun x (n) = Word32.fromLargeWord (PackWord32Little.subVec (buf,n + off))
      val (a,b,c,d) = (A,B,C,D)
      (* fetch to avoid range checks *)
      val x_00 = x (0)  val x_01 = x (1)  val x_02 = x (2)  val x_03 = x (3)
      val x_04 = x (4)  val x_05 = x (5)  val x_06 = x (6)  val x_07 = x (7)
      val x_08 = x (8)  val x_09 = x (9)  val x_10 = x (10) val x_11 = x (11)
      val x_12 = x (12) val x_13 = x (13) val x_14 = x (14) val x_15 = x (15)

      val a = FF (a, b, c, d, x_00, S11, 0wxd76aa478) (* 1 *)
      val d = FF (d, a, b, c, x_01, S12, 0wxe8c7b756) (* 2 *)
      val c = FF (c, d, a, b, x_02, S13, 0wx242070db) (* 3 *)
      val b = FF (b, c, d, a, x_03, S14, 0wxc1bdceee) (* 4 *)
      val a = FF (a, b, c, d, x_04, S11, 0wxf57c0faf) (* 5 *)
      val d = FF (d, a, b, c, x_05, S12, 0wx4787c62a) (* 6 *)
      val c = FF (c, d, a, b, x_06, S13, 0wxa8304613) (* 7 *)
      val b = FF (b, c, d, a, x_07, S14, 0wxfd469501) (* 8 *)
      val a = FF (a, b, c, d, x_08, S11, 0wx698098d8) (* 9 *)
      val d = FF (d, a, b, c, x_09, S12, 0wx8b44f7af) (* 10 *)
      val c = FF (c, d, a, b, x_10, S13, 0wxffff5bb1) (* 11 *)
      val b = FF (b, c, d, a, x_11, S14, 0wx895cd7be) (* 12 *)
      val a = FF (a, b, c, d, x_12, S11, 0wx6b901122) (* 13 *)
      val d = FF (d, a, b, c, x_13, S12, 0wxfd987193) (* 14 *)
      val c = FF (c, d, a, b, x_14, S13, 0wxa679438e) (* 15 *)
      val b = FF (b, c, d, a, x_15, S14, 0wx49b40821) (* 16 *)

      (* Round 2 *)
      val a = GG (a, b, c, d, x_01, S21, 0wxf61e2562) (* 17 *)
      val d = GG (d, a, b, c, x_06, S22, 0wxc040b340) (* 18 *)
      val c = GG (c, d, a, b, x_11, S23, 0wx265e5a51) (* 19 *)
      val b = GG (b, c, d, a, x_00, S24, 0wxe9b6c7aa) (* 20 *)
      val a = GG (a, b, c, d, x_05, S21, 0wxd62f105d) (* 21 *)
      val d = GG (d, a, b, c, x_10, S22,  0wx2441453) (* 22 *)
      val c = GG (c, d, a, b, x_15, S23, 0wxd8a1e681) (* 23 *)
      val b = GG (b, c, d, a, x_04, S24, 0wxe7d3fbc8) (* 24 *)
      val a = GG (a, b, c, d, x_09, S21, 0wx21e1cde6) (* 25 *)
      val d = GG (d, a, b, c, x_14, S22, 0wxc33707d6) (* 26 *)
      val c = GG (c, d, a, b, x_03, S23, 0wxf4d50d87) (* 27 *)
      val b = GG (b, c, d, a, x_08, S24, 0wx455a14ed) (* 28 *)
      val a = GG (a, b, c, d, x_13, S21, 0wxa9e3e905) (* 29 *)
      val d = GG (d, a, b, c, x_02, S22, 0wxfcefa3f8) (* 30 *)
      val c = GG (c, d, a, b, x_07, S23, 0wx676f02d9) (* 31 *)
      val b = GG (b, c, d, a, x_12, S24, 0wx8d2a4c8a) (* 32 *)

      (* Round 3 *)
      val a = HH (a, b, c, d, x_05, S31, 0wxfffa3942) (* 33 *)
      val d = HH (d, a, b, c, x_08, S32, 0wx8771f681) (* 34 *)
      val c = HH (c, d, a, b, x_11, S33, 0wx6d9d6122) (* 35 *)
      val b = HH (b, c, d, a, x_14, S34, 0wxfde5380c) (* 36 *)
      val a = HH (a, b, c, d, x_01, S31, 0wxa4beea44) (* 37 *)
      val d = HH (d, a, b, c, x_04, S32, 0wx4bdecfa9) (* 38 *)
      val c = HH (c, d, a, b, x_07, S33, 0wxf6bb4b60) (* 39 *)
      val b = HH (b, c, d, a, x_10, S34, 0wxbebfbc70) (* 40 *)
      val a = HH (a, b, c, d, x_13, S31, 0wx289b7ec6) (* 41 *)
      val d = HH (d, a, b, c, x_00, S32, 0wxeaa127fa) (* 42 *)
      val c = HH (c, d, a, b, x_03, S33, 0wxd4ef3085) (* 43 *)
      val b = HH (b, c, d, a, x_06, S34,  0wx4881d05) (* 44 *)
      val a = HH (a, b, c, d, x_09, S31, 0wxd9d4d039) (* 45 *)
      val d = HH (d, a, b, c, x_12, S32, 0wxe6db99e5) (* 46 *)
      val c = HH (c, d, a, b, x_15, S33, 0wx1fa27cf8) (* 47 *)
      val b = HH (b, c, d, a, x_02, S34, 0wxc4ac5665) (* 48 *)

      (* Round 4 *)
      val a = II (a, b, c, d, x_00, S41, 0wxf4292244) (* 49 *)
      val d = II (d, a, b, c, x_07, S42, 0wx432aff97) (* 50 *)
      val c = II (c, d, a, b, x_14, S43, 0wxab9423a7) (* 51 *)
      val b = II (b, c, d, a, x_05, S44, 0wxfc93a039) (* 52 *)
      val a = II (a, b, c, d, x_12, S41, 0wx655b59c3) (* 53 *)
      val d = II (d, a, b, c, x_03, S42, 0wx8f0ccc92) (* 54 *)
      val c = II (c, d, a, b, x_10, S43, 0wxffeff47d) (* 55 *)
      val b = II (b, c, d, a, x_01, S44, 0wx85845dd1) (* 56 *)
      val a = II (a, b, c, d, x_08, S41, 0wx6fa87e4f) (* 57 *)
      val d = II (d, a, b, c, x_15, S42, 0wxfe2ce6e0) (* 58 *)
      val c = II (c, d, a, b, x_06, S43, 0wxa3014314) (* 59 *)
      val b = II (b, c, d, a, x_13, S44, 0wx4e0811a1) (* 60 *)
      val a = II (a, b, c, d, x_04, S41, 0wxf7537e82) (* 61 *)
      val d = II (d, a, b, c, x_11, S42, 0wxbd3af235) (* 62 *)
      val c = II (c, d, a, b, x_02, S43, 0wx2ad7d2bb) (* 63 *)
      val b = II (b, c, d, a, x_09, S44, 0wxeb86d391) (* 64 *)

      val A = Word32.+ (A,a)
      val B = Word32.+ (B,b)
      val C = Word32.+ (C,c)
      val D = Word32.+ (D,d)
    in {A=A,B=B,C=C,D=D}
    end
*)

Definition subVec_def:
  subVec (buf:word8 list) n =
    let xs = DROP (4 * n) buf in
      case xs of
      | (x1::x2::x3::x4::_) => w2w x1 || w2w x2 << 8 || w2w x3 << 16 || w2w x4 << 24
      | _ => 0w:word32
End

Definition transform_def:
  transform abcd i (buf:word8 list) =
    let off = i DIV 4 in
    let x = (λn. subVec buf (n + off)) in
    let a = abcd.A in
    let b = abcd.B in
    let c = abcd.C in
    let d = abcd.D in

    (* fetch to avoid range checks *)
    let x_00 = x (0)  in let x_01 = x (1)  in let x_02 = x (2)  in let x_03 = x (3) in
    let x_04 = x (4)  in let x_05 = x (5)  in let x_06 = x (6)  in let x_07 = x (7) in
    let x_08 = x (8)  in let x_09 = x (9)  in let x_10 = x (10) in let x_11 = x (11) in
    let x_12 = x (12) in let x_13 = x (13) in let x_14 = x (14) in let x_15 = x (15) in

    (* Round 1 *)
    let a = FF a b c d x_00 S11 0xd76aa478w in (* 1 *)
    let d = FF d a b c x_01 S12 0xe8c7b756w in (* 2 *)
    let c = FF c d a b x_02 S13 0x242070dbw in (* 3 *)
    let b = FF b c d a x_03 S14 0xc1bdceeew in (* 4 *)
    let a = FF a b c d x_04 S11 0xf57c0fafw in (* 5 *)
    let d = FF d a b c x_05 S12 0x4787c62aw in (* 6 *)
    let c = FF c d a b x_06 S13 0xa8304613w in (* 7 *)
    let b = FF b c d a x_07 S14 0xfd469501w in (* 8 *)
    let a = FF a b c d x_08 S11 0x698098d8w in (* 9 *)
    let d = FF d a b c x_09 S12 0x8b44f7afw in (* 10 *)
    let c = FF c d a b x_10 S13 0xffff5bb1w in (* 11 *)
    let b = FF b c d a x_11 S14 0x895cd7bew in (* 12 *)
    let a = FF a b c d x_12 S11 0x6b901122w in (* 13 *)
    let d = FF d a b c x_13 S12 0xfd987193w in (* 14 *)
    let c = FF c d a b x_14 S13 0xa679438ew in (* 15 *)
    let b = FF b c d a x_15 S14 0x49b40821w in (* 16 *)

    (* Round 2 *)
    let a = GG a b c d x_01 S21 0xf61e2562w in (* 17 *)
    let d = GG d a b c x_06 S22 0xc040b340w in (* 18 *)
    let c = GG c d a b x_11 S23 0x265e5a51w in (* 19 *)
    let b = GG b c d a x_00 S24 0xe9b6c7aaw in (* 20 *)
    let a = GG a b c d x_05 S21 0xd62f105dw in (* 21 *)
    let d = GG d a b c x_10 S22  0x2441453w in (* 22 *)
    let c = GG c d a b x_15 S23 0xd8a1e681w in (* 23 *)
    let b = GG b c d a x_04 S24 0xe7d3fbc8w in (* 24 *)
    let a = GG a b c d x_09 S21 0x21e1cde6w in (* 25 *)
    let d = GG d a b c x_14 S22 0xc33707d6w in (* 26 *)
    let c = GG c d a b x_03 S23 0xf4d50d87w in (* 27 *)
    let b = GG b c d a x_08 S24 0x455a14edw in (* 28 *)
    let a = GG a b c d x_13 S21 0xa9e3e905w in (* 29 *)
    let d = GG d a b c x_02 S22 0xfcefa3f8w in (* 30 *)
    let c = GG c d a b x_07 S23 0x676f02d9w in (* 31 *)
    let b = GG b c d a x_12 S24 0x8d2a4c8aw in (* 32 *)

    (* Round 3 *)
    let a = HH a b c d x_05 S31 0xfffa3942w in (* 33 *)
    let d = HH d a b c x_08 S32 0x8771f681w in (* 34 *)
    let c = HH c d a b x_11 S33 0x6d9d6122w in (* 35 *)
    let b = HH b c d a x_14 S34 0xfde5380cw in (* 36 *)
    let a = HH a b c d x_01 S31 0xa4beea44w in (* 37 *)
    let d = HH d a b c x_04 S32 0x4bdecfa9w in (* 38 *)
    let c = HH c d a b x_07 S33 0xf6bb4b60w in (* 39 *)
    let b = HH b c d a x_10 S34 0xbebfbc70w in (* 40 *)
    let a = HH a b c d x_13 S31 0x289b7ec6w in (* 41 *)
    let d = HH d a b c x_00 S32 0xeaa127faw in (* 42 *)
    let c = HH c d a b x_03 S33 0xd4ef3085w in (* 43 *)
    let b = HH b c d a x_06 S34  0x4881d05w in (* 44 *)
    let a = HH a b c d x_09 S31 0xd9d4d039w in (* 45 *)
    let d = HH d a b c x_12 S32 0xe6db99e5w in (* 46 *)
    let c = HH c d a b x_15 S33 0x1fa27cf8w in (* 47 *)
    let b = HH b c d a x_02 S34 0xc4ac5665w in (* 48 *)

    (* Round 4 *)
    let a = II a b c d x_00 S41 0xf4292244w in (* 49 *)
    let d = II d a b c x_07 S42 0x432aff97w in (* 50 *)
    let c = II c d a b x_14 S43 0xab9423a7w in (* 51 *)
    let b = II b c d a x_05 S44 0xfc93a039w in (* 52 *)
    let a = II a b c d x_12 S41 0x655b59c3w in (* 53 *)
    let d = II d a b c x_03 S42 0x8f0ccc92w in (* 54 *)
    let c = II c d a b x_10 S43 0xffeff47dw in (* 55 *)
    let b = II b c d a x_01 S44 0x85845dd1w in (* 56 *)
    let a = II a b c d x_08 S41 0x6fa87e4fw in (* 57 *)
    let d = II d a b c x_15 S42 0xfe2ce6e0w in (* 58 *)
    let c = II c d a b x_06 S43 0xa3014314w in (* 59 *)
    let b = II b c d a x_13 S44 0x4e0811a1w in (* 60 *)
    let a = II a b c d x_04 S41 0xf7537e82w in (* 61 *)
    let d = II d a b c x_11 S42 0xbd3af235w in (* 62 *)
    let c = II c d a b x_02 S43 0x2ad7d2bbw in (* 63 *)
    let b = II b c d a x_09 S44 0xeb86d391w in (* 64 *)

    let A = word_add abcd.A a in
    let B = word_add abcd.B b in
    let C = word_add abcd.C c in
    let D = word_add abcd.D d in
      <| A:=A ; B:=B ; C:=C ; D:=D |>
End

(*
    fun extract (vec, s, l) =  (* but note that l is always SOME *)
       let
          val n =
             case l of
                NONE => length vec - s
              | SOME i => i
       in
          tabulate (n, fn i => sub (vec, s + i))
       end
*)

Definition genlist_rev_def:
  genlist_rev f 0 = [] ∧
  genlist_rev f (SUC n) = f n :: genlist_rev f n
End

Definition extract_def:
  extract vec s l = genlist_rev (λi. case oEL (s + i) vec of
                                     | NONE => 0w:word8
                                     | SOME b => b) l
End

(*
    fun update ({buf,digest,mlen}:md5state,input) = let
      val inputLen = W8V.length input
      val needBytes = 64 - W8V.length buf
      fun loop (i,digest) =
        if i + 63 < inputLen then
          loop (i + 64,transform (digest,i,input))
        else (i,digest)
      val (buf,(i,digest)) =
        if inputLen >= needBytes then  let
          val buf = W8V.concat [buf,W8V.extract (input,0,SOME needBytes)]
          val digest = transform (digest,0,buf)
        in (empty_buf,loop (needBytes,digest))
        end
        else (buf,(0,digest))
      val buf = W8V.concat [buf, W8V.extract (input,i,SOME (inputLen-i))]
      val mlen = mul8add (mlen,inputLen)
    in {buf=buf,digest=digest,mlen=mlen}
    end
*)

Definition loop_def:
  loop (i:num) digest (input:word8 list) inputLen =
    if i + 63 < inputLen then
      loop (i + 64) (transform digest i input) input inputLen
    else (i,digest)
Termination
  WF_REL_TAC ‘measure (λ(i,digest,input,inputLen). inputLen - i)’
End

Definition take_rev_def:
  take_rev n [] acc = acc ∧
  take_rev n (x::xs) acc = if n = 0 then acc else take_rev (n-1:num) xs (x::acc)
End

Definition update_def:
  update state (input:word8 list) =
    let buf = state.buf in
    let buf_len = state.buf_len in
    let digest = state.digest in
    let mlen = state.mlen in
    let inputLen = LENGTH input in
    let needBytes = 64 - buf_len in
      if inputLen >= needBytes then
        let buf = take_rev needBytes input buf in
        let digest = transform digest 0 (REVERSE buf) in
        let (i,digest) = loop needBytes digest input inputLen in
        let buf_len = inputLen - i in
        let buf = extract input i buf_len in
        let mlen = mul8add mlen inputLen in
          <| buf := buf ; buf_len := buf_len ; digest := digest ; mlen := mlen  |>
      else
        let buf = REVERSE input ++ buf in
        let buf_len = buf_len + inputLen in
        let mlen = mul8add mlen inputLen in
          <| buf := buf ; buf_len := buf_len ; digest := digest ; mlen := mlen  |>
End

(*
    and final (state:md5state) = let
      val {mlen= {lo,hi},buf,...} = state
      val bits = packLittle [lo,hi]
      val index = W8V.length buf
      val padLen = if index < 56 then 56 - index else 120 - index
      val state = update (state,PADDING padLen)
      val {digest= {A,B,C,D},...} = update (state,bits)
    in packLittle [A,B,C,D]
*)

Definition final_def:
  final state =
    let buf = state.buf in
    let buf_len = state.buf_len in
    let mlen = state.mlen in
    let bits = packLittle [mlen.lo;mlen.hi] in
    let index = buf_len in
    let padLen = (if index < 56 then 56 - index else 120 - index) in
    let state = update state (PADDING padLen) in
    let state = update state bits in
    let digest = state.digest in
      packLittle [digest.A; digest.B; digest.C; digest.D]
End

(*
    val hxd = "0123456789abcdef"
    fun toHexString v = let
      fun byte2hex (b,acc) =
        (String.sub (hxd,(Word8.toInt b) div 16))::
        (String.sub (hxd,(Word8.toInt b) mod 16))::acc
      val digits = Word8Vector.foldr byte2hex [] v
    in String.implode digits
    end
*)

Definition hxd_def:
  hxd = "0123456789abcdef"
End

Definition byte2hex_def:
  byte2hex (b:word8) acc =
    let n = w2n b in
      (EL (n DIV 16) hxd) ::
      (EL (n MOD 16) hxd) :: acc
End

Definition toHexString_def:
  toHexString v = FOLDR byte2hex [] v
End

(*
    Specialise update for taking only one input
*)

Definition update1_def:
  update1 state (input:word8) =
    let buf = state.buf in
    let buf_len = state.buf_len in
    let digest = state.digest in
    let mlen = state.mlen in
    let needBytes = 64 - buf_len in
    let mlen = mul8add mlen 1 in
      if 1 < needBytes then
        let buf = input::buf in
        let buf_len = buf_len + 1 in
          <| buf := buf ; buf_len := buf_len ; digest := digest ; mlen := mlen  |>
      else if needBytes = 1 then
        let buf = input::buf in
        let digest = transform digest 0 (REVERSE buf) in
        let buf_len = 0 in
        let buf = [] in
          <| buf := buf ; buf_len := buf_len ; digest := digest ; mlen := mlen  |>
      else
        let digest = transform digest 0 (REVERSE buf) in
        let buf_len = 1 in
        let buf = [input] in
          <| buf := buf ; buf_len := buf_len ; digest := digest ; mlen := mlen  |>
End

Theorem update1_thm:
  update1 state input = update state [input]
Proof
  fs [update_def,update1_def]
  \\ qabbrev_tac ‘n = 64 − state.buf_len’
  \\ Cases_on ‘n’ \\ fs [take_rev_def]
  \\ once_rewrite_tac [loop_def] \\ fs []
  THEN1 fs [extract_def,EVAL “genlist_rev f 1”,oEL_def]
  \\ Cases_on ‘n'’ \\ fs [extract_def,genlist_rev_def]
  \\ once_rewrite_tac [loop_def] \\ fs [extract_def,oEL_def]
QED

fun md5 str = let
  val xs = str |> explode |> map (Word8.fromInt o Char.ord)
  val state = MD5.init
  val state = MD5.update(state,Word8Vector.fromList xs)
  val state = MD5.final state
  in MD5.toHexString state end

Definition md5_def:
  md5 str = toHexString (final (FOLDL update1 init (MAP (n2w o ORD) str)))
End

(*
    Some testing
*)

fun run_test str = let
  val str_tm = str |> stringSyntax.fromMLstring
  val res = EVAL (mk_comb(“md5”,str_tm))
            |> concl |> rand |> stringSyntax.fromHOLstring
  val correct = md5 str
  in if res = correct
     then (print ("Passed for: " ^ str ^ "\n"))
     else (print ("Failed for: " ^ str ^ "\n"); fail()) end;

val _ = run_test "hi";
val _ = run_test "there";
val _ = run_test "This is a longer string.";
val _ = run_test ("Mun mummoni mun mammani. Mun mammani muni mut." ^
                  "Mun mummoni mun mammani. Mun mammani muni mut." ^
                  "Mun mummoni mun mammani. Mun mammani muni mut." ^
                  "Mun mummoni mun mammani. Mun mammani muni mut." ^
                  "Mun mummoni mun mammani. Mun mammani muni mut.");

val _ = export_theory();
