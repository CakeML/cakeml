(*
  Shallow embedding of garbage collector implementation
*)
open preamble

open wordSemTheory data_to_wordTheory gc_sharedTheory

val _ = new_theory "word_gcFunctions"

val shift_def = backend_commonTheory.word_shift_def;

(* move candidates *)
Theorem bytes_in_word_mul_eq_shift:
   good_dimindex (:'a) ==>
   (bytes_in_word * w = (w << shift (:'a)):'a word)
Proof
  fs [bytes_in_word_def,shift_def,WORD_MUL_LSL,word_mul_n2w]
  \\ fs [labPropsTheory.good_dimindex_def,dimword_def] \\ rw [] \\ rfs []
QED

Theorem word_or_eq_0:
   (w || v) = 0w <=> w = 0w /\ v = 0w
Proof
  fs [fcpTheory.CART_EQ,fcpTheory.FCP_BETA,word_or_def,word_index]
  \\ rw [] \\ eq_tac \\ rw [] \\ fs []
QED

val IMP_EQ_DISJ = METIS_PROVE [] ``(b1 ==> b2) <=> ~b1 \/ b2``

Theorem shift_length_has_fp_ops[simp]:
  shift_length (conf with <| has_fp_ops := b1; has_fp_tern := b2 |>) = shift_length conf
Proof
  EVAL_TAC
QED

(* -------------------------------------------------------
    definition and verification of GC functions
   ------------------------------------------------------- *)

val ptr_to_addr_def = Define `
  ptr_to_addr conf base (w:'a word) =
    base + ((w >>> (shift_length conf)) * bytes_in_word)`

val update_addr_def = Define `
  update_addr conf fwd_ptr (old_addr:'a word) =
    ((fwd_ptr << (shift_length conf)) ||
     ((small_shift_length conf - 1) -- 0) old_addr)`

val memcpy_def = Define `
  memcpy w a b m dm =
    if w = 0w then (b,m,T) else
      let (b1,m1,c1) = memcpy (w-1w) (a + bytes_in_word) (b + bytes_in_word)
                      ((b =+ m a) m) dm in
        (b1,m1,c1 /\ a IN dm /\ b IN dm)`

val decode_length_def = Define `
  decode_length conf (w:'a word) = w >>> (dimindex (:'a) - conf.len_size)`;

val word_gc_move_def = Define `
  (word_gc_move conf (Loc l1 l2,i,pa,old,m,dm) = (Loc l1 l2,i,pa,m,T)) /\
  (word_gc_move conf (Word w,i,pa,old,m,dm) =
     if (w && 1w) = 0w then (Word w,i,pa,m,T) else
       let c = (ptr_to_addr conf old w IN dm) in
       let v = m (ptr_to_addr conf old w) in
         if is_fwd_ptr v then
           (Word (update_addr conf (theWord v >>> 2) w),i,pa,m,c)
         else
           let header_addr = ptr_to_addr conf old w in
           let c = (c /\ header_addr IN dm /\ isWord (m header_addr)) in
           let len = decode_length conf (theWord (m header_addr)) in
           let v = i + len + 1w in
           let (pa1,m1,c1) = memcpy (len+1w) header_addr pa m dm in
           let c = (c /\ header_addr IN dm /\ c1) in
           let m1 = (header_addr =+ Word (i << 2)) m1 in
             (Word (update_addr conf i w),v,pa1,m1,c))`

val word_gen_gc_partial_move_def = Define `
  (word_gen_gc_partial_move conf (Loc l1 l2,i,pa,old,m,dm,gs,rs) = (Loc l1 l2,i,pa,m,T)) /\
  (word_gen_gc_partial_move conf (Word w,i,pa,old,m,dm,gs,rs) =
   if (w && 1w) = 0w then (Word w,i,pa,m,T) else
     let header_addr = ptr_to_addr conf old w in
     let tmp = header_addr - old in
       if tmp <+ gs ∨ rs <=+ tmp then
         (Word w, i, pa, m, T)
       else
         let c = (ptr_to_addr conf old w IN dm) in
         let v = m (ptr_to_addr conf old w) in
           if is_fwd_ptr v then
             (Word (update_addr conf (theWord v >>> 2) w),i,pa,m,c)
           else
             let c = (c /\ header_addr IN dm /\ isWord (m header_addr)) in
             let len = decode_length conf (theWord (m header_addr)) in
             let v = i + len + 1w in
             let (pa1,m1,c1) = memcpy (len+1w) header_addr pa m dm in
             let c = (c /\ header_addr IN dm /\ c1) in
             let m1 = (header_addr =+ Word (i << 2)) m1 in
               (Word (update_addr conf i w),v,pa1,m1,c))`

val word_gc_move_roots_def = Define `
  (word_gc_move_roots conf ([],i,pa,old,m,dm) = ([],i,pa,m,T)) /\
  (word_gc_move_roots conf (w::ws,i,pa,old,m,dm) =
     let (w1,i1,pa1,m1,c1) = word_gc_move conf (w,i,pa,old,m,dm) in
     let (ws2,i2,pa2,m2,c2) = word_gc_move_roots conf (ws,i1,pa1,old,m1,dm) in
       (w1::ws2,i2,pa2,m2,c1 /\ c2))`

val word_gc_move_list_def = Define `
  word_gc_move_list conf (a:'a word,l:'a word,i,pa:'a word,old,m,dm) =
   if l = 0w then (a,i,pa,m,T) else
     let w = (m a):'a word_loc in
     let (w1,i1,pa1,m1,c1) = word_gc_move conf (w,i,pa,old,m,dm) in
     let m1 = (a =+ w1) m1 in
     let (a2,i2,pa2,m2,c2) = word_gc_move_list conf (a+bytes_in_word,l-1w,i1,pa1,old,m1,dm) in
       (a2,i2,pa2,m2,a IN dm /\ c1 /\ c2)`

val word_gen_gc_partial_move_roots_def = Define `
  (word_gen_gc_partial_move_roots conf ([],i,pa,old,m,dm,gs,rs) = ([],i,pa,m,T)) /\
  (word_gen_gc_partial_move_roots conf (w::ws,i,pa,old,m,dm,gs,rs) =
     let (w1,i1,pa1,m1,c1) = word_gen_gc_partial_move conf (w,i,pa,old,m,dm,gs,rs) in
     let (ws2,i2,pa2,m2,c2) = word_gen_gc_partial_move_roots conf (ws,i1,pa1,old,m1,dm,gs,rs) in
       (w1::ws2,i2,pa2,m2,c1 /\ c2))`

val word_gen_gc_partial_move_list_def = Define `
  word_gen_gc_partial_move_list conf (a:'a word,l:'a word,i,pa:'a word,old,m,dm,gs,rs) =
   if l = 0w then (a,i,pa,m,T) else
     let w = (m a):'a word_loc in
     let (w1,i1,pa1,m1,c1) = word_gen_gc_partial_move conf (w,i,pa,old,m,dm,gs,rs) in
     let m1 = (a =+ w1) m1 in
     let (a2,i2,pa2,m2,c2) = word_gen_gc_partial_move_list conf (a+bytes_in_word,l-1w,i1,pa1,old,m1,dm,gs,rs) in
       (a2,i2,pa2,m2,a IN dm /\ c1 /\ c2)`

Theorem word_gen_gc_partial_move_list_zero:
    word_gen_gc_partial_move_list conf (a,0w,i,pa,old,m,dm,gs,rs) = (a,i,pa,m,T)
Proof
  fs[Once word_gen_gc_partial_move_list_def]
QED

Theorem word_gen_gc_partial_move_list_suc:
    word_gen_gc_partial_move_list conf (a,(n2w(SUC l):'a word),i,pa,old,m,dm,gs,rs) =
   if n2w(SUC l) = (0w:'a word) then (a,i,pa,m,T) else
     let w = m a in
     let (w1,i1,pa1,m1,c1) = word_gen_gc_partial_move conf (w,i,pa,old,m,dm,gs,rs) in
     let m1 = (a =+ w1) m1 in
     let (a2,i2,pa2,m2,c2) = word_gen_gc_partial_move_list conf (a+bytes_in_word,n2w l,i1,pa1,old,m1,dm,gs,rs) in
       (a2,i2,pa2,m2,a IN dm /\ c1 /\ c2)
Proof
  CONV_TAC(RATOR_CONV(RAND_CONV(PURE_ONCE_REWRITE_CONV[word_gen_gc_partial_move_list_def])))
  >> fs[n2w_SUC]
QED

Theorem word_gen_gc_partial_move_list_append:
    !a l l' i pa old m dm gs rs conf.
  (l+l' < dimword (:'a)) ==> (
  word_gen_gc_partial_move_list conf (a,(n2w(l+l'):'a word),i,pa,old,m,dm,gs,rs) =
    let (a2,i2,pa2,m2,c2) = word_gen_gc_partial_move_list conf (a,n2w l,i,pa,old,m,dm,gs,rs) in
    let (a3,i3,pa3,m3,c3) = word_gen_gc_partial_move_list conf (a2,n2w l',i2,pa2,old,m2,dm,gs,rs) in
      (a3,i3,pa3,m3,(c2 /\ c3)))
Proof
  Induct_on `l`
  >> rpt strip_tac
  >> fs[]
  >> ntac 2 (pairarg_tac >> fs[])
  >- fs[word_gen_gc_partial_move_list_zero]
  >> fs[word_gen_gc_partial_move_list_suc,GSYM ADD_SUC]
  >> ntac 4 (pairarg_tac >> fs[])
  >> rfs[] >> metis_tac[]
QED

val word_gc_move_loop_def = Define `
  word_gc_move_loop k conf (pb,i,pa,old,m,dm,c) =
    if pb = pa then (i,pa,m,c) else
    if k = 0 then (i,pa,m,F) else
      let w = m pb in
      let c = (c /\ pb IN dm /\ isWord w) in
      let len = decode_length conf (theWord w) in
        if word_bit 2 (theWord w) then
          let pb = pb + (len + 1w) * bytes_in_word in
            word_gc_move_loop (k-1n) conf (pb,i,pa,old,m,dm,c)
        else
          let pb = pb + bytes_in_word in
          let (pb,i1,pa1,m1,c1) = word_gc_move_list conf (pb,len,i,pa,old,m,dm) in
            word_gc_move_loop (k-1n) conf (pb,i1,pa1,old,m1,dm,c /\ c1)`

val word_full_gc_def = Define `
  word_full_gc conf (all_roots,new,old:'a word,m,dm) =
    let (rs,i1,pa1,m1,c1) = word_gc_move_roots conf (all_roots,0w,new,old,m,dm) in
    let (i1,pa1,m1,c2) =
          word_gc_move_loop (dimword(:'a)) conf (new,i1,pa1,old,m1,dm,c1)
    in (rs,i1,pa1,m1,c2)`

val word_gc_fun_assum_def = Define `
  word_gc_fun_assum (conf:data_to_word$config) (s:store_name |-> 'a word_loc) <=>
    {Globals; CurrHeap; OtherHeap; HeapLength;
     TriggerGC; GenStart; EndOfHeap} SUBSET FDOM s /\
    isWord (s ' OtherHeap) /\
    isWord (s ' CurrHeap) /\
    isWord (s ' TriggerGC) /\
    isWord (s ' HeapLength) /\
    isWord (s ' GenStart) /\
    isWord (s ' EndOfHeap) /\
    good_dimindex (:'a) /\
    conf.len_size <> 0 /\
    conf.len_size + 2 < dimindex (:'a) /\
    shift_length conf < dimindex (:'a)`

val word_gen_gc_can_do_partial_def = Define `
  word_gen_gc_can_do_partial gen_sizes (s:store_name |-> 'a word_loc) <=>
    gen_sizes <> [] /\
    let allo = theWord (s ' AllocSize) in
    let trig = theWord (s ' TriggerGC) in
    let endh = theWord (s ' EndOfHeap) in
      (* A partial collection is allowed if the following is
         true. This condition guarantees that even if nothing is
         collected by the partial collection, the the requested space
         still exists. *)
      allo <=+ endh - trig`;

val new_trig_def = Define `
  new_trig (heap_space:'a word) (alloc_pref:'a word) gs =
    let a = w2n alloc_pref in
    let g = w2n ((get_gen_size gs):'a word) in
    let h = w2n heap_space in
      if a <= g (* allocation smaller than gen *) then n2w (MIN h g) else
      if h < a (* allocation too big *) then n2w h else
      if byte_aligned alloc_pref (* should always be the case *)
      then alloc_pref else (* very unlikely and a bad choice *) n2w h`

val refs_to_addresses_def = Define `
  (refs_to_addresses [] = []) /\
  (refs_to_addresses (DataElement ptrs _ _::refs) =
    ptrs ++ refs_to_addresses refs) /\
  (refs_to_addresses (_::refs) = refs_to_addresses refs)`;

val word_gen_gc_partial_move_ref_list_def = Define `
  word_gen_gc_partial_move_ref_list k conf (pb,i,pa,old,m,dm,c,gs,rs,re) =
    if pb = re then (i,pa,m,c) else
    if k = 0 then (i,pa,m,F) else
      let w = m pb in
      let c = (c /\ pb IN dm /\ isWord w) in
      let len = decode_length conf (theWord w) in
      let pb = pb + bytes_in_word in
      let (pb,i1,pa1,m1,c1) = word_gen_gc_partial_move_list conf (pb,len,i,pa,old,m,dm,gs,rs) in
        word_gen_gc_partial_move_ref_list (k-1n) conf (pb,i1,pa1,old,m1,dm,c /\ c1,gs,rs,re)`;


val word_gen_gc_partial_move_data_def = Define `
  word_gen_gc_partial_move_data conf k
   (h2a:'a word,i,pa:'a word,old,m,dm,gs,rs) =
    if h2a = pa then (i,pa,m,T) else
    if k = 0n then (i,pa,m,F) else
      let c = (h2a IN dm) in
      let v = m h2a in
      let c = (c /\ isWord v) in
      let l = decode_length conf (theWord v) in
        if word_bit 2 (theWord v) then
          let h2a = h2a + (l + 1w) * bytes_in_word in
          let (i,pa,m,c2) = word_gen_gc_partial_move_data conf (k-1)
                        (h2a,i,pa,old,m,dm,gs,rs) in
            (i,pa,m,c /\ c2)
        else
          let (h2a,i,pa,m,c1) = word_gen_gc_partial_move_list conf
                        (h2a+bytes_in_word,l,i,pa,old,m,dm,gs,rs) in
          let (i,pa,m,c2) = word_gen_gc_partial_move_data conf (k-1)
                        (h2a,i,pa,old,m,dm,gs,rs) in
            (i,pa,m,c /\ c1 /\ c2)`


val word_gen_gc_partial_def = Define `
  word_gen_gc_partial conf (roots,(curr:'a word),new,len,m,dm,gs,rs) =
    let refs_end = curr + len in
    let gen_start = gs ⋙ shift (:α) in
    let (roots,i,pa,m,c1) = word_gen_gc_partial_move_roots conf
                    (roots,gen_start,new,curr,m,dm,gs,rs) in
    let (i,pa,m,c2) = word_gen_gc_partial_move_ref_list (dimword (:'a)) conf
                                 (curr+rs,i,pa,curr,m,dm,c1,gs,rs,refs_end) in
    let (i,pa,m,c3) = word_gen_gc_partial_move_data conf (dimword (:'a))
                                 (new,i,pa,curr,m,dm,gs,rs) in
      (roots,i,pa,m,c2 /\ c3)`;

val word_gen_gc_partial_full_def = Define `
  word_gen_gc_partial_full conf (roots,(curr:'a word),new,len,m,dm,gs,rs) =
    let (roots,i,pa,m,c1) = word_gen_gc_partial conf (roots,curr,new,len,m,dm,gs,rs) in
    let cpy_length = (pa - new) >>> shift(:'a) in
    let (b1,m,c2) = memcpy cpy_length new (curr + gs) m dm in
     (roots,i,b1,m,c1 /\ c2)`;

val is_ref_header_def = Define `
  is_ref_header (v:'a word) <=> ((v && 0b11100w) = 0b01000w)`;

val word_gen_gc_move_def = Define `
  (word_gen_gc_move conf (Loc l1 l2,i,pa,ib,pb,old,m,dm) =
     (Loc l1 l2,i,pa,ib,pb,m,T)) /\
  (word_gen_gc_move conf (Word w,i,pa,ib,pb,old,m,dm) =
     if (1w && w) = 0w then (Word w,i,pa,ib,pb,m,T) else
       let c = (ptr_to_addr conf old w IN dm) in
       let v = m (ptr_to_addr conf old w) in
       let c = (c /\ isWord v) in
         if is_fwd_ptr v then
           (Word (update_addr conf (theWord v >>> 2) w),i,pa,ib,pb,m,c)
         else
           let header_addr = ptr_to_addr conf old w in
           let c = (c /\ header_addr IN dm /\ isWord (m header_addr)) in
           let len = decode_length conf (theWord (m header_addr)) in
             if is_ref_header (theWord v) then
               let v = ib - (len + 1w) in
               let pb1 = pb - (len + 1w) * bytes_in_word in
               let (_,m1,c1) = memcpy (len+1w) header_addr pb1 m dm in
               let c = (c /\ header_addr IN dm /\ c1) in
               let m1 = (header_addr =+ Word (v << 2)) m1 in
                 (Word (update_addr conf v w),i,pa,v,pb1,m1,c)
             else
              let v = i + len + 1w in
              let (pa1,m1,c1) = memcpy (len+1w) header_addr pa m dm in
              let c = (c /\ header_addr IN dm /\ c1) in
              let m1 = (header_addr =+ Word (i << 2)) m1 in
                (Word (update_addr conf i w),v,pa1,ib,pb,m1,c))`

val word_gen_gc_move_roots_def = Define `
  (word_gen_gc_move_roots conf ([],i,pa,ib,pb,old,m,dm) = ([],i,pa,ib,pb,m,T)) /\
  (word_gen_gc_move_roots conf (w::ws,i,pa,ib,pb,old,m,dm) =
     let (w1,i1,pa1,ib,pb,m1,c1) = word_gen_gc_move conf (w,i,pa,ib,pb,old,m,dm) in
     let (ws2,i2,pa2,ib,pb,m2,c2) = word_gen_gc_move_roots conf (ws,i1,pa1,ib,pb,old,m1,dm) in
       (w1::ws2,i2,pa2,ib,pb,m2,c1 /\ c2))`

val word_gen_gc_move_list_def = Define `
  word_gen_gc_move_list conf (a:'a word,l:'a word,i,pa:'a word,ib,pb,old,m,dm) =
   if l = 0w then (a,i,pa,ib,pb,m,T) else
     let w = (m a):'a word_loc in
     let (w1,i1,pa1,ib,pb,m1,c1) = word_gen_gc_move conf (w,i,pa,ib,pb,old,m,dm) in
     let m1 = (a =+ w1) m1 in
     let (a2,i2,pa2,ib,pb,m2,c2) = word_gen_gc_move_list conf (a+bytes_in_word,l-1w,i1,pa1,ib,pb,old,m1,dm) in
       (a2,i2,pa2,ib,pb,m2,a IN dm /\ c1 /\ c2)`

val word_gen_gc_move_data_def = Define `
  word_gen_gc_move_data conf k
   (h2a:'a word,i,pa:'a word,ib,pb,old,m,dm) =
    if h2a = pa then (i,pa,ib,pb,m,T) else
    if k = 0n then (i,pa,ib,pb,m,F) else
      let c = (h2a IN dm) in
      let v = m h2a in
      let c = (c /\ isWord v) in
      let l = decode_length conf (theWord v) in
        if word_bit 2 (theWord v) then
          let h2a = h2a + (l + 1w) * bytes_in_word in
          let (i,pa,ib,pb,m,c2) = word_gen_gc_move_data conf (k-1)
                        (h2a,i,pa,ib,pb,old,m,dm) in
            (i,pa,ib,pb,m,c /\ c2)
        else
          let (h2a,i,pa,ib,pb,m,c1) = word_gen_gc_move_list conf
                        (h2a+bytes_in_word,l,i,pa,ib,pb,old,m,dm) in
          let (i,pa,ib,pb,m,c2) = word_gen_gc_move_data conf (k-1)
                        (h2a,i,pa,ib,pb,old,m,dm) in
            (i,pa,ib,pb,m,c /\ c1 /\ c2)`;

val word_gen_gc_move_refs_def = Define `
  word_gen_gc_move_refs conf k
   (r2a:'a word,r1a:'a word,i,pa:'a word,ib,pb,old,m:'a word -> 'a word_loc,dm) =
    if r2a = r1a then (r2a,i,pa,ib,pb,m,T) else
    if k = 0n then (r2a,i,pa,ib,pb,m,F) else
      let c = (r2a IN dm) in
      let v = m r2a in
      let c = (c /\ isWord v) in
      let l = decode_length conf (theWord v) in
      let (r2a,i,pa,ib,pb,m,c1) = word_gen_gc_move_list conf
                                    (r2a+bytes_in_word,l,i,pa,ib,pb,old,m,dm) in
      let (r2a,i,pa,ib,pb,m,c2) = word_gen_gc_move_refs conf (k-1)
                                    (r2a,r1a,i,pa,ib,pb,old,m,dm) in
        (r2a,i,pa,ib,pb,m,c /\ c1 /\ c2)`;

val word_gen_gc_move_loop_def = Define `
  word_gen_gc_move_loop conf k
   (pax:'a word,i,pa:'a word,ib,pb,pbx,old,m,dm) =
    if pbx = pb then
      if pax = pa then
        (i,pa,ib,pb,m,T)
      else
        let (i,pa,ib,pb,m,c1) = word_gen_gc_move_data conf (dimword (:'a))
                                   (pax,i,pa,ib,pb,old,m,dm) in
          if k = 0 then (i,pa,ib,pb,m,F) else
            let (i,pa,ib,pb,m,c2) = word_gen_gc_move_loop conf (k-1)
                           (pa,i,pa,ib,pb,pbx,old,m,dm) in
              (i,pa,ib,pb,m,c1 /\ c2)
      else
        let (pbx,i,pa,ib,pb',m,c1) = word_gen_gc_move_refs conf (dimword (:'a))
                                   (pb,pbx,i,pa,ib,pb,old,m,dm) in
          if k = 0n then (i,pa,ib,pb,m,F) else
            let (i,pa,ib,pb,m,c2) = word_gen_gc_move_loop conf (k-1)
                           (pax,i,pa,ib,pb',pb,old,m,dm) in
              (i,pa,ib,pb,m,c1 /\ c2)`

val word_gen_gc_def = Define `
  word_gen_gc conf (roots,curr,new,len:'a word,m,dm) =
    let new_end = new + len in
    let len = len >>> shift (:'a) in
    let (roots,i,pa,ib,pb,m,c1) = word_gen_gc_move_roots conf
                    (roots,0w,new,len,new_end,curr,m,dm) in
    let (i,pa,ib,pb,m,c2) = word_gen_gc_move_loop conf (w2n len)
                                 (new,i,pa,ib,pb,new_end,curr,m,dm) in
      (roots,i,pa,ib,pb,m,c1 /\ c2)`;

val word_gc_fun_def = Define `
  (word_gc_fun (conf:data_to_word$config)):'a gc_fun_type = \(roots,m,dm,s).
     let c1 = word_gc_fun_assum conf s in
     let new = theWord (s ' OtherHeap) in
     let old = theWord (s ' CurrHeap) in
     let len = theWord (s ' HeapLength) in
     let all_roots = s ' Globals::roots in
       case conf.gc_kind of
       | None =>
        (let s1 = s |++ [(NextFree, Word old);
                         (TriggerGC, Word old);
                         (EndOfHeap, Word old)] in
           if c1 then SOME (roots,m,s1) else NONE)
       | Simple =>
        (let (roots1,i1,pa1,m1,c2) =
           word_full_gc conf (all_roots,new,old,m,dm) in
         let s1 = s |++ [(CurrHeap, Word new);
                         (OtherHeap, Word old);
                         (NextFree, Word pa1);
                         (TriggerGC, Word (new + len));
                         (EndOfHeap, Word (new + len));
                         (Globals, HD roots1)] in
           if c1 /\ c2 then SOME (TL roots1,m1,s1) else NONE)
       | Generational gen_sizes =>
        if ~c1 then NONE else
        if word_gen_gc_can_do_partial gen_sizes s then
          (let gs = theWord (s ' GenStart) in
           let rs = theWord (s ' EndOfHeap) - theWord (s ' CurrHeap) in
           let len = theWord (s ' HeapLength) in
           let endh = theWord (s ' EndOfHeap) in
           let (roots1,i1,pa1,m1,c2) =
             word_gen_gc_partial_full conf (all_roots,old,new,len,m,dm,gs,rs) in
           let a = theWord (s ' AllocSize) in
           let s1 = s |++ [(CurrHeap, Word old);
                           (OtherHeap, Word new);
                           (NextFree, Word pa1);
                           (GenStart, Word (pa1 - old));
                           (TriggerGC, Word (pa1 + new_trig (endh - pa1) a gen_sizes));
                           (Globals, HD roots1);
                           (Temp 0w, Word 0w);
                           (Temp 1w, Word 0w)] in
           let c3 = (a <=+ endh - pa1 /\ a <=+ new_trig (endh - pa1) a gen_sizes) in
             if c2 /\ c3 then SOME (TL roots1,m1,s1) else NONE)
        else
          (let (roots1,i1,pa1,ib1,pb1,m1,c2) =
             word_gen_gc conf (all_roots,old,new,len,m,dm) in
           let a = theWord (s ' AllocSize) in
           let s1 = s |++ [(CurrHeap, Word new);
                           (OtherHeap, Word old);
                           (NextFree, Word pa1);
                           (GenStart, Word (pa1 - new));
                           (TriggerGC, Word (pa1 + new_trig (pb1 - pa1) a gen_sizes));
                           (EndOfHeap, Word pb1);
                           (Globals, HD roots1);
                           (Temp 0w, Word 0w);
                           (Temp 1w, Word 0w);
                           (Temp 2w, Word 0w);
                           (Temp 3w, Word 0w);
                           (Temp 4w, Word 0w);
                           (Temp 5w, Word 0w);
                           (Temp 6w, Word 0w)] in
             if c2 then SOME (TL roots1,m1,s1) else NONE)`

Theorem word_gc_move_roots_IMP_EVERY2:
   !xs ys pa m i c1 m1 pa1 i1 old dm c.
      word_gc_move_roots c (xs,i,pa,old,m,dm) = (ys,i1,pa1,m1,c1) ==>
      EVERY2 (\x y. (isWord x <=> isWord y) /\
                    (is_gc_word_const x ==> x = y)) xs ys
Proof
  Induct \\ full_simp_tac(srw_ss())[word_gc_move_roots_def]
  \\ full_simp_tac(srw_ss())[IMP_EQ_DISJ,word_gc_fun_def] \\ srw_tac[][]
  \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ res_tac
  \\ full_simp_tac(srw_ss())[GSYM IMP_EQ_DISJ,word_gc_fun_def] \\ srw_tac[][] \\ res_tac
  \\ qpat_x_assum `word_gc_move c (h,i,pa,old,m,dm) = (w1,i1',pa1',m1',c1')` mp_tac
  \\ full_simp_tac(srw_ss())[] \\ Cases_on `h` \\ full_simp_tac(srw_ss())[word_gc_move_def] \\ srw_tac[][]
  \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[isWord_def]
  \\ UNABBREV_ALL_TAC \\ srw_tac[][] \\ pop_assum mp_tac \\ full_simp_tac(srw_ss())[]
  \\ srw_tac[][] \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ fs[isWord_def,word_simpProofTheory.is_gc_word_const_def,
        word_simpTheory.is_gc_const_def]
QED

Theorem word_gen_gc_move_roots_IMP_EVERY2:
   !xs ys pa m i ib pb c1 m1 pa1 i1 ib1 pb1 old dm c.
      word_gen_gc_move_roots c (xs,i,pa,ib,pb,old,m,dm) =
         (ys,i1,pa1,ib1,pb1,m1,c1) ==>
      EVERY2 (\x y. (isWord x <=> isWord y) /\
                    (is_gc_word_const x ==> x = y)) xs ys
Proof
  Induct \\ full_simp_tac(srw_ss())[word_gen_gc_move_roots_def]
  \\ full_simp_tac(srw_ss())[IMP_EQ_DISJ] \\ srw_tac[][]
  \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ res_tac
  \\ full_simp_tac(srw_ss())[GSYM IMP_EQ_DISJ] \\ srw_tac[][] \\ res_tac
  \\ qpat_x_assum `word_gen_gc_move c _ = _` mp_tac
  \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `h` \\ full_simp_tac(srw_ss())[word_gen_gc_move_def] \\ srw_tac[][]
  \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[isWord_def]
  \\ UNABBREV_ALL_TAC \\ srw_tac[][] \\ pop_assum mp_tac \\ full_simp_tac(srw_ss())[]
  \\ srw_tac[][] \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ fs[isWord_def,word_simpProofTheory.is_gc_word_const_def,
        word_simpTheory.is_gc_const_def]
QED

Theorem word_gen_gc_partial_move_roots_IMP_EVERY2:
   !xs ys pa m i gs rs c1 m1 pa1 i1 old dm c.
      word_gen_gc_partial_move_roots c (xs,i,pa,old,m,dm,gs,rs) =
         (ys,i1,pa1,m1,c1) ==>
      EVERY2 (\x y. (isWord x <=> isWord y) /\
                    (is_gc_word_const x ==> x = y)) xs ys
Proof
  Induct \\ full_simp_tac(srw_ss())[word_gen_gc_partial_move_roots_def]
  \\ full_simp_tac(srw_ss())[IMP_EQ_DISJ] \\ srw_tac[][]
  \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ res_tac
  \\ full_simp_tac(srw_ss())[GSYM IMP_EQ_DISJ] \\ srw_tac[][] \\ res_tac
  \\ qpat_x_assum `word_gen_gc_partial_move c _ = _` mp_tac
  \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `h` \\ full_simp_tac(srw_ss())[word_gen_gc_partial_move_def]
  \\ srw_tac[][]
  \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[isWord_def]
  \\ UNABBREV_ALL_TAC \\ srw_tac[][] \\ pop_assum mp_tac \\ full_simp_tac(srw_ss())[]
  \\ srw_tac[][] \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ fs[isWord_def,word_simpProofTheory.is_gc_word_const_def,
        word_simpTheory.is_gc_const_def]
QED

Theorem word_gc_IMP_EVERY2:
   word_gc_fun c (xs,m,dm,st) = SOME (ys,m1,s1) ==>
    EVERY2 (\x y. (isWord x <=> isWord y) /\ (is_gc_word_const x ==> x = y)) xs ys
Proof
  full_simp_tac(srw_ss())[word_gc_fun_def,LET_THM,word_gc_fun_def,
         word_full_gc_def,word_gen_gc_def,word_gen_gc_partial_def,
         word_gen_gc_partial_full_def]
  \\ TOP_CASE_TAC \\ fs []
  \\ rpt (pairarg_tac \\ full_simp_tac(srw_ss())[])
  \\ TRY TOP_CASE_TAC \\ fs []
  \\ rpt (pairarg_tac \\ full_simp_tac(srw_ss())[])
  \\ strip_tac \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[word_gc_move_roots_def,
       word_gen_gc_move_roots_def,word_gen_gc_partial_move_roots_def,LET_THM]
  \\ rpt (pairarg_tac \\ full_simp_tac(srw_ss())[])
  \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  THEN1 (match_mp_tac EVERY2_refl \\ fs [])
  \\ imp_res_tac word_gc_move_roots_IMP_EVERY2
  \\ imp_res_tac word_gen_gc_move_roots_IMP_EVERY2
  \\ imp_res_tac word_gen_gc_partial_move_roots_IMP_EVERY2
  \\ Cases_on `roots` \\ fs []
QED

Theorem word_gc_fun_LENGTH:
   word_gc_fun c (xs,m,dm,s) = SOME (zs,m1,s1) ==> LENGTH xs = LENGTH zs
Proof
  srw_tac[][] \\ drule word_gc_IMP_EVERY2
  \\ srw_tac[][] \\ imp_res_tac EVERY2_LENGTH
QED

(* lemmas about has_fp_ops *)
Theorem word_gc_fun_assum_has_fp_ops[simp]:
   word_gc_fun_assum (conf with <| has_fp_ops := b1; has_fp_tern := b2 |>) s =
    word_gc_fun_assum conf s
Proof
  EVAL_TAC \\ fs []
QED

Theorem word_gc_move_has_fp_ops[simp]:
   !x. word_gc_move (conf with <| has_fp_ops := b1; has_fp_tern := b2 |>) x =
        word_gc_move conf x
Proof
  simp_tac std_ss [FORALL_PROD] \\ Cases
  \\ simp_tac std_ss [FORALL_PROD,word_gc_move_def]
  \\ fs [ptr_to_addr_def,update_addr_def,small_shift_length_def,decode_length_def]
QED

Theorem word_gen_gc_move_has_fp_ops[simp]:
   !x. word_gen_gc_move (conf with <| has_fp_ops := b1; has_fp_tern := b2 |>) x =
        word_gen_gc_move conf x
Proof
  simp_tac std_ss [FORALL_PROD] \\ Cases
  \\ simp_tac std_ss [FORALL_PROD,word_gen_gc_move_def]
  \\ fs [ptr_to_addr_def,update_addr_def,small_shift_length_def,decode_length_def]
QED

Theorem word_gen_gc_partial_move_has_fp_ops[simp]:
   !x. word_gen_gc_partial_move (conf with <| has_fp_ops := b1; has_fp_tern := b2 |>) x =
        word_gen_gc_partial_move conf x
Proof
  simp_tac std_ss [FORALL_PROD] \\ Cases
  \\ simp_tac std_ss [FORALL_PROD,word_gen_gc_partial_move_def]
  \\ fs [ptr_to_addr_def,update_addr_def,small_shift_length_def,decode_length_def]
QED

Theorem word_gc_move_list_has_fp_ops[simp]:
   !conf x. word_gc_move_list (conf with <| has_fp_ops := b1; has_fp_tern := b2 |>) x =
             word_gc_move_list conf x
Proof
  simp_tac std_ss [FORALL_PROD]
  \\ recInduct (fetch "-" "word_gc_move_list_ind")
  \\ rw [] \\ once_rewrite_tac [word_gc_move_list_def] \\ rw []
  \\ rpt (pairarg_tac \\ fs [])
QED

Theorem word_gen_gc_move_list_has_fp_ops[simp]:
   !conf x. word_gen_gc_move_list (conf with <| has_fp_ops := b1; has_fp_tern := b2 |>) x =
             word_gen_gc_move_list conf x
Proof
  simp_tac std_ss [FORALL_PROD]
  \\ recInduct (fetch "-" "word_gen_gc_move_list_ind")
  \\ rw [] \\ once_rewrite_tac [word_gen_gc_move_list_def] \\ rw []
  \\ rpt (pairarg_tac \\ fs [])
QED

Theorem word_gen_gc_partial_move_list_has_fp_ops[simp]:
   !conf x. word_gen_gc_partial_move_list (conf with <| has_fp_ops := b1; has_fp_tern := b2 |>) x =
             word_gen_gc_partial_move_list conf x
Proof
  simp_tac std_ss [FORALL_PROD]
  \\ recInduct (fetch "-" "word_gen_gc_partial_move_list_ind")
  \\ rw [] \\ once_rewrite_tac [word_gen_gc_partial_move_list_def] \\ rw []
  \\ rpt (pairarg_tac \\ fs [])
QED

Theorem word_gc_move_roots_has_fp_ops[simp]:
   !conf x. word_gc_move_roots (conf with <| has_fp_ops := b1; has_fp_tern := b2 |>) x =
             word_gc_move_roots conf x
Proof
  simp_tac std_ss [FORALL_PROD]
  \\ recInduct (fetch "-" "word_gc_move_roots_ind")
  \\ rw [] \\ once_rewrite_tac [word_gc_move_roots_def] \\ rw []
  \\ rpt (pairarg_tac \\ fs [])
QED

Theorem word_gen_gc_move_roots_has_fp_ops[simp]:
   !conf x. word_gen_gc_move_roots (conf with <| has_fp_ops := b1; has_fp_tern := b2 |>) x =
             word_gen_gc_move_roots conf x
Proof
  simp_tac std_ss [FORALL_PROD]
  \\ recInduct (fetch "-" "word_gen_gc_move_roots_ind")
  \\ rw [] \\ once_rewrite_tac [word_gen_gc_move_roots_def] \\ rw []
  \\ rpt (pairarg_tac \\ fs [])
QED

Theorem word_gen_gc_partial_move_roots_has_fp_ops[simp]:
   !conf x. word_gen_gc_partial_move_roots (conf with <| has_fp_ops := b1; has_fp_tern := b2 |>) x =
             word_gen_gc_partial_move_roots conf x
Proof
  simp_tac std_ss [FORALL_PROD]
  \\ recInduct (fetch "-" "word_gen_gc_partial_move_roots_ind")
  \\ rw [] \\ once_rewrite_tac [word_gen_gc_partial_move_roots_def] \\ rw []
  \\ rpt (pairarg_tac \\ fs [])
QED

Theorem word_gc_move_loop_has_fp_ops[simp]:
   !n conf x. word_gc_move_loop n (conf with <| has_fp_ops := b1; has_fp_tern := b2 |>) x =
               word_gc_move_loop n conf x
Proof
  simp_tac std_ss [FORALL_PROD]
  \\ Induct \\ rw []
  \\ once_rewrite_tac [word_gc_move_loop_def] \\ fs []
  \\ fs [ptr_to_addr_def,update_addr_def,small_shift_length_def,decode_length_def]
QED

Theorem word_gen_gc_partial_move_data_has_fp_ops[simp]:
   !n conf x. word_gen_gc_partial_move_data (conf with <| has_fp_ops := b1; has_fp_tern := b2 |>) n x =
               word_gen_gc_partial_move_data conf n x
Proof
  simp_tac std_ss [FORALL_PROD]
  \\ Induct \\ rw []
  \\ once_rewrite_tac [word_gen_gc_partial_move_data_def] \\ fs []
  \\ fs [ptr_to_addr_def,update_addr_def,small_shift_length_def,decode_length_def]
QED

Theorem word_gen_gc_move_data_has_fp_ops[simp]:
   !n conf x. word_gen_gc_move_data (conf with <| has_fp_ops := b1; has_fp_tern := b2 |>) n x =
               word_gen_gc_move_data conf n x
Proof
  simp_tac std_ss [FORALL_PROD]
  \\ Induct \\ rw []
  \\ once_rewrite_tac [word_gen_gc_move_data_def] \\ fs []
  \\ fs [ptr_to_addr_def,update_addr_def,small_shift_length_def,decode_length_def]
QED

Theorem word_gen_gc_move_refs_has_fp_ops[simp]:
   !n conf x. word_gen_gc_move_refs (conf with <| has_fp_ops := b1; has_fp_tern := b2 |>) n x =
               word_gen_gc_move_refs conf n x
Proof
  simp_tac std_ss [FORALL_PROD]
  \\ Induct \\ rw []
  \\ once_rewrite_tac [word_gen_gc_move_refs_def] \\ fs []
  \\ fs [ptr_to_addr_def,update_addr_def,small_shift_length_def,decode_length_def]
QED

Theorem word_gen_gc_partial_move_ref_list_has_fp_ops[simp]:
   !n conf x. word_gen_gc_partial_move_ref_list n (conf with <| has_fp_ops := b1; has_fp_tern := b2 |>) x =
               word_gen_gc_partial_move_ref_list n conf x
Proof
  simp_tac std_ss [FORALL_PROD]
  \\ Induct \\ rw []
  \\ once_rewrite_tac [word_gen_gc_partial_move_ref_list_def] \\ fs []
  \\ fs [ptr_to_addr_def,update_addr_def,small_shift_length_def,decode_length_def]
QED

Theorem word_gen_gc_move_loop_has_fp_ops[simp]:
   !n conf x. word_gen_gc_move_loop (conf with <| has_fp_ops := b1; has_fp_tern := b2 |>) n x =
               word_gen_gc_move_loop conf n x
Proof
  simp_tac std_ss [FORALL_PROD]
  \\ Induct \\ rw []
  \\ once_rewrite_tac [word_gen_gc_move_loop_def] \\ fs []
  \\ fs [ptr_to_addr_def,update_addr_def,small_shift_length_def,decode_length_def]
QED

Theorem word_full_gc_has_fp_ops[simp]:
   !x. word_full_gc (conf with <| has_fp_ops := b1; has_fp_tern := b2 |>) x =
        word_full_gc conf x
Proof
  simp_tac std_ss [FORALL_PROD]
  \\ rewrite_tac [word_full_gc_def] \\ fs []
QED

Theorem word_gen_gc_partial_full_has_fp_ops[simp]:
   !x. word_gen_gc_partial_full (conf with <| has_fp_ops := b1; has_fp_tern := b2 |>) x =
        word_gen_gc_partial_full conf x
Proof
  simp_tac std_ss [FORALL_PROD]
  \\ rewrite_tac [word_gen_gc_partial_full_def]
  \\ fs [word_gen_gc_partial_def]
QED

Theorem word_gen_gc_has_fp_ops[simp]:
   !x. word_gen_gc (conf with <| has_fp_ops := b1; has_fp_tern := b2 |>) x =
        word_gen_gc conf x
Proof
  simp_tac std_ss [FORALL_PROD]
  \\ rewrite_tac [word_gen_gc_def]
  \\ fs [word_gen_gc_partial_def]
QED

Theorem word_gc_fun_has_fp_ops[simp]:
   word_gc_fun (conf with <| has_fp_ops := b1; has_fp_tern := b2 |>) = word_gc_fun conf
Proof
  fs [word_gc_fun_def,FUN_EQ_THM,FORALL_PROD]
  \\ Cases_on `conf.gc_kind` \\ fs []
QED

val _ = export_theory();
