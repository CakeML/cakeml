(*
  A module about hash tables for the CakeML standard basis library.
*)
open preamble
     ml_translatorLib ml_progLib basisFunctionsLib
     MapProgTheory

val _ = new_theory "HashtableProg"
val _ = translation_extends "MapProg"
val () = ml_prog_update(open_module "Hashtable");

(* provides the Hashtable.hashtable name for the hashtable type *)
val _ = ml_prog_update (add_dec
  ``Dtabbrev unknown_loc ["'a";"'b"] "hashtable" (Atapp [Atvar "'a"; Atvar "'b"] (Short "hashtable"))`` I);

val _ = translate (Define `val load_treshold_den = 3`)
val _ = translate (Define `val load_treshold_num = 4`)

val hashtable_hashtable = process_topdecs
`datatype ('k, 'v) hashtable =
  Hashtable (
    int ref * (*Element counter*)
    (('k,'v) Map.map) array ref * (*Buckets*)
    ('k -> int) *(*Hash function*)
    ('k -> 'k -> ordering) (*Key compare function*))`

val _ = append_prog hashtable_hashtable;

val hashtable_initBuckets = process_topdecs
`fun initBuckets n cmp = Array.tabulate n (fn _ => Map.empty cmp)`;

val _ = append_prog hashtable_initBuckets;

val hashtable_empty = process_topdecs
`fun empty size hf cmp =
  Hashtable(
    Ref 0,
    Ref (initBuckets (if size < 1 then 1 else size) cmp),
    hf,
    cmp
  )`;

val _ = append_prog hashtable_empty;

val hashtable_test = process_topdecs
`fun test () = empty 5 (fn x => x) (fn x => (fn y => Equal))`;

val _ = append_prog hashtable_test;

val hashtable_staticInsert = process_topdecs
`fun staticInsert ht k v =
  case ht of Hashtable(usedRef,bucketsRef,hf,cmp) =>
    let
      val index = (hf k) mod (Array.length (!bucketsRef))
      val bucket = Array.sub (!bucketsRef) index
    in
      case Map.lookup bucket k of
        None => (usedRef := (!usedRef)+1;
                Array.update (!bucketsRef) index (Map.insert bucket k v))
        |Some _ => Array.update (!bucketsRef) index (Map.insert bucket k v)
    end`;

val _ = append_prog hashtable_staticInsert;

val hashtable_clear = process_topdecs
`fun clear ht =
 case ht of Hashtable(usedRef,bucketsRef,_,cmp) =>
  (bucketsRef := initBuckets (Array.length (!bucketsRef)) cmp;
  usedRef := 0)`;

val _ = append_prog hashtable_clear;

val hashtable_doubleCapacity = process_topdecs
`fun doubleCapacity ht =
 case ht of Hashtable(usedRef,bucketsRef,_,cmp) =>
  let
    val oldArr = !bucketsRef
  in
    usedRef := 0;
    bucketsRef := initBuckets (Array.length oldArr * 2) cmp;
    Array.app (fn b=>List.app (fn (k,v) => staticInsert ht k v) (Map.toAscList b)) (oldArr)
  end`;

val _ = append_prog hashtable_doubleCapacity;

val hashtable_insert = process_topdecs
`fun insert ht k v =
 case ht of Hashtable(usedRef,bucketsRef,_,_) =>
  if (load_treshold_num*(!usedRef))<(load_treshold_den * (Array.length (!bucketsRef)))
  then staticInsert ht k v
  else (doubleCapacity ht; staticInsert ht k v)`;

val _ = append_prog hashtable_insert;

val hashtable_lookup = process_topdecs
`fun lookup ht k =
 case ht of Hashtable(usedRef,bucketsRef,hf,cmp) =>
  let
    val bucket = Array.sub (!bucketsRef) ((hf k) mod (Array.length (!bucketsRef)))
  in
    Map.lookup bucket k
  end`;

val _ = append_prog hashtable_lookup;

val hashtable_delete = process_topdecs
`fun delete ht k =
 case ht of Hashtable(usedRef,bucketsRef,hf,_) =>
  let
    val index = (hf k) mod (Array.length (!bucketsRef))
    val bucket = Array.sub (!bucketsRef) index
  in
    case bucket Map.map k of
      Some _ => (usedRef:=(!usedRef)-1; Array.update (!bucketsRef) index (Map.delete Map.map k))
      |None => ()
  end`;

val _ = append_prog hashtable_delete;

val hashtable_toAscList = process_topdecs
`fun toAscList ht =
 case ht of Hashtable(_,bucketsRef,_,cmp) =>
  Map.toAscList (Array.foldr Map.union (Map.empty cmp) (!bucketsRef))`;


val _ = append_prog hashtable_toAscList;


val hashtable_size = process_topdecs
`fun size ht =
 case ht of Hashtable(usedRef,bucketsRef,hf,cmp) =>
  !usedRef`;

val _ = append_prog hashtable_size;


val _ = ml_prog_update close_local_blocks;

val _ = ml_prog_update (close_module NONE);

val _ = export_theory ()