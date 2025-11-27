(*
  A module about hash tables for the CakeML standard basis library.
*)
Theory HashtableProg
Ancestors
  SetProg
Libs
  preamble ml_translatorLib ml_progLib basisFunctionsLib

val _ = translation_extends "SetProg"

val () = ml_prog_update(open_module "Hashtable");

(*Local structure:
  local
    hashtable                     -- Hidden
  in
    delete
    lookup
    toAscList
    size
    local
      initBuckets                 -- Hidden
    in
      empty
      clear
      local
        staticInsert              -- Hidden
      in
        local
          doubleCapacity          -- Hidden
        in
          local
            load_treshold_den     -- Hidden
          in
            local
              load_treshold_num   -- Hidden
            in
              insert
*)


val _ = ml_prog_update open_local_block;

Quote add_cakeml:
  datatype ('k, 'v) hashtable =
  Hashtable
    (int ref) (*Element counter*)
    ((('k,'v) Map.map) array ref) (*Buckets*)
    ('k -> int) (*Hash function*)
    ('k -> 'k -> ordering) (*Key compare function*)
End

val hashtable_ty_env = get_env (get_ml_prog_state());
val stamp_eval = EVAL ``nsLookup (^hashtable_ty_env).c (Short "Hashtable")``
val hashtable_con_stamp = rhs (concl stamp_eval)

Definition hashtable_con_stamp_def:
  hashtable_con_stamp = OPTION_MAP SND ^hashtable_con_stamp
End

val _ = ml_prog_update open_local_in_block;

(* provides the Hashtable.hashtable name for the hashtable type *)
val _ = ml_prog_update (add_dec
  ``Dtabbrev unknown_loc ["'a";"'b"] "hashtable" (Atapp [Atvar "'a"; Atvar "'b"] (Short "hashtable"))`` I);

Quote add_cakeml:
  fun delete ht k =
    case ht of Hashtable usedRef bucketsRef hf _ =>
      let
        val buckets = !bucketsRef
        val index = (hf k) mod (Array.length buckets)
        val bucket = Array.sub buckets index
        val newBucket = Map.delete bucket k
      in
        Array.update buckets index newBucket;
        if not (Map.null bucket) andalso Map.null newBucket
              andalso (0 < (!usedRef)) then (
          usedRef := (!usedRef)-1 )
        else
          ()
      end
End

Quote add_cakeml:
  fun lookup ht k =
    case ht of Hashtable usedRef bucketsRef hf cmp =>
      let
        val buckets = !bucketsRef
        val bucket = Array.sub buckets ((hf k) mod (Array.length buckets))
      in
        Map.lookup bucket k
    end
End

Quote add_cakeml:
  fun toAscList ht =
    case ht of Hashtable _ bucketsRef _ cmp =>
      Map.toAscList (Array.foldr Map.union (Map.empty cmp) (!bucketsRef))
End

Quote add_cakeml:
  fun size ht =
    case ht of Hashtable usedRef bucketsRef hf cmp =>
      !usedRef
End

val _ = ml_prog_update open_local_block;

Quote add_cakeml:
  fun initBuckets n cmp = Array.array n (Map.empty cmp)
End

val _ = ml_prog_update open_local_in_block;

Quote add_cakeml:
  fun empty size hf cmp =
    ( Hashtable
      (Ref 0)
      (Ref (initBuckets (if size < 1 then 1 else size) cmp))
      hf
      cmp
    )
End

Quote add_cakeml:
  fun clear ht =
    case ht of Hashtable usedRef bucketsRef _ cmp =>
      (bucketsRef := initBuckets (Array.length (!bucketsRef)) cmp;
      usedRef := (!usedRef)*0)
End

val _ = ml_prog_update open_local_block;

Quote add_cakeml:
  fun staticInsert ht k v =
    case ht of Hashtable usedRef bucketsRef hf cmp =>
      let
        val buckets = !bucketsRef
        val index = (hf k) mod (Array.length buckets)
        val bucket = Array.sub buckets index
      in
        Array.update buckets index (Map.insert bucket k v);
        if Map.null bucket then (
          usedRef := (!usedRef)+1 )
        else
          ()
      end
End

val _ = ml_prog_update open_local_in_block;
val _ = ml_prog_update open_local_block;

Quote add_cakeml:
  fun insertList ht l = List.app (fn (k,v) => staticInsert ht k v) l
End

Quote add_cakeml:
  fun doubleCapacity ht =
    case ht of Hashtable usedRef bucketsRef _ cmp =>
      let
        val oldArr = !bucketsRef
        val newLen = Array.length oldArr * 2
        val oldList = toAscList ht
      in
        usedRef := 0;
        bucketsRef := initBuckets newLen cmp;
        insertList ht oldList
      end
End

val _ = ml_prog_update open_local_in_block;

(*Load treshold values for insert function, default 3/4*)
Quote add_cakeml:
  fun insert ht k v =
    case ht of Hashtable usedRef bucketsRef _ _ =>
      if (4*(!usedRef))<(3* (Array.length (!bucketsRef)))
      then staticInsert ht k v
      else (doubleCapacity ht; staticInsert ht k v)
End

val _ = ml_prog_update close_local_blocks;

val _ = ml_prog_update (close_module NONE);

