(*
  Specifications of the witnessed small-integer operations of Unsafe.Arith
  at the types the checkers use: nums, and ints bounded by a witness
*)
Theory ccnf_arith
Ancestors
  semanticPrimitives ml_translator UnsafeProof
Libs
  preamble basis

(* An array of nums, used for the assignment map *)
Definition NUM_ARRAY_def:
  NUM_ARRAY av ls = SEP_EXISTS vs. ARRAY av vs * &LIST_REL NUM ls vs
End

Theorem NUM_ARRAY_refl:
  (NUM_ARRAY av ls ==>> NUM_ARRAY av ls) ∧
  (NUM_ARRAY av ls ==>> NUM_ARRAY av ls * GC)
Proof
  xsimpl
QED

Theorem index_witness_num_array:
  index_witness_heap p (NUM_ARRAY av ls) av (256 * LENGTH ls)
Proof
  rw[index_witness_heap_def,NUM_ARRAY_def,SEP_EXISTS_THM,cond_STAR]>>
  imp_res_tac LIST_REL_LENGTH>>
  `index_witness_heap p (ARRAY av vs) av (256 * LENGTH vs)`
    by simp[index_witness_array]>>
  gvs[index_witness_heap_def]>>
  metis_tac[]
QED

Theorem index_in_bounds_num[simp]:
  (index_in_bounds (SOME l) (&n) ⇔ n ≤ l) ∧
  (index_in_bounds NONE (&n) ⇔ n < 2 ** 30)
Proof
  rw[index_in_bounds_def]>>
  intLib.ARITH_TAC
QED

Theorem index_in_bounds_int[simp]:
  (index_in_bounds (SOME l) i ⇔ Num (ABS i) ≤ l) ∧
  (index_in_bounds NONE i ⇔ -(2 ** 30) ≤ i ∧ i < 2 ** 30)
Proof
  rw[index_in_bounds_def]>>
  intLib.ARITH_TAC
QED

(*** Vector witness ***)

Theorem num_sub_vec_spec:
  ∀i iv j jv a xs w p.
  NUM i iv ∧ NUM j jv ∧ VECTOR_TYPE a xs w ∧
  j ≤ i ∧ i ≤ 256 * length xs ⇒
  app p Unsafe_subWitness_v [iv; jv; w] emp (POSTv v. &NUM (i - j) v)
Proof
  rw[NUM_def]>>
  `(&(i − j)):int = &i − &j` by simp[integerTheory.INT_SUB]>>
  pop_assum SUBST1_TAC>>
  irule unsafe_arith_sub_vector_spec>>
  first_assum (irule_at Any)>>
  simp[integerTheory.INT_SUB]
QED

(*** Witness: the assignment map ***)

Theorem int_lt_numarr_spec:
  ∀x xv y yv ls av p.
  INT x xv ∧ INT y yv ∧
  Num (ABS x) ≤ 256 * LENGTH ls ∧ Num (ABS y) ≤ 256 * LENGTH ls ⇒
  app p Unsafe_ltWitness_v [xv; yv; av] (NUM_ARRAY av ls)
    (POSTv v. &BOOL (x < y) v * NUM_ARRAY av ls)
Proof
  rw[]>>
  irule unsafe_arith_lt_witness_spec>>
  irule_at Any index_witness_num_array>>
  simp[]
QED

Theorem int_gt_numarr_spec:
  ∀x xv y yv ls av p.
  INT x xv ∧ INT y yv ∧
  Num (ABS x) ≤ 256 * LENGTH ls ∧ Num (ABS y) ≤ 256 * LENGTH ls ⇒
  app p Unsafe_gtWitness_v [xv; yv; av] (NUM_ARRAY av ls)
    (POSTv v. &BOOL (x > y) v * NUM_ARRAY av ls)
Proof
  rw[]>>
  irule unsafe_arith_gt_witness_spec>>
  irule_at Any index_witness_num_array>>
  simp[]
QED

Theorem int_eq_numarr_spec:
  ∀x xv y yv ls av p.
  INT x xv ∧ INT y yv ∧
  Num (ABS x) ≤ 256 * LENGTH ls ∧ Num (ABS y) ≤ 256 * LENGTH ls ⇒
  app p Unsafe_eqWitness_v [xv; yv; av] (NUM_ARRAY av ls)
    (POSTv v. &BOOL (x = y) v * NUM_ARRAY av ls)
Proof
  rw[]>>
  irule unsafe_arith_eq_witness_spec>>
  irule_at Any index_witness_num_array>>
  simp[]
QED

Theorem int_sub_numarr_spec:
  ∀x xv y yv ls av p.
  INT x xv ∧ INT y yv ∧
  Num (ABS x) ≤ 256 * LENGTH ls ∧ Num (ABS y) ≤ 256 * LENGTH ls ∧
  Num (ABS (x - y)) ≤ 256 * LENGTH ls ⇒
  app p Unsafe_subWitness_v [xv; yv; av] (NUM_ARRAY av ls)
    (POSTv v. &INT (x - y) v * NUM_ARRAY av ls)
Proof
  rw[]>>
  irule unsafe_arith_sub_witness_spec>>
  irule_at Any index_witness_num_array>>
  simp[]
QED

(*** Array witness ***)

Theorem num_sub_arr_spec:
  ∀i iv j jv xs av p.
  NUM i iv ∧ NUM j jv ∧
  j ≤ i ∧ i ≤ 256 * LENGTH xs ⇒
  app p Unsafe_subWitness_v [iv; jv; av] (ARRAY av xs)
    (POSTv v. &NUM (i - j) v * ARRAY av xs)
Proof
  rw[NUM_def]>>
  `(&(i − j)):int = &i − &j` by simp[integerTheory.INT_SUB]>>
  pop_assum SUBST1_TAC>>
  irule unsafe_arith_sub_array_spec>>
  simp[integerTheory.INT_SUB]
QED

Theorem num_add_arr_spec:
  ∀i iv j jv xs av p.
  NUM i iv ∧ NUM j jv ∧
  i + j ≤ 256 * LENGTH xs ⇒
  app p Unsafe_addWitness_v [iv; jv; av] (ARRAY av xs)
    (POSTv v. &NUM (i + j) v * ARRAY av xs)
Proof
  rw[NUM_def]>>
  `(&(i + j)):int = &i + &j` by simp[integerTheory.INT_ADD]>>
  pop_assum SUBST1_TAC>>
  irule unsafe_arith_add_array_spec>>
  simp[integerTheory.INT_ADD]
QED

Theorem num_gt_arr_spec:
  ∀i iv j jv xs av p.
  NUM i iv ∧ NUM j jv ∧
  i ≤ 256 * LENGTH xs ∧ j ≤ 256 * LENGTH xs ⇒
  app p Unsafe_gtWitness_v [iv; jv; av] (ARRAY av xs)
    (POSTv v. &BOOL (i > j) v * ARRAY av xs)
Proof
  rw[NUM_def]>>
  `i > j ⇔ (&i:int) > &j` by intLib.ARITH_TAC>>
  pop_assum SUBST1_TAC>>
  irule unsafe_arith_gt_array_spec>>
  simp[]
QED

Theorem int_lt_arr_spec:
  ∀x xv y yv xs av p.
  INT x xv ∧ INT y yv ∧
  Num (ABS x) ≤ 256 * LENGTH xs ∧ Num (ABS y) ≤ 256 * LENGTH xs ⇒
  app p Unsafe_ltWitness_v [xv; yv; av] (ARRAY av xs)
    (POSTv v. &BOOL (x < y) v * ARRAY av xs)
Proof
  rw[]>>
  irule unsafe_arith_lt_array_spec>>
  simp[]
QED

Theorem int_gt_arr_spec:
  ∀x xv y yv xs av p.
  INT x xv ∧ INT y yv ∧
  Num (ABS x) ≤ 256 * LENGTH xs ∧ Num (ABS y) ≤ 256 * LENGTH xs ⇒
  app p Unsafe_gtWitness_v [xv; yv; av] (ARRAY av xs)
    (POSTv v. &BOOL (x > y) v * ARRAY av xs)
Proof
  rw[]>>
  irule unsafe_arith_gt_array_spec>>
  simp[]
QED

(*** Byte-array witness ***)

Theorem num_add_w8_spec:
  ∀i iv j jv cs av p.
  NUM i iv ∧ NUM j jv ∧
  i + j ≤ 32 * LENGTH cs ⇒
  app p Unsafe_addWitness_v [iv; jv; av] (W8ARRAY av cs)
    (POSTv v. &NUM (i + j) v * W8ARRAY av cs)
Proof
  rw[NUM_def]>>
  `(&(i + j)):int = &i + &j` by simp[integerTheory.INT_ADD]>>
  pop_assum SUBST1_TAC>>
  irule unsafe_arith_add_w8array_spec>>
  simp[integerTheory.INT_ADD]
QED

Theorem num_sub_w8_spec:
  ∀i iv j jv cs av p.
  NUM i iv ∧ NUM j jv ∧
  j ≤ i ∧ i ≤ 32 * LENGTH cs ⇒
  app p Unsafe_subWitness_v [iv; jv; av] (W8ARRAY av cs)
    (POSTv v. &NUM (i - j) v * W8ARRAY av cs)
Proof
  rw[NUM_def]>>
  `(&(i − j)):int = &i − &j` by simp[integerTheory.INT_SUB]>>
  pop_assum SUBST1_TAC>>
  irule unsafe_arith_sub_w8array_spec>>
  simp[integerTheory.INT_SUB]
QED

Theorem num_mul_w8_spec:
  ∀i iv j jv cs av p.
  NUM i iv ∧ NUM j jv ∧
  i ≤ 32 * LENGTH cs ∧ j ≤ 32 * LENGTH cs ∧ i * j ≤ 32 * LENGTH cs ⇒
  app p Unsafe_mulWitness_v [iv; jv; av] (W8ARRAY av cs)
    (POSTv v. &NUM (i * j) v * W8ARRAY av cs)
Proof
  rw[NUM_def]>>
  `(&(i * j)):int = &i * &j` by simp[integerTheory.INT_MUL]>>
  pop_assum SUBST1_TAC>>
  irule unsafe_arith_mul_w8array_spec>>
  simp[integerTheory.INT_MUL]
QED

Theorem num_ge_w8_spec:
  ∀i iv j jv cs av p.
  NUM i iv ∧ NUM j jv ∧
  i ≤ 32 * LENGTH cs ∧ j ≤ 32 * LENGTH cs ⇒
  app p Unsafe_geWitness_v [iv; jv; av] (W8ARRAY av cs)
    (POSTv v. &BOOL (i ≥ j) v * W8ARRAY av cs)
Proof
  rw[NUM_def]>>
  `i ≥ j ⇔ (&i:int) ≥ &j` by intLib.ARITH_TAC>>
  pop_assum SUBST1_TAC>>
  irule unsafe_arith_ge_w8array_spec>>
  simp[]
QED

Theorem int_gt_w8_spec:
  ∀x xv y yv cs av p.
  INT x xv ∧ INT y yv ∧
  Num (ABS x) ≤ 32 * LENGTH cs ∧ Num (ABS y) ≤ 32 * LENGTH cs ⇒
  app p Unsafe_gtWitness_v [xv; yv; av] (W8ARRAY av cs)
    (POSTv v. &BOOL (x > y) v * W8ARRAY av cs)
Proof
  rw[]>>
  irule unsafe_arith_gt_w8array_spec>>
  simp[]
QED

(*** No witness: bounded by 2 ** 30 ***)

Theorem num_add_spec:
  ∀i iv j jv p.
  NUM i iv ∧ NUM j jv ∧ i + j < 2 ** 30 ⇒
  app p Unsafe_plus_v [iv; jv] emp (POSTv v. &NUM (i + j) v)
Proof
  rw[NUM_def]>>
  `(&(i + j)):int = &i + &j` by simp[integerTheory.INT_ADD]>>
  pop_assum SUBST1_TAC>>
  irule unsafe_arith_add_spec>>
  simp[integerTheory.INT_ADD]
QED

Theorem num_mul_spec:
  ∀i iv j jv p.
  NUM i iv ∧ NUM j jv ∧ i < 2 ** 30 ∧ j < 2 ** 30 ∧ i * j < 2 ** 30 ⇒
  app p Unsafe_times_v [iv; jv] emp (POSTv v. &NUM (i * j) v)
Proof
  rw[NUM_def]>>
  `(&(i * j)):int = &i * &j` by simp[integerTheory.INT_MUL]>>
  pop_assum SUBST1_TAC>>
  irule unsafe_arith_mul_spec>>
  simp[integerTheory.INT_MUL]
QED

Theorem num_lt_spec:
  ∀i iv j jv p.
  NUM i iv ∧ NUM j jv ∧ i < 2 ** 30 ∧ j < 2 ** 30 ⇒
  app p Unsafe_lt_v [iv; jv] emp (POSTv v. &BOOL (i < j) v)
Proof
  rw[NUM_def]>>
  `i < j ⇔ (&i:int) < &j` by intLib.ARITH_TAC>>
  pop_assum SUBST1_TAC>>
  irule unsafe_arith_lt_spec>>
  simp[]
QED

Theorem num_le_spec:
  ∀i iv j jv p.
  NUM i iv ∧ NUM j jv ∧ i < 2 ** 30 ∧ j < 2 ** 30 ⇒
  app p Unsafe_le_v [iv; jv] emp (POSTv v. &BOOL (i ≤ j) v)
Proof
  rw[NUM_def]>>
  `i ≤ j ⇔ (&i:int) ≤ &j` by intLib.ARITH_TAC>>
  pop_assum SUBST1_TAC>>
  irule unsafe_arith_le_spec>>
  simp[]
QED

Theorem num_eq_spec:
  ∀i iv j jv p.
  NUM i iv ∧ NUM j jv ∧ i < 2 ** 30 ∧ j < 2 ** 30 ⇒
  app p Unsafe_eq_v [iv; jv] emp (POSTv v. &BOOL (i = j) v)
Proof
  rw[NUM_def]>>
  `i = j ⇔ (&i:int) = &j` by intLib.ARITH_TAC>>
  pop_assum SUBST1_TAC>>
  irule unsafe_arith_eq_spec>>
  simp[]
QED
