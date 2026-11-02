Tests for individual compiler backend passes.

[bvi_tailrec_testScript.sml](bvi_tailrec_testScript.sml):
Tests for the BVI tail recursion pass.

[clos_op_testScript.sml](clos_op_testScript.sml):
Tests for ClosLang smart operation construction.

[shift_lit_testScript.sml](shift_lit_testScript.sml):
End-to-end test that word64 shifts by a literal amount, including calls
of the Word64 basis wrappers, compile to shifts by a constant in ClosLang.
This checks that source_lift_consts does not lift the shift amount.

[source_dce_testScript.sml](source_dce_testScript.sml):
Tests for the source dead-code elimination pass.

[source_lift_consts_testScript.sml](source_lift_consts_testScript.sml):
Basic tests and readiness challenges for source_lift_consts, based on plan.txt.

[word_cse_testScript.sml](word_cse_testScript.sml):
Tests for wordLang common subexpression elimination.

[word_unreach_testScript.sml](word_unreach_testScript.sml):
Tests for removal of unreachable wordLang code.
