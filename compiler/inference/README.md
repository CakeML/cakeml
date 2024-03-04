The CakeML type inferencer.

Includes a translation of "specification-level" code into a
cv_compute-based presentation. This is done in a number of stages. The
base complication is the fact that the HOL unification algorithm is
expressed over a different type (`α term` with constructors: `Var`,
`Const` and `Pair`) from the one we want to use (`infer_t` with
constructors: `Infer_Tvar_db`, `Infer_Tapp` and `Infer_Tuvar`), and
uses finite maps to represent its substitutions.

The HOL presentation does provide a version of `unify` that uses
sptrees instead of finite-maps (`sunify`), but we do the conversion to
the `infer_t` type with the functions

        encode_infer_t : infer_t -> atom term
        decode_infer_t : atom term -> infer_t

eventually deriving

        cunify : infer_t num_map -> infer_t -> infer_t -> 
                 infer_t num_map option

The second problem is that `cunify` features nested recursion and a
complicated precondition to guarantee termination. The next part of
the translation is to create an equivalent tail-recursive formulation
of `cunify` which can be more readily translated into cv_compute land.
This process generates a `tcunifywl`. The `tc` prefix indicates that
it tail-calls, and the `wl` suffix says that the process of
contification has made the presentation use a "work-list".

## Guard Removal

There are four important theorems proved for every tail-recursive
constant (cunify and its auxiliaries):

   {const}_preserves_precond:
     |- !x y. precond x /\ {const}_code x = INL y ==> precond y

   {const}_ensures_decrease:
     |- !x y. precond x /\ {const}_code x = INL y ==> {const}R y x

   WF_{const}R:
     |- !x. precond x ==> WF ({const}R x)

   {const}_tcallish:
     |- !x. precond x ==> {const} x = TAILCALL {const}_code {const} x

The `{const}_code` is of type returning a sum, where the `INL`
corresponds to a recursive tail-call and the `INR` case corresponds to
terminating.


[inferScript.sml](inferScript.sml):
Definition of CakeML's type inferencer.

[infer_tScript.sml](infer_tScript.sml):
The infer_t datatype and various to_string functions.

[inferenceComputeLib.sml](inferenceComputeLib.sml):
A compset for the type inferencer. This is to make it easy to
evaluate the type inferencers inside the logic. See tests.

[proofs](proofs):
This directory contains the correctness proofs for the type
inferencer: both soundness and completeness proofs.

[tests](tests):
This directory contains tests that evaluate the type inferencer inside
the logic of HOL.

[unifyLib.sml](unifyLib.sml):
Code that makes evaluating the unification algorithm easy.

[unifyScript.sml](unifyScript.sml):
Defines a unification algorithm for use in the type inferencer.
Based on the triangular unification algorithm in
HOL/examples/unification/triangular/first-order.  We encode our
CakeML types into the term structure used there and them bring over
those definitions and theorems.

[unify_cvScript.sml](unify_cvScript.sml):
Translating unifyTheory to cv equations for use with cv_eval
