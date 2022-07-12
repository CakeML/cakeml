# FloVer - A Certificate Checker for Roundoff Error Bounds

This is a copy of the FloVer code at [https://gitlab.mpi-sws.org/AVA/FloVer]

[CertificateCheckerScript.sml](CertificateCheckerScript.sml):
This file contains the HOL4 implementation of the certificate checker as well
as its soundness proof. The checker is a composition of the range analysis
validator and the error bound validator. Running this function on the encoded
analysis result gives the desired theorem as shown in the soundness theorem.

[CertificateGeneratorScript.sml](CertificateGeneratorScript.sml):
A simple, unverified generator for certificates.
To be used in conjunction with the certificate checker to first analyze
a kernel and then validate the analysis result

[EnvironmentsScript.sml](EnvironmentsScript.sml):
An inductive relation relating real-numbered environments with
an environment with "errors", i.e. where variables are bound to
finite-precision values

[ErrorBoundsScript.sml](ErrorBoundsScript.sml):
Proofs of general bounds on the error of arithmetic Expressions.
This shortens soundness proofs later.
Bounds are exprlained in section 5, Deriving Computable Error Bounds

[ErrorIntervalInferenceScript.sml](ErrorIntervalInferenceScript.sml):
This file contains the HOL4 implementation of the error bound validator as well
as its soundness proof. The function validErrorbound is the Error bound
validator from the certificate checking process. Under the assumption that a
valid range arithmetic result has been computed, it can validate error bounds
encoded in the analysis result. The validator is used in the file
CertificateChecker.v to build the complete checker.

[ErrorValidationScript.sml](ErrorValidationScript.sml):
This file contains the HOL4 implementation of the error bound validator as well
as its soundness proof. The function validErrorbound is the Error bound
validator from the certificate checking process. Under the assumption that a
valid range arithmetic result has been computed, it can validate error bounds
encoded in the analysis result. The validator is used in the file
CertificateChecker.v to build the complete checker.

[FPRangeValidatorScript.sml](FPRangeValidatorScript.sml):
Floating-Point range validator

[IEEE_connectionScript.sml](IEEE_connectionScript.sml):
Connect FloVer's idealized machine semantics to 64-bit
IEEE-754 floating-point semantics

[Infra](Infra):
Infrastructural lemmas and formalizations for FloVer

[IntervalArithScript.sml](IntervalArithScript.sml):
Formalization of real valued interval arithmetic
Used in soundness proofs for error bound validator.

[IntervalValidationScript.sml](IntervalValidationScript.sml):
Interval arithmetic checker and its soundness proof.
The function validIntervalbounds checks wether the given analysis result is
a valid range arithmetic for each sub term of the given exprression e.
The computation is done using our formalized interval arithmetic.
The function is used in CertificateChecker.v to build the full checker.

[RealIntervalInferenceScript.sml](RealIntervalInferenceScript.sml):
Implement  a trusted, unverified inferencer for real range intervals.
The inferred, returned maps should be run through the certificate checker

[RealRangeArithScript.sml](RealRangeArithScript.sml):
Recursive correctness predicate for a range analysis with some supporting
theorems

[TypeValidatorScript.sml](TypeValidatorScript.sml):
Simple Type Inference algorithm with correctness proof to infer machine type
assignments for FloVer's input expressions

[semantics](semantics):
Formalization of idealized semantics of FloVer that handle both real-numbered
semantics and finite-precision semantics.

[sqrtApproxScript.sml](sqrtApproxScript.sml):
Simple approximation of sqrt as it is not computable in HOL4 using
newton iterations.
As the iteration may fail, the process "self-validates", checkign that
the result is an over/under-approximation of the real sqrt

[ssaPrgsScript.sml](ssaPrgsScript.sml):
We define a pseudo SSA predicate.
The formalization is similar to the renamedApart property in the LVC framework
by Schneider, Smolka and Hack (http://dblp.org/rec/conf/itp/SchneiderSH15)
Our predicate is not as fully fledged as theirs, but we especially borrow the
idea of annotating the program with the predicate with the set of free and
defined variables
