(*
  Convenience structure that re-exports all the libraries and theories of the
  CakeML basis library.
*)
structure basis = struct open

ml_translatorTheory ml_progLib ml_translatorLib cfLib
std_preludeTheory

clFFITheory
fsFFITheory fsFFIPropsTheory

mlstringTheory

ListProofTheory
Word8ArrayProofTheory
ArrayProofTheory
CommandLineProofTheory
TextIOProgTheory TextIOProofTheory

basisProgTheory basisFunctionsLib basis_ffiLib

end
