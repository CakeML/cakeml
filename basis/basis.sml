(*
  Convenience structure that re-exports all the libraries and theories of the
  CakeML basis library.
*)
structure basis = struct open

ml_translatorTheory ml_progLib ml_translatorLib cfLib

clFFITheory
fsFFITheory fsFFIPropsTheory

mlstringTheory

ListProofTheory
Word8ArrayProofTheory
ArrayProofTheory
CommandlineProofTheory
textio_initProgTheory mltextioProgTheory mltextioSpecTheory

basisProgTheory basisFunctionsLib basis_ffiLib

end
