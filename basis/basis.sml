(*
  Convenience structure that re-exports all the libraries and theories of the
  CakeML basis library.
*)
structure basis = struct open

ml_translatorTheory ml_progLib ml_translatorLib cfLib

clFFITheory
fsFFITheory fsFFIPropsTheory

ListProofTheory
mlstringTheory
mlw8arrayProgTheory
mlarrayProgTheory
CommandlineProofTheory
textio_initProgTheory mltextioProgTheory mltextioSpecTheory

basisProgTheory basisFunctionsLib basis_ffiLib

end
