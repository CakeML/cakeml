open preamble
     ml_translatorLib
     mlcharioProgTheory rofsFFITheory

val _ = new_theory"mlfileioProg";
val _ = translation_extends "mlcharioProg";

val _ = export_theory();
