open HolKernel Parse boolLib bossLib;

open elf_headerTheory;

val _ = new_theory("x64_elf_header_gen");

(*
type elf64_header =
  <| elf64_ident    : list unsigned_char (** Identification field *)
   ; elf64_type     : elf64_half         (** The object file type *)
   ; elf64_machine  : elf64_half         (** Required machine architecture *)
   ; elf64_version  : elf64_word         (** Object file version *)
   ; elf64_entry    : elf64_addr         (** Virtual address for transfer of control *)
   ; elf64_phoff    : elf64_off          (** Program header table offset in bytes *)
   ; elf64_shoff    : elf64_off          (** Section header table offset in bytes *)
   ; elf64_flags    : elf64_word         (** Processor-specific flags *)
   ; elf64_ehsize   : elf64_half         (** ELF header size in bytes *)
   ; elf64_phentsize: elf64_half         (** Program header table entry size in bytes *)
   ; elf64_phnum    : elf64_half         (** Number of entries in program header table *)
   ; elf64_shentsize: elf64_half         (** Section header table entry size in bytes *)
   ; elf64_shnum    : elf64_half         (** Number of entries in section header table *)
   ; elf64_shstrndx : elf64_half         (** Section header table entry for section name string table *)
   |>
*)

val _ = Define `
  x64_elf64_header : elf64_header =
    <| elf64_ident     = ARB
     ; elf64_type      = ARB
     ; elf64_machine   = ARB
     ; elf64_version   = ARB
     ; elf64_entry     = ARB
     ; elf64_phoff     = ARB
     ; elf64_shoff     = ARB
     ; elf64_flags     = ARB
     ; elf64_ehsize    = ARB
     ; elf64_phentsize = ARB
     ; elf64_phnum     = ARB
     ; elf64_shentsize = ARB
     ; elf64_shnum     = ARB
     ; elf64_shstrndx  = ARB
     |>`;
  

val _ = export_theory();