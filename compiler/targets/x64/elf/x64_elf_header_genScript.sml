open HolKernel Parse boolLib bossLib;

open byte_sequenceTheory;
open elf_headerTheory elf_program_header_tableTheory elf_types_native_uintTheory;

val _ = new_theory "x64_elf_header_gen";

(* Utility for converting a natural number into an unsigned_char. *)
val _ = Define `
  unsigned_char_of_num (x : num) =
    ((n2w x) : unsigned_char)`;

(* Definition of an AMD64 ABI-compliant ELF header.  Fields are, in (line) order:
 *   1. ELF format magic numbers,
 *   2. 64-bit ELF file identifier,
 *   3. 2LSB data encoding, required by AMD64 ABI,
 *   4. Current version of ELF file,
 *   5. Targetting the GNU (Linux) OS/ABI combination,
 *   6. Version number of ABI (arbitrary, but set to 0 to match most AMD64 executables),
 *   7. Final padding to make up 16 bytes of header.
 *)
val _ = Define `
    elf64_ident_field : unsigned_char list =
      [ elf_mn_mag0; elf_mn_mag1; elf_mn_mag2; elf_mn_mag3
      ; unsigned_char_of_num elf_class_64                 
      ; unsigned_char_of_num elf_data_2lsb                
      ; unsigned_char_of_num elf_ev_current               
      ; unsigned_char_of_num elf_osabi_gnu                
      ; unsigned_char_of_num 0                            
      ] ++ repeat 7 (unsigned_char_of_num 0)`;            

(* Creates an AMD64 ABI-compliant ELF64 header for an executable file.  Fields are, in (line) order:
 *   1. Initial 16 bytes of identifying data, defined above,
 *   2. File is of executable type,
 *   3. Targetting the X86-64 machine architecture,
 *   4. Current version of the ELF format (required),
 *   5. Entry point address of the executable file, passed as an argument,
 *   6. File offset to the program header table, describing file segments, here immediately after
        file header, 64 bytes from start of file,
 *   7. File offset to the section header table, describing file sections, missing here,
 *   8. Flags, none set,
 *   9. ELF header size, in bytes (constant 64),
 *  10. Program header table entry size, in bytes (constant 56),
 *  11. Number of program header table entries,
 *  12. Section header table entry size, in bytes (SHT missing, so 0),
 *  13. Number of section header table entries (SHT missing, so 0),
 *  14. Section header string table file offset (SHT missing, so SHN_UNDEF, as required)
 *)
val _ = Define `
  x64_elf64_header (entry : num) : elf64_header =
    <| elf64_ident     := elf64_ident_field
     ; elf64_type      := n2w elf_ft_exec
     ; elf64_machine   := n2w elf_ma_x86_64
     ; elf64_version   := n2w elf_ev_current
     ; elf64_entry     := n2w entry
     ; elf64_phoff     := n2w 64
     ; elf64_shoff     := n2w 0
     ; elf64_flags     := n2w 0
     ; elf64_ehsize    := n2w 64
     ; elf64_phentsize := n2w 56
     ; elf64_phnum     := n2w 2
     ; elf64_shentsize := n2w 0
     ; elf64_shnum     := n2w 0
     ; elf64_shstrndx  := n2w shn_undef
     |>`;

(* Creates a program header table entry describing the .text (code) segment of an executable file.
 * Fields are, in (line) order:
 *   1. Segment is of loadable type,
 *   2. The segment is readable (0x4) and executable (0x1),
 *   3. File offset of the segment is after the ELF header (64 bytes) and two program header table
 *      entries (56 + 56 bytes),
 *   4. Virtual address of the segment is at 176,
 *   5. Physical address of the segment is at 176,
 *   6. The file size is taken to be the size of the generated machine code, parameterised,
 *   7. The memory size is identical to the file size,
 *   8. The alignment is taken to be 0x200000, which seems to be typical for X64 executable files.
 *
 * Note that the virtual address is required to be congruent to the offset modulo alignment, and
 * here 176 = 176 (mod 2097152), as required.
 *)
val _ = Define `
  x64_text_segment_header (code_size : num) : elf64_program_header_table_entry =
    <| elf64_p_type   := n2w elf_pt_load
     ; elf64_p_flags  := n2w (1 + 4)
     ; elf64_p_offset := n2w (64 + 56 + 56)
     ; elf64_p_vaddr  := n2w (64 + 56 + 56)
     ; elf64_p_paddr  := n2w (64 + 56 + 56)
     ; elf64_p_filesz := n2w code_size
     ; elf64_p_memsz  := n2w code_size
     ; elf64_p_align  := n2w 2097152 (* 0x200000 *)
     |>`;

(* Computes the virtual address of a segment given an alignment and an offset.  Per the ELF standard,
 * a segment's virtual address must be equal to the offset modulo the alignment.
 *)
val _ = Define `
  compute_vaddr_modulo (offset : num) (align : num) : num =
    ((offset DIV align) * offset) + offset MOD align`;

(* Creates a program header table entry describing the heap segment of an executable file.
 * Fields are, in (line) order:
 *   1. Segment is of loadable type,
 *   2. The segment is writable (0x2) and readable (0x4),
 *   3. File offset of the segment is after the ELF header (64 bytes), two program header table entries
 *      (56 + 56 bytes) and the .text segment (code_size, a parameter),
 *   4. Virtual address of the segment is computed from the alignment, offset, and code size,
 *   5. Physical address is the same as the virtual address,
 *   6. The file size is taken to be 1 byte,
 *   7. Memory size is parametric, but is always at a minimum 1, per the ELF restriction that memory size
 *      must always be greater than or equal to file size,
 *   8. The alignment is taken to be 0x200000, which seems to be typical for X64 executable files.
 *)
val _ = Define `
  x64_heap_segment_header (code_size : num) (heap_size : num) : elf64_program_header_table_entry =
    let heap_size = MIN 1 heap_size in
      <| elf64_p_type   := n2w elf_pt_load
       ; elf64_p_flags  := n2w (2 + 4)
       ; elf64_p_offset := n2w (64 + 56 + 56 + code_size)
       ; elf64_p_vaddr  := n2w (compute_vaddr_modulo (176 + code_size) 2097152) (* 0x200000 *)
       ; elf64_p_paddr  := n2w (compute_vaddr_modulo (176 + code_size) 2097152) (* 0x200000 *)
       ; elf64_p_filesz := n2w 1
       ; elf64_p_memsz  := n2w heap_size
       ; elf64_p_align  := n2w 2097152    (* 0x200000 *)
       |>`;

(* Creates a byte sequence containing the as-it-appears-on-disk byte signature of an ELF64 executable file
 * from a list of X64-encoded bytes and a given heap size.
 *)
val _ = Define `
  x64_build_elf_file (code : word8 list) (heap_size : num) : byte_sequence =
    let code_size = LENGTH code in
    let entry     = 176 in
    let hdr       = x64_elf64_header entry in
    let text_hdr  = x64_text_segment_header code_size in
    let heap_hdr  = x64_heap_segment_header code_size heap_size in
    let text_seg  = from_byte_lists [code] in
    let heap_seg  = create 1 (n2w 0) in
      byte_sequence$concat0
	[ bytes_of_elf64_header hdr
	; bytes_of_elf64_program_header_table_entry Little text_hdr
	; bytes_of_elf64_program_header_table_entry Little heap_hdr
	; text_seg
	; heap_seg
	]`;

val _ = export_theory();