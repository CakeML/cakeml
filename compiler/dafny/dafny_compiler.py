"""
Module for compiling Dafny programs via the CakeML compiler.

This script ties together all the different components, which allows for
easy end-to-end (i.e. from a Dafny file to a binary) use of the compiler.
"""

import argparse
import os
import shutil
import subprocess
from pathlib import Path

def main():
    """Main function of the end-to-end compiler."""
    args = parse_args()

    program_name = args.program_path.stem
    cakeml_assembly_name = (program_name + '.cake.S')
    program_binary_name = program_name + '.cake'

    dafny_sexp_path = args.output_path / (program_name + '.dfy.sexp')
    cakeml_sexp_path = args.output_path / (program_name +'.cake.sexp')
    cakeml_assembly_path = args.output_path / cakeml_assembly_name
    program_binary_path = args.output_path / program_binary_name

    print("Run Dafny...")
    command = [args.dafny_path, "translate", "sexp", args.program_path]
    if args.emit_uncompilable_code:
        command.append("--emit-uncompilable-code")
    command.extend(["--output", dafny_sexp_path])
    subprocess.run(command, check=True)

    print("Compile from Dafny S-expression to CakeML S-expression...")
    command = [args.dafny_to_cakeml_path]
    with open(dafny_sexp_path, 'r') as dafny_sexp:
        with open(cakeml_sexp_path, 'w') as cakeml_sexp:
            subprocess.run(command, stdin=dafny_sexp, stdout=cakeml_sexp,
                           text=True, check=True)

    print("Generate assembly from CakeML S-expression...")
    command = [args.cakeml_path / "cake", "--sexp=true"]
    with open(cakeml_sexp_path, 'r') as cakeml_sexp:
        with open(cakeml_assembly_path, 'w') as cakeml_assembly:
            subprocess.run(command, stdin=cakeml_sexp, stdout=cakeml_assembly,
                           text=True, check=True)

    print("Make executable:")
    print("Copy assembly to CakeML directory...")
    copied_assembly_path = args.cakeml_path / cakeml_assembly_name
    shutil.copyfile(cakeml_assembly_path, copied_assembly_path)
    print(f"Run make {program_binary_name}...")
    command = ["make", program_binary_name]
    subprocess.run(command, cwd=args.cakeml_path, check=True)
    print("Delete assembly file, move generated program...")
    os.remove(copied_assembly_path)
    shutil.move(args.cakeml_path / program_binary_name, program_binary_path)

    print("Execute generated binary...")
    command = [program_binary_path]
    subprocess.run(command, check=True)

def parse_args():
    """Parse command line arguments."""
    parser = argparse.ArgumentParser(formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    parser.add_argument("program_path", type=program_path,
                        help="Dafny program to be compiled")
    parser.add_argument("--dafny_path", type=file_path, required=True,
                        help="path to Dafny binary")
    parser.add_argument("--dafny_to_cakeml_path", type=file_path, required=True,
                        help="path to Dafny to CakeML compiler binary")
    parser.add_argument("--cakeml_path", type=folder_path, required=True,
                        help="path to folder containing the CakeML binary and Makefile")
    parser.add_argument("--output_path", type=folder_path, required=True,
                        default=os.getcwd(), help="path to store output files")
    parser.add_argument("--emit_uncompilable_code", action="store_true", required=False,
                        help="passes --emit-uncompilable-code to Dafny")
    return parser.parse_args()

def program_path(string):
    """Checks that the string is a valid path to a Dafny program."""
    path = file_path(string)
    if path.suffix != ".dfy":
        raise argparse.ArgumentTypeError(f"Wrong suffix: {path} is not a valid path to a program")
    return path

def file_path(string):
    """Checks that the string is a valid path to a file."""
    if os.path.isfile(string):
        return Path(string)
    else:
        raise argparse.ArgumentTypeError(f"{string} is not a valid path to a file")

def folder_path(string):
    """Checks that the string is a valid path to a folder."""
    if os.path.isdir(string):
        return Path(string)
    else:
        raise argparse.ArgumentTypeError(f"{string} is not a valid path to a folder")

if __name__ == "__main__":
    main()
