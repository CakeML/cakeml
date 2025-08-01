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
from pprint import pprint

def main():
    """Main function of the end-to-end compiler."""
    args = parse_args()

    if args.program_path:
        dafny_compiler(args.program_path, args.dafny_path,
                       args.dafny_to_cakeml_path, args.cakeml_path,
                       args.output_path, capture_output=False,
                       verbose=args.verbose)
    else:
        print("Running test suite...")

        dafny_fails = []
        cakeml_fails = []
        total = 0

        root = "*.dfy" if not args.recursive else "**/*.dfy"
        test_files = sorted(args.test_path.glob(root))
        for test_file in test_files:
            print(f"{test_file}")
            command = [args.dafny_path, "run", test_file, "--no-verify"]
            print("- Running program with Dafny...")
            dfy_result = subprocess.run(command, capture_output=True,
                                        text=True, check=True)
            # Drop empty line + Dafny message
            dfy_result = dfy_result.stdout.split("\n")[2:]
            dfy_result = "\n".join(dfy_result)

            print("- Translating the program to CakeML and running it...")
            dafny_failure, result = dafny_compiler(test_file,
                                                   args.dafny_path,
                                                   args.dafny_to_cakeml_path,
                                                   args.cakeml_path,
                                                   args.output_path,
                                                   capture_output=True,
                                                   verbose=args.verbose)

            if dfy_result == result:
                print(f"\033[92mPASS\033[0m with matching output:")
                print(dfy_result)
            elif dafny_failure:
                print(f"\033[91mDAFNY FAILURE\033[0m")
                result = result.split("\n")[2:]
                result = "\n".join(result)
                print(result)
                dafny_fails.append((test_file, result))
            else:
                print(f"\033[91mFAIL\033[0m")
                print("When ran by Dafny:")
                print(dfy_result)
                print("When trying to compile to CakeML and run:")
                print(result)
                cakeml_fails.append((test_file, result))

            print()
            total += 1

        print()
        nr_dafny_fails = len(dafny_fails)
        nr_cakeml_fails = len(cakeml_fails)
        total_fails = nr_dafny_fails + nr_cakeml_fails
        print(f"{total - total_fails} out of {total} tests passed.")
        print(f"{nr_dafny_fails} Dafny fails, {nr_cakeml_fails} CakeML fails")

        if nr_dafny_fails != 0:
            print(f"The following test(s) failed because of Dafny:")
            pprint(dafny_fails)
        if nr_cakeml_fails != 0:
            print(f"The following test(s) failed because of CakeML:")
            pprint(cakeml_fails)

def dafny_compiler(program_path, dafny_path, dafny_to_cakeml_path, cakeml_path,
                   output_path, capture_output, verbose):
    program_name = program_path.stem
    cakeml_assembly_name = (program_name + '.cake.S')
    program_binary_name = program_name + '.cake'

    dafny_sexp_path = output_path / (program_name + '.dfy.sexp')
    cakeml_sexp_path = output_path / (program_name +'.cake.sexp')
    cakeml_assembly_path = output_path / cakeml_assembly_name
    program_binary_path = output_path / program_binary_name

    if verbose:
        print("- Run Dafny...")
    command = [dafny_path, "bake", dafny_sexp_path, program_path]
    failed_attempts = 0
    while True:
        result = subprocess.run(command, check=False, text=True,
                                capture_output=(not verbose))
        if result.returncode == 0:
            break
        elif failed_attempts < 3:
            failed_attempts += 1
            if verbose:
                print(f"- Command failed with return code {result.returncode}. "
                      "Retrying...")
        elif failed_attempts >= 3:
            dafny_failure = True
            return dafny_failure, result.stdout

    dafny_failure = False

    if verbose:
        print("- Compile from Dafny S-expression to CakeML S-expression...")
    command = [dafny_to_cakeml_path]
    with open(dafny_sexp_path, 'r') as dafny_sexp:
        with open(cakeml_sexp_path, 'w') as cakeml_sexp:
            subprocess.run(command, stdin=dafny_sexp, stdout=cakeml_sexp,
                           text=True, check=True)

    if verbose:
        print("- Generate assembly from CakeML S-expression...")
    command = [cakeml_path / "cake", "--sexp=true",
               # Generated code is not type safe (e.g., initializes arrays with
               # 0) - but that's okay, since we proved our own correctness
               # theorem.
               "--skip_type_inference=true"]
    with open(cakeml_sexp_path, 'r') as cakeml_sexp:
        with open(cakeml_assembly_path, 'w') as cakeml_assembly:
            subprocess.run(command, stdin=cakeml_sexp, stdout=cakeml_assembly,
                           text=True, check=True)

    if verbose:
        print("- Make executable:")
        print("  - Copy assembly to CakeML directory...")
    copied_assembly_path = cakeml_path / cakeml_assembly_name
    shutil.copyfile(cakeml_assembly_path, copied_assembly_path)
    if verbose:
        print(f"  - Run make {program_binary_name}...")
    command = ["make", program_binary_name]
    subprocess.run(command, cwd=cakeml_path, check=True,
                   capture_output=(not verbose))
    if verbose:
        print("  - Delete assembly file, move generated program...")
    os.remove(copied_assembly_path)
    shutil.move(cakeml_path / program_binary_name, program_binary_path)

    if verbose:
        print("- Execute generated binary...")
    command = [program_binary_path]

    if capture_output:
        result = subprocess.run(command, check=True, capture_output=True, text=True)
        return dafny_failure, result.stdout
    else:
        subprocess.run(command, check=True)
        return dafny_failure, None

def parse_args():
    """Parse command line arguments."""
    parser = argparse.ArgumentParser()
    input_group = parser.add_mutually_exclusive_group(required=True)
    input_group.add_argument("--program_path", type=program_path,
                             help="Dafny program to be compiled")
    input_group.add_argument("--test_path", type=folder_path,
                             help=("path to folder containing Dafny programs "
                                   "to test the compiler on"))
    parser.add_argument("--dafny_path", type=file_path, required=True,
                        help="path to Dafny binary")
    parser.add_argument("--dafny_to_cakeml_path", type=file_path, required=True,
                        help="path to Dafny to CakeML compiler binary")
    parser.add_argument("--cakeml_path", type=folder_path, required=True,
                        help="path to folder containing the CakeML binary and Makefile")
    parser.add_argument("--output_path", type=folder_path, required=True,
                        help="path to store output files")
    parser.add_argument("--verbose", action="store_true", required=False,
                        help="print additional info")
    parser.add_argument("--recursive", action="store_true", required=False,
                        help=("whether test path should be traversed "
                              "recursively (no effect if program path is "
                              "given)"))
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
