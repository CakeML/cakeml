#!/usr/bin/env python3

import os
import subprocess
import sys
import argparse

class bcolors:
    HEADER = '\033[95m'
    OKBLUE = '\033[94m'
    OKCYAN = '\033[96m'
    OKGREEN = '\033[92m'
    WARNING = '\033[93m'
    FAIL = '\033[91m'
    ENDC = '\033[0m'
    BOLD = '\033[1m'
    UNDERLINE = '\033[4m'

def print_header(s):
    print(bcolors.HEADER + s + bcolors.ENDC)

base_dir_default = '..'
build_seq_defalut = 'build-sequence'
if (not os.getcwd().endswith('/developers')):
    base_dir_default = '.'
    build_seq_defalut = 'developers/' + build_seq_defalut

# Set up argument parser
parser = argparse.ArgumentParser(description="Run Holmake in multiple directories.")
parser.add_argument('holmake_binary', type=str, help='The Holmake binary to use', nargs='?', default='Holmake')
parser.add_argument('base_dir', type=str, help='Base directory for directories to run Holmake in', nargs='?', default=base_dir_default)
parser.add_argument('directory_file', type=str, help='File containing directory names relative to base_dir', nargs='?', default=build_seq_defalut)
parser.add_argument('-j', '--jobs', type=int, default=4,
                    help='Holmake workers per directory (default: 4)')
parser.add_argument('--attempts', type=int, default=3,
                    help='Maximum build attempts per directory (default: 3)')
parser.add_argument('--holmake-arg', dest='holmake_args', action='append', default=[],
                    metavar='ARG', help='Extra Holmake argument; repeat as needed')

args = parser.parse_args()
for option, value in [('--jobs', args.jobs), ('--attempts', args.attempts)]:
    if value < 1:
        parser.error(f'{option} must be at least 1')

# Assign arguments to variables
holmake_binary = args.holmake_binary
base_dir = args.base_dir
directory_file = args.directory_file

max_retries = args.attempts
jobs = args.jobs
failed_directories = []

all_dirs = []
with open(directory_file, 'r') as file:
    for line in file:
        line = line.strip()  # Remove any leading/trailing whitespace
        if not line or line.startswith('#'):  # Skip empty lines or comments
            continue
        line = line.split(':',1)[0]
        all_dirs.append(line)

def str_fill(s,c,t,n):
  while len(s) + len(t) < n:
      s = s + c
  return s + t

for idx, line in enumerate(all_dirs):
    status = str(idx+1) + ' of ' + str(len(all_dirs))
    print_header(str_fill('== ' + line + ' ','=', ' ' + status + ' ==',80))
    if failed_directories:
        print(bcolors.FAIL + 'Failed so far: ' + ', '.join(failed_directories) + bcolors.ENDC)
    full_path = os.path.join(base_dir, line)  # Construct full path

    # Check if the path is a directory
    if os.path.isdir(full_path):
        retries = 0
        success = False

        while retries < max_retries and not success:
            try:
                # Run the Holmake command
                subprocess.run([holmake_binary, "-k", "-j", str(jobs), *args.holmake_args], cwd=full_path, check=True)
                success = True  # Command succeeded
            except subprocess.CalledProcessError as e:
                retries += 1
                print(f"Error running Holmake in {full_path} (attempt {retries}/{max_retries}): {e}")

        if not success:
            # Add directory to the list of failures
            failed_directories.append(full_path)
    else:
        print(f"Error: Directory {full_path} does not exist.")
        failed_directories.append(full_path)

# Print summary of failures
if failed_directories:
    print("\nThe following directories failed:")
    for directory in failed_directories:
        print(directory)
else:
    print("\nAll directories processed successfully.")

print("Completed running Holmake for all directories.")
sys.exit(1 if failed_directories else 0)
