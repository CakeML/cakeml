#!/usr/bin/env python3

import os
import subprocess
import sys
import argparse

# Set up argument parser
parser = argparse.ArgumentParser(description="Run Holmake in multiple directories.")
parser.add_argument('holmake_binary', type=str, help='The Holmake binary to use')
parser.add_argument('base_dir', type=str, help='Base directory for directories to run Holmake in')
parser.add_argument('directory_file', type=str, help='File containing directory names relative to base_dir')

args = parser.parse_args()

# Assign arguments to variables
holmake_binary = args.holmake_binary
base_dir = args.base_dir
directory_file = args.directory_file

max_retries = 3  # Maximum number of retry attempts
failed_directories = []

with open(directory_file, 'r') as file:
    for line in file:
        line = line.strip()  # Remove any leading/trailing whitespace
        if not line or line.startswith('#'):  # Skip empty lines or comments
            continue

        print(('== ' + line + ' ==').ljust(80, '='))
        full_path = os.path.join(base_dir, line)  # Construct full path

        # Check if the path is a directory
        if os.path.isdir(full_path):
            jobs = 1 if "compiler/bootstrap/translation" in str(full_path) else 4
            retries = 0
            success = False

            while retries < max_retries and not success:
                try:
                    # Run the Holmake command
                    subprocess.run([holmake_binary, "-k", "-j", str(jobs)], cwd=full_path, check=True)
                    success = True  # Command succeeded
                except subprocess.CalledProcessError as e:
                    retries += 1
                    print(f"Error running Holmake in {full_path} (attempt {retries}/{max_retries}): {e}")

            if not success:
                # Add directory to the list of failures
                failed_directories.append(full_path)
        else:
            print(f"Warning: Directory {full_path} does not exist, skipping.")

# Print summary of failures
if failed_directories:
    print("\nThe following directories failed:")
    for directory in failed_directories:
        print(directory)
else:
    print("\nAll directories processed successfully.")

print("Completed running Holmake for all directories.")
