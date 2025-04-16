#!/bin/bash
# Run the test suite on the Dafny compiler.

# Check if correct number of arguments is provided
if [ "$#" -ne 2 ]; then
    echo "Usage: $0 <dafny_path> <cakeml_path>"
    echo "  <dafny_path>   Path to the Dafny binary"
    echo "  <cakeml_path>  Path to the folder containing the CakeML binary and Makefile"
    exit 1
fi

# Store arguments in variables
DAFNY_PATH=$1
CAKEML_PATH=$2

# Save current directory
CURRENT_DIR=$(pwd)

# Change to the compilation directory and run Holmake
cd ../compilation || { echo "Failed to change to ../compilation directory"; exit 1; }
if ! Holmake dafny_compiler; then
    echo "Running Holmake to generate the Dafny compiler failed!"
    cd "$CURRENT_DIR" || { echo "Failed to return to original directory"; exit 1; }
    exit 1
fi

# Return to original directory
cd "$CURRENT_DIR" || { echo "Failed to return to original directory"; exit 1; }

# Run with the provided arguments
python dafny_compiler.py --test_path . \
  --dafny_path "$DAFNY_PATH" \
  --dafny_to_cakeml_path ../compilation/dafny_compiler \
  --cakeml_path "$CAKEML_PATH" \
  --output_path ./output \
  --recursive
