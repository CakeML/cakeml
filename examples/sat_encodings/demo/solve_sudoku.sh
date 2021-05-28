#!/bin/bash

if [ "$#" -ne 1 ]; then
    file=sudokuExample.lisp
else
    file=$1
fi


echo -e "Finding solution for:\n"
cat $file

echo -e "\n"
read -n 1 -s -r -p "Press any key to continue"
echo -e "\n"

echo -e "\nEncoding the problem\n"
cat $file | ../translation/compilation/sudoku_encoder > sudokuInput.txt

echo -e "Solving the problem\n"
if ! [ -x "$(command -v lingeling)" ]; then
  echo 'Error: lingeling SAT solver is not installed.' >&2
  exit 1
fi
cat sudokuInput.txt | lingeling > sudokuOutput.txt

if cat sudokuOutput.txt | grep -q 'UNSATISFIABLE'; then
    echo -e "The problem is UNSATISFIABLE\n"
    exit
fi

echo "The problem is SATISFIABLE"
echo -e "\n"
read -n 1 -s -r -p "Press any key to continue"
echo -e "\n"

echo -e "Encoding the solution\n"
echo "(" > temp.lisp
cat $file >> temp.lisp
echo "(sat" >> temp.lisp
cat sudokuOutput.txt | grep '^v' | sed 's/v//' | sed 's/ 0//' | sed 's/^ //' | sed 's/ /\n/g' | sed 's/-/\(not /' | sed -e '/not [1-9]*/ s/$/\)/' >> temp.lisp
echo "))" >> temp.lisp

cat temp.lisp | ../translation/compilation/sudoku_encoder

echo -e "\n"
