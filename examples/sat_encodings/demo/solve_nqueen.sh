#!/bin/bash

if [ "$#" -ne 1 ]; then
    echo "Please enter a number as an argument"
    exit
fi

n=$1

echo -e "Finding solution for:"
echo -e $n
echo -e "-queens problem\n"

echo -e "\n"
read -n 1 -s -r -p "Press any key to continue"
echo -e "\n"

echo -e "Encoding the problem\n"
echo $n | ../translation/compilation/nQueens_encoder > input_nqueens.txt

echo -e "Solving the problem\n"
if ! [ -x "$(command -v lingeling)" ]; then
  echo 'Error: lingeling SAT solver is not installed.' >&2
  exit 1
fi
cat input_nqueens.txt | lingeling > output_nqueens.txt

if cat output_nqueens.txt | grep -q 'UNSATISFIABLE'; then
    echo -e "The problem is UNSATISFIABLE\n"
    exit
fi

echo "The problem is SATISFIABLE"
echo -e "\n"
read -n 1 -s -r -p "Press any key to continue"
echo -e "\n"

echo -e "Encoding the solution\n"
echo "(" > solution_nqueens.lisp
echo $n >> solution_nqueens.lisp
echo "(sat" >> solution_nqueens.lisp
cat output_nqueens.txt | grep '^v' | sed 's/v//' | sed 's/ 0//' | sed 's/^ //' | sed 's/ /\n/g' | sed 's/-/\(not /' | sed -e '/not [1-9]*/ s/$/\)/' >> solution_nqueens.lisp
echo "))" >> solution_nqueens.lisp

cat solution_nqueens.lisp | ../translation/compilation/nQueens_encoder
