#!/bin/bash

if [ "$#" -ne 1 ]; then
    file=graphProblem.lisp
else
    file=$1
fi

echo -e "Finding solution for:\n"
cat $file

echo -e "\n"
read -n 1 -s -r -p "Press any key to continue"
echo -e "\n"

echo -e "\nEncoding the problem\n"
cat $file | ../translation/compilation/graphColoring_encoder > graphColoringInput.txt

echo -e "Solving the problem\n"
if ! [ -x "$(command -v lingeling)" ]; then
  echo 'Error: lingeling SAT solver is not installed.' >&2
  exit 1
fi
cat graphColoringInput.txt | lingeling > graphColoringOutput.txt

echo -e "Encoding the solution\n"
echo "(" > temp.lisp
cat $file >> temp.lisp
echo "(sat" >> temp.lisp
cat graphColoringOutput.txt | grep '^v' | sed 's/v//' | sed 's/ 0//' | sed 's/^ //' | sed 's/ /\n/g' | sed 's/-/\(not /' | sed -e '/not [1-9]*/ s/$/\)/' >> temp.lisp
echo "))" >> temp.lisp

cat temp.lisp | ../translation/compilation/graphColoring_encoder > graphSolution.txt
cat graphSolution.txt
echo -e "\n"

echo -e "\n"
read -n 1 -s -r -p "Press any key to get a colored graph"
echo -e "\n"

python3 drawGraph.py
xdg-open "graph.png"&
