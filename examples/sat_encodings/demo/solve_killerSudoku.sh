#!/bin/bash

if [ "$#" -ne 1 ]; then
    echo "Please enter the problem file as an argument"
    exit
fi

file=$1

echo -e "Finding solution for:\n"
cat $file

echo -e "\nEncoding the problem\n"
cat $file | $(CAKEMLDIR)/examples/sat_encodings/translation/compilation/killerSudoku_encoder > input.txt

echo -e "Solving the problem\n"
cat input.txt | ~/lingeling/lingeling > output.txt

echo -e "Encoding the solution\n"
echo "(" > temp.lisp
cat $file >> temp.lisp
echo "(sat" >> temp.lisp
cat output.txt | grep '^v' | sed 's/v//' | sed 's/ 0//' | sed 's/^ //' | sed 's/ /\n/g' | sed 's/-/\(not /' | sed -e '/not [1-9]*/ s/$/\)/' >> temp.lisp
echo "))" >> temp.lisp

cat temp.lisp | $(CAKEMLDIR)/examples/sat_encodings/translation/compilation/killerSudoku_encoder
