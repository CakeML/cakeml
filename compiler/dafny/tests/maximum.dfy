function abs(x: int) : int {
	if x < 0 then -x else x
}

function digit_to_string(n: int) : string {
	if n == 0 then "0"
	else if n == 1 then "1"
	else if n == 2 then "2"
	else if n == 3 then "3"
	else if n == 4 then "4"
	else if n == 5 then "5"
	else if n == 6 then "6"
	else if n == 7 then "7"
	else if n == 8 then "8"
	else if n == 9 then "9"
	else "digit_to_string: passed argument was not a digit"
}

function {:tailrecursion false} nat_to_string(n: int) : string {
	if n < 10 then digit_to_string(n)
	else nat_to_string(n / 10) + digit_to_string(n % 10)
}

function int_to_string(x: int) : string {
	if x < 0 then "-" + nat_to_string(abs(x))
	else nat_to_string(x)
}

method Main()
{
	var x: int;
	x := Maximum([1, 3, -3, 18, 0]);
	print(int_to_string(x));
	print(" ");

	x := Maximum([0]);
	print(int_to_string(x));
	print(" ");

	x := Maximum([-3, -3, 18, -174, 1947]);
	print(int_to_string(x));
	print(" ");
}

/*
 * Original code from https://github.com/dafny-lang/dafny/blob/master/Source/IntegrationTests/TestFiles/LitTests/LitTest/examples/maximum.dfy
 * which is released under the MIT license.
 *
 * Replaced for loop with while-loop, since at the time of writing for-loops are
 * not supported by the compilation to the reduced Dafny AST.
 */
method Maximum(values: seq<int>) returns (max: int)
  requires values != []
  ensures max in values
  ensures forall i | 0 <= i < |values| :: values[i] <= max
{
  max := values[0];
	var idx := 0;
  while idx < |values|
    invariant max in values
		invariant idx <= |values|
    invariant forall j | 0 <= j < idx :: values[j] <= max
  {
    if max < values[idx] {
      max := values[idx];
    }
		idx := idx + 1;
  }
}
