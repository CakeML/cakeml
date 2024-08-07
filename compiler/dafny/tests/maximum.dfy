method Main()
{
	var x: int;
	x := Maximum([1, 3, -3, 18, 0]);
	print x, " ";

	x := Maximum([0]);
	print x, " ";

	x := Maximum([-3, -3, 18, -174, 1947]);
	print x, " ";
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
