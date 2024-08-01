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

method Main() {
	var x := 0;
  while x < 5 {
    var y := 0;
    while y != 5 {
      print int_to_string(x + x + x + x + x + y);
			y := y + 1;
    }
		x := x + 1;
  }

	var sum := 0;
	var n := 10;

	var i := 1;
  while i <= n
  {
    sum := sum + i;
    i := i + 1;
  }

	print int_to_string(sum);
}
