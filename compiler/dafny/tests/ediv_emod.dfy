method Main()
{
	// Case 1.1: a = 10, b = 3
	print(int_to_string(10 / 3));
	print(" ");
	print(int_to_string(10 % 3));
	print(" ");

	// Case 1.2: a = 17, b = 5
	print(int_to_string(17 / 5));
	print(" ");
	print(int_to_string(17 % 5));
	print(" ");

	// Case 2.1: a = -10, b = 3
	print(int_to_string(-10 / 3));
	print(" ");
	print(int_to_string(-10 % 3));
	print(" ");

	// Case 2.2: a = -17, b = 5
	print(int_to_string(-17 / 5));
	print(" ");
	print(int_to_string(-17 % 5));
	print(" ");

	// Case 3.1: a = 10, b = -3
	print(int_to_string(10 / -3));
	print(" ");
	print(int_to_string(10 % -3));
	print(" ");

	// Case 3.2: a = 17, b = -5
	print(int_to_string(17 / -5));
	print(" ");
	print(int_to_string(17 % -5));
	print(" ");

	// Case 4.1: a = -10, b = -3
	print(int_to_string(-10 / -3));
	print(" ");
	print(int_to_string(-10 % -3));
	print(" ");

	// Case 4.2: a = -17, b = -5
	print(int_to_string(-17 / -5));
	print(" ");
	print(int_to_string(-17 % -5));
	print(" ");

	// Case 5.1: a = 0, b = 3
	print(int_to_string(0 / 3));
	print(" ");
	print(int_to_string(0 % 3));
	print(" ");

	// Case 5.2: a = 0, b = -3
	print(int_to_string(0 / -3));
	print(" ");
	print(int_to_string(0 % -3));
	print(" ");

	// Case 6.1: a = 10, b = 1
	print(int_to_string(10 / 1));
	print(" ");
	print(int_to_string(10 % 1));
	print(" ");

	// Case 6.2: a = 10, b = -1
	print(int_to_string(10 / -1));
	print(" ");
	print(int_to_string(10 % -1));
	print(" ");

	// Case 7.1: a = 2, b = 3
	print(int_to_string(2 / 3));
	print(" ");
	print(int_to_string(2 % 3));
	print(" ");

	// Case 7.2: a = -2, b = 3
	print(int_to_string(-2 / 3));
	print(" ");
	print(int_to_string(-2 % 3));
	print(" ");

	// Case 7.3: a = 2, b = -3
	print(int_to_string(2 / -3));
	print(" ");
	print(int_to_string(2 % -3));
	print(" ");

	// Case 7.4: a = -2, b = -3
	print(int_to_string(-2 / -3));
	print(" ");
	print(int_to_string(-2 % -3));
	print(" ");

	// Additional Cases
	// Case 8.1: a = 1, b = 3
	print(int_to_string(1 / 3));
	print(" ");
	print(int_to_string(1 % 3));
	print(" ");

	// Case 8.2: a = -1, b = 3
	print(int_to_string(-1 / 3));
	print(" ");
	print(int_to_string(-1 % 3));
	print(" ");

	// Case 8.3: a = 1, b = -3
	print(int_to_string(1 / -3));
	print(" ");
	print(int_to_string(1 % -3));
	print(" ");

	// Case 8.4: a = -1, b = -3
	print(int_to_string(-1 / -3));
	print(" ");
	print(int_to_string(-1 % -3));
	print(" ");

	// Case 9.1: a = 0, b = 1
	print(int_to_string(0 / 1));
	print(" ");
	print(int_to_string(0 % 1));
	print(" ");

	// Case 9.2: a = 0, b = -1
	print(int_to_string(0 / -1));
	print(" ");
	print(int_to_string(0 % -1));
	print(" ");
}

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
