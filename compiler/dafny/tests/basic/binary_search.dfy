// Taken from Source/IntegrationTests/TestFiles/LitTests/LitTest/dafny4/BinarySearch.dfy
// which is released under the MIT license
method BinarySearch(a: array<int>, key: int) returns (r: int)
  requires forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures 0 <= r ==> r < a.Length && a[r] == key
  ensures r < 0 ==> key !in a[..]
{
  var lo, hi := 0, a.Length;
  while lo < hi
    invariant 0 <= lo <= hi <= a.Length
    invariant key !in a[..lo] && key !in a[hi..]
  {
    var mid := (lo + hi) / 2;
    if key < a[mid] {
      hi := mid;
    } else if a[mid] < key {
      lo := mid + 1;
    } else {
      return mid;
    }
  }
  return -1;
}

method Main()
{
  // Test case 1: Empty array
  var emptyArray := new int[0];
  var result1 := BinarySearch(emptyArray, 5);
  print "Test 1 (empty array): ", result1, " (expected: -1)\n";
  
  // Test case 2: Single element array - element present
  var singleArray := new int[1];
  singleArray[0] := 5;
  var result2 := BinarySearch(singleArray, 5);
  print "Test 2 (single element, found): ", result2, " (expected: 0)\n";
  
  // Test case 3: Single element array - element not present
  var result3 := BinarySearch(singleArray, 10);
  print "Test 3 (single element, not found): ", result3, " (expected: -1)\n";
  
  // Test case 4: Multiple elements - element present at beginning
  var multiArray := new int[5];
  multiArray[0] := 1;
  multiArray[1] := 3;
  multiArray[2] := 5;
  multiArray[3] := 7;
  multiArray[4] := 9;
  var result4 := BinarySearch(multiArray, 1);
  print "Test 4 (multiple elements, found at beginning): ", result4, " (expected: 0)\n";
  
  // Test case 5: Multiple elements - element present in middle
  var result5 := BinarySearch(multiArray, 5);
  print "Test 5 (multiple elements, found in middle): ", result5, " (expected: 2)\n";
  
  // Test case 6: Multiple elements - element present at end
  var result6 := BinarySearch(multiArray, 9);
  print "Test 6 (multiple elements, found at end): ", result6, " (expected: 4)\n";
  
  // Test case 7: Multiple elements - element not present
  var result7 := BinarySearch(multiArray, 4);
  print "Test 7 (multiple elements, not found): ", result7, " (expected: -1)\n";
  
  // Test case 8: Duplicate elements
  var dupArray := new int[6];
  dupArray[0] := 1;
  dupArray[1] := 3;
  dupArray[2] := 3;
  dupArray[3] := 3;
  dupArray[4] := 5;
  dupArray[5] := 7;
  var result8 := BinarySearch(dupArray, 3);
  print "Test 8 (duplicate elements): ", result8, " (expected: 1, 2, or 3)\n";
}