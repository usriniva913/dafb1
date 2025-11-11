predicate Sorted(A: array<int>, lo: int, hi: int)
    reads A
    requires 0 <= lo <= hi <= A.Length
{
    forall i, j :: lo <= i <= j < hi ==> A[i] <= A[j]
}


method InsertionSort(n: int, A: array<int>)
  requires n == A.Length
  modifies A
  ensures  Sorted(A, 0, n)              
{
  if n <= 1 { return; } // Length 1 is automatically sorted

  var i := 1;
  while i < n
    invariant 1 <= i <= n
    //invariant Sorted(___________________) // Please fill in
    //decreases ___________________________ // Please fill in
  {
    var j := i;
    // Shift elements greater than Ai one position to the right
    while j >= 1 && A[j-1] > A[j]
      invariant 0 <= j <= i
      //invariant Sorted(___________________) // Please fill in
      //decreases ___________________________ // Please fill in
    {
      A[j-1],A[j] := A[j], A[j-1]; // swap A[j-1] with A[j]
      j := j - 1;
    } // end while j >= 1 && A[j-1] > A[j]
    i := i + 1;
  } // end while i < n
}
