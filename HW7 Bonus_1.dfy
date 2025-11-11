predicate Sorted(A: array<int>, lo: int, hi: int)
    reads A
    requires 0 <= lo <= hi <= A.Length
{
    forall i, j :: lo <= i <= j < hi ==> A[i] <= A[j]
}

method InsertionSort(n: int, A: array<int>)
  requires n == A.Length
  modifies A
  ensures Sorted(A, 0, n)              
{
  if n <= 1 { return; }

  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant Sorted(A, 0, i)
    decreases n - i
  {
    var key := A[i];
    var j := i - 1;
    
    // Find the correct position for key in A[0..i]
    while j >= 0 && A[j] > key
      invariant -1 <= j < i
      invariant Sorted(A, 0, i)
      invariant forall k :: 0 <= k <= j ==> A[k] <= key
      invariant forall k :: j+1 <= k <= i ==> A[k] >= key
      decreases j + 1
    {
      A[j+1] := A[j];
      j := j - 1;
    }
    A[j+1] := key;
    i := i + 1;
  }
}
