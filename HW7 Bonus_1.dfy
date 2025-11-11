predicate Sorted(a: array<int>, lo: int, hi: int)
  reads a
  requires 0 <= lo <= hi <= a.Length
{
  forall i, j :: lo <= i < j < hi ==> a[i] <= a[j]
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
    invariant Sorted(A, 0, i) // only holds after inner loop finishes
    decreases n - i
  {
    var key := A[i];
    var j := i;
    // Insert key into sorted subarray A[0..i)
    while j > 0 && A[j-1] > key
      invariant 0 <= j <= i
      invariant forall k :: 0 <= k < j ==> A[k] <= key
      invariant forall k :: j <= k < i ==> key <= A[k]
      decreases j
    {
      A[j] := A[j-1];
      j := j - 1;
    }
    A[j] := key;
    i := i + 1;
  }
}
