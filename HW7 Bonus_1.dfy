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
    var j := i;
    var key := A[i];
    
    while j > 0 && A[j-1] > key
      invariant 0 <= j <= i
      invariant Sorted(A, 0, j)
      invariant forall k :: j <= k < i ==> A[k] >= key
      invariant A[i] == key
      decreases j
    {
      A[j] := A[j-1];
      j := j - 1;
    }
    A[j] := key;
    i := i + 1;
  }
} 

  
  

