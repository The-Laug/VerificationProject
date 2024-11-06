define V(m) (m) // macro defining the variant m

method foo(M: Int, N: Int)
  returns (res: Int, m: Int)
  requires 0 < N && 0 <= M
  ensures M == res * N + m
{
  res := 0
  m := M

  while (N <= m) 
    invariant M == res * N + m
  {
    var v: Int := (m) // initialize variant
    assert v >= 0 // variant cannot decrease forever
    m := m - N
    res := res + 1
    assert (m) < v // variant has decreased after one iteration
  }
}