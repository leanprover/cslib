program Boogie;

procedure loopSimple (n: int) returns (r: int)
spec {
  requires (n >= 0);
}
{
  var sum : int;
  var i : int;

  sum := 0;
  i := 0;
  while(i < n)
    invariant (i <= n && ((i * (i-1)) div 2 == sum));
  {
    sum := sum + i;
    i := i + 1;
  }
  assert [sum_assert]: ((n * (n-1)) div 2 == sum);
  assert [neg_cond]: (i == n);
  r := sum;
};
