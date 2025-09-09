program Boogie;
procedure FloorSquareRoot(x : int) returns (y : int)
spec {
  requires (x >= 0);
  ensures (y * y <= x && (y + 1) * (y + 1) > x);
}
{
  if (x == 0) {
    y := 0;
  }
  else{
    y := 1;
    while (y * y <= x)
      invariant ((y - 1) * (y - 1) <= x);
    {
      y := y + 1;
    }
    assert (y * y > x);
    assert ((y - 1) * (y - 1) <= x);
    y := y - 1;
  }
};