program Boogie;

procedure p() returns (r: int)
spec
{
  ensures r == 1;  // original code-expression translated to standard ensures
}
{};

procedure ip() returns ()
{
  var x: int;   // declare return variable locally
  x := 1;
};

procedure q() returns ()
spec
{
  //ensures |{ var $b: bool; $0: $b := true; goto $1; $1: return $b; }|;
  ensures true;  // the original code-expression is equivalent to returning a boolean true
}
{};