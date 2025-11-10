program Boogie;

function foo2(x:int) : int
  { x + 1 }
function foo(x:int) : bool
  { foo2(x) > 0 }

procedure test(x:int) returns (r:int)
spec {
  ensures (r > 0);
}
{
  if (foo(x)) {
    r := foo2(x);
  } else {
    r := 1;
  }
};