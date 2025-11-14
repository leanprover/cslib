program Boogie;

// verifies simple control flow, arithmetic, and loop reasoning

var GlobalFlag : bool;

const A: int;
const B: int;
const C: int;

procedure Join (b : bool) returns ()
spec
{
  modifies GlobalFlag;
}
{  
  var x: int;
  var y: int;
  var z: int;

  GlobalFlag := true;
  x := 3;
  y := 4;
  z := x + y;

  if (b) {
    x := x + 1;
  } else {
    y := 4;
  }

  assert y == 4;
  assert z == 7;
  assert GlobalFlag == true;

};    


procedure Loop () returns ()
{

  var c: int;
  var i: int;

  c := 0;
  i := 0;

  while (i < 10)
    invariant 0 <= i && i <= 10;
  {
    i := i + 1;
  }
};

procedure Evaluate () returns ()
{
 var i: int;

  i := 5;
  i := 3 * i + 1;
  i := 3 * (i + 1);
  i := 1 + 3 * i;
  i := (i + 1) * 3;
};