program Boogie;

procedure SimpleLoop () returns ()
{  
  var i: int;

  i := 0;

  while (i < 10)
    invariant 0 <= i && i <= 10;
  {
    i := i + 1;
  }
  // when loop exits, !(i < 10) holds
  assume !(i < 10);
}; 


procedure VariableBoundLoop (n : int) returns ()
{  
  var i: int;

  i := 0;

  while (i < n)
    invariant 0 <= i && i <= n;
  {
    i := i + 1;
  }
  // when loop exits, !(i < n) holds
  assume !(i < n);
}  ;  

procedure Foo () returns ()
{
 var i: int;

  // note: original code used uninitialized i
  // so we keep it that way for semantic equivalence
  i := 3 * i + 1;
  i := 3 * (i + 1);
  i := 1 + 3 * i;
  i := (i + 1) * 3;
};

procedure FooToo () returns ()
{
 var i: int;

  i := 5;
  i := 3 * i + 1;
  i := 3 * (i + 1);
  i := 1 + 3 * i;
  i := (i + 1) * 3;
};

procedure FooTooStepByStep () returns ()
{
 var i: int;

  i := 5;
  i := 3 * i + 1;
  i := 3 * (i + 1);
  i := 1 + 3 * i;
  i := (i + 1) * 3;
};