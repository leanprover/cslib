program Boogie;

// Helper function to compute square
function Square(x: real): real {
  x * x
}

// Main bisection procedure for square root
procedure BisectionSqrt(c: real, epsilon: real) returns (result: real)
spec {
  requires (c > 1.0);
  requires (epsilon > 0.0);
  requires (epsilon <= c);
  requires (-c) * (c*c - c) * c < 0.0; // f(a) * f(b) < 0
  ensures (result > 0.0);
  // The result should be approximately sqrt(c) within epsilon tolerance
  ensures (Square(result) <= c + epsilon);
  ensures (Square(result) >= c - epsilon);
}
{
  var a: real;
  var b: real;
  var p: real;
  var fp: real;
  var fa: real;
  var fb: real;
  
  // Initialize bounds: [0, c]
  a := 0.0;
  b := c;
  
  // Check precondition: f(a) * f(b) < 0
  // f(x) = x^2 - c
  fa := Square(a) - c;  // f(0) = -c < 0
  fb := Square(b) - c;  // f(c) = c^2 - c = c*(c-1) > 0
  
  assert (fa < 0.0);
  assert (fb > 0.0);
  assert (fa * fb < 0.0);

  while (epsilon <= (b - a) div 2.0)
    invariant (a <= b && fa * fb <= 0.0);
    // Root exists in [a,b]
    // [NOTE] specifying decreases clause for reals
  {
    // Compute midpoint
    p := (a + b) div 2.0; //[NOTE] Why not use (a + b) / 2?
    fp := Square(p) - c;
    
    // Check if we found exact root
    if (fp == 0.0) {
      result := p;
      a := p;
      b := p;
    }
    else {
      // Determine which half contains the root
      if (fa * fp < 0.0) {
        // Root is in [a, p]
        b := p;
        fb := fp;
      } else {
        // Root is in [p, b]
        assert (fp * fb < 0.0);  // This follows from fa * fb < 0 and fa * fp >= 0
        a := p;
        fa := fp;
      }
      result := p; // Update result to current midpoint
    }
  }
  // Final result is midpoint of [a, b]
  result := (a + b) div 2.0;
};

// Wrapper procedure for computing square root with default epsilon
procedure SqrtInt(c: int) returns (result: real)
spec {
  requires (c > 1);
  ensures (result > 0.0);
  // Result should be approximately sqrt(c)
  ensures (Square(result * 1.0) <= c + 0.000001);
  //[NOTE] Type casting unsupported
  ensures (Square(result * 1.0) >= c - 0.000001);
}
{
  call result := BisectionSqrt(c * 1.0, 0.000001);
};