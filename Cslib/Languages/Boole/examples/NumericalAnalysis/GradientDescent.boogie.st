program Boogie;

// Helper function to compute absolute value
function Abs(x: real): real {
  if x >= 0.0 then x else -x
}

// Function f(x) = x^2 - 4x + 3
function F(x: real): real {
  x * x - 4.0 * x + 3.0
}

// Derivative f'(x) = 2x - 4
function F_prime(x: real): real {
  2.0 * x - 4.0
}

// Gradient descent with iteration limit
procedure GradientDescentIter(
  x0: real, alpha: real, epsilon: real, iter: int
) returns (result: real)
spec {
  requires (0.0 < alpha && alpha < 1.0);  // learning rate constraints
  requires (epsilon > 0.0);               // tolerance constraint  
  requires (iter >= 0);                   // non-negative iterations
}
{
  // Is it possible to pass a callback function as argument in Boogie?
  var grad: real;
  var x1: real;
  
  grad := F_prime(x0);
  
  if (iter == 0) {
    result := x0;
  }
  else {
    if (Abs(grad) < epsilon) {
        result := x0;
    }
    else {
        // Gradient descent step: x1 = x0 - alpha * grad
        x1 := x0 - alpha * grad;  
        call result := GradientDescentIter(x1, alpha, epsilon, iter - 1);
    }
  }
};

