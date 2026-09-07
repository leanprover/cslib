# Function combinators

These modules state the complexity of a function built from other functions. They are the reusable
interface: a caller combines `ComputableInTimeAndSpace` facts without ever mentioning tapes, head
positions or configurations. The machines behind them come from [Plumbing](../Plumbing) and
[NormalForms](../NormalForms).

- `Concat` computes a function whose encoded result is the concatenation of the encoded results of
  two functions, of which the pair is the typical case. The two machines write straight to the
  append-only output tape, so no intermediate result is ever stored; the cost over the two machines
  is one rewind of the input tape in time, and one idle cell per work tape in space.
