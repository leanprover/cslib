# Machine normal forms

`RewindInput` transforms any machine into one whose halting runs have the native input head at
position one. It sequences the original machine with the shared rewind controller from
[Plumbing](../Plumbing). Output, work-tape contents, and work-tape head positions are retained.
The transformation adds at most the input length plus two steps, including on empty input.

The `HaltsWithInputAtStart` predicate states the property at every halting time, so padded runs
also satisfy it. The construction does not require the original machine to be total.
