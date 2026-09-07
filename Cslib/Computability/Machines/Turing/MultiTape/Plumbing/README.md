# Machine transformations

These modules describe executable machines and their effects on configurations and `runFrom`.

- `Basic` changes a configuration's control state without changing its tapes.
- `Sequential` runs machines with the same work-tape count consecutively. The first halting
  transition hands its tapes, head positions, and accumulated output to the second machine.
- `ExtendTapes` places a machine's tapes along any injection. Time is unchanged; each unused tape
  contributes one visited cell to space. Arbitrary data on unused tapes is preserved.
  `eq_embed_initCfg` reads this backwards, and is what hands a fresh block of tapes to a machine: a
  configuration in that machine's initial state whose own block is blank and rewound, with the
  input head at the start, *is* its embedded initial configuration. So a combinator can start a
  machine on a block without knowing anything about the configuration the previous one left behind,
  beyond its output and that it did not touch this block.
- `OutputToWorkTape` redirects output to one fresh tape, including the symbol on a halting step.
- `InputFromWorkTape` simulates the native input on a work tape, preserving boundary clamping.
- `Rewind` shares one controller between native-input and work-tape rewinding. Work-tape rewind
  starts immediately after contiguous contents and finishes at their first cell, including when empty.
- `Concat` runs two machines one after the other on disjoint blocks of work tapes, rewinding the
  input in between so that both read the same input. Their outputs land on the append-only output
  tape in order, so the composite outputs their concatenation.
