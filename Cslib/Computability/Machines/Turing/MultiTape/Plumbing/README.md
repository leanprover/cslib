# Machine transformations

These modules describe executable machines and their effects on configurations and `runFrom`.

- `Basic` changes a configuration's control state without changing its tapes, transports runs
  along maps that preserve steps, and relates explicit execution paths to `runFrom`.
- `Sequential` runs machines with the same work-tape count consecutively. The first halting
  transition hands its tapes, head positions, and accumulated output to the second machine,
  which starts in its own fixed initial state.
- `ExtendTapes` places a machine's tapes along any injection. Time is unchanged; each unused tape
  contributes one visited cell to space. Arbitrary data on unused tapes is preserved.
