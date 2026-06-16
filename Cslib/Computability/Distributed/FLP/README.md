# Impossibility of distributed consensus

This directory contains a formalization of Völzer's proof [Volzer2004] of the famous result in
distributed computing, first proved by Fischer, Lynch and Paterson [FLP1985], that distributed
consensus is impossible in the presence of even a single crash fault.

## Lean files

1. `Algorithm.lean` defines the "syntax" of a distributed algorithm for solving the consensus problem
   and proves some basic properties.

2. `Consensus.lean` defines what it means for a distributed algorithm to solve the consensus problem
   in a fault-tolerant way and proves some basic properties.

*The following files will appear in future PRs:*

3. `FairScheduler.lean` contains a technical machinery for constructing "fair executions", which is used
    in the proof of `PseudoConsensus.of_consensus` in `PseudoConsensus.lean` and in the proof of
    `OnePseudoConsensus.fair_nonUniform` in `Impossibility.lean`.

4. `CanReachVia.lean` defines the notion of reachability via a subset of processes and proves some of
   its properties.

5. `PseudoConsensus.lean` defines the notion of a fault-tolerant "pseudo-consensus" algorithm, which
   is central to Völzer's proof, and proves that every `f`-tolerant consensus algorithm is also a
   `f`-tolerant pseudo-consensus algorithm.

6. `OnePseudoConsensus.lean` focuses on 1-tolerant pseudo-consensus algorithms, defines the key notion
   of "nonuniformity", and proves a number of their properties.

7. `Impossibility.lean` proves that every 1-tolerant pseudo-consensus algorithms has a fair execution
   which doesn't contain any fault but never reaches a consensus, which then implies that there cannot
   be a consensus algorithm that can tolerate even a single fault.

Files #1 and #2 contains materials common to both [FLP1985] and [Volzer2004].
File #3 provides proof details that are either completely omitted (in the case of
`PseudoConsensus.of_consensus`) or only hinted at (in the case of
`OnePseudoConsensus.fair_nonUniform`) in [Volzer2004].
The remaining files follow the development in [Volzer2004] fairly closely,
as is explained further in each file.

## References

[FLP1985]
M.J. Fischer, N.A. Lynch, M.S. Paterson, Impossibility of distributed consensus with one faulty process,
JACM 32 (2) (April 1985) 374–382.

[Volzer2004]
H. Völzer, A constructive proof for FLP. Information Processing Letters 92(2), (October 2004) 83–87.
