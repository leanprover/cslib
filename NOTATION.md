# Notation

Overview of the notation for common concepts.

## Equivalences
- Alpha equivalence: `m =α n`
- Bisimilarity: `p ~[lts] q` (`p` is bisimilar to `q` in the LTS `lts`)

## Operational semantics

### Option A
This option uses an extra arrow head to denote reflexive and transitive closure.

When there is only 'one' semantics:
- Reduction: `m → n`.
- Multi-step reduction (possibly zero): `m ↠ n`.
- Transition: `p [μ]→ q`, where `μ` is a transition label.
- Multi-step transition (possibly zero): `p [μs]↠ q`, where `μs` is a list of transition labels.
- Saturated transitions: `p [μ]⇒ q`.
- Multi-step saturated transitions: `p [μs]➾ q`.

When there are 'alternative' semantics, we suffix the arrow with the name of the transition relation or LTS under use. For example `m →[cbv] n` means that there is a reduction from `m` to `n` under the `cbv` reduction relation.
Another example: transitions look like `p [μ]→[late] q`, where `late` is an `LTS`.

### Option B

As Option A, but uses `*` to denote reflexive and transitive closure.
- Multi-step reduction (possibly zero): `m →* n`.
- Multi-step transition (possibly zero): `p [μs]→* q`, where `μs` is a list of transition labels.
- Saturated transitions: `p [μ]⇒ q`.
- Multi-step saturated transitions: `p [μs]⇒* q`.