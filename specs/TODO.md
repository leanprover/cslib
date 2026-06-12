---
next_project_number: 164
---

# TODO

## Task Order

*Updated 2026-06-12. Generated from state.json dependency graph.*

**Dependency Waves**:
| Wave | Tasks | Blocked by | Topics |
|------|-------|------------|--------|
| 1 | 36,37,62,127,139,146,147,159 | -- | Bimodal Porting, Submit PRs |
| 2 | 39,40,63,140,148,160 | 36,37,62,139,147,159 | Temporal Logic, Submit PRs |
| 3 | 41,64,141,149,161 | 39,40,63,140,148,160 | Submit PRs, Foundations |
| 4 | 128,129,142,150,162 | 140,141,146,149,161 | Submit PRs |
| 5 | 126,143,151,152,154,163 | 142,150,160 | Submit PRs |
| 6 | 130,133,144,153,155,156 | 126,127,143,151,152,154 | Submit PRs |
| 7 | 131,132,134,135,157 | 127,128,130,133,152,156 | Submit PRs |
| 8 | 158 | 151,153,155,157 | Submit PRs |

**Grouped by Topic** (indented = depends on parent):

### Temporal Logic

39 [NOT STARTED] — Discrete temporal completeness: prove that every formula valid on
40 [BLOCKED] — Continuous temporal completeness: completeness for temporal logic

### Bimodal Porting

36 [BLOCKED] — Port discrete completeness (completeness_discrete theorem) and We
37 [BLOCKED] — Port continuous extension completeness once developed upstream. T

### Submit PRs

62 [RESEARCHED] — pr4_temporal_metalogic_core
  └─ 63 [NOT STARTED] — pr5_chronicle_infrastructure
    └─ 64 [NOT STARTED] — pr6_completeness_theorem
127 [NOT STARTED] — Sub-PR 1.3: Propositional semantics (bivalent + Kripke). Introduc
  └─ 130 [NOT STARTED] — Sub-PR 1.6: Classical soundness and completeness. Proves classica
    └─ 131 [NOT STARTED] — Sub-PR 1.7: Intuitionistic soundness and completeness via Kripke 
    └─ 132 [NOT STARTED] — Sub-PR 1.8: Minimal soundness and completeness via Kripke models.
  └─ 131 [NOT STARTED] — Sub-PR 1.7: Intuitionistic soundness and completeness via Kripke  (see above)
  └─ 132 [NOT STARTED] — Sub-PR 1.8: Minimal soundness and completeness via Kripke models. (see above)
139 [NOT STARTED] — Sub-PR 1.1.2: Polymorphic axiom definitions. Adds Axioms.lean wit
  └─ 140 [NOT STARTED] — Sub-PR 1.1.3: Hilbert proof system typeclass hierarchy. Adds Proo
    └─ 141 [NOT STARTED] — Sub-PR 1.1.4: Propositional Hilbert instances and derivation tree
      └─ 128 [NOT STARTED] — Sub-PR 1.4: ND derived connective rules (standalone). Adds derive
        └─ 135 [NOT STARTED] — Sub-PR 1.11: ND-Hilbert extensional equivalence. Proves Hilbert d
      └─ 129 [NOT STARTED] — Sub-PR 1.5: Modal logical equivalence + Basic update. Adds Logica
      └─ 142 [NOT STARTED] — Sub-PR 1.1.5: Core theorems and barrel file. Adds Theorems/Propos
        └─ 126 [NOT STARTED] — Sub-PR 1.2: Propositional axiom extensions and IntMin instances. 
          └─ 130 [NOT STARTED] — Sub-PR 1.6: Classical soundness and completeness. Proves classica (see above)
          └─ 133 [NOT STARTED] — Sub-PR 1.9: ND-Hilbert bridge parameterization. Parameterizes Fro
            └─ 134 [NOT STARTED] — Sub-PR 1.10: Hilbert-style derived connective rules. Adds derived
            └─ 135 [NOT STARTED] — Sub-PR 1.11: ND-Hilbert extensional equivalence. Proves Hilbert d (see above)
        └─ 143 [NOT STARTED] — Sub-PR 1.1.6: Connective and combinator theorems. Adds Theorems/P
          └─ 144 [NOT STARTED] — Sub-PR 1.1.7: Metalogic foundations. Adds Consistency.lean (278),
        └─ 163 [NOT STARTED] — Sub-PR 3.5: Temporal semantics and PL embedding. Adds Model.lean 
    └─ 162 [NOT STARTED] — Sub-PR 3.4: Temporal proof system instances. Adds Instances.lean 
146 [NOT STARTED] — Sub-PR 2.2: Proof system hierarchy + PL embedding. Adds 13 bundle
  └─ 150 [NOT STARTED] — Sub-PR 2.6: K soundness and completeness. Adds ProofSystem/Instan
    └─ 151 [NOT STARTED] — Sub-PR 2.7: T and B soundness and completeness. T (reflexive fram
      └─ 153 [NOT STARTED] — Sub-PR 2.9: S4 and S5 soundness and completeness. S4 (reflexive+t
        └─ 158 [NOT STARTED] — Sub-PR 2.14: TB system + barrel files. TB (reflexive+symmetric): 
      └─ 155 [NOT STARTED] — Sub-PR 2.11: K45 and KB5 soundness and completeness. K45 (transit
        └─ 158 [NOT STARTED] — Sub-PR 2.14: TB system + barrel files. TB (reflexive+symmetric):  (see above)
      └─ 158 [NOT STARTED] — Sub-PR 2.14: TB system + barrel files. TB (reflexive+symmetric):  (see above)
    └─ 152 [NOT STARTED] — Sub-PR 2.8: D soundness and completeness. Adds Instances/D.lean (
      └─ 156 [NOT STARTED] — Sub-PR 2.12: D4 and D5 soundness and completeness. D4 (serial+tra
        └─ 157 [NOT STARTED] — Sub-PR 2.13: D45 and DB soundness and completeness. D45 (serial+t
          └─ 158 [NOT STARTED] — Sub-PR 2.14: TB system + barrel files. TB (reflexive+symmetric):  (see above)
      └─ 157 [NOT STARTED] — Sub-PR 2.13: D45 and DB soundness and completeness. D45 (serial+t (see above)
    └─ 154 [NOT STARTED] — Sub-PR 2.10: K4 and K5 soundness and completeness. K4 (transitive
      └─ 155 [NOT STARTED] — Sub-PR 2.11: K45 and KB5 soundness and completeness. K45 (transit (see above)
147 [NOT STARTED] — Sub-PR 2.3: Derivation trees and deduction theorem. Adds Metalogi
  └─ 148 [NOT STARTED] — Sub-PR 2.4: Maximal consistent sets + generic soundness framework
    └─ 149 [NOT STARTED] — Sub-PR 2.5: Generic completeness framework. Adds Metalogic/Comple
      └─ 150 [NOT STARTED] — Sub-PR 2.6: K soundness and completeness. Adds ProofSystem/Instan (see above)
159 [NOT STARTED] — Sub-PR 3.1: Temporal formula type. Introduces Syntax/Formula.lean
  └─ 160 [NOT STARTED] — Sub-PR 3.2: Temporal syntax utilities. Adds Context.lean (131 lin
    └─ 161 [NOT STARTED] — Sub-PR 3.3: Temporal axioms and derivation trees. Adds Axioms.lea
      └─ 162 [NOT STARTED] — Sub-PR 3.4: Temporal proof system instances. Adds Instances.lean  (see above)
    └─ 163 [NOT STARTED] — Sub-PR 3.5: Temporal semantics and PL embedding. Adds Model.lean  (see above)

### Foundations

41 [NOT STARTED] — Abstract shared completeness infrastructure between temporal and 

## Tasks

### 163. Subpr 3 5 semantics embedding
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Submit PRs
- **Dependencies**: Task 160, Task 142

**Description**: Sub-PR 3.5: Temporal semantics and PL embedding. Adds Model.lean (60 lines, TemporalModel structure on LinearOrder), Satisfies.lean (177 lines, recursive satisfaction relation with Burgess convention), Validity.lean (198 lines, validity hierarchy: Valid/ValidSerial/ValidDense/ValidDiscrete), FromPropositional.lean (56 lines, structural PL -> Temporal embedding with coercion), and Theorems.lean barrel (19 lines, re-exports Foundation temporal derived theorems). ~510 diff lines across 5 files. External dependencies: Cslib.Foundations.Logic.Theorems.Temporal.TemporalDerived and FrameConditions (PR1 sub-PRs 1.1.5/1.1.6, tasks 142-143).

---

### 162. Subpr 3 4 proof system instances
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Submit PRs
- **Dependencies**: Task 161, Task 140

**Description**: Sub-PR 3.4: Temporal proof system instances. Adds Instances.lean (214 lines, registers InferenceSystem, ModusPonens, ClassicalHilbert, TemporalNecessitation, 22 HasAxiom* instances, and TemporalBXHilbert for HilbertBX tag type) and ProofSystem.lean barrel (23 lines). Bridges abstract Foundation typeclass hierarchy to concrete derivation tree. ~237 diff lines across 2 files. External dependency: Cslib.Foundations.Logic.ProofSystem (PR1 sub-PR 1.1.3, task 140).

---

### 161. Subpr 3 3 axioms derivation
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Submit PRs
- **Dependencies**: Task 160

**Description**: Sub-PR 3.3: Temporal axioms and derivation trees. Adds Axioms.lean (235 lines, 26 BX axiom constructors with FrameClass classification: Base/Dense/Discrete), Derivation.lean (98 lines, Type-valued DerivationTree with 6 inference rules: axiom, assumption, modus_ponens, temporal_necessitation, temporal_duality, weakening), and Derivable.lean (99 lines, Prop-valued Nonempty wrapper with constructor-mirroring lemmas). ~432 diff lines across 3 files.

---

### 160. Subpr 3 2 syntax utilities
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Submit PRs
- **Dependencies**: Task 159

**Description**: Sub-PR 3.2: Temporal syntax utilities. Adds Context.lean (131 lines, Context = List (Formula Atom) with map/membership lemmas), BigConj.lean (52 lines, big conjunction over formula lists), and Subformulas.lean (218 lines, subformula closure with membership and transitivity lemmas). ~401 diff lines across 3 files.

---

### 159. Subpr 3 1 temporal formula
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Submit PRs
- **Dependencies**: Task 138

**Description**: Sub-PR 3.1: Temporal formula type. Introduces Syntax/Formula.lean (549 lines) defining the temporal logic Formula inductive with primitives {atom, bot, imp, untl, snce}, all derived connectives (neg, top, or, and, iff, allFuture/G, someFuture/F, allPast/H, somePast/P), the swapTemporal involution, Encodable/Denumerable instances, and connective typeclass registrations (HasBot, HasImp, HasUntil, HasSince, TemporalConnectives). Gateway PR for all temporal logic. ~549 diff lines. External dependency: Cslib.Foundations.Logic.Connectives (PR1 sub-PR 1.1.1, task 138).

---

### 158. Subpr 2 14 tb barrels
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: Submit PRs
- **Dependencies**: Task 151, Task 153, Task 155, Task 157

**Description**: Sub-PR 2.14: TB system + barrel files. TB (reflexive+symmetric): Instances/TB.lean (138), Systems/TB/Soundness.lean (107), Systems/TB/Completeness.lean (129). Also adds Metalogic.lean barrel (55 lines) aggregating all core metalogic + system imports. Includes final Cslib.lean import updates. Last sub-PR in the chain. ~485 new lines across 4 files.

---

### 157. Subpr 2 13 d45 db systems
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: Submit PRs
- **Dependencies**: Task 152, Task 156

**Description**: Sub-PR 2.13: D45 and DB soundness and completeness. D45 (serial+transitive+Euclidean): Instances/D45.lean (153), Systems/D45/Soundness.lean (115), Systems/D45/Completeness.lean (130). DB (serial+symmetric): Instances/DB.lean (139), Systems/DB/Soundness.lean (103), Systems/DB/Completeness.lean (119). Both are serial double-axiom extensions. D45 extends D4. Over 500-line limit (~759 lines) but logically grouped. ~759 new lines across 6 files.

---

### 156. Subpr 2 12 d4 d5 systems
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: Submit PRs
- **Dependencies**: Task 152

**Description**: Sub-PR 2.12: D4 and D5 soundness and completeness. D4 (serial+transitive): Instances/D4.lean (139), Systems/D4/Soundness.lean (103), Systems/D4/Completeness.lean (118). D5 (serial+Euclidean): Instances/D5.lean (140), Systems/D5/Soundness.lean (104), Systems/D5/Completeness.lean (119). Both are serial + single-axiom extensions. Over 500-line limit (~723 lines) but logically grouped. ~723 new lines across 6 files.

---

### 155. Subpr 2 11 k45 kb5 systems
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: Submit PRs
- **Dependencies**: Task 151, Task 154

**Description**: Sub-PR 2.11: K45 and KB5 soundness and completeness. K45 (transitive+Euclidean): Instances/K45.lean (139), Systems/K45/Soundness.lean (109), Systems/K45/Completeness.lean (117). KB5 (symmetric+Euclidean): Instances/KB5.lean (139), Systems/KB5/Soundness.lean (116), Systems/KB5/Completeness.lean (121). Both involve axiom 5; K45 extends K4 and KB5 extends B. Over 500-line limit (~741 lines) but mathematically related. ~741 new lines across 6 files.

---

### 154. Subpr 2 10 k4 k5 systems
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: Submit PRs
- **Dependencies**: Task 150

**Description**: Sub-PR 2.10: K4 and K5 soundness and completeness. K4 (transitive): Instances/K4.lean (124), Systems/K4/Soundness.lean (97), Systems/K4/Completeness.lean (107). K5 (Euclidean): Instances/K5.lean (125), Systems/K5/Soundness.lean (91), Systems/K5/Completeness.lean (93). Both are single-axiom extensions of K with related frame properties. Over 500-line limit (~637 lines) but logically grouped. ~637 new lines across 6 files.

---

### 153. Subpr 2 9 s4 s5 systems
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: Submit PRs
- **Dependencies**: Task 151

**Description**: Sub-PR 2.9: S4 and S5 soundness and completeness. S4 (reflexive+transitive): Instances/S4.lean (137), Systems/S4/Soundness.lean (106), Systems/S4/Completeness.lean (115). S5 (equivalence relations): Instances/S5.lean (111), Systems/S5/Soundness.lean (103), Systems/S5/Completeness.lean (94). S5 extends S4 — natural dependency chain. Over 500-line limit (~666 lines) but logically grouped. ~666 new lines across 6 files.

---

### 152. Subpr 2 8 d system
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: Submit PRs
- **Dependencies**: Task 150

**Description**: Sub-PR 2.8: D soundness and completeness. Adds Instances/D.lean (125), Systems/D/Soundness.lean (90), Systems/D/Completeness.lean (428). Serial frames — the D completeness proof is the largest individual completeness proof. Over 500-line limit (~643 lines) but logically indivisible. ~643 new lines across 3 files.

---

### 151. Subpr 2 7 t b systems
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: Submit PRs
- **Dependencies**: Task 150

**Description**: Sub-PR 2.7: T and B soundness and completeness. T (reflexive frames): Instances/T.lean (124), Systems/T/Soundness.lean (89), Systems/T/Completeness.lean (105). B (symmetric frames): Instances/B.lean (124), Systems/B/Soundness.lean (90), Systems/B/Completeness.lean (98). Both are simple single-axiom extensions of K. Slightly over 500-line limit (~630 lines) but closely related systems. ~630 new lines across 6 files.

---

### 150. Subpr 2 6 k system
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: Submit PRs
- **Dependencies**: Task 146, Task 149

**Description**: Sub-PR 2.6: K soundness and completeness. Adds ProofSystem/Instances/K.lean (112 lines) defining KAxiom inductive and HilbertK InferenceSystem instance. Adds Systems/K/Soundness.lean (82 lines) and Systems/K/Completeness.lean (301 lines). Base modal system K — establishes the pattern for all subsequent system PRs. ~495 new lines across 3 files.

---

### 149. Subpr 2 5 completeness
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: Submit PRs
- **Dependencies**: Task 148

**Description**: Sub-PR 2.5: Generic completeness framework. Adds Metalogic/Completeness.lean (475 lines) providing the canonical model construction for modal completeness via Zorn's lemma. Mathematical centerpiece of PR 2 — the generic completeness infrastructure that all 15 system-specific completeness proofs instantiate. ~475 new lines in 1 file.

---

### 148. Subpr 2 4 mcs soundness
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: Submit PRs
- **Dependencies**: Task 147

**Description**: Sub-PR 2.4: Maximal consistent sets + generic soundness framework. Adds Metalogic/MCS.lean (392 lines) constructing maximal consistent sets via Zorn's lemma with iterated deduction. Adds Metalogic/Soundness.lean (84 lines) providing the generic soundness framework for all modal systems. ~476 new lines across 2 files.

---

### 147. Subpr 2 3 derivation deduction
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: Submit PRs
- **Dependencies**: Task 145

**Description**: Sub-PR 2.3: Derivation trees and deduction theorem. Adds Metalogic/DerivationTree.lean (218 lines) defining Hilbert-style derivation trees parameterized over axiom predicates. Adds Metalogic/DeductionTheorem.lean (215 lines) proving the deduction theorem for modal Hilbert systems. Core proof infrastructure that all system-specific files depend on. ~433 new lines across 2 files.

---

### 146. Subpr 2 2 proof system hierarchy
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: Submit PRs
- **Dependencies**: Task 145

**Description**: Sub-PR 2.2: Proof system hierarchy + PL embedding. Adds 13 bundled typeclasses (ModalTHilbert through ModalDBHilbert) and 14 opaque tag types to Foundations/Logic/ProofSystem.lean. Adds FromPropositional.lean (103 lines) providing structural embedding from PL into modal logic with semantic coherence theorem. Adds ProofSystem/Instances.lean barrel file (56 lines). Pure definitions, no proofs beyond the embedding. ~280 diff lines across 3 files.

---

### 145. Subpr 2 1 lukasiewicz primitives
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Topic**: Submit PRs
- **Dependencies**: None
- **Research**: [145_subpr_2_1_lukasiewicz_primitives/reports/01_lukasiewicz-primitives.md]
- **Plan**: [145_subpr_2_1_lukasiewicz_primitives/plans/01_lukasiewicz-primitives.md]
- **Summary**: [145_subpr_2_1_lukasiewicz_primitives/summaries/01_lukasiewicz-primitives-summary.md]

**Description**: Sub-PR 2.1: Lukasiewicz primitive refactoring. Refactors Modal/Basic.lean from {atom, not, and, diamond} to {atom, bot, imp, box} primitives with derived connectives as abbrevs. Updates Modal/Denotation.lean for new primitives. Deletes LogicalEquivalence.lean (incompatible with new primitives). Replaces all grind-based proofs with explicit term-mode proofs for axiom validity theorems. This is the gateway PR — clear, focused, and establishes the Lukasiewicz convention for all subsequent PRs. ~440 diff lines across 3 files.

---

### 144. Subpr 1 1 7 metalogic
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: Submit PRs
- **Dependencies**: Task 143

**Description**: Sub-PR 1.1.7: Metalogic foundations. Adds Consistency.lean (278), DeductionHelpers.lean (120), DeductionTheorem.lean (217), MCS.lean (161). ~776 diff lines total, will likely need splitting into 2 PRs to stay under 500 lines each.

---

### 143. Subpr 1 1 6 connective theorems
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: Submit PRs
- **Dependencies**: Task 142

**Description**: Sub-PR 1.1.6: Connective and combinator theorems. Adds Theorems/Propositional/Connectives.lean (De Morgan, double negation stratified by logic strength), Theorems/Combinators.lean, and Theorems/Temporal/FrameConditions.lean. May need splitting if total exceeds 500 lines (~428-539 diff lines).

---

### 142. Subpr 1 1 5 core theorems barrel
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: Submit PRs
- **Dependencies**: Task 141

**Description**: Sub-PR 1.1.5: Core theorems and barrel file. Adds Theorems/Propositional/Core.lean (311 lines, stratified by logic strength), Theorems/BigConj.lean (142 lines), and reduced Theorems.lean barrel (~45 lines, excluding modal/temporal imports). ~498 diff lines.

---

### 141. Subpr 1 1 4 propositional instances
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: Submit PRs
- **Dependencies**: Task 140

**Description**: Sub-PR 1.1.4: Propositional Hilbert instances and derivation trees. Adds PropositionalAxiom inductive, DerivationTree parameterized over axiom type, HilbertCl/HilbertInt/HilbertMin instances, and ListHelpers utilities. 4 new files + Cslib.lean imports. ~430 diff lines.

---

### 140. Subpr 1 1 3 proof system hierarchy
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: Submit PRs
- **Dependencies**: Task 139

**Description**: Sub-PR 1.1.3: Hilbert proof system typeclass hierarchy. Adds ProofSystem.lean defining MinimalHilbert/IntuitionisticHilbert/ClassicalHilbert 3-tier propositional hierarchy plus modal extensions (K through S5, D-family) and temporal/bimodal systems. Needs curation to handle extra modal classes from tasks 92/100. ~490 diff lines.

---

### 139. Subpr 1 1 2 axiom definitions
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: Submit PRs
- **Dependencies**: Task 138

**Description**: Sub-PR 1.1.2: Polymorphic axiom definitions. Adds Axioms.lean with axiom formulas (ImplyK, ImplyS, EFQ, Peirce, modal K/T/4/B/5/D, temporal BX1-BX13) as polymorphic abbreviations over connective typeclasses. Pure definitions, no proofs. ~300 diff lines.

---

### 138. Subpr 1 1 1 proposition refactor
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Topic**: Submit PRs
- **Dependencies**: None
- **Research**: [138_subpr_1_1_1_proposition_refactor/reports/01_proposition-refactor.md]
- **Plan**: [138_subpr_1_1_1_proposition_refactor/plans/01_proposition-refactor.md]
- **Summary**: [138_subpr_1_1_1_proposition_refactor/summaries/01_proposition-refactor-summary.md]

**Description**: Sub-PR 1.1.1: Proposition type to Lukasiewicz convention. Introduces Connectives.lean (98 lines), refactors Defs.lean to bot/imp primitives with derived connectives, updates NaturalDeduction/Basic.lean (3 rules replacing 8). Includes Zulip topic creation before PR submission. Adds ChagrovZakharyaschev1997 to references.bib. ~302 diff lines across 6 files.

---

### 137. Refactor modal directory structure
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Topic**: Modal Logic
- **Dependencies**: None
- **Research_report**: [137_refactor_modal_directory_structure/reports/01_directory-structure-research.md]
- **Summary**:
  - [137_refactor_modal_directory_structure/summaries/01_modal-directory-refactor-summary.md]
  - [137_refactor_modal_directory_structure/summaries/01_modal-directory-refactor-summary.md]
- **Plan**: [137_refactor_modal_directory_structure/plans/01_modal-directory-refactor.md]

**Description**: Refactor Modal/ directory structure for the modal cube. Systematically reorganize Cslib/Logics/Modal/ to make the architecture self-documenting through clear directory names and small files, while respecting the upstream/fork boundary for clean PRs. PR 1 restructures fork-only files (Hilbert/, Metalogic/Systems/, split Instances.lean). PR 2 restructures upstream-originating files (Syntax.lean, Semantics/).

---

### 136. Pr1 citation conformance
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Dependencies**: None
- **Research**: [136_pr1_citation_conformance/reports/01_citation-conformance.md]
- **Plan**: [136_pr1_citation_conformance/plans/01_citation-conformance-plan.md]

**Description**: Revise citations on the pr1/foundations-logic branch to conform to the canonical citation conventions (standards/citation-conventions.md). Scope: (1) Remove orphaned HughesCresswell1996 entry from references.bib (uncited anywhere). (2) Add SorensenUrzyczyn2006 bib entry and convert the inline Sorensen & Urzyczyn mention in NaturalDeduction/Basic.lean to a proper BibKey citation on its own bullet. (3) Standardize internal cross-reference formatting — some files use backtick-wrapped paths (e.g., `Cslib/...`) while others use bare paths; pick one convention and apply consistently across all PR 1 Propositional and Modal files. (4) Review all 22 Propositional and 4 Modal files on the PR branch for any remaining discrepancies against the citation standard (dash bullets, missing BibKeys, inconsistent formatting). All work targets the pr1/foundations-logic branch. Documentation-only changes — no Lean code modifications.

---

### 135. Subpr 1 11 nd hilbert equivalence
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: Submit PRs
- **Dependencies**: Task 128, Task 133

**Description**: Sub-PR 1.11: ND-Hilbert extensional equivalence. Proves Hilbert derivability and ND derivability are extensionally equivalent, with instances for classical, intuitionistic, and minimal logic.

---

### 134. Subpr 1 10 hilbert derived rules
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: Submit PRs
- **Dependencies**: Task 133

**Description**: Sub-PR 1.10: Hilbert-style derived connective rules. Adds derived rules for negation/top/conjunction/disjunction/biconditional at 3 logic levels, built over parameterized FromHilbert. Slightly over 500-line limit (559 lines) but indivisible.

---

### 133. Subpr 1 9 fromhilbert parameterization
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: Submit PRs
- **Dependencies**: Task 126

**Description**: Sub-PR 1.9: ND-Hilbert bridge parameterization. Parameterizes FromHilbert.lean over axiom sets, enabling the ND-Hilbert bridge to work for classical, intuitionistic, and minimal logic.

---

### 132. Subpr 1 8 minimal soundness completeness
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: Submit PRs
- **Dependencies**: Task 127, Task 130

**Description**: Sub-PR 1.8: Minimal soundness and completeness via Kripke models. Slightly over 500-line limit (514 lines) but logically indivisible: MinSoundness + MinLindenbaum + MinCompleteness.

---

### 131. Subpr 1 7 intuitionistic soundness completeness
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: Submit PRs
- **Dependencies**: Task 127, Task 130

**Description**: Sub-PR 1.7: Intuitionistic soundness and completeness via Kripke models. Slightly over 500-line limit (555 lines) but logically indivisible: IntSoundness + IntLindenbaum (DCCS extension lemma) + IntCompleteness.

---

### 130. Subpr 1 6 classical soundness completeness
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: Submit PRs
- **Dependencies**: Task 126, Task 127

**Description**: Sub-PR 1.6: Classical soundness and completeness. Proves classical propositional Hilbert logic is sound and complete w.r.t. bivalent semantics. Depends on 1.2 (IntMin instances) and 1.3 (semantics).

---

### 129. Subpr 1 5 modal logical equivalence
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: Submit PRs
- **Dependencies**: Task 141

**Description**: Sub-PR 1.5: Modal logical equivalence + Basic update. Adds LogicalEquivalence typeclass instance for modal logic and updates Modal/Basic.lean for MinimalHilbert rename.

---

### 128. Subpr 1 4 nd derived rules
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: Submit PRs
- **Dependencies**: Task 141

**Description**: Sub-PR 1.4: ND derived connective rules (standalone). Adds derived rules for natural deduction connectives using the standalone NaturalDeduction/Basic.lean already in upstream.

---

### 127. Subpr 1 3 propositional semantics
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: Submit PRs
- **Dependencies**: Task 138

**Description**: Sub-PR 1.3: Propositional semantics (bivalent + Kripke). Introduces Valuation/Evaluate/Tautology (bivalent) and KripkeModel/IForces/IValid/MValid (Kripke) for propositional logic.

---

### 126. Subpr 1 2 intmin instances
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: Submit PRs
- **Dependencies**: Task 142

**Description**: Sub-PR 1.2: Propositional axiom extensions and IntMin instances. Extends axiom system with IntPropAxiom/MinPropAxiom and adds instance registrations for intuitionistic and minimal Hilbert logics.

---

### 125. Subpr 1 1 hilbert hierarchy refactoring
- **Status**: [EXPANDED]
- **Task Type**: lean4
- **Topic**: Submit PRs
- **Dependencies**: None
- **Research**:
  - [125_subpr_1_1_hilbert_hierarchy_refactoring/reports/02_research-report.md]
  - [125_subpr_1_1_hilbert_hierarchy_refactoring/reports/03_feedback-analysis.md]
- **Plan**: [125_subpr_1_1_hilbert_hierarchy_refactoring/plans/01_implementation-plan.md]

**Description**: Sub-PR 1.1: 3-tier Hilbert hierarchy refactoring. Modifies 12 already-merged files to introduce MinimalHilbert/IntuitionisticHilbert/ClassicalHilbert 3-level hierarchy, replacing the flat PropositionalHilbert. Pure refactoring - no new logic. Foundation for all other sub-PRs.

---

### 124. Plan pr1 decomposition into smaller prs
- **Status**: [COMPLETED]
- **Task Type**: general
- **Topic**: Submit PRs
- **Dependencies**: None
- **Plan**: [124_plan_pr1_decomposition_into_smaller_prs/plans/01_pr1-decomposition-plan.md]
- **Summary**: [124_plan_pr1_decomposition_into_smaller_prs/summaries/01_pr1-decomposition-summary.md]

---

### 123. Add bib references pr1
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Topic**: Submit PRs
- **Dependencies**: None
- **Research**: [123_add_bib_references_pr1/reports/01_bib-references-research.md]
- **Plan**: [123_add_bib_references_pr1/plans/01_bib-references-plan.md]
- **Summary**: [123_add_bib_references_pr1/summaries/01_bib-references-summary.md]

---

### 64. Pr6 completeness theorem
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: Submit PRs
- **Dependencies**: Task 63

---

### 63. Pr5 chronicle infrastructure
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: Submit PRs
- **Dependencies**: Task 62

---

### 62. Pr4 temporal metalogic core
- **Status**: [RESEARCHED]
- **Task Type**: lean4
- **Topic**: Submit PRs
- **Dependencies**: Task 61
- **Research_report**: [062_pr4_temporal_metalogic_core/reports/01_pr4-subdivision.md]

---

### 61. Pr3 temporal proof system
- **Status**: [EXPANDED]
- **Task Type**: lean4
- **Topic**: Submit PRs
- **Dependencies**: None
- **Research_report**: [061_pr3_temporal_proof_system/reports/01_temporal-proof-pr-division.md]
- **Plan**: [061_pr3_temporal_proof_system/plans/01_temporal-proof-pr-division.md]

---

### 60. Pr2 modal metalogic
- **Status**: [EXPANDED]
- **Task Type**: lean4
- **Topic**: Submit PRs
- **Dependencies**: None
- **Research**:
  - [060_pr2_modal_metalogic/reports/01_team-research.md]
  - [060_pr2_modal_metalogic/reports/02_pr2-preparation.md]
- **Plan**: [060_pr2_modal_metalogic/plans/02_pr2-preparation.md]

---

### 41. Abstract completeness infrastructure
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: Foundations
- **Dependencies**: Task 38, Task 39, Task 40

**Description**: Abstract shared completeness infrastructure between temporal and bimodal logic once concrete completeness proofs are finished for both.

The temporal (tasks 31, 38, 39) and bimodal (tasks 34, 35) completeness proofs share structural patterns that can be factored into a generic completeness scaffold in Cslib/Foundations/Logic/Metalogic/, extending the existing generic MCS framework (Task 29).

Candidate abstractions (to be confirmed once concrete implementations exist):
1. Generic neg_consistent_of_not_derivable: if φ is not derivable then {¬φ} is consistent — identical structure in both logics, parameterized over DerivationSystem
2. Generic completeness contrapositive skeleton: not derivable → consistent → Lindenbaum → MCS → canonical model → countermodel — the overall proof shape is shared
3. Dense/discrete case split pattern: the three-way case split on □(F'T) / □(U(T,⊥)) / mixed is structurally similar (temporal uses G/H instead of □)
4. Canonical order construction patterns: both define canonical_lt via G-sets (temporal) or box-sets (bimodal); the linearity/irreflexivity/transitivity proofs follow parallel structures
5. Dense indicator elimination: both dense completeness proofs eliminate the non-dense branch by showing the dense indicator axiom is a theorem — identical pattern

Scope: Identify which abstractions yield genuine code savings vs. premature generalization, implement those that do, and refactor both temporal and bimodal completeness to use the shared infrastructure.

Target: Cslib/Foundations/Logic/Metalogic/Completeness.lean (or similar)
Depends on: Tasks 35 (dense bimodal), 38 (dense temporal), 39 (discrete temporal) — transitively includes 31 (base temporal) and 34 (base bimodal MCS)

---

### 40. Temporal continuous completeness
- **Status**: [BLOCKED]
- **Task Type**: lean4
- **Topic**: Temporal Logic
- **Dependencies**: Task 37

**Description**: Continuous temporal completeness: completeness for temporal logic over Dedekind-complete (continuous) linear orders, e.g. the reals.

Scope: Define a Continuous frame class extending Dense, add any required axioms (e.g., Dedekind completeness schema or equivalent), prove soundness over conditionally complete linear orders, prove completeness via canonical model on Real or equivalent.

Blocked: The continuous case has not been developed for either the temporal or bimodal logic upstream. Requires foundational research into which additional axioms (if any) are needed beyond density to characterize continuous time. The standard result (Burgess 1982) is that the Until/Since temporal logic over the reals has the same theorems as over the rationals (density suffices), which would make this task trivial — but this equivalence itself needs to be formalized.

Target: Cslib/Logics/Temporal/Metalogic/ContinuousCompleteness.lean
Blocker: Research needed on whether continuous frames require additional axioms beyond density

---

### 39. Temporal discrete completeness
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: Temporal Logic
- **Dependencies**: Task 36

**Description**: Discrete temporal completeness: prove that every formula valid on all discrete serial linear orders is derivable in the Discrete temporal proof system.

Scope:
1. Add discrete-specific axioms to Temporal.Axiom: `prior_UZ` (F(φ) → U(φ,¬φ)), `prior_SZ` (P(φ) → S(φ,¬φ)), `z1` (G(Gφ→φ) → (F(Gφ)→Gφ)), and discrete uniformity axioms (discrete_symm_fwd/bwd, discrete_propagate_fwd/bwd), gated to FrameClass.Discrete via minFrameClass.
2. Prove discrete soundness: each discrete axiom valid on SuccOrder+PredOrder+IsSuccArchimedean.
3. Prove discrete completeness via contrapositive + MCS + canonical model on Int. The non-discrete branch is eliminated by deriving U(⊤,⊥) as a Discrete theorem.

New development (not a port). The canonical model specializes the base temporal canonical order to Int. The discrete uniformity axioms (minus discrete_box_necessity which is bimodal-only) ensure U(⊤,⊥) propagates uniformly.

Target: Cslib/Logics/Temporal/Metalogic/DiscreteCompleteness.lean + axiom additions to Axioms.lean
Estimated scope: ~500-700 lines (new axioms + discrete soundness + discrete completeness)

---

### 38. Temporal dense completeness
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Topic**: Temporal Logic
- **Dependencies**: None

**Description**: Dense temporal completeness: prove that every formula valid on all dense serial linear orders is derivable in the Dense temporal proof system.

Scope:
1. Add dense-specific axioms to Temporal.Axiom: `density` (G(G φ) → G φ) and `dense_indicator` (¬U(⊤,⊥)), gated to FrameClass.Dense via minFrameClass.
2. Prove dense soundness: density axiom valid on DenselyOrdered, dense_indicator valid on DenselyOrdered (no immediate successor).
3. Prove dense completeness via contrapositive + MCS + canonical model on Rat. The dense case eliminates the non-dense branch by deriving ¬U(⊤,⊥) as a Dense theorem, so □(¬U(⊤,⊥)) is in every Dense-MCS.

New development (not a port), following the pattern established by bimodal completeness_dense. The canonical model construction reuses the base temporal canonical order from task 31, specialized to Rat (DenselyOrdered).

Target: Cslib/Logics/Temporal/Metalogic/DenseCompleteness.lean + axiom additions to Axioms.lean
Estimated scope: ~400-600 lines (new axioms + dense soundness + dense completeness)

---

### 37. Port continuous completeness bimodal
- **Status**: [BLOCKED]
- **Task Type**: lean4
- **Topic**: Bimodal Porting
- **Dependencies**: Task BimodalLogic:continuous_extension

**Description**: Port continuous extension completeness once developed upstream. The continuous case (FrameClass for continuous/real-valued time) has not been started in BimodalLogic. This task is blocked pending upstream development of continuous frame completeness.

**Source**: Not yet developed in BimodalLogic
**Target**: Cslib/Logics/Bimodal/Metalogic/
**Blocker**: Upstream BimodalLogic continuous extension development
**Parent task**: 8 (expanded)

---

### 36. Port discrete completeness bimodal
- **Status**: [BLOCKED]
- **Task Type**: lean4
- **Topic**: Bimodal Porting
- **Dependencies**: Task BimodalLogic:discrete_sorry_elimination

**Description**: Port discrete completeness (completeness_discrete theorem) and WeakCanonical/IntegerModel/ infrastructure (~6 files). The discrete branch constructs countermodels on Int via the Reynolds pipeline. Currently blocked: upstream BimodalLogic has sorryAx tracing through chronicle_gap_contradiction → succ_cofinal → limitDomSubtype_isSuccArchimedean → succ_embed_surjective. Port after upstream sorry elimination completes.

**Source**: BimodalLogic/Theories/Bimodal/Metalogic/WeakCanonical/IntegerModel/ (~6 files), discrete branch of BXCanonical/Completeness.lean
**Target**: Cslib/Logics/Bimodal/Metalogic/
**Blocker**: Upstream BimodalLogic discrete completeness sorry elimination (36 sorries across IntegerModel/)
**Parent task**: 8 (expanded)

---

### 12. Coordinate cslib pr submission bimodal logic
- **Status**: [EXPANDED]
- **Task Type**: general
- **Topic**: Project Management
- **Dependencies**: Task 41

**Description**: Coordinate the cslib PR submission process for the modular logic integration (standalone modules + bimodal). This task runs in parallel with porting tasks and handles maintainer communication, namespace decisions, and CI compliance.

**Standalone Module PRs** (can proceed in parallel with bimodal PRs since they target different directories):
- PR-Foundations (Task 20): Propositional Hilbert theorems to Cslib/Foundations/Logic/Theorems/ -- Wave 1, no dependencies
- PR-Modal (Task 21): Modal proof system + theorems to Cslib/Logics/Modal/ProofSystem/ + Theorems/ -- after PR-Foundations
- PR-Temporal-Infra (Task 22): Temporal infrastructure + theorems to Cslib/Logics/Temporal/ProofSystem/ + Theorems/ -- after PR-Foundations
- PR-TempSem (Task 23): Temporal semantics to Cslib/Logics/Temporal/Semantics/ -- after PR-Temporal-Infra

**Bimodal PRs** (in dependency order):
- PR 1 (Bimodal Syntax, task 2): submit first, establish review pattern
- PR 2 (Semantics, task 3) and PR 3 (ProofSystem, task 4): after PR 1 merged, can overlap
- PR 4 (Perpetuity Theorems, task 5): after PRs 3, PR-Modal, PR-Temporal-Infra merged
- PR 5 (FrameConditions+Soundness, task 6): after PRs 2+3 merged
- PR 6 (MCS/Deduction, task 7): after PRs 3+4 merged
- PR 7 (Completeness, task 8): after PRs 5+6 merged
- PR 8 (Decidability, task 9): after PRs 3+6 merged (largest PR, ~10k lines)
- PR 9 (Separation, task 10): after PRs 3+4+6 merged
- PR 10 (ConservativeExtension, task 11): after PR 3 merged (independent of 5-9)

**Coordination Workflow**:

1. **Open Zulip Discussion** (first step): propose modular architecture (standalone Foundations/Modal/Temporal modules + Bimodal), PR strategy (4 standalone PRs + 10 bimodal PRs)
2. **Namespace Decision**: confirm before starting task 2
3. **CI Checks** (before each PR): lake build, lake shake, linter.all, zero sorry, Apache 2.0 headers
4. **Review Cycle**: keep PRs small (max ~3,500 lines); address feedback within 48 hours
