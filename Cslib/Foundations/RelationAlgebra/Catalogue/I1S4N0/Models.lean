/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Models000
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Models001
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Models002
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Models003
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Models004
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Models005
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Models006
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Models007
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Models008
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Models009
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Models010
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Models011
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Models012
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Models013
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Models014
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Models015
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Models016
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Models017
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Models018
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Models019
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Models020
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Models021
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Models022
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Models023
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Models024
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Models025
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Models026
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Models027
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Models028
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Models029
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Models030
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Models031
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Models032
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Models033
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Models034
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Models035
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Models036
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Models037
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Models038
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Models039
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Models040
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Models041
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Models042
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Models043
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Models044
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Models045
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Models046
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Models047

/-!
# Certified model dispatch for the ⟨1, 4, 0⟩ row

The two-level array selects the named entries in consecutive blocks of 64. The profile
alignment theorem checks every index, including the final partial block.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Models

/-- A total lookup default; every valid index is checked to select its own entry. -/
def fallback : ProfiledCycleTable Data.cycleReps :=
  ProfiledCycleTable.ofEncoded Data.cycleReps
    { table := Ra0001.table, code := 4074513065921488898219576396966268993,
      encodes := Ra0001.tableCode_eq ▸ encodesTable_tableCode Ra0001.cycles }
    1009 (by decide +kernel)

/-- Consecutive blocks containing all explicitly named models. -/
def blocks : Array (Array (ProfiledCycleTable Data.cycleReps)) :=
  #[Models000.entries,
    Models001.entries,
    Models002.entries,
    Models003.entries,
    Models004.entries,
    Models005.entries,
    Models006.entries,
    Models007.entries,
    Models008.entries,
    Models009.entries,
    Models010.entries,
    Models011.entries,
    Models012.entries,
    Models013.entries,
    Models014.entries,
    Models015.entries,
    Models016.entries,
    Models017.entries,
    Models018.entries,
    Models019.entries,
    Models020.entries,
    Models021.entries,
    Models022.entries,
    Models023.entries,
    Models024.entries,
    Models025.entries,
    Models026.entries,
    Models027.entries,
    Models028.entries,
    Models029.entries,
    Models030.entries,
    Models031.entries,
    Models032.entries,
    Models033.entries,
    Models034.entries,
    Models035.entries,
    Models036.entries,
    Models037.entries,
    Models038.entries,
    Models039.entries,
    Models040.entries,
    Models041.entries,
    Models042.entries,
    Models043.entries,
    Models044.entries,
    Models045.entries,
    Models046.entries,
    Models047.entries]

/-- Select a certified model by its zero-based catalogue index. -/
def get (i : ℕ) : ProfiledCycleTable Data.cycleReps :=
  (blocks.getD (i / 64) #[]).getD (i % 64) fallback

/-- Each valid model index selects the corresponding canonical profile. -/
theorem get_profile : ∀ i : Fin 3013, (get i.val).profile = Data.canonicalMask i.val := by
  apply forall_of_blocks (n := 3013)
    (property := fun i => (get i).profile = Data.canonicalMask i)
  intro b i
  have hi : i.val < 64 := lt_of_lt_of_le i.isLt (min_le_left _ _)
  have hd : (b.val * 64 + i.val) / 64 = b.val := by omega
  have hm : (b.val * 64 + i.val) % 64 = i.val := by omega
  simp only [get, hd, hm]
  fin_cases b
  · exact Models000.entries_profile fallback i
  · exact Models001.entries_profile fallback i
  · exact Models002.entries_profile fallback i
  · exact Models003.entries_profile fallback i
  · exact Models004.entries_profile fallback i
  · exact Models005.entries_profile fallback i
  · exact Models006.entries_profile fallback i
  · exact Models007.entries_profile fallback i
  · exact Models008.entries_profile fallback i
  · exact Models009.entries_profile fallback i
  · exact Models010.entries_profile fallback i
  · exact Models011.entries_profile fallback i
  · exact Models012.entries_profile fallback i
  · exact Models013.entries_profile fallback i
  · exact Models014.entries_profile fallback i
  · exact Models015.entries_profile fallback i
  · exact Models016.entries_profile fallback i
  · exact Models017.entries_profile fallback i
  · exact Models018.entries_profile fallback i
  · exact Models019.entries_profile fallback i
  · exact Models020.entries_profile fallback i
  · exact Models021.entries_profile fallback i
  · exact Models022.entries_profile fallback i
  · exact Models023.entries_profile fallback i
  · exact Models024.entries_profile fallback i
  · exact Models025.entries_profile fallback i
  · exact Models026.entries_profile fallback i
  · exact Models027.entries_profile fallback i
  · exact Models028.entries_profile fallback i
  · exact Models029.entries_profile fallback i
  · exact Models030.entries_profile fallback i
  · exact Models031.entries_profile fallback i
  · exact Models032.entries_profile fallback i
  · exact Models033.entries_profile fallback i
  · exact Models034.entries_profile fallback i
  · exact Models035.entries_profile fallback i
  · exact Models036.entries_profile fallback i
  · exact Models037.entries_profile fallback i
  · exact Models038.entries_profile fallback i
  · exact Models039.entries_profile fallback i
  · exact Models040.entries_profile fallback i
  · exact Models041.entries_profile fallback i
  · exact Models042.entries_profile fallback i
  · exact Models043.entries_profile fallback i
  · exact Models044.entries_profile fallback i
  · exact Models045.entries_profile fallback i
  · exact Models046.entries_profile fallback i
  · exact Models047.entries_profile fallback i

/-- All packed profiles are the corresponding permutations of the canonical mask. -/
theorem profiles_eq : ∀ i : Fin 3013, ∀ p : Fin 24,
    Data.profiles i.val p.val =
      Code.permuteProfile (Data.canonicalMask i.val) (Data.orbitAction p) := by
  apply forall_of_blocks (n := 3013)
    (property := fun i => ∀ p : Fin 24, Data.profiles i p.val =
      Code.permuteProfile (Data.canonicalMask i) (Data.orbitAction p))
  intro b i
  fin_cases b
  · exact Models000.profiles_eq i
  · exact Models001.profiles_eq i
  · exact Models002.profiles_eq i
  · exact Models003.profiles_eq i
  · exact Models004.profiles_eq i
  · exact Models005.profiles_eq i
  · exact Models006.profiles_eq i
  · exact Models007.profiles_eq i
  · exact Models008.profiles_eq i
  · exact Models009.profiles_eq i
  · exact Models010.profiles_eq i
  · exact Models011.profiles_eq i
  · exact Models012.profiles_eq i
  · exact Models013.profiles_eq i
  · exact Models014.profiles_eq i
  · exact Models015.profiles_eq i
  · exact Models016.profiles_eq i
  · exact Models017.profiles_eq i
  · exact Models018.profiles_eq i
  · exact Models019.profiles_eq i
  · exact Models020.profiles_eq i
  · exact Models021.profiles_eq i
  · exact Models022.profiles_eq i
  · exact Models023.profiles_eq i
  · exact Models024.profiles_eq i
  · exact Models025.profiles_eq i
  · exact Models026.profiles_eq i
  · exact Models027.profiles_eq i
  · exact Models028.profiles_eq i
  · exact Models029.profiles_eq i
  · exact Models030.profiles_eq i
  · exact Models031.profiles_eq i
  · exact Models032.profiles_eq i
  · exact Models033.profiles_eq i
  · exact Models034.profiles_eq i
  · exact Models035.profiles_eq i
  · exact Models036.profiles_eq i
  · exact Models037.profiles_eq i
  · exact Models038.profiles_eq i
  · exact Models039.profiles_eq i
  · exact Models040.profiles_eq i
  · exact Models041.profiles_eq i
  · exact Models042.profiles_eq i
  · exact Models043.profiles_eq i
  · exact Models044.profiles_eq i
  · exact Models045.profiles_eq i
  · exact Models046.profiles_eq i
  · exact Models047.profiles_eq i

/-- The canonical profile of each model is least under atom renaming. -/
theorem profiles_minimal : ∀ i : Fin 3013, ∀ p : Fin 24,
    Data.profiles i.val 0 ≤ Data.profiles i.val p.val := by
  apply forall_of_blocks (n := 3013)
    (property := fun i => ∀ p : Fin 24, Data.profiles i 0 ≤ Data.profiles i p.val)
  intro b i
  fin_cases b
  · exact Models000.profiles_minimal i
  · exact Models001.profiles_minimal i
  · exact Models002.profiles_minimal i
  · exact Models003.profiles_minimal i
  · exact Models004.profiles_minimal i
  · exact Models005.profiles_minimal i
  · exact Models006.profiles_minimal i
  · exact Models007.profiles_minimal i
  · exact Models008.profiles_minimal i
  · exact Models009.profiles_minimal i
  · exact Models010.profiles_minimal i
  · exact Models011.profiles_minimal i
  · exact Models012.profiles_minimal i
  · exact Models013.profiles_minimal i
  · exact Models014.profiles_minimal i
  · exact Models015.profiles_minimal i
  · exact Models016.profiles_minimal i
  · exact Models017.profiles_minimal i
  · exact Models018.profiles_minimal i
  · exact Models019.profiles_minimal i
  · exact Models020.profiles_minimal i
  · exact Models021.profiles_minimal i
  · exact Models022.profiles_minimal i
  · exact Models023.profiles_minimal i
  · exact Models024.profiles_minimal i
  · exact Models025.profiles_minimal i
  · exact Models026.profiles_minimal i
  · exact Models027.profiles_minimal i
  · exact Models028.profiles_minimal i
  · exact Models029.profiles_minimal i
  · exact Models030.profiles_minimal i
  · exact Models031.profiles_minimal i
  · exact Models032.profiles_minimal i
  · exact Models033.profiles_minimal i
  · exact Models034.profiles_minimal i
  · exact Models035.profiles_minimal i
  · exact Models036.profiles_minimal i
  · exact Models037.profiles_minimal i
  · exact Models038.profiles_minimal i
  · exact Models039.profiles_minimal i
  · exact Models040.profiles_minimal i
  · exact Models041.profiles_minimal i
  · exact Models042.profiles_minimal i
  · exact Models043.profiles_minimal i
  · exact Models044.profiles_minimal i
  · exact Models045.profiles_minimal i
  · exact Models046.profiles_minimal i
  · exact Models047.profiles_minimal i

/-- Identity renaming reads exactly the increasing canonical masks. -/
theorem profiles_zero : ∀ i : Fin 3013, Data.profiles i.val 0 = Data.canonicalMask i.val := by
  apply forall_of_blocks (n := 3013)
    (property := fun i => Data.profiles i 0 = Data.canonicalMask i)
  intro b i
  fin_cases b
  · exact Models000.profiles_zero i
  · exact Models001.profiles_zero i
  · exact Models002.profiles_zero i
  · exact Models003.profiles_zero i
  · exact Models004.profiles_zero i
  · exact Models005.profiles_zero i
  · exact Models006.profiles_zero i
  · exact Models007.profiles_zero i
  · exact Models008.profiles_zero i
  · exact Models009.profiles_zero i
  · exact Models010.profiles_zero i
  · exact Models011.profiles_zero i
  · exact Models012.profiles_zero i
  · exact Models013.profiles_zero i
  · exact Models014.profiles_zero i
  · exact Models015.profiles_zero i
  · exact Models016.profiles_zero i
  · exact Models017.profiles_zero i
  · exact Models018.profiles_zero i
  · exact Models019.profiles_zero i
  · exact Models020.profiles_zero i
  · exact Models021.profiles_zero i
  · exact Models022.profiles_zero i
  · exact Models023.profiles_zero i
  · exact Models024.profiles_zero i
  · exact Models025.profiles_zero i
  · exact Models026.profiles_zero i
  · exact Models027.profiles_zero i
  · exact Models028.profiles_zero i
  · exact Models029.profiles_zero i
  · exact Models030.profiles_zero i
  · exact Models031.profiles_zero i
  · exact Models032.profiles_zero i
  · exact Models033.profiles_zero i
  · exact Models034.profiles_zero i
  · exact Models035.profiles_zero i
  · exact Models036.profiles_zero i
  · exact Models037.profiles_zero i
  · exact Models038.profiles_zero i
  · exact Models039.profiles_zero i
  · exact Models040.profiles_zero i
  · exact Models041.profiles_zero i
  · exact Models042.profiles_zero i
  · exact Models043.profiles_zero i
  · exact Models044.profiles_zero i
  · exact Models045.profiles_zero i
  · exact Models046.profiles_zero i
  · exact Models047.profiles_zero i

/-- Canonical masks increase strictly with the catalogue index. -/
theorem canonicalMask_strictMono : StrictMono (fun i : Fin 3013 => Data.canonicalMask i.val) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have h : ∀ i : Fin 3012, Data.canonicalMask i.val < Data.canonicalMask (i.val + 1) := by
    apply forall_of_blocks (n := 3012)
      (property := fun i => Data.canonicalMask i < Data.canonicalMask (i + 1))
    intro b i
    fin_cases b
    · exact Models000.canonicalMask_increasing i
    · exact Models001.canonicalMask_increasing i
    · exact Models002.canonicalMask_increasing i
    · exact Models003.canonicalMask_increasing i
    · exact Models004.canonicalMask_increasing i
    · exact Models005.canonicalMask_increasing i
    · exact Models006.canonicalMask_increasing i
    · exact Models007.canonicalMask_increasing i
    · exact Models008.canonicalMask_increasing i
    · exact Models009.canonicalMask_increasing i
    · exact Models010.canonicalMask_increasing i
    · exact Models011.canonicalMask_increasing i
    · exact Models012.canonicalMask_increasing i
    · exact Models013.canonicalMask_increasing i
    · exact Models014.canonicalMask_increasing i
    · exact Models015.canonicalMask_increasing i
    · exact Models016.canonicalMask_increasing i
    · exact Models017.canonicalMask_increasing i
    · exact Models018.canonicalMask_increasing i
    · exact Models019.canonicalMask_increasing i
    · exact Models020.canonicalMask_increasing i
    · exact Models021.canonicalMask_increasing i
    · exact Models022.canonicalMask_increasing i
    · exact Models023.canonicalMask_increasing i
    · exact Models024.canonicalMask_increasing i
    · exact Models025.canonicalMask_increasing i
    · exact Models026.canonicalMask_increasing i
    · exact Models027.canonicalMask_increasing i
    · exact Models028.canonicalMask_increasing i
    · exact Models029.canonicalMask_increasing i
    · exact Models030.canonicalMask_increasing i
    · exact Models031.canonicalMask_increasing i
    · exact Models032.canonicalMask_increasing i
    · exact Models033.canonicalMask_increasing i
    · exact Models034.canonicalMask_increasing i
    · exact Models035.canonicalMask_increasing i
    · exact Models036.canonicalMask_increasing i
    · exact Models037.canonicalMask_increasing i
    · exact Models038.canonicalMask_increasing i
    · exact Models039.canonicalMask_increasing i
    · exact Models040.canonicalMask_increasing i
    · exact Models041.canonicalMask_increasing i
    · exact Models042.canonicalMask_increasing i
    · exact Models043.canonicalMask_increasing i
    · exact Models044.canonicalMask_increasing i
    · exact Models045.canonicalMask_increasing i
    · exact Models046.canonicalMask_increasing i
    · exact Models047.canonicalMask_increasing i
  exact h

/-- Packed numeric profiles equal the profiles of the actual explicitly defined cycle tables. -/
theorem profiles_spec (i : Fin 3013) (p : Fin 24) :
    choiceMask (fun c => decide (cycleClosure (get i.val).table.cycles
      (Data.rename p (some (Data.cycleReps c).1))
      (Data.rename p (some (Data.cycleReps c).2.1))
      (Data.rename p (some (Data.cycleReps c).2.2)))) = Data.profiles i.val p.val := by
  have hbase := (get i.val).profile_eq
  rw [get_profile i] at hbase
  exact (profileCode_eq_of_orbit_renaming Data.cycleReps (get i.val).table.cycles
    (Data.renameDiversity p) (Data.orbitAction p) (Data.orbitAction_spec p)
    (Data.canonicalMask i.val) hbase).trans (profiles_eq i p).symm

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Models
