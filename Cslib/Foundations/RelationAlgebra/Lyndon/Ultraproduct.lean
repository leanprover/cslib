/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.AtomStructure.FilterProduct
public import Cslib.Foundations.RelationAlgebra.Lyndon.Representation

/-!
# Ultraproducts of Lyndon algebras

Lyndon's atom structure is defined from equality and the distinguished element alone, so an
ultraproduct of Lyndon atom structures is again a Lyndon atom structure. Consequently an
ultraproduct of Lyndon algebras embeds into a Lyndon algebra, and is representable over a group as
soon as the ultraproduct of the types of atoms is infinite. This is the positive half of the proof
of Theorem 1 of [Monk1964].

## References

* [J. D. Monk, *On representable relation algebras*][Monk1964]

-/

@[expose] public section

universe u v

namespace Cslib.RelationAlgebra

open AtomStructure Filter.Product

variable {ι : Type v} {α : ι → Type u} (e : ∀ i, α i) (h : ∀ i, 5 ≤ ENat.card (α i))
  (U : Ultrafilter ι)

/-- An ultraproduct of Lyndon atom structures is the Lyndon atom structure on the ultraproduct of
the types of atoms. -/
theorem AtomStructure.filterProduct_lyndon (h' : 5 ≤ ENat.card ((U : Filter ι).Product α)) :
    filterProduct (fun i => lyndon (e i) (h i)) (U : Filter ι) =
      lyndon (Filter.Product.mk (U : Filter ι) e) h' := by
  apply AtomStructure.ext
  · funext x
    induction x using induction_on with | h f
    rfl
  · ext x
    induction x using induction_on with | h f
    refine (mk_mem_filterProductId _ _).trans ?_
    simp only [lyndon_id, Set.mem_singleton_iff, mk_eq_mk]
  · ext ⟨x, y, z⟩
    induction x using induction_on with | h f
    induction y using induction_on with | h g
    induction z using induction_on with | h k
    refine (mk_mem_filterProductCycles _ _).trans ?_
    simp only [lyndon_cycles, mem_lyndonCycles, ne_eq, mk_eq_mk, Ultrafilter.eventually_or,
      Filter.eventually_and, Ultrafilter.eventually_not]

/-- An ultraproduct of Lyndon algebras is representable over a group when the ultraproduct of the
types of atoms is infinite. -/
theorem groupRepresentable_product_lyndon [Infinite ((U : Filter ι).Product α)] :
    GroupRepresentable ((U : Filter ι).Product fun i => ComplexAlgebra (lyndon (e i) (h i))) := by
  have : ∀ i, Nonempty (α i) := fun i => ⟨e i⟩
  have h' : 5 ≤ ENat.card ((U : Filter ι).Product α) := by
    rw [ENat.card_eq_top_of_infinite]
    exact le_top
  refine .of_injective (ComplexAlgebra.productHom _ U) (ComplexAlgebra.productHom_injective _ U) ?_
  rw [filterProduct_lyndon e h U h']
  exact groupRepresentable_lyndon _ h'

end Cslib.RelationAlgebra
