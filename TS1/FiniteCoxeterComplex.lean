import TS1.FiniteOrderedPartitions
import TS1.AbstractSimplicialComplex
import TS1.preorder_to_powerset

set_option autoImplicit false


universe u


variable (α : Type u) 

namespace FiniteCoxeterComplex

open AbstractSimplicialComplex Preorder

def Faces : Set (Finset (Set α)) := {E | Total (fun (X : E) => fun (Y : E) => X.1 ⊆ Y.1) ∧ ∀ (X : E), X.1 ≠ ⊥ ∧ X.1 ≠ ⊤}

lemma Faces_down_closed : ∀ {E F : Finset (Set α)}, E ∈ Faces α → F ⊆ E → F ∈ Faces α := by 
  intro E F hE hFE 
  constructor
  . intro X Y 
    have hXE : X.1 ∈ E := hFE X.2
    have hYE : Y.1 ∈ E := hFE Y.2
    exact hE.1 ⟨X.1, hXE⟩ ⟨Y.1, hYE⟩
  . intro X 
    have hXE : X.1 ∈ E := hFE X.2
    exact hE.2 ⟨X.1, hXE⟩ 

def CoxeterComplex  := of_erase (Faces α) (Faces_down_closed α)

-- Let's assume α finite.
variable [Fintype α]


/- The set Faces α is in order-reversing bijection with the set of inearly ordered partitions of α. (If α is not finite, we have to use
finite linearly ordered partitions with finite proper initial intervals.)-/



def CoxeterComplextoPartitions : OrderIso (Faces α) (LinearOrderedPartitions α)ᵒᵈ where
toFun := fun E => ⟨powersetToPreorder E.1, powersetToPreorder_total_is_total E.2.1⟩
invFun := fun p => sorry -- ⟨preorderToPowerset p.1, preorderToPowerset_total_is_total p.2⟩ 
left_inv := sorry 
right_inv := sorry 
map_rel_iff' := sorry



/- The facets of the Coxeter complex correspond to linear orders on α. (If α is infinite, the Coxeter complex has no facets, and the linear orders
will define maximal ideals of the face poset of the Coxeter complex, though we don't get all maximal ideals this way.)-/




end FiniteCoxeterComplex
