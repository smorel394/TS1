import Mathlib.Tactic 
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.CategoryTheory.ConcreteCategory.Bundled
import Mathlib.CategoryTheory.ConcreteCategory.BundledHom

universe u v 

open Classical 

@[ext]
structure AbstractSimplicialComplex (α : Type u) :=
(faces : Set (Finset V))
(nonempty_of_mem : ∀ {s : Finset V}, s ∈ faces → s.Nonempty)
(down_closed : ∀ {s t : Finset V}, s ∈ faces → t ⊆ s → t.Nonempty → t ∈ faces)

instance : Membership (Finset α) (AbstractSimplicialComplex α) := ⟨fun s K => s ∈ K.faces⟩ 


def AbstractSimplicialComplex.vertices (K : AbstractSimplicialComplex α) : Set α := {v : α | {v} ∈ K}



noncomputable def face_to_finset_vertices {K : AbstractSimplicialComplex α} (s : Finset α) : Finset (K.vertices) := 
s.subtype (fun a => a ∈ K.vertices)

@[ext]
structure SimplicialMap {α : Type u} {β : Type v} (K : AbstractSimplicialComplex α) (L : AbstractSimplicialComplex β) :=
(vertex_map : K.vertices → L.vertices)
(face : ∀ (s : K.faces), Finset.image (fun a => ↑(vertex_map a)) (face_to_finset_vertices s.1) ∈ L.faces)

@[nolint checkUnivs]
def AbstractSimplicialComplexCat :=
  Bundled AbstractSimplicialComplex.{u}


namespace AbstractSimplicialComplexCat

instance : CoeSort AbstractSimplicialComplexCat (Type u) where coe := Bundled.α

/-- Construct a bundled `AbstractSimplicialComplexCat` from the underlying type and the typeclass. -/
def of (V : Type u) (K : AbstractSimplicialComplex V) : AbstractSimplicialComplexCat.{u} :=
  @Bundled.of _ V K 

/-Not used.
lemma complex_of (α : Type u) (K : AbstractSimplicialComplex α) : (of α K).2 = K := sorry 
-/

instance : Inhabited AbstractSimplicialComplexCat :=
  ⟨AbstractSimplicialComplexCat.of Empty (@AbstractSimplicialComplex.Bot Empty).1⟩


/-- Morphisms. --/
protected def Hom (C D : AbstractSimplicialComplexCat) :=
  C.2 →ₛ D.2  

/-- Make a morphism from a simplicial map. -/
def mk {C D : AbstractSimplicialComplexCat} (f : C.2 →ₛ D.2) : AbstractSimplicialComplexCat.Hom C D :=
  f

/-- Category structure on `AbstractSimplicialComplexCat` -/
noncomputable instance category : LargeCategory.{u} AbstractSimplicialComplexCat.{u}
    where
  Hom C D := AbstractSimplicialComplexCat.Hom C D 
  id C := SimplicialMap.id C.2 
  comp F G := SimplicialMap.comp G F  


  
