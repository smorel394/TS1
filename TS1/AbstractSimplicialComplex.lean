-- Lean4 version
/-
Copyright (c) 2022 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel

Adapted from the Lean3 file of Shing Tak Lam.
-/

import Mathlib.Tactic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Data.ENat.Basic 
import Mathlib.Data.Set.Lattice
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Nat.PartENat



open Classical 


/-!
# Abstract Simplicial Complex

In this file, we define abstract simplicial complexes over a vertex set `V`. An abstract simplicial
complex is collection of simplices which is closed by inclusion (of vertices).

We model them as downwards-closed collections of finite subsets of `V`.

## Main definitions

* `AbstractSimplicialComplex V`: An abstract simplicial complex with vertices in `V`.
* `AbstractSimplicialComplex.vertices`: The zero dimensional faces of a simplicial complex.
* `AbstractSimplicialComplex.facets`: The maximal faces of a simplicial complex.
* `SimplicialMap K L`: Simplicial maps from a simplicial complex `K` to another
  simplicial complex `L`.

## Notation

* `s ∈ K` means `s` is a face of `K`.
* `K ≤ L` means that `K` is a subcomplex of `L`. That is, all faces of `K` are faces of `L`.
* `K →ₛ L` is a `simplicial_map K L`.

## TODO (maybe)

* `geometry.simplicial_complex` can `extend AbstractSimplicialComplex`.
* Define the geometric realisation of an abstract simplicial complex.

-/

set_option autoImplicit false


universe u v w


@[ext]
structure AbstractSimplicialComplex (V : Type u) :=
(faces : Set (Finset V))
(nonempty_of_mem : ∀ {s : Finset V}, s ∈ faces → s.Nonempty)
(down_closed : ∀ {s t : Finset V}, s ∈ faces → t ⊆ s → t.Nonempty → t ∈ faces)


namespace AbstractSimplicialComplex

variable {V : Type u}

instance : Membership (Finset V) (AbstractSimplicialComplex V) := ⟨fun s K => s ∈ K.faces⟩ 


/-- Construct an abstract simplicial complex by removing the empty face for you. -/
@[simps!] def of_erase
  (faces : Set (Finset V))
  (down_closed : ∀ {s t : Finset V}, s ∈ faces → t ⊆ s → t ∈ faces) :
  AbstractSimplicialComplex V :=
{ faces := faces \ {∅},
  nonempty_of_mem := fun h => by simp only [Set.mem_diff, Set.mem_singleton_iff] at h;
                                 rw [←ne_eq, ←Finset.nonempty_iff_ne_empty] at h
                                 exact h.2   
  down_closed := fun hs hts ht => ⟨down_closed hs.1 hts, by rw [Finset.nonempty_iff_ne_empty, ne_eq] at ht; exact ht⟩} 


/-- Construct an abstract simplicial complex as a subset of a given abstract simplicial complex. -/
@[simps] def of_subcomplex (K : AbstractSimplicialComplex V)
  (faces : Set (Finset V))
  (subset : faces ⊆ K.faces)
  (down_closed : ∀ {s t}, s ∈ faces → t ⊆ s → t.Nonempty → t ∈ faces) :
  AbstractSimplicialComplex V :=
{ faces := faces
  nonempty_of_mem := fun h => K.nonempty_of_mem (subset h)
  down_closed := fun hs hts ht => down_closed hs hts ht}
  

/- Faces have nonzero cardinality.-/

lemma face_card_nonzero {K : AbstractSimplicialComplex V} {s : Finset V} (hsf : s ∈ K.faces) : Finset.card s ≠ 0 := by 
  cases K.nonempty_of_mem hsf with
  |intro _ has => exact Finset.card_ne_zero_of_mem has 


/- Vertices are the element a of V such that {a} is a face.-/

def vertices (K : AbstractSimplicialComplex V) : Set V := {v : V | {v} ∈ K}

lemma mem_vertices (K : AbstractSimplicialComplex V) (v : V) : v ∈ K.vertices ↔ {v} ∈ K := Iff.rfl

lemma vertices_eq (K : AbstractSimplicialComplex V) : K.vertices = ⋃ s ∈ K.faces, (s : Set V) := by
  ext v
  constructor
  . intro hv
    rw [Set.mem_iUnion]
    simp only [Set.mem_iUnion, Finset.mem_coe, exists_prop]
    exists {v}
    exact ⟨hv, Finset.mem_singleton_self v⟩
  . intro hv
    rw [Set.mem_iUnion] at hv
    simp only [Set.mem_iUnion, Finset.mem_coe, exists_prop] at hv
    match hv with 
    | ⟨s,hsf,hsv⟩ => exact K.down_closed hsf (Finset.singleton_subset_iff.mpr hsv) (Finset.singleton_nonempty v) 


lemma mem_vertices_iff (K : AbstractSimplicialComplex V) (x : V) : x ∈ K.vertices ↔ ∃ (s : K.faces), x ∈ s.1 := by
  rw [mem_vertices]
  constructor
  . exact fun hx => by simp only [Subtype.exists, exists_prop]; exists {x}; exact ⟨hx, Finset.mem_singleton.mpr (Eq.refl x)⟩
  . exact fun hx => by simp only [Subtype.exists, exists_prop] at hx 
                       match hx with
                       |  ⟨s, hsf, hsx⟩ => exact K.down_closed hsf (Finset.singleton_subset_iff.mpr hsx) (Finset.singleton_nonempty _)          



lemma face_subset_vertices (K : AbstractSimplicialComplex V) (s : K.faces) : ↑s.1 ⊆ K.vertices := by 
  rw [vertices_eq]
  have h := Set.subset_iUnion (fun (t : K.faces) => (t : Set V)) s 
  simp only [Set.iUnion_coe_set] at h
  exact h 

noncomputable def face_to_finset_vertices {K : AbstractSimplicialComplex V} (s : K.faces) : Finset (K.vertices) := 
s.1.subtype (fun a => a ∈ K.vertices)

lemma face_to_finset_vertices_mem {K : AbstractSimplicialComplex V} (s : K.faces) (a : V) :
(∃ (hav : a ∈ K.vertices), ⟨a, hav⟩ ∈ (face_to_finset_vertices s)) ↔ a ∈ s.1 := by 
  unfold face_to_finset_vertices
  simp only [Finset.mem_subtype, exists_prop, and_iff_right_iff_imp]
  exact fun has => by rw [mem_vertices_iff]; exists s 

lemma face_to_finset_vertices_mem' {K : AbstractSimplicialComplex V} (s : K.faces) {a : V} (hav : a ∈ K.vertices) :
⟨a, hav⟩ ∈ (face_to_finset_vertices s) ↔ a ∈ s.1 := by 
  unfold face_to_finset_vertices
  simp only [Finset.mem_subtype]


lemma face_to_finset_vertices_eq {K : AbstractSimplicialComplex V} (s : K.faces) :
s.1 = Finset.image (fun a => ↑a) (face_to_finset_vertices s) := by 
  ext a 
  simp only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
  apply Iff.symm 
  exact face_to_finset_vertices_mem _ _ 

/- Facets. -/

def facets (K : AbstractSimplicialComplex V) : Set (Finset V) := {s ∈ K.faces | ∀ ⦃t⦄, t ∈ K.faces → s ⊆ t → s = t}

lemma mem_facets_iff (K : AbstractSimplicialComplex V) (s : Finset V) : s ∈ K.facets ↔ s ∈ K.faces ∧ ∀ ⦃t : Finset V⦄, t ∈ K.faces → s ≤ t → s =t := by 
  unfold facets 
  simp only [Set.mem_setOf_eq, Finset.le_eq_subset]

lemma facets_subset {K : AbstractSimplicialComplex V} {s : Finset V} (hsf : s ∈ K.facets) : s ∈ K.faces := by
  rw [mem_facets_iff] at hsf 
  exact hsf.1 

/- Lattice structure on the set of abstract simplicial complexes: we say that K is a subcomplex of L if every face of K is also a face of L. -/
section Lattice

instance instPartialOrderFaces : PartialOrder.{u} (AbstractSimplicialComplex V) := PartialOrder.lift faces (fun _ _ heq => by ext; rw [heq])

/- If K is a subcomplex of L, then every facet of L that is a face of K is also a facet of K.-/

lemma Facets_subcomplex {K L : AbstractSimplicialComplex V} (hKL : K ≤ L) {s : Finset V} (hsK : s ∈ K.faces) (hsL : s ∈ L.facets) :
s ∈ K.facets := by 
  rw [mem_facets_iff, and_iff_right hsK] 
  exact fun _ htK hst => hsL.2 (hKL htK) hst 

instance Inf : Inf.{u} (AbstractSimplicialComplex V) :=
⟨fun K L =>
{ faces := K.faces ∩ L.faces
  nonempty_of_mem := fun hs => K.nonempty_of_mem hs.1  
  down_closed := fun ⟨hsK, hsL⟩ hts ht => ⟨K.down_closed hsK hts ht, L.down_closed hsL hts ht⟩ }⟩

lemma inf_faces {K L : AbstractSimplicialComplex V} : (K ⊓ L).faces = K.faces ⊓ L.faces := rfl


instance Sup : Sup.{u} (AbstractSimplicialComplex V) :=
⟨fun K L => 
{ faces := K.faces ∪ L.faces
  nonempty_of_mem := fun hs => by cases hs with
                                  | inl h => exact K.nonempty_of_mem h 
                                  | inr h => exact L.nonempty_of_mem h 
  down_closed := fun hs hts ht => by cases hs with
                                     | inl hsK => exact Or.inl $ K.down_closed hsK hts ht
                                     | inr hsL => exact Or.inr $ L.down_closed hsL hts ht }⟩

lemma sup_faces {K L : AbstractSimplicialComplex V} : (K ⊔ L).faces = K.faces ⊔ L.faces := rfl



instance DistribLattice : DistribLattice.{u} (AbstractSimplicialComplex V) :=
  {AbstractSimplicialComplex.instPartialOrderFaces,
  AbstractSimplicialComplex.Inf,
  AbstractSimplicialComplex.Sup with
  le_sup_inf := fun K L M => @le_sup_inf _ _ K.faces L.faces M.faces
  le_sup_left := fun K L => @le_sup_left _ _ K.faces L.faces
  le_sup_right := fun K L => @le_sup_right _ _ K.faces L.faces
  sup_le := fun K L M (hKM : K.faces ≤ M.faces) (hLM : L.faces ≤ M.faces) => sup_le hKM hLM
  inf_le_left := fun K L => @inf_le_left _ _ K.faces L.faces
  inf_le_right := fun K L => @inf_le_right _ _ K.faces L.faces
  le_inf := fun K L M (hKL : K.faces ≤ L.faces) (hKM : K.faces ≤ M.faces) => le_inf hKL hKM  
  }




instance Top : Top.{u} (AbstractSimplicialComplex V) :=
⟨{faces := {s : Finset V | s.Nonempty}
  nonempty_of_mem := fun hs => hs
  down_closed := fun _ _ ht => ht }⟩


instance Bot : Bot.{u} (AbstractSimplicialComplex V) :=
⟨{faces := (∅ : Set (Finset V)) 
  nonempty_of_mem := fun hs => by exfalso; exact Set.not_mem_empty _ hs
  down_closed := fun hs => by exfalso; exact Set.not_mem_empty _ hs}⟩


instance OrderBot : OrderBot.{u} (AbstractSimplicialComplex V) := 
{AbstractSimplicialComplex.Bot with
 bot_le := fun K σ hσ => by exfalso; exact Set.not_mem_empty _ hσ}

instance OrderTop : OrderTop.{u} (AbstractSimplicialComplex V) :=
{ AbstractSimplicialComplex.Top with
  le_top := fun K _ hσ => K.nonempty_of_mem hσ
}


instance SupSet : SupSet.{u} (AbstractSimplicialComplex V) :=
⟨fun s =>
{ faces := sSup $ faces '' s
  nonempty_of_mem := fun ⟨k, ⟨K, _, hkK⟩, h⟩ => by rw [←hkK] at h; exact K.nonempty_of_mem h 
  down_closed := fun ⟨_, ⟨K, hKs, rfl⟩, hk⟩ hlk hl =>
    ⟨K.faces, ⟨K, hKs, rfl⟩, K.down_closed hk hlk hl⟩ }⟩

lemma sSup_faces (s : Set (AbstractSimplicialComplex V)) : (sSup s).faces = sSup (faces '' s) := rfl


instance InfSet : InfSet.{u} (AbstractSimplicialComplex V) :=
⟨fun s =>
{ faces := {t ∈ sInf $ faces '' s | t.Nonempty}
  nonempty_of_mem := fun ⟨_, hσ⟩ => hσ
  down_closed := fun ⟨hk₁, _⟩ hlk hl => ⟨by intro m ⟨M, hM, hmM⟩
                                            rw [←hmM]
                                            exact M.down_closed (hk₁ M.faces ⟨M, hM, rfl⟩) hlk hl, hl⟩ }⟩

lemma sInf_faces (s : Set (AbstractSimplicialComplex V)) : (sInf s).faces = {t ∈ sInf $ faces '' s | t.Nonempty} :=
rfl



lemma sInf_faces_of_nonempty {s : Set (AbstractSimplicialComplex V)} (h : s.Nonempty) :
  faces (sInf s) = sInf (faces '' s) := by
  rw [sInf_faces]
  ext σ
  simp only [Set.sInf_eq_sInter, Set.sInter_image, Set.mem_iInter, Set.mem_setOf_eq, and_iff_left_iff_imp]
  intro hσ 
  obtain ⟨K, hK⟩ := h 
  exact K.nonempty_of_mem (hσ K hK) 


-- Abstract simplicial complexes with vertices in `V` form a `CompleteDistribLattice`

instance CompleteLattice  : CompleteLattice.{u} (AbstractSimplicialComplex V) := 
{ AbstractSimplicialComplex.DistribLattice.toLattice, 
  AbstractSimplicialComplex.SupSet.{u}, 
  AbstractSimplicialComplex.InfSet.{u}, 
  AbstractSimplicialComplex.OrderTop,
  AbstractSimplicialComplex.OrderBot with
  sInf_le := fun s K hK σ hσ => by rw [sInf_faces_of_nonempty ⟨K, hK⟩] at hσ
                                   exact hσ K.faces ⟨K, hK, rfl⟩
  le_sInf := fun s K h σ hσ => by constructor
                                  . intro l ⟨L, hL, hlL⟩
                                    rw [←hlL]
                                    exact h _ hL hσ 
                                  . exact K.nonempty_of_mem hσ
  sSup_le := fun s K h σ ⟨_, ⟨L, hLs, hLw⟩, hσL⟩ => by rw [←hLw] at hσL; exact h _ hLs hσL 
  le_sSup := fun s K hK σ hσ => ⟨K.faces, ⟨K, hK, rfl⟩, hσ⟩
  toTop := AbstractSimplicialComplex.Top
  toBot := AbstractSimplicialComplex.Bot 
  }


instance CompleteDistribLattice : CompleteDistribLattice.{u} (AbstractSimplicialComplex V) :=
{ AbstractSimplicialComplex.CompleteLattice.{u} with  
  iInf_sup_le_sup_sInf := by intro K s σ hσ 
                             rw [iInf, sInf_faces] at hσ
                             obtain ⟨hσ₁, hσ₂ : σ.Nonempty⟩ := hσ
                             rw [sup_faces, sInf_faces]
                             by_cases hσK : σ ∈ K 
                             . exact Or.inl hσK 
                             . apply Or.inr 
                               refine ⟨?_, hσ₂⟩
                               intro l ⟨L,hL,hlL⟩
                               rw [←hlL]
                               specialize hσ₁ (K ⊔ L).faces ⟨K ⊔ L, ⟨L, _⟩, rfl⟩
                               simp only
                               classical
                               rw [iInf_eq_if, if_pos hL]
                               exact Or.resolve_left hσ₁ hσK 
  inf_sSup_le_iSup_inf := by intro K s σ hσ 
                             obtain ⟨hσ₁, l, ⟨L, hL, hlL⟩, hσ₂⟩ := hσ 
                             rw [iSup, sSup_faces]
                             rw [←hlL] at hσ₂ 
                             refine ⟨(K ⊓ L).faces, ⟨K ⊓ L, ⟨L, ?_⟩, rfl⟩, ⟨hσ₁, hσ₂⟩⟩
                             simp only
                             classical
                             rw [iSup_eq_if, if_pos hL] 
  }



end Lattice


def FiniteComplex (K : AbstractSimplicialComplex V) : Prop := Finite K.faces

lemma Finite_IsLowerSet {K L : AbstractSimplicialComplex V} (hKL : K ≤ L) (hLfin : FiniteComplex L) : FiniteComplex K := 
@Finite.Set.subset (Finset V) L.faces K.faces hLfin hKL    

/- A finite simplicial complex has a finite set of facets.-/

lemma FiniteComplex_has_finite_facets {K : AbstractSimplicialComplex V} (hfin : FiniteComplex K) : Finite K.facets := 
@Finite.Set.subset _ K.faces _ hfin (fun _ hsf => facets_subset hsf)

section Classical

open Classical


noncomputable def dimension (K : AbstractSimplicialComplex V) : ENat :=
  iSup (fun (s : K.faces) => (Finset.card s.1 : ENat)) - 1  



def Pure (K : AbstractSimplicialComplex V) : Prop :=
  ∀ ⦃s : Finset V⦄, s ∈ K.facets → ((s.card - 1 : ℕ) : ENat) = K.dimension

end Classical


def skeleton (K : AbstractSimplicialComplex V) (d : ℕ) : AbstractSimplicialComplex V :=
{ faces := {s ∈ K.faces | s.card ≤ d + 1}
  nonempty_of_mem := fun hs => K.nonempty_of_mem hs.1
  down_closed := fun ⟨hsK, hsd⟩ hts ht => ⟨K.down_closed hsK hts ht,
    le_trans (Finset.card_le_of_subset hts) hsd⟩}


section

variable [DecidableEq V]


def link (K : AbstractSimplicialComplex V) (s : Finset V) : AbstractSimplicialComplex V :=
{ faces := {t ∈ K.faces | s ∩ t = ∅ ∧ s ∪ t ∈ K}
  nonempty_of_mem := fun hσ => K.nonempty_of_mem hσ.1
  down_closed := fun ⟨hσK, hσint, hσunion⟩ hτσ hτ => ⟨K.down_closed hσK hτσ hτ,
    eq_bot_iff.2 $ le_trans (Finset.inter_subset_inter_left hτσ) (eq_bot_iff.1 hσint),
    K.down_closed hσunion (Finset.union_subset_union (Finset.Subset.refl _) hτσ)
      (by rw[Finset.nonempty_iff_ne_empty, ne_eq, Finset.union_eq_empty_iff, not_and_or, ←ne_eq, ←ne_eq, ←Finset.nonempty_iff_ne_empty,
            ←Finset.nonempty_iff_ne_empty]; exact Or.inr hτ)⟩ }

end


/- We define the "infinite simplex" on a type α as an abstract simplicial complex. It is an actual simplex if α is a fintype.-/

def Simplex (α : Type u) : AbstractSimplicialComplex α where 
  faces := {s : Finset α | s.Nonempty}
  nonempty_of_mem h := h   
  down_closed := fun _ _ ht => ht 

lemma faces_Simplex {α : Type u} (s : Finset α) : s.Nonempty ↔ s ∈ (Simplex α).faces := by
  constructor 
  . intro hSne 
    unfold Simplex 
    simp only [Set.mem_setOf_eq]
    exact hSne
  . exact fun hSf => (Simplex α).nonempty_of_mem hSf 

lemma vertices_Simplex (α : Type u) : (Simplex α).vertices = ⊤ := by 
  rw [Set.top_eq_univ, Set.eq_univ_iff_forall]
  intro a 
  rw [mem_vertices]
  exists a 
  exact Finset.mem_singleton_self _ 


end AbstractSimplicialComplex


open AbstractSimplicialComplex


/- We allowed simplicial complexes on a set bigger than the set of vertices because it was convenient. To define simplicial maps, we restrict
ourselves to the set of vertices (so the forgetful functor from simplicial complexes to sets will send K to K.vertices). This spares us a
localization when defining the catgeory of abstract simplicial complexes.-/


@[ext]
structure SimplicialMap {U : Type u} {V : Type v} (K : AbstractSimplicialComplex U) (L : AbstractSimplicialComplex V) :=
(vertex_map : K.vertices → L.vertices)
(face_map : K.faces → L.faces)
(compatibility_vertex_face : ∀ (a : K.vertices), face_map ⟨{a.1}, a.2⟩ = ⟨{(vertex_map a).1}, (vertex_map a).2⟩)
(compatibility_face_vertex : ∀ (s : K.faces) (b : V), b ∈ (face_map s).1 ↔ (∃ (a : U) (has : a ∈ s.1), 
  (vertex_map ⟨a, face_subset_vertices K s has⟩).1 = b))




notation:100 K:100 " →ₛ " L:100 => SimplicialMap K L  --not sure how to choose the parsing precedence

namespace SimplicialMap

variable {α : Type u} {β : Type v} {γ : Type w}
variable {K : AbstractSimplicialComplex α} {L : AbstractSimplicialComplex β} {M : AbstractSimplicialComplex γ}

@[simp]
lemma ext_vertex  (f g : SimplicialMap K L) :
f.vertex_map = g.vertex_map → f = g := by 
  intro heq 
  ext s a 
  . rw [heq]
  . rw [f.compatibility_face_vertex, g.compatibility_face_vertex, heq]

/- If f is a map from α to β such that, for every face s of K, f(s) is a face of L, then f defines a simplicial map from K to L.-/

noncomputable def SimplicialMapofMap (f : α → β) (hf : ∀ (s : Finset α), s ∈ K.faces → Finset.image f s ∈ L.faces) :
K →ₛ L 
    where 
  vertex_map := by 
    intro ⟨a, hav⟩ 
    refine ⟨f a, ?_⟩
    rw [mem_vertices] at hav |- 
    exact hf {a} hav 
  face_map := fun s => ⟨Finset.image f s, hf s.1 s.2⟩
  compatibility_vertex_face := fun _ => by simp only [Finset.image_singleton]
  compatibility_face_vertex := fun _ _ => by simp only [Finset.mem_image, exists_prop]

lemma SimplicialMapofMap.vertex_map (f : α → β) (hf : ∀ (s : Finset α), s ∈ K.faces → Finset.image f s ∈ L.faces) (a : K.vertices) :
((SimplicialMapofMap f hf).vertex_map a).1 = f a.1 := sorry


/- If f is any map from a fintype α to a fintype β, it defines a simplicial map between the corresponding simplices.-/

noncomputable def MapSimplex (f : α → β) : SimplicialMap (Simplex α) (Simplex β) := 
{
vertex_map := fun ⟨a, _⟩ => by refine ⟨f a, ?_⟩
                               rw [vertices_Simplex]
                               simp only [Set.top_eq_univ, Set.mem_univ]
face_map := by 
  intro ⟨s, hsf⟩
  refine ⟨Finset.image f s, ?_⟩
  rw [←faces_Simplex] at hsf |-
  simp only [Finset.Nonempty.image_iff, hsf]
compatibility_vertex_face := fun _ => by simp only [Finset.image_singleton]
compatibility_face_vertex := fun _ _ => by simp only [Finset.mem_image, exists_prop]
}


def comp (g : L →ₛ M) (f : K →ₛ L) : K →ₛ M :=
{ vertex_map := g.vertex_map ∘ f.vertex_map,
  face_map := g.face_map ∘ f.face_map,
  compatibility_vertex_face := by 
    intro a
    simp only [Function.comp_apply]
    rw [f.compatibility_vertex_face a, g.compatibility_vertex_face (f.vertex_map a)]
  compatibility_face_vertex := by 
    intro s c 
    simp only [Function.comp_apply]
    rw [g.compatibility_face_vertex]
    simp_rw [f.compatibility_face_vertex]
    constructor
    . intro hc 
      match hc with 
      | ⟨b, ⟨a, has, hab⟩, hbc⟩ => 
        exists a; exists has 
        have hav : a ∈ K.vertices := face_subset_vertices K s has 
        have hbv : b ∈ L.vertices := by rw [←hab]; exact (f.vertex_map ⟨a, hav⟩).2
        have hab' : f.vertex_map ⟨a, hav⟩ = ⟨b, hbv⟩ := by rw [←SetCoe.ext_iff]; simp only [hab]
        rw [hab', hbc]
    . intro hc 
      match hc with 
      | ⟨a, has, hac⟩ => 
        set b := f.vertex_map ⟨a, face_subset_vertices K s has⟩
        exists b.1
        simp only [Subtype.coe_eta, exists_prop]
        constructor 
        . exists a; exists has 
        . simp only [hac]
}


noncomputable def id (K : AbstractSimplicialComplex α) : K →ₛ K :=
{ vertex_map := fun a => a
  face_map := fun s => s
  compatibility_vertex_face := fun _ => by simp only
  compatibility_face_vertex := fun _ _ => by simp only [exists_prop, exists_eq_right]
}

lemma MapSimplex.id : MapSimplex (fun x => x) = SimplicialMap.id (Simplex α) := by 
  apply SimplicialMap.ext_vertex 
  unfold MapSimplex SimplicialMap.id  
  simp only 

lemma MapSimplex.comp (f : α → β) (g : β → γ) : (MapSimplex g).comp (MapSimplex f) = MapSimplex (g ∘ f) := by 
  apply SimplicialMap.ext_vertex 
  ext ⟨a, hav⟩
  unfold MapSimplex SimplicialMap.comp   
  simp only [Function.comp_apply]


end SimplicialMap



/- Subcomplex generated by a set of faces, or by one face. -/

namespace AbstractSimplicialComplex 

variable {V : Type u}

def SubcomplexGenerated (K : AbstractSimplicialComplex V) (F : Set (Finset V)) : AbstractSimplicialComplex V := 
of_subcomplex K {s : Finset V | s ∈ K.faces ∧ ∃ (t : Finset V), t ∈ F ∧ s ⊆ t} (by simp only [Set.sep_subset]) 
(by intro s t hs hts htne 
    constructor
    . exact K.down_closed hs.1 hts htne 
    . match hs.2 with 
      | ⟨u, ⟨huF, hsu⟩⟩ => exact ⟨u, ⟨huF, subset_trans hts hsu⟩⟩)



lemma SubcomplexGenerated_mem (K : AbstractSimplicialComplex V) (F : Set (Finset V)) (s : Finset V) :
s ∈ SubcomplexGenerated K F ↔ s ∈ K.faces ∧ ∃ (t : F), s ⊆ t := by 
  unfold SubcomplexGenerated 
  change s ∈ {s | s ∈ K.faces ∧ ∃ (t : Finset V), t ∈ F ∧  s ⊆ t} ↔ _ 
  simp only [Set.mem_setOf_eq, Subtype.exists, exists_prop]
  

/- The boundary of a simplex of K is the set of subspaces of s that are different from s. -/

def Boundary {K : AbstractSimplicialComplex V} (s : K.faces) : AbstractSimplicialComplex V := --note that K is not needed, any nonempty subset of s is a face
of_subcomplex K {t : Finset V | t ∈ K.faces ∧ t ⊂ s} (by simp only [Set.sep_subset])
(by intro t u ht hut hune 
    constructor
    . exact K.down_closed ht.1 hut hune 
    . exact lt_of_le_of_lt hut ht.2)

lemma Boundary_mem {K : AbstractSimplicialComplex V} (s : K.faces) (t : Finset V):
t ∈ (Boundary s).faces ↔ t ∈ K.faces ∧ t ⊆ s.1 ∧ t ≠ s.1 := by 
  unfold Boundary 
  change t ∈ {t : Finset V | t ∈ K.faces ∧ t ⊂ s} ↔ _ 
  simp only [Set.mem_setOf_eq, ne_eq, and_congr_right_iff]
  exact fun _ => by rw [Finset.ssubset_iff_subset_ne]




lemma BoundaryFinite {K : AbstractSimplicialComplex V} (s : K.faces) : FiniteComplex (Boundary s) := by 
  apply @Finite.of_injective (Boundary s).faces {u : Set V | u ⊆ ↑s.1} (Set.finite_coe_iff.mpr (@Set.Finite.finite_subsets V ↑s.1 (Finset.finite_toSet _))) 
    (fun (t : (Boundary s).faces) => by have ht := t.2 
                                        rw [Boundary_mem, ←Finset.coe_subset] at ht 
                                        exact (⟨↑t.1, ht.2.1⟩ : {u : Set V | u ⊆ ↑s.1}))
  intro t u heq 
  simp only [Set.coe_setOf, Set.mem_setOf_eq, Subtype.mk.injEq, Finset.coe_inj] at heq
  rw [SetCoe.ext_iff] at heq
  exact heq 
  


end AbstractSimplicialComplex

