import TS1.Decomposability 

set_option autoImplicit false

universe u 

variable {α : Type u} {K : AbstractSimplicialComplex α} [DecidableEq α]

/- Shellability : an abstract simplicial complex is shellable if there exists a well-order on its
facets such that, for every non-minimal facet s, the corresponding set of old faces is 
empty or pure of dimension dim(s)-1. We will define IsShellingOrder for a linear order on the facets.-/

namespace AbstractSimplicialComplex 

def IsShellingOrder (r : LinearOrder K.facets) : Prop := 
(WellFounded r.lt) ∧ ∀ (s : K.facets), (OldFaces r.toPartialOrder s).faces = ∅ ∨ 
(Pure (OldFaces r.toPartialOrder s) ∧ (OldFaces r.toPartialOrder s).dimension = Finset.card s.1 - 2)

/- We have two goals in this file: to show that a shellable complex is decomposable, and to show that a decomposable complex with a
compatible well-order on its facets is shellable.-/

/- To show that a shellable complex is decomposable, we need to define maps R and DF; we will call then the "restricton map" and the
"smallest facet map". -/

lemma ShellingOrderRestriction_aux (r : PartialOrder K.facets) (s : K.facets) : {a : α | a ∈ s.1 ∧ (Finset.erase s.1 a) ∈ (OldFaces r s).faces}.Finite := by
  apply Set.Finite.subset (Finset.finite_toSet s)
  rw [Set.subset_def]
  exact fun _ ha => ha.1 

noncomputable def ShellingOrderRestriction (r : PartialOrder K.facets) (s : K.facets) : Finset α :=
Set.Finite.toFinset (ShellingOrderRestriction_aux r s)

lemma ShellingOrderRestriction_def (r : PartialOrder K.facets) (s : K.facets) (a : α) :
a ∈ ShellingOrderRestriction r s ↔ a ∈ s.1 ∧ Finset.erase s.1 a ∈ (OldFaces r s).faces := by 
  unfold ShellingOrderRestriction
  rw [Set.Finite.mem_toFinset]
  simp only [Set.mem_setOf_eq]

lemma ShellingOrderRestriction_mem (r : PartialOrder K.facets) (s : K.facets) (a : α) :
a ∈ ShellingOrderRestriction r s ↔ a ∈ s.1 ∧ s.1 ≠ {a} ∧ (∃ (u : K.facets), r.lt u s ∧ Finset.erase s.1 a ⊆ u.1) := by 
  rw [ShellingOrderRestriction_def]
  simp only [ne_eq, Subtype.exists, exists_and_right, and_congr_right_iff]
  intro _ 
  erw [OldFaces_mem]
  constructor 
  . intro ha 
    have hne := K.nonempty_of_mem ha.1
    rw [Finset.nonempty_iff_ne_empty, ne_eq, Finset.erase_eq_empty_iff, not_or] at hne
    rw [and_iff_right hne.2]
    match ha.2.2 with 
    | ⟨u, ⟨hus, hau⟩⟩ => exists u 
                         simp only [Subtype.coe_eta, Subtype.coe_prop, exists_prop, true_and]
                         exact ⟨hus, hau⟩
  . intro ha 
    have hne : (Finset.erase s.1 a).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty, ne_eq, Finset.erase_eq_empty_iff, not_or, ←ne_eq, ←Finset.nonempty_iff_ne_empty]
      exact ⟨K.nonempty_of_mem (facets_subset s.2), ha.1⟩
    have has : Finset.erase s.1 a ⊆ s.1 := Finset.erase_subset _ _ 
    rw [and_iff_right (K.down_closed (facets_subset s.2) has hne), and_iff_right has]
    match ha.2 with 
  | ⟨u, ⟨⟨huf, hus⟩, hau⟩⟩ => exists ⟨u, huf⟩ 

lemma ShellingOrderRestriction_smaller (r : PartialOrder K.facets) (s : K.facets) :
ShellingOrderRestriction r s ⊆ s.1 := by 
  rw [Finset.subset_iff]
  intro a haR 
  rw [ShellingOrderRestriction_def] at haR 
  exact haR.1 

lemma not_containing_restriction_is_old_face (r : PartialOrder K.facets) (s : K.facets) (t : K.faces) (hts : t.1 ⊆ s.1) 
(htR : ¬(ShellingOrderRestriction r s ⊆ t.1)) : t.1 ∈ (OldFaces r s).faces := by 
  rw [Finset.not_subset] at htR 
  match htR with 
  | ⟨a, ⟨haR, hat⟩⟩ => rw [ShellingOrderRestriction_def] at haR 
                       apply (OldFaces r s).down_closed haR.2 ?_ (K.nonempty_of_mem t.2)
                       rw [Finset.subset_erase]
                       exact ⟨hts, hat⟩
               
lemma old_face_does_not_contain_restriction (r : PartialOrder K.facets) (s : K.facets) 
(hof : Pure (OldFaces r s) ∧ (OldFaces r s).dimension = Finset.card s.1 - 2) {t : Finset α}
(htof : t ∈ (OldFaces r s).faces) : ¬(ShellingOrderRestriction r s ⊆ t) := by 
  match Noetherian_implies_every_face_contained_in_facet (Finite_implies_Noetherian (OldFacesFinite r s)) ⟨t, htof⟩ with 
  | ⟨u, ⟨huf, htu⟩⟩ => have hus : u.1 ⊆ s.1 := by 
                         rw [mem_facets_iff] at huf 
                         erw [OldFaces_mem] at huf
                         exact huf.1.2.1 
                       have hcard : Finset.card u.1 = Finset.card s.1 - 1 := by 
                         have hdim := hof.1 huf
                         rw [hof.2] at hdim 
                         erw [←ENat.coe_sub, WithTop.coe_eq_coe, Nat.cast_inj] at hdim
                         apply_fun Nat.succ at hdim 
                         rw [←Nat.pred_eq_sub_one, Nat.succ_pred (face_card_nonzero u.2)] at hdim
                         rw [←(Nat.succ_sub (OldFacesNonempty_implies_not_vertex r s ⟨u.1, u.2⟩))] at hdim
                         rw [Nat.succ_eq_add_one, Nat.add_sub_add_right] at hdim
                         exact hdim 
                       have hdiff : Finset.card (s.1 \ u.1) = 1 := by 
                         rw [Finset.card_sdiff hus, hcard, Nat.sub_sub_self]
                         rw [Nat.succ_le_iff, Nat.pos_iff_ne_zero]
                         exact face_card_nonzero (facets_subset s.2)
                       rw [Finset.card_eq_one] at hdiff
                       match hdiff with 
                      | ⟨a, ha⟩ => have hau : u.1 = s.1 \ {a} := by 
                                     have h := Finset.sdiff_sdiff_eq_self hus
                                     rw [ha] at h 
                                     exact Eq.symm h 
                                   have haR : a ∈ ShellingOrderRestriction r s := by 
                                     rw [ShellingOrderRestriction_def]
                                     have has : a ∈ s.1 := by 
                                       rw [←Finset.singleton_subset_iff, ←ha]
                                       simp only [Finset.sdiff_subset]
                                     rw [and_iff_right has, Finset.erase_eq, ←hau]
                                     exact u.2 
                                   rw [Finset.not_subset]
                                   exists a 
                                   rw [and_iff_right haR]
                                   by_contra hat 
                                   rw [←Finset.erase_eq] at hau 
                                   have hau' := htu hat
                                   rw [hau] at hau'
                                   exact Finset.not_mem_erase a s.1 hau' 


/- Definition of the "smallest facet" map. As the name indicates, it sends a face s to the smallest facet (for the shelling order) containing s.
For this set to be nonempty, we need to know that s is contained in at least one facet; we call this condition "ExistsFacet". It is satisfied by
Noetherian complexes.
-/

def ExistsFacet (K : AbstractSimplicialComplex α): Prop := ∀ (s : K.faces), ∃ (t : K.facets), s.1 ⊆ t.1 

lemma Noetherian_ExistsFacet (hnoeth : IsNoetherianPoset K.faces) : ExistsFacet K := by 
  intro s 
  match Noetherian_implies_every_face_contained_in_facet hnoeth s with 
  | ⟨t, htf⟩ => exists ⟨t.1, htf.1⟩; exact htf.2 

noncomputable def ShellingOrderSmallestFacet (r : LinearOrder K.facets) (hwf : WellFounded r.lt) (hef : ExistsFacet K) 
(s : K.faces) : K.facets := 
WellFounded.min hwf {t : K.facets | s.1 ⊆ t.1} (by match hef s with
                                                  | ⟨t, _⟩ => exists t)

lemma ShellingOrderSmallestFacet_bigger (r : LinearOrder K.facets) (hwf : WellFounded r.lt) (hef : ExistsFacet K) 
(s : K.faces) : s.1 ⊆ (ShellingOrderSmallestFacet r hwf hef s).1 :=  
WellFounded.min_mem hwf {t : K.facets | s.1 ⊆ t.1} (by match hef s with
                                                       | ⟨t, _⟩ => exists t)


lemma ShellingOrderSmallestFacet_smallest (r : LinearOrder K.facets) (hwf : WellFounded r.lt) (hef : ExistsFacet K) 
(s : K.faces) (u : K.facets) (hus : s.1 ⊆ u.1) : r.le (ShellingOrderSmallestFacet r hwf hef s) u := by 
  have hnlt := WellFounded.not_lt_min hwf {t : K.facets | s.1 ⊆ t.1} (by match hef s with
                                                                         | ⟨t, _⟩ => exists t) hus 
  rw [lt_iff_not_le, not_not] at hnlt
  exact hnlt 

 
/- We now that a Noetherian shellable complex is decomposable. -/


lemma ShellableIsDecomposable {r : LinearOrder K.facets} (hshel : IsShellingOrder r) (hef : ExistsFacet K) : 
IsDecomposition (ShellingOrderRestriction r.toPartialOrder) (ShellingOrderSmallestFacet r hshel.1 hef) := by 
  unfold IsDecomposition 
  rw [and_iff_right (fun s => ShellingOrderRestriction_smaller r.toPartialOrder s)]
  intro s t 
  rw [←not_iff_not]
  constructor 
  . intro hst 
    by_cases hsub : s.1 ⊆ t.1 
    . rw [and_comm, not_and] at hst
      have hsof := not_containing_restriction_is_old_face r.toPartialOrder t s hsub (hst hsub) 
      erw [OldFaces_mem] at hsof 
      match hsof.2.2 with
    | ⟨u,⟨hut, hsu⟩⟩ => by_contra habs 
                        rw [habs] at hut
                        exact @not_le_of_lt _ r.toPartialOrder.toPreorder _ _ hut (ShellingOrderSmallestFacet_smallest r hshel.1 hef s u hsu)
    . by_contra habs 
      rw [habs] at hsub
      exact hsub (ShellingOrderSmallestFacet_bigger r hshel.1 hef s) 
  . intro hst 
    rw [not_and_or]
    by_cases hsub : s.1 ⊆ t.1 
    . apply Or.inl 
      have hsof : s.1 ∈ (OldFaces r.toPartialOrder t).faces := by 
        erw [OldFaces_mem]
        rw [and_iff_right s.2, and_iff_right hsub]
        exists (ShellingOrderSmallestFacet r hshel.1 hef s)
        rw [and_iff_left (ShellingOrderSmallestFacet_bigger r hshel.1 hef s)]
        by_contra habs 
        rw [lt_iff_not_le, not_not] at habs 
        exact hst (r.le_antisymm _ _ habs (ShellingOrderSmallestFacet_smallest r hshel.1 hef s t hsub)) 
      have hofne : (OldFaces r.toPartialOrder t).faces ≠ ∅ := by 
        rw [←Set.nonempty_iff_ne_empty]
        exists s.1 
      have hpure := hshel.2 t
      rw [or_iff_right hofne] at hpure   
      exact old_face_does_not_contain_restriction r.toPartialOrder t hpure hsof
    . exact Or.inr hsub 


/- If a decomposable complex has a compatible well-order on its facets, then this order is a shelling order. Moreover, the smallest facet
map is DF, and the restriction defines the same intervals as R.-/

lemma ShellableofDecomposable {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF)
{r : LinearOrder K.facets} (hcomp : CompatibleOrder DF r.toPartialOrder) (hwf : WellFounded r.lt) : 
IsShellingOrder r := by 
  unfold IsShellingOrder 
  rw [and_iff_right hwf]
  intro s 
  by_cases hof : (OldFaces r.toPartialOrder s).faces = ∅
  . exact Or.inl hof 
  . rw [←ne_eq, ←Set.nonempty_iff_ne_empty] at hof
    exact Or.inr ⟨OldFacesDecompositionIsPure hdec hcomp s, OldFacesDecompositionDimension hdec hcomp s hof⟩

lemma ExistsFacetofDecomposable {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF) :
ExistsFacet K := fun s => by exists (DF s); exact Decomposition_DF_bigger_than_source hdec s 

lemma ShellableofDecomposable_smallestfacet {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF)
{r : LinearOrder K.facets} (hcomp : CompatibleOrder DF r.toPartialOrder) (hwf : WellFounded r.lt) : 
ShellingOrderSmallestFacet r hwf (ExistsFacetofDecomposable hdec) = DF := by  
  funext s 
  have h1 := ShellingOrderSmallestFacet_smallest r hwf (ExistsFacetofDecomposable hdec) s (DF s) (Decomposition_DF_bigger_than_source hdec s)
  have h2 : s.1 ∉ OldFaces r.toPartialOrder (DF s) := by 
    rw [OldFacesCompatibleOrder hcomp]
    exact Decomposition_DF_bigger_than_source hdec s 
    exact Decomposition_DF_bigger_than_source hdec s 
  rw [OldFaces_mem] at h2 
  push_neg at h2 
  apply @eq_of_le_of_not_lt _ r.toPartialOrder _ _ h1 
  by_contra habs 
  exact h2 s.2 (Decomposition_DF_bigger_than_source hdec s) (ShellingOrderSmallestFacet r hwf (ExistsFacetofDecomposable hdec) s) habs 
    (ShellingOrderSmallestFacet_bigger r hwf (ExistsFacetofDecomposable hdec) s)

lemma ShellableofDecomposable_intervals {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF)
{r : LinearOrder K.facets} (hcomp : CompatibleOrder DF r.toPartialOrder) (hwf : WellFounded r.lt) (s : K.facets) :
DecompositionInterval hdec s = DecompositionInterval (ShellableIsDecomposable (ShellableofDecomposable hdec hcomp hwf)
  (ExistsFacetofDecomposable hdec)) s := by 
  ext t 
  rw [DecompositionInterval_eq, DecompositionInterval_eq]
  rw [ShellableofDecomposable_smallestfacet hdec hcomp hwf]






end AbstractSimplicialComplex