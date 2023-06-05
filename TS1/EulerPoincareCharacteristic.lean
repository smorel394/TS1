import TS1.Decomposability 
import Mathlib.Algebra.BigOperators.Ring



universe u 

variable {α : Type u} {K : AbstractSimplicialComplex α} 

namespace AbstractSimplicialComplex 

/- The Euler-Poincaré characteristic of a finite simplicial complex K is the sum over all faces of K of -1 to the dimension of the face (i.e.
the cardinality minus 1). -/

noncomputable def FacesFinset (hfin : FiniteComplex K) : Finset (Finset α) := by
  have hf : K.faces.Finite := by rw [←Set.finite_coe_iff]; exact hfin 
  exact Set.Finite.toFinset hf

noncomputable def FacetsFinset (hfin : FiniteComplex K) : Finset (Finset α) := by 
  have hf : K.facets.Finite := by 
    rw [←Set.finite_coe_iff]
    refine @Finite.of_injective _ K.faces hfin (fun s => ⟨s.1, facets_subset s.2⟩) ?_
    intro s t hst 
    simp only [Subtype.mk.injEq] at hst
    rw [SetCoe.ext_iff] at hst
    exact hst
  exact Set.Finite.toFinset hf 

noncomputable def EulerPoincareCharacteristic (hfin : FiniteComplex K) : ℤ := Finset.sum (FacesFinset hfin) 
(fun s => (-1 : ℤ)^(Finset.card s - 1))  



/- If two abstract simplicial complexes have the same set of faces, then they have the same Euler-Poincaré characteristic.-/

lemma EulerPoincareCharacteristic_ext {K L : AbstractSimplicialComplex α} (hKfin : FiniteComplex K) (hLfin : FiniteComplex L)
(heq : K.faces = L.faces) :
EulerPoincareCharacteristic hKfin = EulerPoincareCharacteristic hLfin := by
  have heqfin : FacesFinset hKfin = FacesFinset hLfin := by 
    ext s 
    unfold FacesFinset
    rw [Set.Finite.mem_toFinset, Set.Finite.mem_toFinset, heq]
  unfold EulerPoincareCharacteristic
  rw [heqfin]

/- We want to calculate the Euler-Poincaré characteristic of a decomposable simplicial complex. To express the result, we define the sets
of π0 and homology facets. -/

def π₀Facets {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF) : 
Set (Finset α) := {s | ∃ (hsf : s ∈ K.facets), IsPi0Facet hdec ⟨s, hsf⟩}

def HomologyFacets {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF) : 
Set (Finset α) := {s | ∃ (hsf : s ∈ K.facets), IsHomologyFacet hdec ⟨s, hsf⟩}

/- We prove that these sets are finite if K is finite.-/

lemma π₀Facets_finite {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF)
(hfin : FiniteComplex K) : (π₀Facets hdec).Finite := by 
  rw [←Set.finite_coe_iff]
  apply @Finite.of_injective _ K.faces hfin (fun s => ⟨s.1, facets_subset (by match s.2 with | ⟨hsf,_⟩ => exact hsf)⟩)
  intro s t heq 
  simp only [Subtype.mk.injEq] at heq
  rw [SetCoe.ext_iff] at heq 
  exact heq 

lemma HomologyFacets_finite {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF) (hfin : FiniteComplex K) : 
(HomologyFacets hdec).Finite := by 
  rw [←Set.finite_coe_iff]
  apply @Finite.of_injective _ K.faces hfin (fun s => ⟨s.1, facets_subset (by match s.2 with | ⟨hsf,_⟩ => exact hsf)⟩)
  intro s t heq 
  simp only [Subtype.mk.injEq] at heq
  rw [SetCoe.ext_iff] at heq 
  exact heq 

/- Now we prove the formula for the Euler-Poincaré characteristic of a finite decomposable complex.-/

/- First we will split the sum as a sum over the fibers of the map DF, so for technical reasons it is convenient to extend DF to a function
from Finset α to itself.-/

open Classical 

noncomputable def DFe (DF : K.faces → K.facets) : Finset α → Finset α := by
  intro s 
  by_cases hsf : s ∈ K.faces 
  . exact (DF ⟨s, hsf⟩).1 
  . exact (∅ : Finset α)


/- Then we construct a bijection between the image by DFe of the set of faces and the set of facets, as a Finset of Finset α (this is what
we call FacetsFinset). To use Finset.sum_bij, we need this bijection to send the sum of (-1)^(card s-1) over a fiber to DF to the function
Sum_on_DecompositionInterval, which we define using a version of the decomposition interval that is a Finset of Finset α (instead of K.faces).-/



noncomputable def Quotient_DFe_to_finset (DF : K.faces → K.facets) : Quotient (Setoid.ker (DFe DF)) → Finset α := 
Quotient.lift (fun s => DFe DF s) (by intro s t hst; change Setoid.Rel (Setoid.ker (DFe DF)) s t at hst; rw [Setoid.ker_def] at hst; exact hst)

lemma Quotient_DFe_to_finset_is_facet_aux (DF : K.faces → K.facets) (hfin : FiniteComplex K) {x : Quotient (Setoid.ker (DFe DF))} 
(hx : x ∈ Finset.image (@Quotient.mk'' _ (Setoid.ker (DFe DF))) (FacesFinset hfin)) : 
Quotient_DFe_to_finset DF x ∈ K.facets := by
  unfold Quotient_DFe_to_finset Quotient.lift 
  rw [Finset.mem_image] at hx 
  match hx with 
  | ⟨s, ⟨hsf, hsx⟩⟩ => erw [Set.Finite.mem_toFinset] at hsf 
                       rw [←hsx]  
                       erw [Quot.liftBeta (DFe DF) 
                         (by intro s t hst; change Setoid.Rel (Setoid.ker (DFe DF)) s t at hst; rw [Setoid.ker_def] at hst; exact hst)]
                       unfold DFe
                       simp only [hsf, dite_true, Subtype.coe_prop]

lemma Quotient_DFe_to_finset_is_facet (DF : K.faces → K.facets) (hfin : FiniteComplex K) {x : Quotient (Setoid.ker (DFe DF))} 
(hx : x ∈ Finset.image (@Quotient.mk'' _ (Setoid.ker (DFe DF))) (FacesFinset hfin)) : 
Quotient_DFe_to_finset DF x ∈ FacetsFinset hfin := by
  unfold FacetsFinset 
  rw [Set.Finite.mem_toFinset] 
  exact Quotient_DFe_to_finset_is_facet_aux DF hfin hx 


noncomputable def DecompositionInterval' (R : K.facets → Finset α) (s : K.facets) : Finset (Finset α) := by 
  by_cases R s = ∅
  . exact Finset.Ioc ∅ s.1 
  . exact Finset.Icc (R s) s.1 


lemma ComparisonIntervals {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF) (s : K.facets)
(t : Finset α) :
t ∈ DecompositionInterval' R s ↔ ∃ (htf : t ∈ K.faces), ⟨t, htf⟩ ∈ DecompositionInterval hdec s := by 
  unfold DecompositionInterval' 
  by_cases he : R s = ∅
  . simp only [he, ge_iff_le, Finset.le_eq_subset, gt_iff_lt, Finset.lt_eq_subset, Finset.not_ssubset_empty,
  dite_eq_ite, ite_true, Finset.mem_Ioc, Finset.empty_ssubset]
    constructor 
    . intro ⟨htne, hts⟩
      exists K.down_closed (facets_subset s.2) hts htne
      rw [DecompositionInterval_def, he]
      simp only [Finset.le_eq_subset, Finset.empty_subset, true_and]
      exact hts
    . intro ⟨htf, ht⟩
      rw [DecompositionInterval_def] at ht
      exact ⟨K.nonempty_of_mem htf, ht.2⟩
  . simp only [he, ge_iff_le, Finset.le_eq_subset, gt_iff_lt, Finset.lt_eq_subset, dite_eq_ite, ite_false,
  Finset.mem_Icc]
    constructor
    . intro ⟨hRt, hts⟩
      have htne : t.Nonempty := by
        by_contra hte 
        rw [Finset.not_nonempty_iff_eq_empty] at hte
        rw [hte, Finset.subset_empty] at hRt
        exact he hRt
      exists K.down_closed (facets_subset s.2) hts htne
      rw [DecompositionInterval_def]
      exact ⟨hRt, hts⟩
    . intro ⟨htf, htint⟩ 
      rw [DecompositionInterval_def] at htint
      exact htint 


noncomputable def Sum_on_DecompositionInterval (R : K.facets → Finset α) (s : Finset α) : ℤ := by
  by_cases hsf : s ∈ K.facets  
  . exact Finset.sum (DecompositionInterval' R ⟨s, hsf⟩) (fun t => (-1 :ℤ)^(Finset.card t - 1)) 
  . exact (0 : ℤ)

lemma ComparisonFunctionsonQuotient {DF : K.faces → K.facets} {R : K.facets → Finset α} (hdec : IsDecomposition R DF)
(hfin : FiniteComplex K) (x : Quotient (Setoid.ker (DFe DF))) 
(hx : x ∈ Finset.image (@Quotient.mk'' _ (Setoid.ker (DFe DF))) (FacesFinset hfin)) : 
Finset.sum (Finset.filter (fun s => Quotient.mk (Setoid.ker (DFe DF)) s = x) (FacesFinset hfin)) (fun t => (-1 : ℤ)^(Finset.card t -1))
= Sum_on_DecompositionInterval R (Quotient_DFe_to_finset DF x) := by 
  rw [@Finset.sum_bij ℤ (Finset α) (Finset α) _ (Finset.filter (fun s => Quotient.mk (Setoid.ker (DFe DF)) s = x) (FacesFinset hfin))
    (DecompositionInterval' R ⟨Quotient_DFe_to_finset DF x, Quotient_DFe_to_finset_is_facet_aux DF hfin hx⟩)
    (fun s => (-1 : ℤ)^(Finset.card s - 1)) (fun s => (-1 : ℤ)^(Finset.card s - 1)) 
    (fun x _ => x) (fun y hy => by simp only [Finset.mem_filter] at hy
                                   simp only
                                   have hyf : y ∈ K.faces := by 
                                     unfold FacesFinset at hy 
                                     rw [Set.Finite.mem_toFinset] at hy 
                                     exact hy.1
                                   unfold DecompositionInterval'
                                   have h : ⟨Quotient_DFe_to_finset DF x, Quotient_DFe_to_finset_is_facet_aux DF hfin hx⟩ =
                                     DF ⟨y, hyf⟩ := by
                                     rw [←SetCoe.ext_iff]
                                     simp only
                                     unfold Quotient_DFe_to_finset Quotient.lift
                                     rw [←hy.2]
                                     erw [Quot.liftBeta (DFe DF) 
                                       (by intro s t hst; change Setoid.Rel (Setoid.ker (DFe DF)) s t at hst; rw [Setoid.ker_def] at hst; exact hst)]
                                     unfold DFe 
                                     simp only [hyf, dite_true]
                                   have hyx := (hdec.2 ⟨y, hyf⟩ ⟨Quotient_DFe_to_finset DF x, 
                                     Quotient_DFe_to_finset_is_facet_aux DF hfin hx⟩).mpr h 
                                   by_cases he : R ⟨Quotient_DFe_to_finset DF x, Quotient_DFe_to_finset_is_facet_aux DF hfin hx⟩ = ∅
                                   . simp only [he, ge_iff_le, Finset.le_eq_subset, gt_iff_lt, Finset.lt_eq_subset, Finset.not_ssubset_empty,
  dite_eq_ite, ite_true, Finset.mem_Ioc, Finset.empty_ssubset]
                                     unfold FacesFinset at hy
                                     rw [Set.Finite.mem_toFinset] at hy
                                     exact ⟨K.nonempty_of_mem hy.1, hyx.2⟩  
                                   . simp only [he, ge_iff_le, Finset.le_eq_subset, gt_iff_lt, Finset.lt_eq_subset, dite_eq_ite, ite_false,
                                       Finset.mem_Icc]
                                     exact hyx)
    (fun x _ => by simp only [ge_iff_le])
    (fun x y hx hy heq => by simp only at heq; exact heq)
    (fun s hsint => by exists s
                       simp only [Finset.mem_filter, exists_prop, and_true]
                       unfold FacesFinset
                       rw [Set.Finite.mem_toFinset]
                       have hxf := Quotient_DFe_to_finset_is_facet_aux DF hfin hx
                       have hxlift : x = Quotient.mk (Setoid.ker (DFe DF)) (Quotient_DFe_to_finset DF x) := by
                        simp only [Finset.mem_image] at hx
                        match hx with 
                        | ⟨a, ⟨haf, hax⟩⟩ => unfold FacesFinset at haf
                                             letI : Setoid (Finset α) := Setoid.ker (DFe DF)
                                             rw [Set.Finite.mem_toFinset] at haf
                                             apply Eq.symm
                                             rw [←hax]
                                             apply Quotient.sound
                                             change Setoid.Rel (inferInstance) _ _ 
                                             rw [Setoid.ker_def]
                                             unfold Quotient_DFe_to_finset Quotient.lift 
                                             erw [Quot.liftBeta (DFe DF) 
                                       (by intro s t hst; change Setoid.Rel (Setoid.ker (DFe DF)) s t at hst; rw [Setoid.ker_def] at hst; exact hst)]
                                             unfold DFe 
                                             simp only [haf, dite_true]
                                             simp only [facets_subset (DF ⟨a, haf⟩).2, dite_true]
                                             apply Eq.symm
                                             rw [SetCoe.ext_iff]
                                             exact Decomposition_DF_of_a_facet hdec (DF ⟨a, haf⟩) 
                       rw [ComparisonIntervals hdec ⟨Quotient_DFe_to_finset DF x, hxf⟩] at hsint
                       match hsint with 
                      | ⟨hsf, hsint⟩ => rw [DecompositionInterval_eq hdec] at hsint
                                        rw [←SetCoe.ext_iff] at hsint
                                        simp only at hsint
                                        rw [and_iff_right hsf]
                                        rw [hxlift]
                                        letI : Setoid (Finset α) := Setoid.ker (DFe DF)
                                        apply Quotient.sound 
                                        change Setoid.Rel (inferInstance) _ _ 
                                        rw [Setoid.ker_def]
                                        rw [hsint]
                                        unfold DFe 
                                        simp only [hsf, dite_true, facets_subset (DF ⟨s, hsf⟩).2]
                                        rw [SetCoe.ext_iff]
                                        exact Decomposition_DF_of_a_facet hdec (DF ⟨s, hsf⟩)
      )]
  unfold Sum_on_DecompositionInterval
  simp only [ge_iff_le, Quotient_DFe_to_finset_is_facet_aux DF hfin hx, dite_true]


-- We should not need K to be finite for this.
lemma Quotient_DFe_to_finset_inj (DF : K.faces → K.facets) (hfin : FiniteComplex K) (x y : Quotient (Setoid.ker (DFe DF))) 
(hx : x ∈ Finset.image (@Quotient.mk'' _ (Setoid.ker (DFe DF))) (FacesFinset hfin))
(hy : y ∈ Finset.image (@Quotient.mk'' _ (Setoid.ker (DFe DF))) (FacesFinset hfin))
(heq : Quotient_DFe_to_finset DF x = Quotient_DFe_to_finset DF y) : x = y := by 
  unfold Quotient_DFe_to_finset Quotient.lift at heq 
  rw [Finset.mem_image] at hx hy 
  match hx with 
  | ⟨s, ⟨hsf, hsx⟩⟩ => rw [←hsx] at heq   
                       erw [Quot.liftBeta (DFe DF) 
                         (by intro s t hst; change Setoid.Rel (Setoid.ker (DFe DF)) s t at hst; rw [Setoid.ker_def] at hst; exact hst)]
                         at heq 
                       match hy with 
                       | ⟨t, ⟨htf, hty⟩⟩ => rw [←hty] at heq   
                                            erw [Quot.liftBeta (DFe DF) 
                                              (by intro s t hst; change Setoid.Rel (Setoid.ker (DFe DF)) s t at hst; rw [Setoid.ker_def] at hst; exact hst)]
                                              at heq 
                                            rw [←hsx, ←hty]
                                            apply Quotient.sound 
                                            change Setoid.Rel (Setoid.ker (DFe DF)) s t 
                                            rw [Setoid.ker_def]
                                            exact heq 

-- We should not need K to be finite for this.
lemma Quotient_DFe_to_finset_surj {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF) 
(hfin : FiniteComplex K) (s : Finset α) (hsf : s ∈ FacetsFinset hfin) :
∃ (x : Quotient (Setoid.ker (DFe DF))), ∃ (_ : x ∈ Finset.image (@Quotient.mk'' _ (Setoid.ker (DFe DF))) (FacesFinset hfin)),
s = Quotient_DFe_to_finset DF x := by 
  unfold FacetsFinset at hsf
  rw [Set.Finite.mem_toFinset] at hsf 
  have hsf' : s ∈ FacesFinset hfin := by 
    unfold FacesFinset
    rw [Set.Finite.mem_toFinset]
    exact facets_subset hsf 
  exists Quotient.mk (Setoid.ker (DFe DF)) s 
  rw [Finset.mem_image]
  simp only [exists_prop]
  constructor 
  . exists s
  . unfold Quotient_DFe_to_finset Quotient.lift 
    erw [Quot.liftBeta (DFe DF) (by intro s t hst; change Setoid.Rel (Setoid.ker (DFe DF)) s t at hst; rw [Setoid.ker_def] at hst; exact hst)]
    unfold DFe 
    simp only [facets_subset hsf, dite_true]
    have heq := Decomposition_DF_of_a_facet hdec ⟨s, hsf⟩
    apply_fun (fun s => s.1) at heq
    simp only at heq
    exact heq  


/- The next step is to write FacetsFinset as a disjoint union of the finset of π₀ facets, the finset of homology facets and the finset of other
facets (which we call "boring facets"). -/

def BoringFacets {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF) : 
Set (Finset α) := {s | ∃ (hsf : s ∈ K.facets), ¬(IsPi0Facet hdec ⟨s, hsf⟩) ∧ ¬(IsHomologyFacet hdec ⟨s, hsf⟩)}

lemma BoringFacets_finite {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF) (hfin : FiniteComplex K) : 
(BoringFacets hdec).Finite := by 
  rw [←Set.finite_coe_iff]
  apply @Finite.of_injective _ K.faces hfin (fun s => ⟨s.1, facets_subset (by match s.2 with | ⟨hsf,_⟩ => exact hsf)⟩)
  intro s t heq 
  simp only [Subtype.mk.injEq] at heq
  rw [SetCoe.ext_iff] at heq 
  exact heq 

lemma every_facet_is_boring_or_interesting {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF) (hfin : FiniteComplex K) :
FacetsFinset hfin = Set.Finite.toFinset (BoringFacets_finite hdec hfin) ∪ (Set.Finite.toFinset (π₀Facets_finite hdec hfin)
∪ Set.Finite.toFinset (HomologyFacets_finite hdec hfin)) := by
  ext s 
  unfold FacetsFinset
  rw [Finset.mem_union, Finset.mem_union, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
  unfold BoringFacets π₀Facets HomologyFacets
  simp only [Set.mem_setOf_eq]
  constructor
  . intro hsf
    by_cases IsPi0Facet hdec ⟨s, hsf⟩
    . right; left; exists hsf 
    . by_cases IsHomologyFacet hdec ⟨s, hsf⟩
      . right; right; exists hsf
      . left; exists hsf
  . intro hsf 
    cases hsf with 
    | inr hmed => cases hmed with
                  | inl hpi => exact hpi.1
                  | inr hhom => exact hhom.1
    | inl hbor => exact hbor.1

lemma boring_is_not_interesting {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF) (hfin : FiniteComplex K) :
Disjoint (Set.Finite.toFinset (BoringFacets_finite hdec hfin)) (Set.Finite.toFinset (π₀Facets_finite hdec hfin)
∪ Set.Finite.toFinset (HomologyFacets_finite hdec hfin)) := by 
  rw [Finset.disjoint_iff_ne]
  intro s hsbor t htint 
  rw [Set.Finite.mem_toFinset] at hsbor
  unfold BoringFacets at hsbor
  rw [Finset.mem_union, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset] at htint
  unfold π₀Facets HomologyFacets at htint
  simp only [Set.mem_setOf_eq] at hsbor htint
  by_contra hst
  match hsbor with
  | ⟨hsf, hsbor⟩ => match htint with
                    | Or.inl ⟨_, htpi⟩ => simp_rw [hst] at hsbor
                                          exact hsbor.1 htpi  
                    | Or.inr ⟨_, hthom⟩ => simp_rw [hst] at hsbor
                                           exact hsbor.2 hthom 


lemma pi0_and_homology_are_disjoint {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF) (hfin : FiniteComplex K) :
Disjoint (Set.Finite.toFinset (π₀Facets_finite hdec hfin)) (Set.Finite.toFinset (HomologyFacets_finite hdec hfin)) := by
  rw [Finset.disjoint_iff_ne]
  intro s hspi t hthom
  rw [Set.Finite.mem_toFinset] at hspi hthom
  unfold π₀Facets at hspi 
  unfold HomologyFacets at hthom
  simp only [Set.mem_setOf_eq] at hspi hthom
  match hspi with 
  | ⟨hsf, hspi⟩ => match hthom with
                   | ⟨htf, hthom⟩ => by_contra hst 
                                     simp_rw [hst] at hspi
                                     unfold IsHomologyFacet at hthom
                                     exact hthom.1 hspi                                     

/- Now we have to actually calculate some sums. Firs, if s is boring facet, then the sum on the corresponding interval is 0.-/

lemma AlternatingSumPowerset {s : Finset α} (hsne : s.Nonempty) :
Finset.sum (Finset.powerset s) (fun (t : Finset α) => (-1 : ℤ)^(t.card)) = 0 := by
  have h := Finset.sum_pow_mul_eq_add_pow (-1 : ℤ) (1 : ℤ) s 
  rw [←Finset.card_pos] at hsne 
  simp only [zero_pow hsne, one_pow, mul_one, add_left_neg] at h 
  exact h 

lemma Sum_on_FinsetInterval1 {s t : Finset α} (hst : s ⊂ t) : Finset.sum (Finset.Icc s t) (fun s => (-1 :ℤ)^(Finset.card s)) = 0 := by 
  rw [@Finset.sum_bij ℤ (Finset α) (Finset α) _ (Finset.Icc s t) (Finset.powerset (t \ s)) (fun s => (-1)^(Finset.card s))
  (fun x => (-1)^(Finset.card x + Finset.card s)) (fun x _ => x \ s)
  (fun _ hx => by simp only [Finset.mem_powerset]
                  simp only [gt_iff_lt, Finset.lt_eq_subset, Finset.mem_Icc, Finset.le_eq_subset] at hx
                  exact Finset.sdiff_subset_sdiff hx.2 (le_refl _)
                  )
  (fun x hx => by simp only
                  simp only [gt_iff_lt, Finset.lt_eq_subset, Finset.mem_Icc, Finset.le_eq_subset] at hx
                  rw [←(Finset.card_sdiff_add_card_eq_card hx.1)])
  (fun x y hx hy heq => by simp only at heq 
                           simp only [gt_iff_lt, Finset.lt_eq_subset, Finset.mem_Icc, Finset.le_eq_subset] at hx hy
                           rw [←(Finset.union_sdiff_of_subset hx.1), ←(Finset.union_sdiff_of_subset hy.1)]
                           rw [heq]) 
  (fun x hx => by exists x ∪ s
                  simp only [gt_iff_lt, Finset.lt_eq_subset, Finset.mem_Icc, Finset.le_eq_subset, exists_prop]
                  simp only [Finset.mem_powerset] at hx
                  constructor
                  . constructor
                    . exact Finset.subset_union_right _ _ 
                    . rw [←(Finset.union_sdiff_of_subset (le_of_lt hst)), Finset.union_comm]
                      exact Finset.union_subset_union (le_refl _) hx 
                  . apply Eq.symm
                    apply Finset.union_sdiff_cancel_right
                    apply Finset.disjoint_of_subset_left hx
                    exact Finset.sdiff_disjoint
                     )                 
                  ]
  rw [@Finset.sum_congr ℤ (Finset α) (Finset.powerset (t \ s)) (Finset.powerset (t \ s)) 
  (fun x => (-1 : ℤ)^(Finset.card x + Finset.card s))
  (fun x => (-1 : ℤ)^(Finset.card s) * (-1 : ℤ)^(Finset.card x)) _ rfl
  (fun x _ => by simp only 
                 rw [add_comm, pow_add])]
  rw [←Finset.mul_sum, AlternatingSumPowerset, mul_zero]
  rw [Finset.sdiff_nonempty]
  exact not_le_of_lt hst


lemma Sum_on_FinsetInterval2 {s : Finset α} (hsne : s.Nonempty) : Finset.sum (Finset.Ioc ∅ s) (fun s => (-1 :ℤ)^(Finset.card s - 1)) = 1 := by 
  rw [@Finset.sum_congr ℤ (Finset α) (Finset.Ioc ∅ s) _ (fun s => (-1)^(Finset.card s - 1)) (fun s => (-1 : ℤ) * (-1 : ℤ)^(Finset.card s)) _ rfl
  (fun s hs => by simp only [ge_iff_le, Finset.le_eq_subset, Finset.mem_Ioc, Finset.lt_eq_subset, Finset.empty_ssubset] at hs
                  simp only
                  conv => rhs 
                          congr
                          rw [←(pow_one (-1 : ℤ))]
                  rw [←pow_add]
                  conv => lhs 
                          rw [←(one_mul ((-1 : ℤ)^(Finset.card s - 1)))]
                          congr
                          rw [←neg_one_pow_two]
                  rw [←pow_add]
                  apply congr_arg
                  rw [add_comm, add_comm 1 _, Nat.add_succ, ←(Nat.succ_eq_add_one (Finset.card s)), Nat.succ_inj', ←Nat.succ_eq_add_one,
                         ←Nat.pred_eq_sub_one, Nat.succ_pred_eq_of_pos (by rw [←Finset.card_pos] at hs; exact hs.1)]
  )]
  rw [←Finset.mul_sum]
  have hsum := AlternatingSumPowerset hsne
  have hunion : Finset.powerset s = {∅} ∪ Finset.Ioc ∅ s := by 
    ext t 
    simp only [Finset.mem_powerset, ge_iff_le, Finset.le_eq_subset, Finset.mem_union, Finset.mem_singleton,
  Finset.mem_Ioc, Finset.lt_eq_subset, Finset.empty_ssubset]
    constructor
    . exact fun ht => by by_cases hte : t = ∅
                         . exact Or.inl hte
                         . rw [←ne_eq, ←Finset.nonempty_iff_ne_empty] at hte
                           exact Or.inr ⟨hte, ht⟩
    . exact fun ht => by cases ht with 
                         | inl hte => rw [hte]; simp only [Finset.empty_subset]
                         | inr htne => exact htne.2
  have hdisj : Disjoint {∅} (Finset.Ioc ∅ s) := by 
    rw [Finset.disjoint_iff_ne]
    intro t ht u hu
    simp only [Finset.mem_singleton] at ht
    by_contra habs
    rw [ht] at habs
    rw [←habs] at hu
    simp only [ge_iff_le, Finset.le_eq_subset, Finset.mem_Ioc, lt_self_iff_false, Finset.empty_subset, and_true] at hu
  rw [←(Finset.disjUnion_eq_union _ _ hdisj)] at hunion
  rw [hunion] at hsum 
  rw [Finset.sum_disjUnion hdisj] at hsum
  simp only [Finset.sum_singleton, Finset.card_empty, pow_zero, ge_iff_le, Finset.le_eq_subset] at hsum
  rw [add_comm, ←eq_neg_iff_add_eq_zero] at hsum
  rw [hsum]
  simp only 


lemma BoringFacet_image_by_R {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF) {s : Finset α}
(hs : s ∈ BoringFacets hdec) : R ⟨s, hs.1⟩ ≠ ∅ ∧ R ⟨s, hs.1⟩ ⊂ s :=  by
  unfold BoringFacets at hs
  simp only [Set.mem_setOf_eq] at hs
  match hs with 
  | ⟨hsf, ⟨hs1, hs2⟩⟩ => unfold IsHomologyFacet at hs2 
                         push_neg at hs2
                         constructor
                         . unfold IsPi0Facet at hs1 
                           by_contra hRe 
                           have habs : DecompositionInterval hdec ⟨s, hsf⟩ = Finset.Iic ⟨s, facets_subset hsf⟩ := by 
                             ext t 
                             rw [DecompositionInterval_def]
                             rw [hRe]
                             simp only [Finset.le_eq_subset, Finset.empty_subset, true_and, Finset.mem_Iic]
                             exact ⟨fun h => h, fun h => h⟩
                           exact hs1 habs 
                         . by_contra hRs 
                           have heq := eq_of_le_of_not_lt (hdec.1 ⟨s, hsf⟩) hRs
                           have habs : DecompositionInterval hdec ⟨s, hsf⟩ = {⟨s, facets_subset hsf⟩} := by 
                             ext t 
                             rw [DecompositionInterval_def]
                             rw [heq]
                             simp only [Finset.le_eq_subset, Finset.mem_singleton]
                             constructor
                             . exact fun ⟨hst, hts⟩ => le_antisymm hts hst
                             . exact fun heq => by rw [heq]; exact ⟨le_refl _, le_refl _⟩
                           exact hs2 hs1 habs 


lemma Sum_on_DecompositionInterval_BoringFacet {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF)
{s : Finset α} (hs : s ∈ BoringFacets hdec) : Sum_on_DecompositionInterval R s = 0 := by 
  unfold Sum_on_DecompositionInterval
  unfold DecompositionInterval'
  simp only [(BoringFacet_image_by_R hdec hs).1, ge_iff_le, Finset.le_eq_subset, gt_iff_lt, Finset.lt_eq_subset,
  dite_eq_ite, ite_false, dite_eq_right_iff]
  intro hsf
  rw [@Finset.sum_congr ℤ (Finset α) (Finset.Icc (R ⟨s,hsf⟩) s) _ (fun s => (-1 : ℤ)^(Finset.card s - 1)) 
      (fun s => (-1 : ℤ) * (-1 : ℤ)^(Finset.card s)) _ rfl
      (fun s hsi => by simp only
                       simp only [gt_iff_lt, Finset.lt_eq_subset, Finset.mem_Icc, Finset.le_eq_subset] at hsi
                       have hsne : s.Nonempty := by 
                         by_contra hse 
                         rw [Finset.not_nonempty_iff_eq_empty] at hse
                         rw [hse, Finset.subset_empty] at hsi
                         exact (BoringFacet_image_by_R hdec hs).1 hsi.1
                       rw [←(one_mul ((-1 : ℤ)^(Finset.card s - 1)))]
                       conv => lhs 
                               congr 
                               rw [←neg_one_pow_two]
                       rw [←pow_add]
                       conv => rhs
                               congr
                               rw [←(pow_one (-1 : ℤ))]
                       rw [←pow_add]
                       apply congr_arg
                       rw [add_comm, add_comm 1 _, Nat.add_succ, ←(Nat.succ_eq_add_one (Finset.card s)), Nat.succ_inj', ←Nat.succ_eq_add_one,
                         ←Nat.pred_eq_sub_one, Nat.succ_pred_eq_of_pos (by rw [←Finset.card_pos] at hsne; exact hsne)]
      )]
  rw [←Finset.mul_sum, Sum_on_FinsetInterval1 (BoringFacet_image_by_R hdec hs).2, mul_zero] 
  

lemma π₀Facet_interval {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF) {s : Finset α}
(hs : s ∈ π₀Facets hdec) : DecompositionInterval' R ⟨s, hs.1⟩ = Finset.Ioc ∅ s := by 
  unfold π₀Facets at hs 
  match hs with 
  | ⟨hsf, hs⟩ => unfold IsPi0Facet at hs 
                 ext t 
                 rw [ComparisonIntervals hdec]
                 constructor
                 . exact fun ⟨htf, ht⟩ => by rw [hs] at ht
                                             simp only [Finset.mem_Iic, Subtype.mk_le_mk, Finset.le_eq_subset] at ht
                                             simp only [ge_iff_le, Finset.le_eq_subset, Finset.mem_Ioc, Finset.lt_eq_subset, Finset.empty_ssubset]
                                             exact ⟨K.nonempty_of_mem htf, ht⟩
                 . exact fun ht => by simp only [ge_iff_le, Finset.le_eq_subset, Finset.mem_Ioc, Finset.lt_eq_subset, Finset.empty_ssubset] at ht
                                      exists K.down_closed (facets_subset hsf) ht.2 ht.1
                                      rw [hs]
                                      simp only [Finset.mem_Iic, Subtype.mk_le_mk, Finset.le_eq_subset]
                                      exact ht.2

lemma Sum_on_DecompositionInterval_π₀Facet {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF)
{s : Finset α} (hs : s ∈ π₀Facets hdec) : Sum_on_DecompositionInterval R s = 1 := by 
  unfold Sum_on_DecompositionInterval
  simp only [hs.1, ge_iff_le, dite_true]
  rw [π₀Facet_interval hdec hs]
  exact Sum_on_FinsetInterval2 (K.nonempty_of_mem (facets_subset hs.1))

lemma HomologyFacet_interval {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF) {s : Finset α}
(hs : s ∈ HomologyFacets hdec) : DecompositionInterval' R ⟨s, hs.1⟩ = {s} := by 
  unfold HomologyFacets at hs 
  match hs with 
  | ⟨hsf, hs⟩ => unfold IsHomologyFacet at hs 
                 ext t 
                 rw [ComparisonIntervals hdec]
                 constructor 
                 . exact fun ⟨htf, ht⟩ => by rw [hs.2] at ht
                                             simp only [Finset.mem_singleton, Subtype.mk.injEq] at ht
                                             rw [ht]
                                             simp only [Finset.mem_singleton]
                 . exact fun ht => by simp only [Finset.mem_singleton] at ht
                                      rw [ht]
                                      exists (facets_subset hsf)
                                      rw [hs.2]
                                      simp only [Finset.mem_singleton]


lemma Sum_on_DecompositionInterval_HomologyFacet {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF)
{s : Finset α} (hs : s ∈ HomologyFacets hdec) : Sum_on_DecompositionInterval R s = (-1 : ℤ)^(Finset.card s - 1) := by 
  unfold Sum_on_DecompositionInterval
  simp only [hs.1, ge_iff_le, dite_true]
  rw [HomologyFacet_interval hdec hs]
  simp only [ge_iff_le, Finset.sum_singleton]


/- Finally we put everything to calculate the Euler-Poincaré characteristic of K.-/

lemma EulerPoincareCharacteristicDecomposable (hfin : FiniteComplex K) {R : K.facets → Finset α}  {DF : K.faces → K.facets} 
(hdec : IsDecomposition R DF) :
EulerPoincareCharacteristic hfin = Finset.card (Set.Finite.toFinset (π₀Facets_finite hdec hfin)) + 
Finset.sum (Set.Finite.toFinset (HomologyFacets_finite hdec hfin)) (fun s => (-1 : ℤ)^(Finset.card s - 1)) := by 
  unfold EulerPoincareCharacteristic   
  rw [Finset.sum_partition (Setoid.ker (DFe DF))]
  rw [@Finset.sum_bij ℤ (Quotient (Setoid.ker (DFe DF))) (Finset α) _ (Finset.image (@Quotient.mk'' _ (Setoid.ker (DFe DF))) (FacesFinset hfin))
     (FacetsFinset hfin) _ (Sum_on_DecompositionInterval R) 
     (fun x _ => Quotient_DFe_to_finset DF x) (fun _ hx => Quotient_DFe_to_finset_is_facet DF hfin hx)
     (fun x hx => ComparisonFunctionsonQuotient hdec hfin x hx) (Quotient_DFe_to_finset_inj DF hfin) (Quotient_DFe_to_finset_surj hdec hfin)]
  have hunion := every_facet_is_boring_or_interesting hdec hfin 
  rw [←(Finset.disjUnion_eq_union _ _ (boring_is_not_interesting hdec hfin))] at hunion 
  rw [hunion]
  rw [Finset.sum_disjUnion]
  rw [←(Finset.disjUnion_eq_union _ _ (pi0_and_homology_are_disjoint hdec hfin))] 
  rw [Finset.sum_disjUnion]
  rw [Finset.sum_eq_zero (fun s hs => by rw [Set.Finite.mem_toFinset] at hs
                                         exact Sum_on_DecompositionInterval_BoringFacet hdec hs)]
  rw [zero_add]
  rw [Finset.sum_eq_card_nsmul (fun _ hs => by rw [Set.Finite.mem_toFinset] at hs 
                                               exact Sum_on_DecompositionInterval_π₀Facet hdec hs)]
  erw [smul_eq_mul, mul_one]
  rw [@Finset.sum_congr _ _ _ _ (fun s => Sum_on_DecompositionInterval R s) (fun s => (-1 : ℤ)^(Finset.card s - 1)) _ rfl  
                           (fun s hs => by rw [Set.Finite.mem_toFinset] at hs
                                           exact Sum_on_DecompositionInterval_HomologyFacet hdec hs)]
  

end AbstractSimplicialComplex 

