import TS1.FiniteCoxeterComplex  
import Mathlib.Data.Real.Basic



set_option autoImplicit false

open Classical 

universe u


variable {α : Type u} (μ : α → ℝ)

namespace FiniteWeightedComplex

open AbstractSimplicialComplex Preorder LinearOrderedPartitions FiniteCoxeterComplex 

/- The weighted complex is the subcomplex of the Coxeter complex whose faces are nonempty elements E of AFLOPowerset such that
∑_X μ is nonnegative for every X ∈ E.-/

def IsPositiveSet {X : Set α} (hXfin : Finite X) : Prop := Finset.sum (Set.Finite.toFinset (Set.finite_coe_iff.mp hXfin)) μ ≥ 0 


def AFLOPowerset_positive : Set (Finset (Set α)) := 
{E | ∃ (hE : E ∈ AFLOPowerset α), ∀ {X : Set α} (hXE : X ∈ E), IsPositiveSet μ (hE.2 X hXE).2}

instance AFLOPowerset_positive.PartialOrder : PartialOrder (AFLOPowerset_positive μ) :=
Subtype.partialOrder _ 

lemma AFLOPowerset_forget_positive : AFLOPowerset_positive μ ⊆ AFLOPowerset α := fun _ ⟨hE, _⟩ => hE  

def AFLOPartitions_positive : Set (Preorder α) := {p | ∃ (hp : p ∈ AFLOPartitions α), preorderToPowersetFinset ⟨p, hp⟩ ∈ AFLOPowerset_positive μ}

instance AFLOPartitions_positive.PartialOrder : PartialOrder (AFLOPartitions_positive μ) :=
Subtype.partialOrder _ 


lemma AFLOPartitions_forget_positive : AFLOPartitions_positive μ ⊆ AFLOPartitions α := fun _ ⟨hp, _⟩ => hp
  

lemma AFLOPowerset_positive_down_closed : ∀ {E F : Finset (Set α)}, E ∈ AFLOPowerset_positive μ → F ⊆ E → F ∈ AFLOPowerset_positive μ := by 
  intro E F hE hFE 
  exists (AFLOPowerset_down_closed α (AFLOPowerset_forget_positive μ hE) hFE)
  intro X hXF 
  match hE with 
  | ⟨_, hpos⟩ => exact hpos (hFE hXF)


def WeightedComplex  := of_erase (AFLOPowerset_positive μ) (AFLOPowerset_positive_down_closed μ)


lemma FacesWeightedComplex (s : Finset (Set α)) : s ∈ (WeightedComplex μ).faces ↔ s ∈ (AFLOPowerset_positive μ) ∧ s ≠ ∅ := by 
  unfold WeightedComplex
  simp only [of_erase_faces, Set.mem_diff, Set.mem_singleton_iff, ne_eq]

lemma WeightedComplex_subcomplex : WeightedComplex μ ≤ CoxeterComplex α := by 
  intro s hsf 
  rw [FacesWeightedComplex] at hsf 
  rw [FacesCoxeterComplex]
  exact ⟨AFLOPowerset_forget_positive μ hsf.1, hsf.2⟩

/- The set AFLOPowerset_positive μ is in order-reversing bijection with the set of positive linearly ordered partitions of α. 
(If α is not finite, we have to use finite linearly ordered partitions with finite proper initial intervals.)-/

lemma AFLO_positive_powersetToPreorder (E : AFLOPowerset_positive μ) : powersetToPreorder (E.1 : Set (Set α)) ∈ AFLOPartitions_positive μ := by 
  have hE := E.2 
  match hE with 
  | ⟨hE, hpos⟩ => 
    unfold AFLOPartitions_positive 
    exists (AFLO_powersetToPreorder ⟨E.1, hE⟩) 
    unfold AFLOPowerset_positive 
    exists (AFLO_preorderToPowerset ⟨_, (AFLO_powersetToPreorder ⟨E.1, hE⟩)⟩)
    intro X hXE 
    unfold preorderToPowersetFinset at hXE
    rw [Set.Finite.mem_toFinset] at hXE 
    simp only at hXE 
    have heq : ⟨E.1, hE⟩ = (CoxeterComplextoPartitions α).invFun ((CoxeterComplextoPartitions α).toFun ⟨E.1, hE⟩) := by 
      simp only [Equiv.toFun_as_coe_apply, RelIso.coe_toEquiv, Equiv.invFun_as_coe, OrderIso.toEquiv_symm, OrderIso.symm_apply_apply]
    rw [←SetCoe.ext_iff] at heq
    unfold CoxeterComplextoPartitions preorderToPowersetFinset at heq
    simp only at heq 
    rw [←Finset.coe_inj, Set.Finite.coe_toFinset] at heq 
    rw [←heq] at hXE
    exact hpos hXE    

lemma AFLO_positive_preorderToPowerset (p : AFLOPartitions_positive μ) : 
preorderToPowersetFinset ⟨p.1, AFLOPartitions_forget_positive μ p.2⟩ ∈ AFLOPowerset_positive μ := by
  have hp := p.2 
  match hp  with 
  | ⟨hp, hpos⟩ => 
    unfold AFLOPowerset_positive 
    exists (AFLO_preorderToPowerset ⟨p.1, hp⟩)
    exact fun hXE => hpos.2 hXE 



noncomputable def WeightedComplextoPositivePartitions : OrderIso (AFLOPowerset_positive μ) (AFLOPartitions_positive μ)ᵒᵈ where
toFun := fun E => ⟨powersetToPreorder E.1, AFLO_positive_powersetToPreorder μ E⟩
invFun := fun p => ⟨preorderToPowersetFinset ⟨p.1, AFLOPartitions_forget_positive μ p.2⟩, AFLO_positive_preorderToPowerset μ p⟩ 
left_inv := fun E => by simp only; rw [←SetCoe.ext_iff]
                        match E.2 with 
                        | ⟨hE, _⟩ => 
                          apply Eq.symm; apply subset_antisymm 
                          . rw [Set.Finite.subset_toFinset] 
                            intro X hXE 
                            apply powersetToPreorderToPowerset (E.1 : Set (Set α)) hXE (hE.2 X hXE).1.1 (hE.2 X hXE).1.2    
                          . rw [Set.Finite.toFinset_subset]
                            apply TotalELFP_powersetToPreorderToPowerset (E : Set (Set α))
                            . exact (AFLO_powersetToPreorder ⟨E.1, hE⟩).1  
                            . exact AFLOPartition_is_ELF ⟨powersetToPreorder (E.1 : Set (Set α)), AFLO_powersetToPreorder ⟨E.1, hE⟩⟩    
right_inv := fun p => by simp only [Set.Finite.coe_toFinset]
                         rw [←SetCoe.ext_iff]
                         exact Eq.symm (preorderToPowersetToPreorder p.1) 
map_rel_iff' := by intro E F
                   match E.2, F.2 with 
                   | ⟨hE, _⟩, ⟨hF, _⟩ =>  
                     simp only [Equiv.coe_fn_mk]
                     constructor 
                     . intro hEF 
                       have hE : ↑E.1 ⊆ preorderToPowerset (powersetToPreorder (E.1 : Set (Set α))) := by 
                         intro X hXE 
                         exact powersetToPreorderToPowerset (E.1 : Set (Set α)) hXE (hE.2 X hXE).1.1 (hE.2 X hXE).1.2 
                       have hF : preorderToPowerset (powersetToPreorder (F.1 : Set (Set α))) ⊆ ↑F.1 :=  
                         TotalELFP_powersetToPreorderToPowerset (F.1 : Set (Set α)) (AFLO_powersetToPreorder ⟨F.1, hF⟩).1
                            (AFLOPartition_is_ELF ⟨powersetToPreorder (F.1 : Set (Set α)), AFLO_powersetToPreorder ⟨F.1, hF⟩⟩)
                       change E.1 ⊆ F.1 
                       rw [←Finset.coe_subset]
                       refine le_trans hE ?_
                       refine le_trans ?_ hF 
                       exact preorderToPowerset_antitone hEF 
                     . exact powersetToPreorder_antitone 






/- For future use, we isolate the fact that, is s in Finset (Set α) corresponds to a face of the weighted complex, then we have
s = preorderToPowerset (powersetToPreorder s).-/

lemma WeightedFaces_powersetToPreordertoPowerset {s : Finset (Set α)} (hsf : s ∈ (WeightedComplex μ).faces) : 
↑s = preorderToPowerset (powersetToPreorder (s : Set (Set α))) := 
Faces_powersetToPreordertoPowerset (WeightedComplex_subcomplex μ hsf)



/- The restriction map: it is given by applying the order isomorphisms to ordered partitions, taking the descent partition (with respect to a fixed auxiliary
linear order) and applying the inverse of the order isomorphism.-/

/- To show that the descent partition of a positive AFLO partition is AFLO, we show that positive AFLO partitions form an upper set. 
This is a formal consequences of the fact (proved above) that the positive AFLO powerset is a lower set.-/

lemma AFLOPartitions_positive_IsUpperSet : IsUpperSet (AFLOPartitions_positive μ) := by 
  intro p q hpq hp 
  match hp with
  | ⟨hp, hpos⟩ => 
    exists AFLOPartitions_IsUpperSet α hpq hp  
    match hpos with 
    | ⟨_, hpos⟩ => 
      unfold AFLOPowerset_positive
      simp 
      have hq := AFLOPartitions_IsUpperSet α hpq hp  
      have hsub : preorderToPowersetFinset ⟨q, hq⟩ ⊆ preorderToPowersetFinset ⟨p, hp⟩ := by 
        unfold preorderToPowersetFinset 
        rw [Set.Finite.toFinset_subset, Set.Finite.coe_toFinset]
        apply preorderToPowerset_antitone
        exact hpq 
      exists AFLOPowerset_down_closed α (AFLO_preorderToPowerset ⟨p, hp⟩) hsub     
      intro X hXE 
      exact hpos (hsub hXE) 


lemma AscentPartition_respects_AFLO_positive (r : LinearOrder α) {s : Preorder α} (hs : s ∈ AFLOPartitions_positive μ) : 
AscentPartition r (AFLOPartitions_forget_positive μ hs).1 ∈ AFLOPartitions_positive μ := by 
  apply AFLOPartitions_positive_IsUpperSet μ (AscentPartition_is_greater r (AFLOPartitions_forget_positive μ hs).1)
  exact hs 


noncomputable def restriction_weighted (r : LinearOrder α) (E : AFLOPowerset_positive μ) : AFLOPowerset_positive μ := 
  (WeightedComplextoPositivePartitions μ).invFun 
   ⟨@AscentPartition _ r (powersetToPreorder (E.1 :Set (Set α))) (AFLO_powersetToPreorder ⟨E.1, AFLOPowerset_forget_positive μ E.2⟩).1,
    AscentPartition_respects_AFLO_positive μ r (AFLO_positive_powersetToPreorder μ E)⟩ 


lemma restriction_weighted_is_smaller (r : LinearOrder α) (E : AFLOPowerset_positive μ) : restriction_weighted μ r E ≤ E := by
  unfold restriction_weighted 
  have hEeq := (WeightedComplextoPositivePartitions μ).left_inv E 
  rw [←hEeq]
  rw [←(WeightedComplextoPositivePartitions μ).map_rel_iff']
  simp only [Equiv.toFun_as_coe_apply, RelIso.coe_toEquiv, Equiv.invFun_as_coe, OrderIso.toEquiv_symm,
    OrderIso.symm_apply_apply, OrderIso.apply_symm_apply]
  unfold WeightedComplextoPositivePartitions
  simp only [RelIso.coe_fn_mk, Equiv.coe_fn_mk]
  change @AscentPartition _ r (powersetToPreorder (E.1 :Set (Set α))) (AFLO_powersetToPreorder ⟨E.1, AFLOPowerset_forget_positive μ E.2⟩).1 
    ≥ powersetToPreorder E.1 
  exact AscentPartition_is_greater r _ 



/- Version for the weighted complex.-/

noncomputable def R_weighted (r : LinearOrder α) : (WeightedComplex μ).facets → Finset (Set α) := by 
  intro ⟨s, hsf⟩
  rw [mem_facets_iff] at hsf 
  rw [FacesWeightedComplex] at hsf 
  exact (restriction_weighted μ r ⟨s,hsf.1.1⟩).1 



-- Finite α only.

variable [Fintype α]



/- Simpler descriptions of positive AFLO partitions and powerset.-/

lemma AFLOPartitions_iff (p : Preorder α) : p ∈ AFLOPartitions_positive μ ↔ Total p.le ∧ ∀ (X : Set α), 
X ∈ preorderToPowerset p → @IsPositiveSet _ μ X inferInstance := by 
  constructor 
  . intro hp 
    rw [and_iff_right (AFLOPartitions_forget_positive μ hp).1]
    match hp with 
    | ⟨_, hpos⟩ => 
      match hpos with 
      | ⟨_, hpos⟩ =>
        intro X hXp 
        have hXp' : X ∈ preorderToPowersetFinset ⟨p, AFLOPartitions_forget_positive μ hp⟩ := by 
          rw [Set.Finite.mem_toFinset]
          exact hXp
        exact hpos hXp'
  . intro hp 
    have hp' : p ∈ AFLOPartitions α := by
      rw [←AFLOPartitions_is_everything]
      exact hp.1
    exists hp'
    exists (AFLO_preorderToPowerset ⟨p, hp'⟩)
    intro X hXp 
    rw [Set.Finite.mem_toFinset] at hXp 
    exact hp.2 X hXp 


lemma AFLOPowerset_positive_iff (E : Finset (Set α)) : E ∈ AFLOPowerset_positive μ ↔ 
(Total (fun (X : E) => fun (Y : E) => X.1 ⊆ Y.1) ∧ ∀ (X : Set α), X ∈ E → (X ≠ ⊥ ∧ X ≠ ⊤) ∧ @IsPositiveSet _ μ X inferInstance) := by 
  constructor 
  . intro h 
    match h with 
    | ⟨hE, hpos⟩ => exact ⟨hE.1, fun X hXE => ⟨(hE.2 X hXE).1, hpos hXE⟩⟩ 
  . intro h 
    have hE : E ∈ AFLOPowerset α := by 
      rw [←AFLOPowerset_is_everything]
      rw [and_iff_right h.1]
      exact fun X hXE => (h.2 X hXE).1 
    exists hE 
    exact fun hXE => (h.2 _ hXE).2 

#exit 


/- The facets of the Coxeter complex correspond to linear orders on α. (If α is infinite, the Coxeter complex has no facets, and the linear orders
will define maximal ideals of the face poset of the Coxeter complex, though we don't get all maximal ideals this way.)-/

lemma Facets_are_linear_orders {s : Finset (Set α)} (hsF : s ∈ (CoxeterComplex α).faces) : 
s ∈ (CoxeterComplex α).facets ↔ IsLinearOrder α (powersetToPreorder ↑s).le := by 
  constructor 
  . intro hsf 
    rw [mem_facets_iff] at hsf 
    have hsf' := hsf.1 
    rw [FacesCoxeterComplex] at hsf 
    set p:= (CoxeterComplextoPartitions α).toFun ⟨s, hsf.1.1⟩
    apply minimal_partition_is_linear_order ⟨p.1, p.2.1⟩ 
    intro ⟨q, hq⟩ hqp
    rw [AFLOPartitions_is_everything] at hq 
    set t := (CoxeterComplextoPartitions α).invFun ⟨q, hq⟩
    have ht := t.2 
    have hst : s ⊆ t.1 := by 
      change ⟨s, hsf.1.1⟩ ≤ t 
      rw [←(CoxeterComplextoPartitions α).map_rel_iff']
      simp only [RelIso.coe_toEquiv, Equiv.invFun_as_coe, OrderIso.toEquiv_symm, OrderIso.apply_symm_apply] 
      change q ≤ p.1 
      exact hqp 
    have htne : t.1 ≠ ∅ := by 
      by_contra habs 
      rw [habs, Finset.subset_empty, ←Finset.not_nonempty_iff_eq_empty] at hst 
      exact hst ((CoxeterComplex α).nonempty_of_mem hsf') 
    have htf : t.1 ∈ (CoxeterComplex α).faces := by 
      rw [FacesCoxeterComplex]
      exact ⟨ht, htne⟩
    have heq := Eq.symm (hsf.2 htf hst)
    have heq' : t = ⟨s, hsf.1.1⟩ := by 
      rw [←SetCoe.ext_iff]
      exact heq
    apply_fun (CoxeterComplextoPartitions α).toFun at heq'
    simp only [Equiv.invFun_as_coe, OrderIso.toEquiv_symm, RelIso.coe_toEquiv, Equiv.toFun_as_coe_apply,
       OrderIso.apply_symm_apply] at heq'
    rw [←SetCoe.ext_iff] at heq' |-
    exact heq' 
  . intro hlins 
    rw [mem_facets_iff, and_iff_right hsF]
    intro t htf hst 
    rw [FacesCoxeterComplex] at hsF htf 
    set p := (CoxeterComplextoPartitions α).toFun ⟨s, hsF.1⟩
    set q := (CoxeterComplextoPartitions α).toFun ⟨t, htf.1⟩
    have hqp : q.1 ≤ p.1 := by 
      change p ≤ q 
      simp only [Equiv.toFun_as_coe_apply, RelIso.coe_toEquiv, map_le_map_iff, Subtype.mk_le_mk,
         Finset.le_eq_subset]
      exact hst 
    have heq := linearOrder_is_minimal_partition hlins q.2.1 hqp 
    have heq' : q = p := by 
      rw [←SetCoe.ext_iff]
      exact heq
    simp only [Equiv.toFun_as_coe_apply, RelIso.coe_toEquiv, EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq] at heq'
    exact Eq.symm heq' 

/- We identify the facets whose R is ∅ or the facet itself. We assume α finite for this, otherwise there are no facets (*) and the statement is
empty.-/
/- (*) TODO: prove this statement-/

lemma R_eq_empty_iff (r : LinearOrder α) {s : Finset (Set α)} (hsf : s ∈ (CoxeterComplex α).facets) : 
R r ⟨s, hsf⟩ = ∅ ↔ powersetToPreorder (s : Set (Set α)) = r.toPartialOrder.toPreorder := by 
  have hsf' := hsf
  unfold R restriction CoxeterComplextoPartitions
  simp only [Set.Finite.toFinset_eq_empty]
  rw [mem_facets_iff, FacesCoxeterComplex] at hsf 
  have hiff : ∀ (p : Preorder α) (hlinp : IsLinearOrder α p.le), preorderToPowerset (AscentPartition r hlinp.toIsTotal.total) = ∅ 
    ↔ p = r.toPartialOrder.toPreorder := by 
    intro p hlinp 
    rw [←preorderToPowerset_TrivialPreorder_is_empty]
    constructor 
    . exact fun h =>
       AscentPartition_trivial_implies_fixed_linear_order r hlinp (preorderToPowerset_injective h)   
    . intro h  
      rw [←(AscentPartition_fixed_linear_order r)]
      apply congr_arg 
      ext a b 
      change (AscentPartition_aux _ _ a b) ↔ (AscentPartition_aux _ _ a b) 
      rw [h]
  rw [hiff]
  rw [←Facets_are_linear_orders]
  exact hsf' 
  exact (facets_subset hsf') 


lemma R_eq_self_iff (r : LinearOrder α) {s : Finset (Set α)} (hsf : s ∈ (CoxeterComplex α).facets) : 
R r ⟨s, hsf⟩ = s ↔ powersetToPreorder (s : Set (Set α)) = (dual r).toPartialOrder.toPreorder := by 
  have hsf' := hsf 
  unfold R restriction CoxeterComplextoPartitions
  rw [←Finset.coe_inj, Set.Finite.coe_toFinset]
  rw [mem_facets_iff] at hsf  
  simp only 
  have heq := Faces_powersetToPreordertoPowerset hsf.1  
  nth_rewrite 2 [heq]
  have hiff : ∀ (p : Preorder α) (hlinp : IsLinearOrder α p.le), AscentPartition r hlinp.toIsTotal.total = 
    p  ↔ p = (dual r).toPartialOrder.toPreorder := by 
    intro p hlinp 
    constructor 
    . intro heq 
      refine AscentPartition_linear_implies_dual_linear_order r hlinp ?_ heq
      exact Fintype.toLocallyFiniteOrder  
    . intro heq 
      simp_rw [heq]
      rw [AscentPartition_dual_fixed_linear_order]
  constructor 
  . intro h 
    have h:= preorderToPowerset_injective h
    rw [hiff] at h
    exact h
    rw [←Facets_are_linear_orders]
    exact hsf'
    exact facets_subset hsf'  
  . intro heq 
    nth_rewrite 2 [heq]
    rw [←AscentPartition_dual_fixed_linear_order]
    apply congr_arg
    ext a b 
    change AscentPartition_aux r _ a b ↔ AscentPartition_aux r _ a b
    rw [heq] 



/- The "distinguished facet" of the decomposition. (For this we need to choose an auxiliary linear order on α.)-/

lemma LinearOrder_etc_respects_AFLO (r : LinearOrder α) {s : Preorder α} (hs : s ∈ AFLOPartitions α) : 
LinearOrder_of_total_preorder_and_linear_order r s ∈ AFLOPartitions α := by 
  rw [←AFLOPartitions_is_everything]
  exact LinearOrder_of_total_preorder_and_linear_order_is_total r hs.1 


noncomputable def distinguishedFacet (r : LinearOrder α) (E : AFLOPowerset α) : AFLOPowerset α := 
  (CoxeterComplextoPartitions α).invFun 
   ⟨@LinearOrder_of_total_preorder_and_linear_order _ r (powersetToPreorder (E.1 :Set (Set α))),
    LinearOrder_etc_respects_AFLO r (AFLO_powersetToPreorder E)⟩ 
  

lemma distinguishedFacet_is_bigger (r : LinearOrder α) (E : AFLOPowerset α) : E ≤ distinguishedFacet r E := by
  unfold distinguishedFacet
  have hEeq := (CoxeterComplextoPartitions α).left_inv E 
  rw [←hEeq]
  rw [←(CoxeterComplextoPartitions α).map_rel_iff']
  simp only [Equiv.toFun_as_coe_apply, RelIso.coe_toEquiv, Equiv.invFun_as_coe, OrderIso.toEquiv_symm,
    OrderIso.symm_apply_apply, OrderIso.apply_symm_apply]
  unfold CoxeterComplextoPartitions
  simp only [RelIso.coe_fn_mk, Equiv.coe_fn_mk]
  change @LinearOrder_of_total_preorder_and_linear_order _ r (powersetToPreorder (E.1 :Set (Set α))) ≤ powersetToPreorder E.1 
  exact LinearOrder_of_total_preorder_and_linear_order_is_smaller _ _ 

lemma distinguishedFacet_is_facet (r : LinearOrder α) (E : AFLOPowerset α) (hEf : E.1 ∈ (CoxeterComplex α).faces) : 
(distinguishedFacet r E).1 ∈ (CoxeterComplex α).facets := by
  have hf : (distinguishedFacet r E).1 ∈ (CoxeterComplex α).faces := by 
    rw [FacesCoxeterComplex]
    rw [and_iff_right (distinguishedFacet r E).2]
    have hsub := distinguishedFacet_is_bigger r E 
    change E.1 ⊆ _ at hsub 
    by_contra habs 
    rw [habs, Finset.subset_empty, ←Finset.not_nonempty_iff_eq_empty] at hsub
    exact hsub ((CoxeterComplex α).nonempty_of_mem hEf) 
  rw [Facets_are_linear_orders hf]
  unfold distinguishedFacet 
  unfold CoxeterComplextoPartitions
  simp only [Set.Finite.coe_toFinset]
  rw [←preorderToPowersetToPreorder]
  refine LinearOrder_of_total_preorder_and_linear_order_is_linear r ?_  
  apply powersetToPreorder_total_is_total 
  exact E.2.1 

/- Version for the Coxeter complex.-/

noncomputable def DF (r : LinearOrder α) : (CoxeterComplex α).faces → (CoxeterComplex α).facets := by 
  intro ⟨s, hsf⟩
  have hsf' := hsf
  rw [FacesCoxeterComplex] at hsf'
  exact ⟨distinguishedFacet r ⟨s, hsf'.1⟩, distinguishedFacet_is_facet r ⟨s, hsf'.1⟩ hsf⟩


/- We prove that the Coxeter complex is decomposable.-/

lemma CoxeterComplex_is_decomposable (r : LinearOrder α) : IsDecomposition (R r) (DF r) := by 
  constructor 
  . intro ⟨s, hsf⟩
    rw [mem_facets_iff, FacesCoxeterComplex] at hsf
    exact restriction_is_smaller r ⟨s, hsf.1.1⟩ 
  . intro ⟨s, hsf⟩ ⟨t, htf⟩ 
    have htf' := htf 
    rw [mem_facets_iff] at htf 
    rw [FacesCoxeterComplex] at hsf htf 
    unfold R DF restriction distinguishedFacet
    simp only [Equiv.invFun_as_coe, OrderIso.toEquiv_symm, RelIso.coe_toEquiv, Subtype.mk.injEq]
    set p := (CoxeterComplextoPartitions α).toFun ⟨s, hsf.1⟩
    set q := (CoxeterComplextoPartitions α).toFun ⟨t, htf.1.1⟩
    constructor 
    . intro hint 
      rw [and_comm] at hint 
      have hqp : q.1 ≤ p.1 := by 
        change p ≤ q
        simp only [Equiv.toFun_as_coe_apply, RelIso.coe_toEquiv, map_le_map_iff, Subtype.mk_le_mk, Finset.le_eq_subset]
        exact hint.1 
      have hpq : p.1 ≤ @AscentPartition _ r q.1 q.2.1 := by 
        change ⟨@AscentPartition _ r q.1 q.2.1, AscentPartition_respects_AFLO r q.2⟩ ≤ p 
        have h := hint.2 
        change (CoxeterComplextoPartitions α).invFun ⟨@AscentPartition _ r q.1 q.2.1, AscentPartition_respects_AFLO r q.2⟩ ≤ 
           (⟨s, hsf.1⟩ : AFLOPowerset α) at h
        apply_fun (CoxeterComplextoPartitions α).toFun at h 
        simp only [Equiv.toFun_as_coe_apply, RelIso.coe_toEquiv, Equiv.invFun_as_coe, OrderIso.toEquiv_symm,
            OrderIso.apply_symm_apply] at h
        exact h   
        exact (CoxeterComplextoPartitions α).monotone 
      have hqlin : IsLinearOrder α q.1.le := by 
        rw [Facets_are_linear_orders (facets_subset htf')] at htf' 
        exact htf' 
      have halmost := @LinearOrder_of_total_preorder_and_linear_order_on_ascent_interval' _ r q.1 p.1 hqlin p.2.1 hqp hpq
      have h' : q = ⟨LinearOrder_of_total_preorder_and_linear_order r p.1, LinearOrder_etc_respects_AFLO r p.2⟩ := by 
        rw [←SetCoe.ext_iff]
        exact halmost   
      apply_fun (CoxeterComplextoPartitions α).invFun at h'
      simp only [Equiv.toFun_as_coe_apply, RelIso.coe_toEquiv, Equiv.invFun_as_coe, OrderIso.toEquiv_symm,
         OrderIso.symm_apply_apply] at h'
      rw [←SetCoe.ext_iff] at h' 
      exact h' 
    . intro heq 
      have hqp : q.1 = LinearOrder_of_total_preorder_and_linear_order r p.1 := by 
        simp only [Equiv.toFun_as_coe_apply, RelIso.coe_toEquiv]
        have h : q = ⟨LinearOrder_of_total_preorder_and_linear_order r p.1, LinearOrder_etc_respects_AFLO r p.2⟩ := by
          apply Equiv.injective (CoxeterComplextoPartitions α).toEquiv.symm 
          simp only [OrderIso.toEquiv_symm, Equiv.toFun_as_coe_apply, RelIso.coe_toEquiv, OrderIso.symm_apply_apply]
          rw [←SetCoe.ext_iff]
          exact heq
        rw [←SetCoe.ext_iff] at h 
        exact h 
      have hqlin : IsLinearOrder α q.1.le := by 
        rw [hqp]
        exact LinearOrder_of_total_preorder_and_linear_order_is_linear r p.2.1 
      have halmost := @LinearOrder_of_total_preorder_and_linear_order_fibers _ r q.1 p.1 hqlin p.2.1 (Eq.symm hqp)        
      rw [and_comm]
      change p ≤ q ∧ ⟨@AscentPartition _ r q.1 q.2.1, AscentPartition_respects_AFLO r q.2⟩ ≤ p  at halmost 
      erw [(CoxeterComplextoPartitions α).map_rel_iff'] at halmost 
      erw [and_iff_right halmost.1] 
      have halmost := halmost.2 
      simp only [Equiv.toFun_as_coe_apply, RelIso.coe_toEquiv] at halmost
      apply_fun (CoxeterComplextoPartitions α).invFun at halmost 
      simp only [Equiv.invFun_as_coe, OrderIso.toEquiv_symm, RelIso.coe_toEquiv, OrderIso.symm_apply_apply] at halmost
      exact halmost 
      exact (CoxeterComplextoPartitions α).symm.monotone 


/- The Coxeter complex is nonempty if and only if Fintype.card α ≥ 2.-/


variable (α)

lemma CoxeterComplex_nonempty_iff : (CoxeterComplex α).faces.Nonempty ↔ Fintype.card α ≥ 2 := by 
  constructor 
  . intro hne 
    match hne with
  | ⟨s, hsf⟩ => rw [FacesCoxeterComplex] at hsf 
                have heq : ⟨s, hsf.1⟩ = (CoxeterComplextoPartitions α).invFun ((CoxeterComplextoPartitions α).toFun ⟨s, hsf.1⟩) := by
                  simp only [Equiv.toFun_as_coe_apply, RelIso.coe_toEquiv, Equiv.invFun_as_coe, OrderIso.toEquiv_symm,
                  OrderIso.symm_apply_apply]
                unfold CoxeterComplextoPartitions at heq 
                simp only at heq 
                rw [←SetCoe.ext_iff] at heq 
                unfold preorderToPowersetFinset at heq
                simp only at heq 
                rw [←Finset.coe_inj, Set.Finite.coe_toFinset] at heq  
                have hnt : powersetToPreorder (s : Set (Set α)) ≠ trivialPreorder α := by 
                  by_contra habs 
                  rw [habs] at heq 
                  rw [(preorderToPowerset_is_empty_iff_TrivialPreorder (trivialPreorder α)).mpr rfl] at heq 
                  rw [Finset.coe_eq_empty] at heq 
                  exact hsf.2 heq
                simp_rw [nontrivial_preorder_iff_exists_not_le] at hnt 
                change Nat.succ 1 ≤ _ 
                rw [Nat.succ_le_iff, Fintype.one_lt_card_iff]
                match hnt with 
                | ⟨a, b, hab⟩ => have hne : a ≠ b := by 
                                   by_contra heq 
                                   rw [heq] at hab 
                                   exact hab ((powersetToPreorder (s : Set (Set α))).le_refl _)
                                 exact ⟨a, b, hne⟩
  . intro hcard
    change Nat.succ 1  ≤ _ at hcard 
    rw [Nat.succ_le_iff, Fintype.one_lt_card_iff] at hcard
    match hcard with 
    | ⟨a, b, hab⟩ => set p := twoStepPreorder a  
                     have hp := (AFLOPartitions_is_everything p).mp (twoStepPreorder_IsTotal a)
                     set s := (CoxeterComplextoPartitions α).invFun ⟨p, hp⟩ with hsdef 
                     have hsne : s.1 ≠ ∅ := by 
                       by_contra he 
                       rw [hsdef] at he 
                       unfold CoxeterComplextoPartitions at he 
                       simp only at he 
                       unfold preorderToPowersetFinset at he 
                       rw [Set.Finite.toFinset_eq_empty] at he  
                       change preorderToPowerset (twoStepPreorder a) = ∅ at he 
                       rw [preorderToPowerset_is_empty_iff_TrivialPreorder] at he 
                       exact twoStepPreorder_nontrivial hab he
                     have hsf : s.1 ∈ (CoxeterComplex α).faces := by 
                       rw [FacesCoxeterComplex]
                       exact ⟨s.2, hsne⟩
                     exact ⟨s.1, hsf⟩ 

                      

/- The Coxeter complex is finite.-/
 

lemma CoxeterComplex_is_finite : FiniteComplex (CoxeterComplex α) := by 
  rw [FiniteComplex]
  have hsub : (CoxeterComplex α).faces ⊆ @Set.univ (Finset (Set α)) := by 
    simp only [Set.subset_univ]
  exact Finite.Set.subset _ hsub  

variable {α}

/- Dimension of the facets of the Coxeter complex.-/

lemma NonemptyType_of_face_CoxeterComplex {s : Finset (Set α)} (hs : s ∈ (CoxeterComplex α).faces) : 
Nonempty α := by 
  rw [←Fintype.card_pos_iff]
  refine lt_trans Nat.zero_lt_one ?_ 
  rw [←Nat.succ_le_iff]
  exact (CoxeterComplex_nonempty_iff α).mp ⟨s, hs⟩ 

lemma CoxeterComplex_dimension_facet (s : (CoxeterComplex α).facets) :
Finset.card s.1 = Fintype.card α -1 := by 
  have hsf := s.2 
  rw [mem_facets_iff, FacesCoxeterComplex] at hsf
  rw [CoxeterComplex_dimension_face ⟨s.1, hsf.1.1⟩ (NonemptyType_of_face_CoxeterComplex (facets_subset s.2))]
  set p := (CoxeterComplextoPartitions α).toFun ⟨s, hsf.1.1⟩
  have hlinp : IsLinearOrder α p.1.le := (Facets_are_linear_orders (facets_subset s.2)).mp s.2
  have hAR := @antisymmRel_iff_eq _ p.1.le hlinp.toIsPartialOrder.toIsPreorder.toIsRefl hlinp.toIsPartialOrder.toIsAntisymm 
  haveI := p.2.2.2 
  rw [@Fintype.card_of_bijective _ _ _ (Fintype.ofFinite _) (toAntisymmetrization p.1.le)] 
  unfold Function.Bijective 
  erw [and_iff_left (@surjective_quotient_mk _ (AntisymmRel.setoid α p.1.le))]
  intro a b hab
  have hab := Quotient.exact hab 
  change AntisymmRel p.1.le a b at hab
  exact hAR.mp hab  


/- The Coxeter complex is pure (of dimension Fintype.card α - 2, since we know that the facets have cardinality Fintype.card α - 1).-/

variable (α)

lemma CoxeterComplex_is_pure : Pure (CoxeterComplex α) := 
Dimension_of_Noetherian_pure (Finite_implies_Noetherian (CoxeterComplex_is_finite α)) 
(fun s t hsf htf => by rw [CoxeterComplex_dimension_facet ⟨s, hsf⟩, CoxeterComplex_dimension_facet ⟨t, htf⟩])

/- The Coxeter complex has (Fintype.card α)! facets.-/

lemma FacetsCoxeterComplex.card : Finset.card (Set.Finite.toFinset (Set.finite_coe_iff.mp (FiniteComplex_has_finite_facets (CoxeterComplex_is_finite α)))) 
= Nat.factorial (Fintype.card α) := sorry 

/- We find the π₀ and homology facets: the unique π₀ facet is the minimal one for the weak Bruhat order (i.e. the one corresponding to r), and
the unique homology facet is the maximal one for the weak Bruhat order (i.e. the one corresponding to the dual of r).-/

variable {α} 

lemma CoxeterComplex_Pi0Facet (r : LinearOrder α) {s : Finset (Set α)} (hsf : s ∈ (CoxeterComplex α).facets) :
IsPi0Facet (CoxeterComplex_is_decomposable r) ⟨s, hsf⟩ ↔ powersetToPreorder (s : Set (Set α)) = r.toPartialOrder.toPreorder ∨ Fintype.card α = 2 := by 
  rw [IsPi0Facet_iff, R_eq_empty_iff]
  constructor 
  . intro h 
    cases h with 
    | inl hR => exact Or.inl hR
    | inr hcard => rw [CoxeterComplex_dimension_facet ⟨s, hsf⟩] at hcard 
                   change _ = Nat.succ 0 at hcard 
                   rw [←Nat.pred_eq_sub_one, Nat.pred_eq_succ_iff, zero_add] at hcard
                   exact Or.inr hcard  
  . intro h 
    cases h with 
    | inl hR => exact Or.inl hR 
    | inr hcard => apply Or.inr 
                   rw [CoxeterComplex_dimension_facet ⟨s, hsf⟩, hcard]


                  
  

lemma CoxeterComplex_HomologyFacet (r : LinearOrder α) {s : Finset (Set α)} (hsf : s ∈ (CoxeterComplex α).facets) :
IsHomologyFacet (CoxeterComplex_is_decomposable r) ⟨s, hsf⟩ ↔ 
powersetToPreorder (s : Set (Set α)) = (dual r).toPartialOrder.toPreorder ∧ Fintype.card α > 2 := by 
  rw [IsHomologyFacet_iff, R_eq_self_iff]
  constructor 
  . intro h 
    rw [and_iff_right h.1]
    rw [CoxeterComplex_dimension_facet ⟨s, hsf⟩, ←Nat.pred_eq_sub_one] at h 
    change _ ∧ 1 < Nat.pred _ at h 
    rw [Nat.lt_pred_iff] at h 
    exact h.2  
  . intro h 
    rw [and_iff_right h.1]
    rw [CoxeterComplex_dimension_facet ⟨s, hsf⟩, ←Nat.pred_eq_sub_one, gt_iff_lt, Nat.lt_pred_iff]
    exact h.2 


/- Shellability of the Coxeter complex: any linear order on the facets that refines the weak Bruhat is a shelling order. To make
it more convenient to state the lemmas, we first lift the weak Bruhat order to facets of the Coxeter complex.-/

open WeakBruhatOrder 

variable (α)

def CoxeterComplexFacets_to_LinearOrders (s : (CoxeterComplex α).facets) : 
{p : Preorder α | IsLinearOrder α p.le} := by 
  have hsf := s.2 
  rw [Facets_are_linear_orders (facets_subset hsf)] at hsf
  exact ⟨powersetToPreorder s.1, hsf⟩

lemma CoxeterComplexFacets_to_LinearOrders_injective : Function.Injective (CoxeterComplexFacets_to_LinearOrders α) := by 
  intro s t hst 
  unfold CoxeterComplexFacets_to_LinearOrders at hst
  simp only [Set.coe_setOf, Set.mem_setOf_eq, Subtype.mk.injEq] at hst
  have hsf := s.2 
  have htf := t.2 
  rw [mem_facets_iff] at hsf htf
  have heqs := Faces_powersetToPreordertoPowerset hsf.1 
  have heqt := Faces_powersetToPreordertoPowerset htf.1  
  rw [←SetCoe.ext_iff, ←Finset.coe_inj]
  rw [heqs, heqt, hst]

variable {α}


def WeakBruhatOrder_facets (r : LinearOrder α) : PartialOrder (CoxeterComplex α).facets :=
@PartialOrder.lift _ _ (WeakBruhatOrder r) (CoxeterComplexFacets_to_LinearOrders α) (CoxeterComplexFacets_to_LinearOrders_injective α)

lemma WeakBruhat_compatible_with_DF (r : LinearOrder α) : CompatibleOrder (DF r) (WeakBruhatOrder_facets r) := by 
  intro s t hst 
  have hstot : Total  (powersetToPreorder (s.1 : (Set (Set α)))).le := by 
    have hsf := s.2 
    rw [FacesCoxeterComplex] at hsf 
    have heq : ((CoxeterComplextoPartitions α).toFun ⟨s, hsf.1⟩).1 = powersetToPreorder (s.1 : (Set (Set α))) := by 
      unfold CoxeterComplextoPartitions 
      simp only 
    rw [←heq]
    exact ((CoxeterComplextoPartitions α).toFun ⟨s, hsf.1⟩).2.1    
  have httot : Total  (powersetToPreorder (t.1 : (Set (Set α)))).le := by 
    have htf := facets_subset t.2 
    rw [FacesCoxeterComplex] at htf 
    have heq : ((CoxeterComplextoPartitions α).toFun ⟨t, htf.1⟩).1 = powersetToPreorder (t.1 : (Set (Set α))) := by 
      unfold CoxeterComplextoPartitions 
      simp only 
    rw [←heq]
    exact ((CoxeterComplextoPartitions α).toFun ⟨t, htf.1⟩).2.1  
  change Inversions r.lt (CoxeterComplexFacets_to_LinearOrders α (DF r s)).1.lt ⊆ Inversions r.lt (CoxeterComplexFacets_to_LinearOrders α t).1.lt 
  have hsimp1 : (CoxeterComplexFacets_to_LinearOrders α (DF r s)).1 = LinearOrder_of_total_preorder_and_linear_order r (powersetToPreorder s) := by 
    unfold CoxeterComplexFacets_to_LinearOrders 
    simp only 
    unfold DF distinguishedFacet 
    simp only [Equiv.invFun_as_coe, OrderIso.toEquiv_symm, RelIso.coe_toEquiv] 
    change powersetToPreorder (((CoxeterComplextoPartitions α).invFun _) : Set (Set α)) = _  
    unfold CoxeterComplextoPartitions preorderToPowersetFinset 
    simp only 
    rw [Set.Finite.coe_toFinset, ←preorderToPowersetToPreorder]
  have hsimp2 : (CoxeterComplexFacets_to_LinearOrders α t).1 = powersetToPreorder t.1 := by 
    unfold CoxeterComplexFacets_to_LinearOrders 
    simp only 
  rw [hsimp1, hsimp2, ←Inversions_of_associated_linear_order]
  have hst := powersetToPreorder_antitone hst
  intro ⟨a,b⟩ hinv
  rw [Inversions_def] at hinv |-
  rw [and_iff_right hinv.1]
  rw [←(@TotalPreorder_lt_iff_not_le _ (powersetToPreorder (t.1 : (Set (Set α)))) httot)]
  rw [←(@TotalPreorder_lt_iff_not_le _ (powersetToPreorder (s.1 : (Set (Set α)))) hstot)] at hinv
  by_contra habs 
  exact hinv.2 (hst habs)
  exact hstot 

  


lemma CoxeterComplexShelling (r : LinearOrder α) {so : LinearOrder (CoxeterComplex α).facets} (hcomp : ∀ {s t : (CoxeterComplex α).facets},
(WeakBruhatOrder_facets r).le s t  → so.le s t) : IsShellingOrder so :=  
  ShellableofDecomposable (CoxeterComplex_is_decomposable r) (fun s t hst => hcomp (WeakBruhat_compatible_with_DF r s t hst))
   (@Finite.Preorder.wellFounded_lt _ (Finite.of_injective (fun s => s.1) (fun s t hst => by rw [SetCoe.ext_iff] at hst; exact hst)) 
   so.toPartialOrder.toPreorder) 


/-Calcul of the Euler-Poincaré characteristic of the Coxeter complex. (We assume that α is nonempty to get a uniform formula: if Fintype.card α ≤ 1,
then the Coxeter complex is empty so its EP characteristic is 0.)-/


noncomputable def FacetofLinearOrder (hcard : Fintype.card α > 1) (r : LinearOrder α): (CoxeterComplex α).facets := by 
  have hr : r.toPartialOrder.toPreorder ∈ AFLOPartitions α := by 
    rw [←AFLOPartitions_is_everything]
    exact r.le_total 
  refine ⟨preorderToPowersetFinset ⟨r.toPartialOrder.toPreorder, hr⟩, ?_⟩
  rw [Facets_are_linear_orders]
  unfold preorderToPowersetFinset
  rw [Set.Finite.coe_toFinset]
  rw [←preorderToPowersetToPreorder]  
  exact @instIsLinearOrderLeToLEToPreorderToPartialOrder _ r 
  rw [FacesCoxeterComplex]
  rw [←AFLOPowerset_is_everything]
  unfold preorderToPowersetFinset
  constructor 
  . constructor 
    . intro ⟨X, hX⟩ ⟨Y, hY⟩
      rw [Set.Finite.mem_toFinset] at hX hY 
      exact preorderToPowerset_total_is_total r.le_total ⟨X, hX⟩ ⟨Y, hY⟩ 
    . intro X hX 
      rw [Set.Finite.mem_toFinset] at hX 
      exact ⟨hX.1, hX.2.1⟩ 
  . rw [ne_eq, Set.Finite.toFinset_eq_empty, preorderToPowerset_is_empty_iff_TrivialPreorder]
    rw [gt_iff_lt, Fintype.one_lt_card_iff] at hcard 
    match hcard with 
    | ⟨a, b, hne⟩ => by_contra heq 
                     simp only at heq 
                     have hab : r.le a b := by 
                       rw [heq]
                       trivial 
                     have hba : r.le b a := by 
                       rw [heq]
                       trivial
                     exact hne (r.le_antisymm _ _ hab hba)  

/-Maybe not necessary. 
lemma PreorderofFacetofLinearOrder (hcard : Fintype.card α > 1) (r : LinearOrder α) : 
powersetToPreorder ((FacetofLinearOrder hcard r).1 : Set (Set α)) = r.toPartialOrder.toPreorder := sorry 
-/

lemma EulerPoincareCharacteristic_CoxeterComplex (hne : Nonempty α) : 
EulerPoincareCharacteristic (CoxeterComplex_is_finite α) = 1 + (-1 : ℤ)^(Fintype.card α) := by 
  by_cases hcard : Fintype.card α ≤ 1 
  . have hcard : Fintype.card α = 1 := by 
      refine le_antisymm hcard ?_ 
      rw [Nat.succ_le, Fintype.card_pos_iff]
      exact hne 
    rw [hcard, pow_one]
    simp only [add_right_neg]
    have he : (CoxeterComplex α).faces = ∅ := by 
      by_contra habs 
      rw [←ne_eq, ←Set.nonempty_iff_ne_empty] at habs 
      have hcard' := (CoxeterComplex_nonempty_iff α).mp habs 
      rw [hcard] at hcard' 
      linarith
    unfold EulerPoincareCharacteristic FacesFinset 
    simp_rw [he]
    rw [Set.Finite.toFinset_empty, Finset.sum_empty]
  . rw [EulerPoincareCharacteristicDecomposable (CoxeterComplex_is_finite α) (CoxeterComplex_is_decomposable (ArbitraryLinearOrder α))]
    by_cases hcard' : Fintype.card α = 2 
    . rw [hcard', neg_one_pow_two]
      have hpi : Set.Finite.toFinset (π₀Facets_finite (CoxeterComplex_is_decomposable (ArbitraryLinearOrder α)) (CoxeterComplex_is_finite α)) = 
        Set.Finite.toFinset (Set.finite_coe_iff.mp (FiniteComplex_has_finite_facets (CoxeterComplex_is_finite α))) := by 
        rw [Set.Finite.toFinset_inj]
        unfold π₀Facets 
        ext s           
        simp only [Set.mem_setOf_eq]
        constructor 
        . intro h 
          match h with 
          | ⟨hsf, _⟩ => exact hsf 
        . intro hsf 
          exists hsf 
          rw [IsPi0Facet_iff]
          apply Or.inr 
          rw [CoxeterComplex_dimension_facet ⟨s, hsf⟩, hcard']
      have hhom : Set.Finite.toFinset (HomologyFacets_finite (CoxeterComplex_is_decomposable (ArbitraryLinearOrder α)) (CoxeterComplex_is_finite α)) = 
        ∅ := by 
        rw [Set.Finite.toFinset_eq_empty, Set.eq_empty_iff_forall_not_mem]
        intro s 
        unfold HomologyFacets
        simp only [Set.mem_setOf_eq, not_exists]
        intro hsf 
        rw [IsHomologyFacet_iff, CoxeterComplex_dimension_facet, hcard', not_and_or]
        apply Or.inr 
        linarith 
      rw [hpi, hhom, Finset.sum_empty, add_zero, FacetsCoxeterComplex.card, hcard']
      simp only 
    . rw [←lt_iff_not_le] at hcard 
      have hcard' : Fintype.card α > 2 := by 
        rw [gt_iff_lt, lt_iff_le_and_ne, ne_eq, and_iff_left (Ne.symm hcard')]
        rw [←Nat.succ_le_iff] at hcard
        exact hcard 
      have hpi : Set.Finite.toFinset (π₀Facets_finite (CoxeterComplex_is_decomposable (ArbitraryLinearOrder α)) (CoxeterComplex_is_finite α)) = 
        {(FacetofLinearOrder hcard (ArbitraryLinearOrder α)).1} := by 
        ext s 
        rw [Set.Finite.mem_toFinset, Finset.mem_singleton]
        unfold π₀Facets
        simp only [Set.mem_setOf_eq]
        constructor 
        . intro h 
          match h with 
          | ⟨hsf, hs⟩ => rw [IsPi0Facet_iff, CoxeterComplex_dimension_facet] at hs 
                         have hright : ¬(Fintype.card α - 1 = 1) := by 
                           by_contra habs 
                           rw [←Nat.pred_eq_sub_one] at habs 
                           have h : Nat.pred (Fintype.card α) ≤ 1 := by 
                             rw [habs]
                           rw [Nat.pred_le_iff] at h
                           rw [gt_iff_lt, lt_iff_not_le] at hcard'
                           exact hcard' h   
                         rw [or_iff_left hright, R_eq_empty_iff] at hs
                         unfold FacetofLinearOrder preorderToPowersetFinset 
                         simp only 
                         rw [←Finset.coe_inj, Set.Finite.coe_toFinset]
                         rw [Faces_powersetToPreordertoPowerset (facets_subset hsf)]
                         apply congr_arg 
                         exact hs 
        . intro h; rw [h]
          exists (FacetofLinearOrder hcard (ArbitraryLinearOrder α)).2
          simp only [Subtype.coe_eta]
          rw [IsPi0Facet_iff]
          apply Or.inl 
          rw [R_eq_empty_iff]
          unfold FacetofLinearOrder preorderToPowersetFinset
          simp only 
          rw [Set.Finite.coe_toFinset]
          rw [←preorderToPowersetToPreorder]
      have hhom : Set.Finite.toFinset (HomologyFacets_finite (CoxeterComplex_is_decomposable (ArbitraryLinearOrder α)) 
        (CoxeterComplex_is_finite α)) = {(FacetofLinearOrder hcard (dual (ArbitraryLinearOrder α))).1} := by 
        ext s 
        rw [Set.Finite.mem_toFinset, Finset.mem_singleton]
        unfold HomologyFacets
        simp only [Set.mem_setOf_eq]
        constructor 
        . intro h 
          match h with 
          | ⟨hsf, hs⟩ => rw [IsHomologyFacet_iff, R_eq_self_iff] at hs 
                         unfold FacetofLinearOrder preorderToPowersetFinset 
                         simp only 
                         rw [←Finset.coe_inj, Set.Finite.coe_toFinset]
                         rw [Faces_powersetToPreordertoPowerset (facets_subset hsf)]
                         apply congr_arg 
                         exact hs.1
        . intro h 
          rw [h]
          exists (FacetofLinearOrder hcard (dual (ArbitraryLinearOrder α))).2
          rw [IsHomologyFacet_iff, R_eq_self_iff]
          constructor 
          . unfold FacetofLinearOrder preorderToPowersetFinset 
            simp only 
            rw [Set.Finite.coe_toFinset, ←preorderToPowersetToPreorder]
          . rw [CoxeterComplex_dimension_facet]
            rw [←Nat.pred_eq_sub_one, gt_iff_lt, Nat.lt_pred_iff]
            exact hcard'
      rw [hpi, hhom]
      simp only [Finset.card_singleton, Nat.cast_one, ge_iff_le, Finset.sum_singleton, add_right_inj]
      rw [CoxeterComplex_dimension_facet]
      rw [←(Nat.sub_succ' _ 1)]
      have haux : Fintype.card α = Fintype.card α - 2 + 2 := by 
        rw [tsub_add_eq_max]
        apply Eq.symm 
        apply max_eq_left
        exact le_of_lt hcard'  
      nth_rewrite 2 [haux]
      rw [pow_add, neg_one_pow_two, mul_one]
      

end FiniteCoxeterComplex
