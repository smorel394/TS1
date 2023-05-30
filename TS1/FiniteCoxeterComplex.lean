import TS1.FiniteOrderedPartitions 
import TS1.Decomposability 

set_option autoImplicit false

open Classical 

universe u


variable (α : Type u) 

namespace FiniteCoxeterComplex

open AbstractSimplicialComplex Preorder LinearOrderedPartitions 

/- The faces are the subset AFLOPowerset of Finset (Set α) define in FiniteOrderedPartitions.-/

lemma AFLOPowerset_down_closed : ∀ {E F : Finset (Set α)}, E ∈ AFLOPowerset α → F ⊆ E → F ∈ AFLOPowerset α := by 
  intro E F hE hFE 
  constructor
  . intro X Y 
    have hXE : X.1 ∈ E := hFE X.2
    have hYE : Y.1 ∈ E := hFE Y.2
    exact hE.1 ⟨X.1, hXE⟩ ⟨Y.1, hYE⟩
  . exact fun X hXF => hE.2 X (hFE hXF) 

def CoxeterComplex  := of_erase (AFLOPowerset α) (AFLOPowerset_down_closed α)

lemma FacesCoxeterComplex (s : Finset (Set α)) : s ∈ (CoxeterComplex α).faces ↔ s ∈ (AFLOPowerset α) ∧ s ≠ ∅ := by 
  unfold CoxeterComplex
  simp only [of_erase_faces, Set.mem_diff, Set.mem_singleton_iff, ne_eq]


/- The set AFLOPowerset α is in order-reversing bijection with the set of inearly ordered partitions of α. (If α is not finite, we have to use
finite linearly ordered partitions with finite proper initial intervals.)-/


noncomputable def CoxeterComplextoPartitions : OrderIso (AFLOPowerset α) (AFLOPartitions α)ᵒᵈ where
toFun := fun E => ⟨powersetToPreorder E.1, AFLO_powersetToPreorder E⟩
invFun := fun p => ⟨preorderToPowersetFinset p, AFLO_preorderToPowerset p⟩ 
left_inv := fun E => by simp only; rw [←SetCoe.ext_iff]
                        apply Eq.symm; apply subset_antisymm
                        . rw [Set.Finite.subset_toFinset] 
                          intro X hXE 
                          apply powersetToPreorderToPowerset (E.1 : Set (Set α)) hXE (E.2.2 X hXE).1.1 (E.2.2 X hXE).1.2   
                        . rw [Set.Finite.toFinset_subset]
                          apply TotalELFP_powersetToPreorderToPowerset (E : Set (Set α))
                          . exact (AFLO_powersetToPreorder E).1  
                          . exact AFLOPartition_is_ELF ⟨powersetToPreorder (E.1 : Set (Set α)), AFLO_powersetToPreorder E⟩    
right_inv := fun p => by simp only [Set.Finite.coe_toFinset]
                         rw [←SetCoe.ext_iff]
                         exact Eq.symm (preorderToPowersetToPreorder p.1) 
map_rel_iff' := by intro E F 
                   simp only [Equiv.coe_fn_mk]
                   constructor 
                   . intro hEF 
                     have hE : ↑E.1 ⊆ preorderToPowerset (powersetToPreorder (E.1 : Set (Set α))) := by 
                       intro X hXE 
                       exact powersetToPreorderToPowerset (E.1 : Set (Set α)) hXE (E.2.2 X hXE).1.1 (E.2.2 X hXE).1.2 
                     have hF : preorderToPowerset (powersetToPreorder (F.1 : Set (Set α))) ⊆ ↑F.1 :=  
                       TotalELFP_powersetToPreorderToPowerset (F.1 : Set (Set α)) (AFLO_powersetToPreorder F).1
                          (AFLOPartition_is_ELF ⟨powersetToPreorder (F.1 : Set (Set α)), AFLO_powersetToPreorder F⟩)
                     change E.1 ⊆ F.1 
                     rw [←Finset.coe_subset]
                     refine le_trans hE ?_
                     refine le_trans ?_ hF 
                     exact preorderToPowerset_antitone hEF 
                   . exact powersetToPreorder_antitone 

/- If s is a face of the Coxeter complex, then the cardinality of s is equal to the number of blocks of the corresponding partition minus 1.-/

lemma CoxeterComplex_dimension_face (s : AFLOPowerset α) (hne : Nonempty α) : 
Finset.card s.1 = @Fintype.card (Antisymmetrization α ((CoxeterComplextoPartitions α).toFun s).1.le)
(@Fintype.ofFinite _ ((CoxeterComplextoPartitions α).toFun s).2.2.2) -1 := by 
  have h : s = (CoxeterComplextoPartitions α).invFun ((CoxeterComplextoPartitions α).toFun s) := by 
    simp only [Equiv.toFun_as_coe_apply, RelIso.coe_toEquiv, Equiv.invFun_as_coe, OrderIso.toEquiv_symm,
    OrderIso.symm_apply_apply]
  rw [←SetCoe.ext_iff] at h 
  rw [h]
  generalize (CoxeterComplextoPartitions α).toFun s = p 
  unfold CoxeterComplextoPartitions 
  simp only [ge_iff_le]
  unfold preorderToPowersetFinset
  have := Set.Finite.coeSort_toFinset (Set.finite_coe_iff.mp (AFLO_preorderToPowerset_finite p)) 
  rw [←Fintype.card_coe]
  haveI I : Fintype (preorderToPowerset p.1) := @Fintype.ofFinite _ (AFLO_preorderToPowerset_finite p)    
  simp_rw [this] 
  haveI hfin : Finite (Antisymmetrization α p.1.le) := p.2.2.2
  haveI hfint : Fintype (Antisymmetrization α p.1.le):= @Fintype.ofFinite _ hfin   
  haveI : Finite (Antisymmetrization_nonmaximal p.1) := inferInstance 
  haveI : Fintype (Antisymmetrization_nonmaximal p.1) := Fintype.ofFinite _  
  rw [←(Fintype.card_congr (@Equiv_Antisymmetrization_nonmaximal_to_PreorderToPowerset _ p.1 p.2.1 (AFLOPartition_is_ELF p)))]
  simp_rw [@FiniteAntisymmetrization_nonmaximal _ p.1 p.2.1 inferInstance hne] 
  simp only [Finset.coe_sort_coe, Fintype.card_coe, ge_iff_le]
  rw [Finset.card_erase_of_mem ?_] 
  rw [@Finset.card_univ _ (@Fintype.ofFinite _ hfin)] 
  refine @Finset.mem_univ _ ?_ _  


/- The restriction map: it is given by applying the order isomorphisms to ordered partitions, taking the descent partition (with respect to a fixed auxiliary
linear order) and applying the inverse of the order isomorphism.-/

/- To show that the descent partition of an AFLO partition is AFLO, we show that AFLO partitions form an upper set. This is a formal consequences of the
fact (proved above) that AFLO powerset is a lower set.-/

lemma AFLOPartitions_IsUpperSet : IsUpperSet (AFLOPartitions α) := by 
  intro p q hpq hp 
  have hfin : (preorderToPowerset q).Finite := by 
    rw [←Set.finite_coe_iff]
    exact @Finite.Set.subset _ _ _ (AFLO_preorderToPowerset_finite ⟨p, hp⟩) (preorderToPowerset_antitone hpq) 
  set F := Set.Finite.toFinset hfin 
  have hFAFLO : F ∈ AFLOPowerset α := by
    refine AFLOPowerset_down_closed α ((CoxeterComplextoPartitions α).invFun ⟨p, hp⟩).2 ?_
    simp only [RelIso.coe_toEquiv, Set.Finite.toFinset_subset] 
    unfold CoxeterComplextoPartitions 
    simp only [Set.Finite.coe_toFinset]
    exact preorderToPowerset_antitone hpq 
  have hq := AFLO_powersetToPreorder ⟨F, hFAFLO⟩ 
  simp only [Set.Finite.coe_toFinset] at hq
  rw [←preorderToPowersetToPreorder] at hq 
  exact hq 

variable {α : Type u}

lemma AscentPartition_respects_AFLO (r : LinearOrder α) {s : Preorder α} (hs : s ∈ AFLOPartitions α) : 
AscentPartition r hs.1 ∈ AFLOPartitions α := by 
  apply AFLOPartitions_IsUpperSet α (AscentPartition_is_greater r hs.1)
  exact hs 


noncomputable def restriction (r : LinearOrder α) (E : AFLOPowerset α) : AFLOPowerset α := 
  (CoxeterComplextoPartitions α).invFun 
   ⟨@AscentPartition _ r (powersetToPreorder (E.1 :Set (Set α))) (AFLO_powersetToPreorder E).1,
    AscentPartition_respects_AFLO r (AFLO_powersetToPreorder E)⟩ 
  
lemma restriction_is_smaller (r : LinearOrder α) (E : AFLOPowerset α) : restriction r E ≤ E := by
  unfold restriction 
  have hEeq := (CoxeterComplextoPartitions α).left_inv E 
  rw [←hEeq]
  rw [←(CoxeterComplextoPartitions α).map_rel_iff']
  simp only [Equiv.toFun_as_coe_apply, RelIso.coe_toEquiv, Equiv.invFun_as_coe, OrderIso.toEquiv_symm,
    OrderIso.symm_apply_apply, OrderIso.apply_symm_apply]
  unfold CoxeterComplextoPartitions
  simp only [RelIso.coe_fn_mk, Equiv.coe_fn_mk]
  change @AscentPartition _ r (powersetToPreorder (E.1 :Set (Set α))) (AFLO_powersetToPreorder E).1 ≥ powersetToPreorder E.1 
  exact AscentPartition_is_greater r _ 


/- Version for the Coxeter complex.-/

noncomputable def R (r : LinearOrder α) : (CoxeterComplex α).facets → Finset (Set α) := by 
  intro ⟨s, hsf⟩
  rw [mem_facets_iff] at hsf 
  rw [FacesCoxeterComplex] at hsf
  exact (restriction r ⟨s,hsf.1.1⟩).1 


-- Finite α only.

variable [Fintype α]

/- Every linearly ordered partition is AFLO, a subset of Set α is AFLO if and only if it is totally ordered by inclusion and doesn't contain
⊥ and ⊤.-/

lemma AFLOPartitions_is_everything (p : Preorder α) : p ∈ LinearOrderedPartitions α ↔ p ∈ AFLOPartitions α := by 
  constructor 
  . intro h 
    change _ ∧ _ 
    erw [and_iff_right h]
    constructor 
    . intro _ _ 
      rw [←Set.finite_coe_iff]
      exact inferInstance  
    . change Finite (Quotient _)
      exact inferInstance  
  . exact fun h => h.1

lemma AFLOPowerset_is_everything (E : Finset (Set α)) : (Total (fun (X : E) => fun (Y : E) => X.1 ⊆ Y.1) ∧ ∀ (X : Set α), X ∈ E → (X ≠ ⊥ ∧ X ≠ ⊤)) ↔ 
E ∈ AFLOPowerset α := by 
  constructor 
  . intro h 
    change _ ∧ _ 
    rw [and_iff_right h.1]
    intro X hXE 
    rw [and_iff_right (h.2 X hXE)]
    exact inferInstance 
  . intro h 
    rw [and_iff_right h.1]
    exact fun X hXE => (h.2 X hXE).1 

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

lemma CoxeterComplex_nonempty_iff (α : Type u) [Fintype α] : (CoxeterComplex α).faces.Nonempty ↔ Fintype.card α ≥ 2 := by 
  constructor 
  . sorry 
  . sorry 

/- The Coxeter complex is finite.-/

lemma CoxeterComplex_is_finite (α : Type u) [Fintype α] : FiniteComplex (CoxeterComplex α) := by 
  rw [FiniteComplex]
  have hsub : (CoxeterComplex α).faces ⊆ @Set.univ (Finset (Set α)) := by 
    simp only [Set.subset_univ]
  exact Finite.Set.subset _ hsub  

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
  rw [CoxeterComplex_dimension_face α ⟨s.1, hsf.1.1⟩ (NonemptyType_of_face_CoxeterComplex (facets_subset s.2))]
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

lemma CoxeterComplex_is_pure (α : Type u) [Fintype α] : Pure (CoxeterComplex α) := 
Dimension_of_Noetherian_pure (Finite_implies_Noetherian (CoxeterComplex_is_finite α)) 
(fun s t hsf htf => by rw [CoxeterComplex_dimension_facet ⟨s, hsf⟩, CoxeterComplex_dimension_facet ⟨t, htf⟩])


/- We find the π₀ and homology facets: the unique π₀ facet is the minimal one for the weak Bruhat order (i.e. the one corresponding to r), and
the unique homology facet is the maximal one for the weak Bruhat order (i.e. the one corresponding to the dual of r).-/

lemma CoxeterComplex_Pi0Facet (r : LinearOrder α) {s : Finset (Set α)} (hsf : s ∈ (CoxeterComplex α).facets) :
IsPi0Facet (CoxeterComplex_is_decomposable r) ⟨s, hsf⟩ ↔ powersetToPreorder (s : Set (Set α)) = r.toPartialOrder.toPreorder := sorry 
  

lemma CoxeterComplex_HomologyFacet (r : LinearOrder α) {s : Finset (Set α)} (hsf : s ∈ (CoxeterComplex α).facets) :
IsHomologyFacet (CoxeterComplex_is_decomposable r) ⟨s, hsf⟩ ↔ powersetToPreorder (s : Set (Set α)) = (dual r).toPartialOrder.toPreorder := sorry 

      


end FiniteCoxeterComplex
