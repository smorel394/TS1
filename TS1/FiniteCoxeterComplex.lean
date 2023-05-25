import TS1.FiniteOrderedPartitions
import TS1.AbstractSimplicialComplex

set_option autoImplicit false


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

-- Let's assume α finite.
variable [Fintype α]


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

lemma DescentPartitions_respects_AFLO (r : LinearOrder α) {s : Preorder α} (hs : s ∈ AFLOPartitions α) : 
DescentPartition r hs.1 ∈ AFLOPartitions α := by 
  apply AFLOPartitions_IsUpperSet α (DescentPartition_is_greater r hs.1)
  exact hs 


noncomputable def restriction (r : LinearOrder α) (E : AFLOPowerset α) : AFLOPowerset α := 
  (CoxeterComplextoPartitions α).invFun 
   ⟨@DescentPartition _ r (powersetToPreorder (E.1 :Set (Set α))) (AFLO_powersetToPreorder E).1,
    DescentPartitions_respects_AFLO r (AFLO_powersetToPreorder E)⟩ 
  
lemma restriction_is_smaller (r : LinearOrder α) (E : AFLOPowerset α) : restriction r E ≤ E := by
  unfold restriction 
  have hEeq := (CoxeterComplextoPartitions α).left_inv E 
  rw [←hEeq]
  rw [←(CoxeterComplextoPartitions α).map_rel_iff']
  simp only [Equiv.toFun_as_coe_apply, RelIso.coe_toEquiv, Equiv.invFun_as_coe, OrderIso.toEquiv_symm,
    OrderIso.symm_apply_apply, OrderIso.apply_symm_apply]
  unfold CoxeterComplextoPartitions
  simp only [RelIso.coe_fn_mk, Equiv.coe_fn_mk]
  change @DescentPartition _ r (powersetToPreorder (E.1 :Set (Set α))) (AFLO_powersetToPreorder E).1 ≥ powersetToPreorder E.1 
  exact DescentPartition_is_greater r _ 




-- Finite α only.
/- The facets of the Coxeter complex correspond to linear orders on α. (If α is infinite, the Coxeter complex has no facets, and the linear orders
will define maximal ideals of the face poset of the Coxeter complex, though we don't get all maximal ideals this way.)-/

/- The "distinguished facet" of the decomposition. (For this we need to choose an auxiliary linear order on α.)-/



end FiniteCoxeterComplex
