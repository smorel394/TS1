import TS1.FiniteCoxeterComplex  
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Normed.Group.Basic 



set_option autoImplicit false

open Classical 

open LinearOrderedPartitions 

universe u

/-The weighted complex depends on the choice of a function μ : α → ℝ. The idea is that only keep the total preoders such that
∑ μ is nonnegative on each lower set. We also this condition for the lower set ⊤, so we will μ to be summable and have nonnegative
sum. (Otherwise we set the weighted complex to be empty.)-/

section Infinite 

variable {α : Type u} (μ : α → ℝ)

/- If μ is a function from α to ℝ, we can find a linear order on α for which μ is antitone.-/

lemma Exists_LinearOrder_antitone : ∃ (r : LinearOrder α), @Antitone α ℝ r.toPartialOrder.toPreorder _ μ := by 
  set s := @OrderDual.preorder _ (Preorder.lift μ)
  have hsmon : @Antitone α ℝ s _ μ := by 
    apply @Monotone.dual_left _ _ (Preorder.lift μ) _ μ 
    exact fun _ _ h => h
  have hstot : Total s.le := by 
    intro a b 
    cases (le_total (μ a) (μ b)) with 
    | inl hab => exact Or.inr hab 
    | inr hba => exact Or.inl hba 
  set t := LinearOrder_of_total_preorder_and_linear_order (ArbitraryLinearOrder α) s 
  have htmon : @Antitone α ℝ t _ μ := fun _ _ hab =>  
    hsmon (LinearOrder_of_total_preorder_and_linear_order_is_smaller (ArbitraryLinearOrder α) s hab)  
  have htlin : IsLinearOrder α t.le := LinearOrder_of_total_preorder_and_linear_order_is_linear (ArbitraryLinearOrder α) hstot 
  set u : PartialOrder α := {t with le_antisymm := htlin.toIsPartialOrder.toIsAntisymm.antisymm}
  exists @AsLinearOrder.linearOrder _ u {total := LinearOrder_of_total_preorder_and_linear_order_is_total (ArbitraryLinearOrder α) hstot}



/- A sanity check: if α is finite, then the summability condition on μ is automatic, and the positivity condition reduces to 
Finset.sum Finset.univ μ ≥ 0.-/

lemma Positivity_condition [Fintype α] (μ : α → ℝ) : Summable μ ∧ (tsum μ ≥ 0 ↔ Finset.sum Finset.univ μ ≥ 0) := by 
  have h := hasSum_fintype μ 
  constructor 
  . exact h.summable 
  . rw [h.tsum_eq] 

variable {hsummable : Summable μ} {hpos : tsum μ ≥ 0}


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


end FiniteWeightedComplex

end Infinite 

-- Now we suppose α finite.


namespace FiniteWeightedComplex

open AbstractSimplicialComplex Preorder LinearOrderedPartitions FiniteCoxeterComplex 

variable {α : Type u} (μ : α → ℝ)
variable [Fintype α] (hsum : Finset.sum Finset.univ μ ≥ 0)





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

/- The weighted complex is nonempty if and only if the Coxeter complex is nonempty (i.e. Fintype.card α ≥ 2) and ∑ μ ≥ 0.-/

lemma WeightedComplex_nonempty_iff : (WeightedComplex μ).faces.Nonempty ↔ Fintype.card α ≥ 2  := by 
  constructor 
  . rw [←CoxeterComplex_nonempty_iff]
    exact fun ⟨s, hsf⟩ => ⟨s, WeightedComplex_subcomplex μ hsf⟩
  . intro hcard 
    set x := List.argmax μ Finset.univ.toList with hxdef 
    match x with 
    | none => exfalso
              have h := Eq.symm hxdef 
              rw [List.argmax_eq_none, Finset.toList_eq_nil, Finset.univ_eq_empty_iff] at h 
              rw [ge_iff_le, Nat.succ_le_iff, Fintype.one_lt_card_iff] at hcard
              match hcard with 
              | ⟨a, _, _⟩ => exact h.false a  
    | some a => rw [ge_iff_le, Nat.succ_le_iff] at hcard
                match Fintype.exists_ne_of_one_lt_card hcard a with 
                | ⟨b, hba⟩ => 
                  set p := twoStepPreorder a  
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
                    exact twoStepPreorder_nontrivial (Ne.symm hba) he   
                  have hsfw : s.1 ∈ (WeightedComplex μ).faces := by 
                    rw [FacesWeightedComplex]
                    rw [and_iff_left hsne]
                    exists s.2 
                    intro X hXs 
                    have heq : (s.1 : Set (Set α)) = preorderToPowerset (twoStepPreorder a) := by 
                      rw [hsdef]
                      unfold CoxeterComplextoPartitions 
                      simp only 
                      unfold preorderToPowersetFinset 
                      rw [Set.Finite.coe_toFinset]
                    rw [preorderToPowerset_TwoStepPreorder (Ne.symm hba)] at heq 
                    rw [←Finset.mem_coe, heq, Set.mem_singleton_iff] at hXs
                    unfold IsPositiveSet 
                    simp_rw [hXs] 
                    rw [Set.Finite.toFinset_singleton, Finset.sum_singleton]
                    by_contra hneg
                    rw [←lt_iff_not_le] at hneg
                    have hneg' : ∀ (c : α), μ c < 0 := by 
                      intro c 
                      have hc : c ∈ Finset.univ.toList := by 
                        simp only [Finset.mem_toList, Finset.mem_univ]
                      have ha : a ∈ List.argmax μ Finset.univ.toList := by 
                        simp only [Option.mem_def]
                        exact Eq.symm hxdef 
                      have h := List.not_lt_of_mem_argmax hc ha
                      rw [lt_iff_not_le, not_not] at h
                      exact lt_of_le_of_lt h hneg    
                    have habs : Finset.sum Finset.univ μ < 0 := by 
                      apply Finset.sum_neg (fun d _ => hneg' d)
                      exists a; exact Finset.mem_univ _ 
                    rw [lt_iff_not_le] at habs 
                    exact habs hsum 
                  exists s 



/- The weighted complex is equal to the Coxeter complex if and only if Finset.card α < 2 (then they are both empty) or 
μ takes nonnegative values.-/

lemma WeightedComplex_all_iff : (WeightedComplex μ).faces = (CoxeterComplex α).faces ↔ Fintype.card.{u} α < 2 ∨ ∀ (a : α),  μ a ≥ 0 := by 
  by_cases hcard : Fintype.card.{u} α < 2 
  . simp only [ge_iff_le, Or.inl hcard, iff_true]
    have hce : (CoxeterComplex α).faces = ∅ := by 
      rw [←Set.not_nonempty_iff_eq_empty, CoxeterComplex_nonempty_iff, ←lt_iff_not_le] 
      exact hcard
    have hwe : (WeightedComplex μ).faces = ∅ := by 
      rw [←Set.not_nonempty_iff_eq_empty, WeightedComplex_nonempty_iff, ←lt_iff_not_le]
      exact hcard 
      exact hsum
    rw [hce, hwe]
  . simp only [hcard, ge_iff_le, false_or]
    rw [lt_iff_not_le, not_not, Nat.succ_le_iff] at hcard
    constructor 
    . intro heq a 
      match Fintype.exists_ne_of_one_lt_card hcard a with 
      | ⟨b, hba⟩ => have h := twoStepPreorder_in_CoxeterComplex (Ne.symm hba)
                    rw [←heq, FacesWeightedComplex] at h
                    unfold AFLOPowerset_positive at h 
                    match h.1 with 
                    | ⟨_, hpos⟩ => 
                      have ha : {a} ∈ preorderToPowersetFinset ⟨twoStepPreorder a, twoStepPreorder_AFLO a⟩ := by 
                        rw [Set.Finite.mem_toFinset, preorderToPowerset_TwoStepPreorder (Ne.symm hba)]
                        simp only [Set.mem_singleton_iff]
                      have hpos := hpos ha
                      unfold IsPositiveSet at hpos 
                      rw [Set.Finite.toFinset_singleton, Finset.sum_singleton] at hpos
                      exact hpos  
    . intro hpos 
      refine subset_antisymm (WeightedComplex_subcomplex μ) ?_ 
      intro s hsf 
      rw [FacesWeightedComplex, ←Finset.nonempty_iff_ne_empty, and_iff_left ((CoxeterComplex α).nonempty_of_mem hsf)]
      unfold AFLOPowerset_positive 
      simp only [Set.mem_setOf_eq]
      exists hsf.1 
      intro _ _ 
      unfold IsPositiveSet 
      apply Finset.sum_nonneg 
      intro b _ 
      exact hpos b 
      

/- If r is a linear order on α that makes μ antitone, then the map LinearOrder_of_etc preserves positive AFLO partitions, so we
can define a "distinguished facet" map on the weighted complex. The existence of that map then implies that facets of the weighted
complex are also facets of the Coxeter complex.-/


lemma LinearOrder_etc_respects_AFLO_positive {r : LinearOrder α} (hmon : @Antitone α ℝ r.toPartialOrder.toPreorder _ μ) 
{s : Preorder α} (hs : s ∈ AFLOPartitions_positive μ) : 
LinearOrder_of_total_preorder_and_linear_order r s ∈ AFLOPartitions_positive μ := by 
  exists (LinearOrder_etc_respects_AFLO r (AFLOPartitions_forget_positive μ hs))
  exists AFLO_preorderToPowerset ⟨LinearOrder_of_total_preorder_and_linear_order r s, 
    LinearOrder_etc_respects_AFLO r (AFLOPartitions_forget_positive μ hs)⟩
  intro X hXs 
  rw [Set.Finite.mem_toFinset] at hXs 
  match @TotalELFP_LowerSet_is_principal _ (LinearOrder_of_total_preorder_and_linear_order r s) 
    (LinearOrder_of_total_preorder_and_linear_order_is_total r (AFLOPartitions_forget_positive μ hs).1) 
    (EssentiallyLocallyFinite_ofLocallyFinite (@Fintype.toLocallyFiniteOrder _ 
    (LinearOrder_of_total_preorder_and_linear_order r s) _ _ _)) X hXs with
  | ⟨a, ha⟩ => 
    by_cases hsign : μ a ≥ 0
    . match LowerSet_LinearOrder_etc_is_disjoint_union r s ha with 
    | ⟨Y, hY, hunion, hdisj⟩ => 
      set Z := {b : α | r.le b a ∧ AntisymmRel s.le a b}
      have hufin : Set.Finite.toFinset ((@Set.finite_coe_iff _ X).mp inferInstance) = 
        Set.Finite.toFinset ((@Set.finite_coe_iff _ Y).mp inferInstance) ∪ Set.Finite.toFinset ((@Set.finite_coe_iff _ Z).mp inferInstance) := by 
        rw [←(Set.Finite.toFinset_union ((Set.finite_coe_iff).mp inferInstance) ((Set.finite_coe_iff).mp inferInstance) 
        ((Set.finite_coe_iff).mp inferInstance))]
        rw [Set.Finite.toFinset_inj]
        exact hunion
      have hdisjfin : Disjoint (Set.Finite.toFinset ((@Set.finite_coe_iff _ Y).mp inferInstance)) 
        (Set.Finite.toFinset ((@Set.finite_coe_iff _ Z).mp inferInstance)) := by 
        rw [Set.Finite.disjoint_toFinset]
        exact hdisj 
      rw [←(Finset.disjUnion_eq_union _ _ hdisjfin)] at hufin 
      unfold IsPositiveSet 
      rw [hufin, Finset.sum_disjUnion hdisjfin]
      apply add_nonneg
      . cases hY with
        | inl hYe => rw [hYe, Set.Finite.toFinset_empty, Finset.sum_empty]
        | inr hYs =>  have hYs' : Y ∈ preorderToPowersetFinset ⟨s, AFLOPartitions_forget_positive μ hs⟩ := by 
                         rw [Set.Finite.mem_toFinset]
                         exact hYs
                      match hs with 
                      | ⟨_, _, hpos⟩ => exact hpos hYs'   
      . apply Finset.sum_nonneg 
        intro b hb 
        rw [Set.Finite.mem_toFinset] at hb 
        simp only [Set.mem_setOf_eq] at hb
        refine le_trans hsign (hmon hb.1)  
    . rw [←lt_iff_not_le] at hsign
      match LowerSet_LinearOrder_etc_is_difference r (AFLOPartitions_forget_positive μ hs).1 ha with 
      | ⟨Y, hY, hdiff, hsub⟩ => 
        set Z := {b : α | r.lt a b ∧ AntisymmRel s.le a b}
        have hsdiff : Set.Finite.toFinset ((@Set.finite_coe_iff _ X).mp inferInstance) = 
        Set.Finite.toFinset ((@Set.finite_coe_iff _ Y).mp inferInstance) \ Set.Finite.toFinset ((@Set.finite_coe_iff _ Z).mp inferInstance) := by 
          rw [←(Set.Finite.toFinset_diff ((Set.finite_coe_iff).mp inferInstance) ((Set.finite_coe_iff).mp inferInstance) 
            ((Set.finite_coe_iff).mp inferInstance))]
          rw [hdiff]
        have hsubfin : Set.Finite.toFinset ((@Set.finite_coe_iff _ Z).mp inferInstance) ⊆ 
          Set.Finite.toFinset ((@Set.finite_coe_iff _ Y).mp inferInstance) := by 
          rw [Set.Finite.toFinset_subset, Set.Finite.coe_toFinset]
          exact hsub
        unfold IsPositiveSet  
        rw [hsdiff, Finset.sum_sdiff_eq_sub hsubfin, ge_iff_le, sub_nonneg]
        have hYpos : Finset.sum (Set.Finite.toFinset ((@Set.finite_coe_iff _ Y).mp inferInstance)) μ ≥ 0 := by 
          cases hY with 
          | inl htop => rw [htop]
                        simp only [Set.top_eq_univ, Set.Finite.toFinset_setOf, Finset.mem_univ, forall_true_left, implies_true,
                          Finset.filter_true_of_mem]
                        exact hsum 
          | inr hYs => have hYs' : Y ∈ preorderToPowersetFinset ⟨s, AFLOPartitions_forget_positive μ hs⟩ := by 
                         rw [Set.Finite.mem_toFinset]
                         exact hYs 
                       match hs with 
                       | ⟨_, _, hpos⟩ => exact hpos hYs'   
        refine le_trans ?_ hYpos 
        apply Finset.sum_nonpos 
        intro b hb 
        rw [Set.Finite.mem_toFinset] at hb 
        simp only [Set.mem_setOf_eq] at hb
        exact le_trans (hmon (@le_of_lt _ r.toPartialOrder.toPreorder _ _ hb.1)) (le_of_lt hsign)


/- The "distinguished facet" of the decomposition. (For this we need to choose an auxiliary linear order on α.)-/

noncomputable def distinguishedFacet_weighted {r : LinearOrder α} (hmon : @Antitone _ _ r.toPartialOrder.toPreorder _ μ) 
 (E : AFLOPowerset_positive μ) : AFLOPowerset_positive μ := 
  (WeightedComplextoPositivePartitions μ).invFun 
   ⟨@LinearOrder_of_total_preorder_and_linear_order _ r (powersetToPreorder (E.1 :Set (Set α))),
    @LinearOrder_etc_respects_AFLO_positive α μ _ hsum r hmon (powersetToPreorder (E.1 : Set (Set α))) (AFLO_positive_powersetToPreorder μ E)⟩ 



lemma distinguishedFacet_weighted_is_bigger {r : LinearOrder α} (hmon : @Antitone _ _ r.toPartialOrder.toPreorder _ μ) 
(hsum : Finset.sum Finset.univ μ ≥ 0) (E : AFLOPowerset_positive μ) : E ≤ distinguishedFacet_weighted μ hsum hmon E := by
  unfold distinguishedFacet_weighted 
  have hEeq := (WeightedComplextoPositivePartitions μ).left_inv E 
  rw [←hEeq]
  rw [←(WeightedComplextoPositivePartitions μ).map_rel_iff']
  simp only [Equiv.toFun_as_coe_apply, RelIso.coe_toEquiv, Equiv.invFun_as_coe, OrderIso.toEquiv_symm,
    OrderIso.symm_apply_apply, OrderIso.apply_symm_apply]
  unfold WeightedComplextoPositivePartitions
  simp only [RelIso.coe_fn_mk, Equiv.coe_fn_mk]
  change @LinearOrder_of_total_preorder_and_linear_order _ r (powersetToPreorder (E.1 :Set (Set α))) ≤ powersetToPreorder E.1 
  exact LinearOrder_of_total_preorder_and_linear_order_is_smaller _ _ 


lemma distinguishedFacet_weighted_is_facet_CoxeterComplex {r : LinearOrder α} (hmon : @Antitone _ _ r.toPartialOrder.toPreorder _ μ) 
(E : AFLOPowerset_positive μ) (hEf : E.1 ∈ (WeightedComplex μ).faces) : 
(distinguishedFacet_weighted μ hsum hmon E).1 ∈ (CoxeterComplex α).facets := 
distinguishedFacet_is_facet r ⟨E.1, hEf.1.1⟩ (WeightedComplex_subcomplex μ hEf) 


lemma distinguishedFacet_weighted_is_face_WeightedComplex {r : LinearOrder α} (hmon : @Antitone _ _ r.toPartialOrder.toPreorder _ μ) 
(s : AFLOPowerset_positive μ) (hsf : s.1 ∈ (WeightedComplex μ).faces) : 
(distinguishedFacet_weighted μ hsum hmon s).1 ∈ (WeightedComplex μ).faces := by 
  have hsf' := (FacesWeightedComplex μ s).mp hsf
  have hst := distinguishedFacet_weighted_is_bigger μ hmon hsum ⟨s.1, hsf'.1⟩
  change s.1 ⊆ _ at hst 
  rw [FacesWeightedComplex, and_iff_right (distinguishedFacet_weighted μ hsum hmon ⟨s, hsf'.1⟩).2]
  by_contra hte 
  rw [hte, Finset.subset_empty, ←Finset.not_nonempty_iff_eq_empty] at hst 
  exact hst ((WeightedComplex μ).nonempty_of_mem hsf)


/- Now we can characterize facets of the weighted complex: they are exactly the faces of the weighted complex that are also facets
of the Coxeter complex.-/

lemma FacetWeightedComplex_iff (s : Finset (Set α)) : 
s ∈ (WeightedComplex μ).facets ↔ s ∈ (CoxeterComplex α).facets ∧ s ∈ (WeightedComplex μ).faces := by 
  constructor 
  . intro hsf 
    rw [mem_facets_iff] at hsf 
    rw [and_iff_left hsf.1]
    have hsf' := (FacesWeightedComplex μ s).mp hsf.1 
    match Exists_LinearOrder_antitone μ with 
    | ⟨r, hmon⟩ => 
      have hst := distinguishedFacet_weighted_is_bigger μ hmon hsum ⟨s, hsf'.1⟩
      have htfw := distinguishedFacet_weighted_is_face_WeightedComplex μ hsum hmon ⟨s, hsf'.1⟩ hsf.1 
      rw [hsf.2 htfw hst]
      exact distinguishedFacet_weighted_is_facet_CoxeterComplex μ hsum hmon ⟨s, hsf'.1⟩ hsf.1 
  . exact fun ⟨hsf, hsfw⟩ => Facets_subcomplex (WeightedComplex_subcomplex μ) hsfw hsf 

/- Comparison of the two restriction maps.-/

lemma R_comparison (r : LinearOrder α) {s : Finset (Set α)} (hsf : s ∈ (WeightedComplex μ).facets) :
R_weighted μ r ⟨s, hsf⟩ = R r ⟨s, ((FacetWeightedComplex_iff μ hsum s).mp hsf).1⟩ := by 
  unfold R_weighted R restriction_weighted restriction 
  simp only [Equiv.invFun_as_coe, OrderIso.toEquiv_symm, RelIso.coe_toEquiv]
  change preorderToPowersetFinset _ = preorderToPowersetFinset _
  simp only [Set.Finite.toFinset_setOf, Set.bot_eq_empty, ne_eq, Set.top_eq_univ, Finset.mem_univ,
    forall_true_left]
 


/- Version for the weighted complex.-/

noncomputable def DF_weighted {r : LinearOrder α} (hmon : @Antitone _ _ r.toPartialOrder.toPreorder _ μ) : 
(WeightedComplex μ).faces → (WeightedComplex μ).facets := by  
  intro ⟨s, hsf⟩
  have hsf' := hsf 
  rw [FacesWeightedComplex] at hsf'
  refine ⟨(distinguishedFacet_weighted μ hsum hmon ⟨s, hsf'.1⟩).1, ?_⟩ 
  rw [FacetWeightedComplex_iff μ hsum] 
  refine ⟨distinguishedFacet_weighted_is_facet_CoxeterComplex μ hsum hmon ⟨s, hsf'.1⟩ hsf, ?_⟩ 
  exact distinguishedFacet_weighted_is_face_WeightedComplex μ hsum hmon ⟨s, hsf'.1⟩ hsf 

lemma DF_comparison {r : LinearOrder α} (hmon : @Antitone _ _ r.toPartialOrder.toPreorder _ μ) {s : Finset (Set α)}
(hsf : s ∈ (WeightedComplex μ).faces) :
(DF_weighted μ hsum hmon ⟨s, hsf⟩).1 = (DF r ⟨s, WeightedComplex_subcomplex μ hsf⟩).1 := by 
  unfold DF_weighted distinguishedFacet_weighted
  simp only 
  unfold DF distinguishedFacet 
  simp only 
  change preorderToPowersetFinset _ = preorderToPowersetFinset _ 
  simp only [Set.Finite.toFinset_setOf, Set.bot_eq_empty, ne_eq, Set.top_eq_univ, Finset.mem_univ, forall_true_left]

/- We identify the facets whose R is ∅ or the facet itself. We assume α finite for this, otherwise there are no facets and the statement is
empty.-/


lemma R_weighted_eq_empty_iff (r : LinearOrder α) {s : Finset (Set α)} (hsf : s ∈ (WeightedComplex μ).facets) : 
R_weighted μ r ⟨s, hsf⟩ = ∅ ↔ powersetToPreorder (s : Set (Set α)) = r.toPartialOrder.toPreorder := by 
  have hsf' := ((FacetWeightedComplex_iff μ hsum s).mp hsf).1 
  have heq : R_weighted μ r ⟨s, hsf⟩ = R r ⟨s, hsf'⟩ := by tauto 
  rw [heq]
  exact R_eq_empty_iff r hsf'



lemma R_weighted_eq_self_iff (r : LinearOrder α) {s : Finset (Set α)} (hsf : s ∈ (WeightedComplex μ).facets) : 
R_weighted μ r ⟨s, hsf⟩ = s ↔ powersetToPreorder (s : Set (Set α)) = (dual r).toPartialOrder.toPreorder := by 
  have hsf' := ((FacetWeightedComplex_iff μ hsum s).mp hsf).1 
  have heq : R_weighted μ r ⟨s, hsf⟩ = R r ⟨s, hsf'⟩ := by tauto 
  rw [heq]
  exact R_eq_self_iff r hsf'

/- When are the two facets corresponding to r and its dual in the weighted complex ? If μ is antitone, then r is in the weighted complex
if and only if Fintype.card α ≥ 2 i.e. if and only the weighted complex is nonempty (we also need ∑ μ ≥ 0 but that's always assumed
with our current conventions).
As for the dual of r, it is in the weighted complex if and only μ takes nonnegative values, i.e. if and only if the weighted complex is 
equal to the Coxeter complex.-/

lemma Fixed_linear_order_in_AFLO_positive {r : LinearOrder α} (hmon : @Antitone _ _ r.toPartialOrder.toPreorder _ μ) :
r.toPartialOrder.toPreorder ∈ AFLOPartitions_positive μ := by 
  exists (AFLOPartitions_is_everything r.toPartialOrder.toPreorder).mp r.le_total
  exists (AFLO_preorderToPowerset ⟨r.toPartialOrder.toPreorder, (AFLOPartitions_is_everything r.toPartialOrder.toPreorder).mp r.le_total⟩)
  intro X hX 
  unfold IsPositiveSet 
  have hX':= (AFLO_preorderToPowerset ⟨r.toPartialOrder.toPreorder, (AFLOPartitions_is_everything r.toPartialOrder.toPreorder).mp r.le_total⟩).2 X hX 
  rw [Set.Finite.mem_toFinset] at hX 
  unfold preorderToPowerset at hX 
  simp only [Set.mem_setOf_eq] at hX
  match @TotalELFP_LowerSet_is_principal _ r.toPartialOrder.toPreorder r.le_total 
    (EssentiallyLocallyFinite_ofLocallyFinite (@Fintype.toLocallyFiniteOrder _ r.toPartialOrder.toPreorder _ _ _)) X hX  with 
  | ⟨a, haX⟩ => 
    by_cases hsign : μ a ≥ 0 
    . apply Finset.sum_nonneg 
      intro b hbX 
      rw [Set.Finite.mem_toFinset, haX, Set.mem_Iic] at hbX 
      exact le_trans hsign (hmon hbX) 
    . rw [←lt_iff_not_le] at hsign
      have hsdiff : Set.Finite.toFinset ((@Set.finite_coe_iff _ (Set.Iic a)).mp inferInstance) = Finset.univ \ 
        Set.Finite.toFinset ((@Set.finite_coe_iff _ (Set.Ioi a)).mp inferInstance) := by 
        ext b 
        simp only [Set.Finite.toFinset_setOf, Finset.mem_univ, forall_true_left, Finset.mem_filter, true_and,
          Finset.mem_sdiff, not_lt]
      have hsub : Set.Finite.toFinset ((@Set.finite_coe_iff _ (Set.Ioi a)).mp inferInstance) ⊆ Finset.univ := by 
        exact fun _ _ => Finset.mem_univ _ 
      simp_rw [haX, hsdiff, Finset.sum_sdiff_eq_sub hsub, sub_nonneg]
      refine le_trans ?_ hsum 
      apply Finset.sum_nonpos 
      intro b hb 
      rw [Set.Finite.mem_toFinset, Set.mem_Ioi] at hb  
      exact le_trans (hmon (le_of_lt hb)) (le_of_lt hsign) 


lemma Fixed_linear_order_in_WeightedComplex {r : LinearOrder α} (hmon : @Antitone _ _ r.toPartialOrder.toPreorder _ μ) 
(hcard : Fintype.card α ≥ 2) :
preorderToPowersetFinset ⟨r.toPartialOrder.toPreorder, (AFLOPartitions_is_everything r.toPartialOrder.toPreorder).mp r.le_total⟩ 
∈ (WeightedComplex μ).faces := by 
  rw [FacesWeightedComplex]
  have h := ((WeightedComplextoPositivePartitions μ).invFun ⟨r.toPartialOrder.toPreorder, Fixed_linear_order_in_AFLO_positive μ hsum hmon⟩).2 
  unfold WeightedComplextoPositivePartitions at h 
  simp only at h 
  rw [and_iff_right h]
  rw [ne_eq, Set.Finite.toFinset_eq_empty, preorderToPowerset_is_empty_iff_TrivialPreorder, ←ne_eq, nontrivial_preorder_iff_exists_not_le]
  simp only [not_le]
  rw [ge_iff_le, Nat.succ_le, Fintype.one_lt_card_iff] at hcard 
  match hcard with 
  | ⟨a, b, hab⟩ => cases lt_or_gt_of_ne hab with 
                   | inl hab => exists b; exists a;  
                   | inr hba => exists a; exists b 


lemma Dual_linear_order_in_AFLO_positive {r : LinearOrder α} (hmon : @Antitone _ _ r.toPartialOrder.toPreorder _ μ) :
(dual r).toPartialOrder.toPreorder ∈ AFLOPartitions_positive μ ↔ (∀ (a : α), μ a ≥ 0):= by
  constructor 
  . intro hr a 
    have hne : (@Set.univ α).Nonempty := ⟨a, Set.mem_univ _⟩
    set b := WellFounded.min (@Finite.Preorder.wellFounded_gt α _ r.toPartialOrder.toPreorder) Set.univ hne  
    set X := ({b} : Set α) with hXdef 
    by_cases hsin : ∀ (c : α), c = b 
    . have huniv : Finset.univ = {a} := by
        ext c 
        simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
        rw [hsin c]
        exact Eq.symm (hsin a) 
      rw [huniv, Finset.sum_singleton] at hsum 
      exact hsum 
    . push_neg at hsin 
      match hsin with 
    | ⟨c, hc⟩ => have hX : X ∈ preorderToPowersetFinset ⟨(dual r).toPartialOrder.toPreorder, (AFLOPartitions_is_everything 
                   (dual r).toPartialOrder.toPreorder).mp (dual r).le_total⟩ := by 
                   rw [Set.Finite.mem_toFinset]
                   unfold preorderToPowerset 
                   erw [Set.mem_setOf]
                   simp only [Set.bot_eq_empty, Set.top_eq_univ, ←Set.nonempty_iff_ne_empty, Set.ne_univ_iff_exists_not_mem]
                   rw [and_iff_right ⟨b, Set.mem_singleton _⟩]
                   constructor 
                   . exists c 
                   . intro d e hde 
                     simp only [gt_iff_lt, Set.mem_singleton_iff]
                     intro hdb 
                     rw [hdb] at hde 
                     have h := WellFounded.not_lt_min (@Finite.Preorder.wellFounded_gt α _ r.toPartialOrder.toPreorder) Set.univ hne 
                       (Set.mem_univ e)
                     rw [gt_iff_lt, lt_iff_not_le, not_not] at h
                     exact le_antisymm hde h   
                 have hXpos := hr.2.2 hX
                 unfold IsPositiveSet at hXpos 
                 simp_rw [hXdef, Set.Finite.toFinset_singleton, Finset.sum_singleton] at hXpos 
                 have hab : r.le a b := by 
                   have h := WellFounded.not_lt_min (@Finite.Preorder.wellFounded_gt α _ r.toPartialOrder.toPreorder) Set.univ hne 
                     (Set.mem_univ a)
                   rw [gt_iff_lt, lt_iff_not_le, not_not] at h
                   exact h  
                 exact le_trans hXpos (hmon hab)     
  . intro hpos 
    exists (AFLOPartitions_is_everything (dual r).toPartialOrder.toPreorder).mp (dual r).le_total
    exists (AFLO_preorderToPowerset ⟨(dual r).toPartialOrder.toPreorder, (AFLOPartitions_is_everything (dual r).toPartialOrder.toPreorder).mp 
      (dual r).le_total⟩)
    intro X hXs 
    unfold IsPositiveSet 
    apply Finset.sum_nonneg 
    intro a _ 
    exact hpos a 

lemma Dual_linear_order_in_WeightedComplex {r : LinearOrder α} (hmon : @Antitone _ _ r.toPartialOrder.toPreorder _ μ) 
(hcard : Fintype.card α ≥ 2) :
preorderToPowersetFinset ⟨(dual r).toPartialOrder.toPreorder, (AFLOPartitions_is_everything (dual r).toPartialOrder.toPreorder).mp 
(dual r).le_total⟩ ∈ (WeightedComplex μ).faces ↔ (∀ (a : α), μ a ≥ 0):= by 
  rw [FacesWeightedComplex]
  constructor 
  . intro hr 
    have heq : (dual r).toPartialOrder.toPreorder = ((WeightedComplextoPositivePartitions μ).toFun 
      ⟨preorderToPowersetFinset ⟨(dual r).toPartialOrder.toPreorder, (AFLOPartitions_is_everything (dual r).toPartialOrder.toPreorder).mp 
      (dual r).le_total⟩, hr.1⟩).1 := by 
      unfold WeightedComplextoPositivePartitions 
      simp only 
      unfold preorderToPowersetFinset
      rw [Set.Finite.coe_toFinset, ←preorderToPowersetToPreorder, Subtype.coe_mk]
    apply (Dual_linear_order_in_AFLO_positive μ hsum hmon).mp  
    rw [heq]
    simp only [Set.Finite.toFinset_setOf, Set.bot_eq_empty, ne_eq, Set.top_eq_univ, Finset.mem_univ,
      forall_true_left, Equiv.toFun_as_coe_apply, RelIso.coe_toEquiv, Subtype.coe_prop]
  . intro hpos 
    constructor 
    . unfold AFLOPowerset_positive 
      rw [Set.mem_setOf] 
      exists AFLO_preorderToPowerset ⟨(dual r).toPartialOrder.toPreorder, (AFLOPartitions_is_everything (dual r).toPartialOrder.toPreorder).mp 
        (dual r).le_total⟩ 
      intro X hX 
      unfold IsPositiveSet 
      apply Finset.sum_nonneg 
      intro a _ 
      exact hpos a 
    . rw [ne_eq, Set.Finite.toFinset_eq_empty, preorderToPowerset_is_empty_iff_TrivialPreorder, ←ne_eq, nontrivial_preorder_iff_exists_not_le]
      simp only [not_le]
      rw [ge_iff_le, Nat.succ_le, Fintype.one_lt_card_iff] at hcard 
      match hcard with 
      | ⟨a, b, hab⟩ => cases lt_or_gt_of_ne hab with 
                      | inl hab => exists a; exists b  
                      | inr hba => exists b; exists a 
    



/- We prove that the weighted complex is decomposable.-/

lemma WeightedComplex_is_decomposable {r : LinearOrder α} (hmon : @Antitone _ _ r.toPartialOrder.toPreorder _ μ) : 
IsDecomposition (R_weighted μ r) (DF_weighted μ hsum hmon) := by  
  constructor 
  . intro ⟨s, hsf⟩
    rw [mem_facets_iff, FacesWeightedComplex] at hsf 
    exact restriction_is_smaller r ⟨s, hsf.1.1.1⟩ 
  . intro ⟨s, hsf⟩ ⟨t, htf⟩ 
    have htf' := htf 
    rw [mem_facets_iff] at htf 
    rw [WeightedComplex] at hsf htf  
    unfold R_weighted DF_weighted 
    simp only 
    unfold restriction_weighted distinguishedFacet_weighted 
    simp only [Equiv.invFun_as_coe, OrderIso.toEquiv_symm, RelIso.coe_toEquiv, Subtype.mk.injEq] 
    set p := (WeightedComplextoPositivePartitions μ).toFun ⟨s, hsf.1⟩
    set q := (WeightedComplextoPositivePartitions μ).toFun ⟨t, htf.1.1⟩
    constructor 
    . intro hint 
      rw [and_comm] at hint 
      have hqp : q.1 ≤ p.1 := by 
        change p ≤ q
        simp only [Equiv.toFun_as_coe_apply, RelIso.coe_toEquiv, map_le_map_iff, Subtype.mk_le_mk, Finset.le_eq_subset]
        exact hint.1 
      have hpq : p.1 ≤ @AscentPartition _ r q.1 q.2.1.1 := by 
        change ⟨@AscentPartition _ r q.1 q.2.1.1, AscentPartition_respects_AFLO_positive μ r q.2⟩ ≤ p 
        have h := hint.2 
        change (WeightedComplextoPositivePartitions μ).invFun ⟨@AscentPartition _ r q.1 q.2.1.1, 
          AscentPartition_respects_AFLO_positive μ r q.2⟩ ≤ (⟨s, hsf.1⟩ : AFLOPowerset_positive μ) at h
        apply_fun (WeightedComplextoPositivePartitions μ).toFun at h 
        simp only [Equiv.toFun_as_coe_apply, RelIso.coe_toEquiv, Equiv.invFun_as_coe, OrderIso.toEquiv_symm,
            OrderIso.apply_symm_apply] at h
        exact h   
        exact (WeightedComplextoPositivePartitions μ).monotone 
      have hqlin : IsLinearOrder α q.1.le := by 
        rw [FacetWeightedComplex_iff, Facets_are_linear_orders (facets_subset htf'.1)] at htf' 
        exact htf'.1 
        exact hsum 
      have halmost := @LinearOrder_of_total_preorder_and_linear_order_on_ascent_interval' _ r q.1 p.1 hqlin p.2.1.1 hqp hpq
      have h' : q = ⟨LinearOrder_of_total_preorder_and_linear_order r p.1, LinearOrder_etc_respects_AFLO_positive μ hsum hmon p.2⟩ := by 
        rw [←SetCoe.ext_iff]
        exact halmost   
      apply_fun (WeightedComplextoPositivePartitions μ).invFun at h'
      simp only [Equiv.toFun_as_coe_apply, RelIso.coe_toEquiv, Equiv.invFun_as_coe, OrderIso.toEquiv_symm,
         OrderIso.symm_apply_apply] at h'
      rw [←SetCoe.ext_iff] at h' 
      exact h' 
    . intro heq 
      have hqp : q.1 = LinearOrder_of_total_preorder_and_linear_order r p.1 := by 
        simp only [Equiv.toFun_as_coe_apply, RelIso.coe_toEquiv]
        have h : q = ⟨LinearOrder_of_total_preorder_and_linear_order r p.1, LinearOrder_etc_respects_AFLO_positive μ hsum hmon p.2⟩ := by
          apply Equiv.injective (WeightedComplextoPositivePartitions μ).toEquiv.symm 
          simp only [OrderIso.toEquiv_symm, Equiv.toFun_as_coe_apply, RelIso.coe_toEquiv, OrderIso.symm_apply_apply]
          rw [←SetCoe.ext_iff]
          exact heq
        rw [←SetCoe.ext_iff] at h 
        exact h 
      have hqlin : IsLinearOrder α q.1.le := by 
        rw [hqp]
        exact LinearOrder_of_total_preorder_and_linear_order_is_linear r p.2.1.1  
      have halmost := @LinearOrder_of_total_preorder_and_linear_order_fibers _ r q.1 p.1 hqlin p.2.1.1 (Eq.symm hqp)        
      rw [and_comm]
      change p ≤ q ∧ ⟨@AscentPartition _ r q.1 q.2.1.1, AscentPartition_respects_AFLO_positive μ r q.2⟩ ≤ p  at halmost 
      erw [(WeightedComplextoPositivePartitions μ).map_rel_iff'] at halmost 
      erw [and_iff_right halmost.1] 
      have halmost := halmost.2 
      simp only [Equiv.toFun_as_coe_apply, RelIso.coe_toEquiv] at halmost
      apply_fun (WeightedComplextoPositivePartitions μ).invFun at halmost 
      simp only [Equiv.invFun_as_coe, OrderIso.toEquiv_symm, RelIso.coe_toEquiv, OrderIso.symm_apply_apply] at halmost
      exact halmost 
      exact (WeightedComplextoPositivePartitions μ).symm.monotone 


                      

/- The weighted complex is finite.-/
 
lemma WeightedComplex_is_finite : FiniteComplex (WeightedComplex μ) := 
Finite_IsLowerSet (WeightedComplex_subcomplex μ) (CoxeterComplex_is_finite α)


/- Dimension of the facets of the weighted complex.-/

lemma WeightedComplex_dimension_facet (s : (WeightedComplex μ).facets) :
Finset.card s.1 = Fintype.card α -1 := by 
  have hsf := s.2 
  rw [FacetWeightedComplex_iff] at hsf 
  exact @CoxeterComplex_dimension_facet α _ ⟨s, hsf.1⟩
  exact hsum  


/- The weighted complex is pure (of dimension Fintype.card α - 2, since we know that the facets have cardinality Fintype.card α - 1).-/

lemma WeightedComplex_is_pure : Pure (WeightedComplex μ) := 
Dimension_of_Noetherian_pure (Finite_implies_Noetherian (WeightedComplex_is_finite μ)) 
(fun s t hsf htf => by rw [WeightedComplex_dimension_facet μ hsum ⟨s, hsf⟩, WeightedComplex_dimension_facet μ hsum ⟨t, htf⟩])


/- We find the π₀ and homology facets: the unique π₀ facet is the minimal one for the weak Bruhat order (i.e. the one corresponding to r), and
the unique homology facet is the maximal one for the weak Bruhat order (i.e. the one corresponding to the dual of r), if it is in the
weighted complex.-/


lemma WeightedComplex_Pi0Facet {r : LinearOrder α} (hmon : @Antitone _ _ r.toPartialOrder.toPreorder _ μ)  {s : Finset (Set α)} 
(hsf : s ∈ (WeightedComplex μ).facets) :
IsPi0Facet (WeightedComplex_is_decomposable μ hsum hmon) ⟨s, hsf⟩ ↔ powersetToPreorder (s : Set (Set α)) = r.toPartialOrder.toPreorder 
∨ Fintype.card α = 2 := by 
  rw [FacetWeightedComplex_iff] at hsf 
  rw [←(CoxeterComplex_Pi0Facet r hsf.1)]
  rw [IsPi0Facet_iff, IsPi0Facet_iff]
  rw [R_comparison]
  exact hsum; exact hsum 
                

lemma WeightedComplex_HomologyFacet {r : LinearOrder α} (hmon : @Antitone _ _ r.toPartialOrder.toPreorder _ μ)  {s : Finset (Set α)} 
(hsf : s ∈ (WeightedComplex μ).facets) :
IsHomologyFacet (WeightedComplex_is_decomposable μ hsum hmon) ⟨s, hsf⟩ ↔ 
powersetToPreorder (s : Set (Set α)) = (dual r).toPartialOrder.toPreorder ∧ Fintype.card α > 2 := by  
  rw [FacetWeightedComplex_iff] at hsf 
  rw [←(CoxeterComplex_HomologyFacet r hsf.1)]
  rw [IsHomologyFacet_iff, IsHomologyFacet_iff, R_comparison]
  exact hsum; exact hsum 


/- Shellability of the Coxeter complex: any linear order on the facets that refines the weak Bruhat is a shelling order. To make
it more convenient to state the lemmas, we first lift the weak Bruhat order to facets of the Coxeter complex.-/

open WeakBruhatOrder 

def WeightedComplexFacets_to_LinearOrders (s : (WeightedComplex μ).facets) : 
{p : Preorder α | IsLinearOrder α p.le} := by 
  have hsf := s.2 
  rw [FacetWeightedComplex_iff, Facets_are_linear_orders (facets_subset hsf.1)] at hsf
  exact ⟨powersetToPreorder s.1, hsf.1⟩
  exact hsum 


lemma WeightedComplexFacets_to_LinearOrders_injective : Function.Injective (WeightedComplexFacets_to_LinearOrders μ hsum) := by 
  intro s t hst 
  unfold WeightedComplexFacets_to_LinearOrders at hst
  simp only [Set.coe_setOf, Set.mem_setOf_eq, Subtype.mk.injEq] at hst
  have hsf := s.2 
  have htf := t.2 
  rw [FacetWeightedComplex_iff, mem_facets_iff] at hsf htf 
  have heqs := Faces_powersetToPreordertoPowerset hsf.1.1 
  have heqt := Faces_powersetToPreordertoPowerset htf.1.1 
  rw [←SetCoe.ext_iff, ←Finset.coe_inj]
  rw [heqs, heqt, hst]
  exact hsum; exact hsum 


def WeakBruhatOrder_facets_WeightedComplex (r : LinearOrder α) : PartialOrder (WeightedComplex μ).facets :=
@PartialOrder.lift _ _ (WeakBruhatOrder r) (WeightedComplexFacets_to_LinearOrders μ hsum) 
(WeightedComplexFacets_to_LinearOrders_injective μ hsum)


lemma WeakBruhat_compatible_with_DF_weighted {r : LinearOrder α} (hmon : @Antitone _ _ r.toPartialOrder.toPreorder _ μ) :
CompatibleOrder (DF_weighted μ hsum hmon) (WeakBruhatOrder_facets_WeightedComplex μ hsum r) := by 
  unfold CompatibleOrder
  intro ⟨s, hsf⟩ ⟨t, htf⟩  
  change s ⊆ t → Inversions r.lt (powersetToPreorder (DF_weighted μ hsum hmon ⟨s, hsf⟩).1).lt ⊆ _ 
  rw [DF_comparison]
  rw [FacetWeightedComplex_iff] at htf 
  exact WeakBruhat_compatible_with_DF r ⟨s, WeightedComplex_subcomplex μ hsf⟩ ⟨t, htf.1⟩
  exact hsum 



lemma WeightedComplexShelling {r : LinearOrder α} (hmon : @Antitone _ _ r.toPartialOrder.toPreorder _ μ)  
{so : LinearOrder (WeightedComplex μ).facets} (hcomp : ∀ {s t : (WeightedComplex μ).facets},
(WeakBruhatOrder_facets_WeightedComplex μ hsum r).le s t  → so.le s t) : IsShellingOrder so :=  
  ShellableofDecomposable (WeightedComplex_is_decomposable μ hsum hmon) (fun s t hst => hcomp (WeakBruhat_compatible_with_DF_weighted 
  μ hsum hmon s t hst)) (@Finite.Preorder.wellFounded_lt _ (Finite.of_injective (fun s => s.1) 
  (fun s t hst => by rw [SetCoe.ext_iff] at hst; exact hst)) so.toPartialOrder.toPreorder) 



/-Calcul of the Euler-Poincaré characteristic of the weighted complex. (We assume that α is nonempty to get a uniform formula: if Fintype.card α ≤ 1,
then the Coxeter complex is empty so its EP characteristic is 0.) Is is equal to 1 + (-1)^(Fintype.card α) if all μ a are ≥ 0, and to 1
otherwise.-/

noncomputable def FacetWeightedComplexofLinearOrder (hcard : Fintype.card α ≥ 2) {r : LinearOrder α} 
(hmon : @Antitone _ _ r.toPartialOrder.toPreorder _ μ) : (WeightedComplex μ).facets := by 
  have hr := Fixed_linear_order_in_AFLO_positive μ hsum hmon 
  refine ⟨preorderToPowersetFinset ⟨r.toPartialOrder.toPreorder, hr.1⟩, ?_⟩
  rw [FacetWeightedComplex_iff]
  rw [and_iff_left (Fixed_linear_order_in_WeightedComplex μ hsum hmon hcard)]
  exact (FacetofLinearOrder hcard r).2
  exact hsum  

lemma WeightedComplex_of_pair {a b : α} (hab : a ≠ b) (hall : Finset.univ = {a,b}) (ha : μ a ≥ 0) (hb : μ b < 0) 
(s : Finset (Set α)) :  s ∈ (WeightedComplex μ).faces ↔ s = {{a}} := by 
  constructor 
  . intro hsw 
    erw [FacesWeightedComplex, AFLOPowerset_positive_iff] at hsw
    have h : ∀ (X : Set α), X ∈ s → X = {a} := by
      intro X hX 
      by_cases hbX : b ∈ X 
      . exfalso 
        have haX : a ∉ X := by 
          by_contra habs 
          have hXtop : X = ⊤ := by 
            rw [Set.top_eq_univ]
            ext c 
            simp only [Set.mem_univ, iff_true]
            cases Elements_pair a b hall c with 
            | inl hca => rw [hca]; exact habs 
            | inr hcb => rw [hcb]; exact hbX 
          exact (hsw.1.2 X hX).1.2 hXtop   
        have hXsin : X = {b} := by 
          ext c 
          simp only [Set.mem_singleton_iff]
          constructor 
          . intro hcX 
            by_contra hcb 
            have hc := Elements_pair a b hall c 
            rw [or_iff_left hcb] at hc
            rw [hc] at hcX 
            exact haX hcX  
          . exact fun hcb => by rw [hcb]; exact hbX
        have hpos := (hsw.1.2 X hX).2 
        unfold IsPositiveSet at hpos 
        rw [hXsin, Set.Finite.toFinset_singleton, Finset.sum_singleton] at hpos
        rw [lt_iff_not_le] at hb 
        exact hb hpos 
      . have haX : a ∈ X := by 
          by_contra habs 
          have hXbot : X = ⊥ := by 
            rw [Set.bot_eq_empty, Set.eq_empty_iff_forall_not_mem]
            intro c 
            cases Elements_pair a b hall c with 
            | inl hca => rw [hca]; exact habs 
            | inr hcb => rw [hcb]; exact hbX 
          exact (hsw.1.2 X hX).1.1 hXbot
        ext c 
        simp only [Set.mem_singleton_iff]
        constructor 
        . intro hcX 
          cases Elements_pair a b hall c with 
          | inl hca => exact hca 
          | inr hcb => exfalso; rw [hcb] at hcX; exact hbX hcX
        . exact fun hca => by rw [hca]; exact haX 
    ext X 
    simp only [Finset.mem_singleton]
    constructor 
    . exact fun hXs => h X hXs 
    . intro hXa 
      by_contra habs 
      have hse : s = ∅ := by 
        rw [Finset.eq_empty_iff_forall_not_mem]
        intro Y hYs 
        have hYa := h Y hYs 
        rw [hYa, ←hXa] at hYs
        exact habs hYs 
      exact hsw.2 hse  
  . intro hsa 
    rw [FacesWeightedComplex, AFLOPowerset_positive_iff, hsa]
    constructor 
    . constructor 
      . intro ⟨X, hX⟩ ⟨Y, hY⟩
        simp only [Finset.mem_singleton] at hX hY
        simp only 
        rw [hX, hY]
        exact Or.inl (subset_refl _)
      . intro X hX 
        rw [Finset.mem_singleton] at hX
        rw [hX]  
        rw [Set.bot_eq_empty, Set.top_eq_univ, ←Set.nonempty_iff_ne_empty, Set.ne_univ_iff_exists_not_mem]
        constructor 
        . rw [and_iff_right ⟨a, Set.mem_singleton _⟩]
          exists b 
          simp only [Set.mem_singleton_iff]
          exact Ne.symm hab 
        . unfold IsPositiveSet 
          rw [Set.Finite.toFinset_singleton, Finset.sum_singleton]
          exact ha 
    . rw [←Finset.nonempty_iff_ne_empty]
      exists {a}
      exact Finset.mem_singleton_self _ 

lemma preorderToPowerset_of_pair (r : LinearOrder α) {a b : α} (hab : r.lt a b) (hall : Finset.univ = {a,b}) :
preorderToPowerset r.toPartialOrder.toPreorder = {{a}} := by 
  unfold preorderToPowerset 
  ext X 
  simp only [Set.bot_eq_empty, Set.top_eq_univ, Set.mem_setOf_eq, Set.mem_singleton_iff]
  rw [←Set.nonempty_iff_ne_empty, Set.ne_univ_iff_exists_not_mem]
  have hall' : Finset.univ = @insert α (Finset α) (@Finset.instInsertFinset α fun a b => propDecidable (a = b)) a {b} := by 
    ext c 
    rw [hall]
    rw [Finset.mem_insert, @Finset.mem_insert _ (fun a b => propDecidable (a = b))]
  constructor 
  . intro hX 
    by_cases hbX : b ∈ X 
    . exfalso 
      have haX : a ∈ X := hX.2.2 (le_of_lt hab) hbX 
      match hX.2.1 with 
      | ⟨c, hcX⟩ => 
        cases Elements_pair a b hall' c with 
        | inl hca => rw [hca] at hcX; exact hcX haX 
        | inr hcb => rw [hcb] at hcX; exact hcX hbX 
    . have haX : a ∈ X := by 
        match hX.1 with 
      | ⟨c, hcX⟩ => 
        cases Elements_pair a b hall' c with 
        | inl hca => rw [hca] at hcX; exact hcX 
        | inr hcb => exfalso; rw [hcb] at hcX; exact hbX hcX 
      ext c 
      simp only [Set.mem_singleton_iff]
      constructor 
      . intro hcX 
        cases Elements_pair a b hall' c with 
        | inl hca => exact hca  
        | inr hcb => exfalso; rw [hcb] at hcX; exact hbX hcX 
      . exact fun hca => by rw [hca]; exact haX 
  . intro hXa 
    rw [hXa]
    rw [and_iff_right ⟨a, Set.mem_singleton _⟩]
    constructor 
    . exists b 
      simp only [Set.mem_singleton_iff]
      exact Ne.symm (ne_of_lt hab)
    . intro c d hcd 
      simp only [Set.mem_singleton_iff]
      intro hca 
      rw [hca] at hcd 
      cases Elements_pair a b hall' d with 
      | inl hda => exact hda 
      | inr hdb => exfalso; rw [hdb] at hcd; rw [lt_iff_not_le] at hab; exact hab hcd 

lemma EulerPoincareCharacteristic_WeightedComplex (hne : Nonempty α) : 
EulerPoincareCharacteristic (WeightedComplex_is_finite μ) = if (∀  (a : α), μ a ≥ 0) then 1 + (-1 : ℤ)^(Fintype.card α) else 1 := by 
  by_cases hpos : ∀ (a : α), μ a ≥ 0 
  . simp only [ge_iff_le, hpos, forall_const, ite_true]
    rw [EulerPoincareCharacteristic_ext (WeightedComplex_is_finite μ) (CoxeterComplex_is_finite α) 
      ((WeightedComplex_all_iff μ hsum).mpr (Or.inr hpos))]
    exact EulerPoincareCharacteristic_CoxeterComplex hne 
  . simp only [ge_iff_le, hpos, ite_false]
    have hcard : Fintype.card α ≥ 2 := by 
      push_neg at hpos 
      match hpos with 
      | ⟨a, ha⟩ => 
        by_contra hless 
        rw [←lt_iff_not_le, Nat.lt_succ, Fintype.card_le_one_iff] at hless
        have hneg : Finset.sum Finset.univ μ < 0 := by 
          apply Finset.sum_neg 
          . exact fun b _ => by rw [hless b a]; exact ha 
          . exact ⟨a, Finset.mem_univ _⟩
        rw [lt_iff_not_le] at hneg 
        exact hneg hsum 
    match Exists_LinearOrder_antitone μ with 
    | ⟨r, hmon⟩ => 
        rw [EulerPoincareCharacteristicDecomposable (WeightedComplex_is_finite μ) (WeightedComplex_is_decomposable μ hsum hmon)]
        have hpi : Set.Finite.toFinset (π₀Facets_finite (WeightedComplex_is_decomposable μ hsum hmon) (WeightedComplex_is_finite μ)) =
          {(FacetWeightedComplexofLinearOrder μ hsum hcard hmon).1} := by 
          rw [←Finset.coe_inj, Set.Finite.coe_toFinset, Finset.coe_singleton]
          ext s 
          unfold π₀Facets
          simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
          constructor 
          . intro hspi 
            match hspi with 
            | ⟨hsf, hspi⟩ => 
              rw [WeightedComplex_Pi0Facet] at hspi 
              cases hspi with 
              | inl hsr => unfold FacetWeightedComplexofLinearOrder 
                           simp only 
                           rw [←Finset.coe_inj, Set.Finite.coe_toFinset, Subtype.coe_mk, ←hsr]
                           apply Faces_powersetToPreordertoPowerset
                           rw [mem_facets_iff] at hsf 
                           exact WeightedComplex_subcomplex μ hsf.1 
              | inr hscard => rw [←Finset.card_univ, @Finset.card_eq_two _ _ inferInstance] at hscard
                              unfold FacetWeightedComplexofLinearOrder 
                              simp only 
                              rw [←Finset.coe_inj, Set.Finite.coe_toFinset, Subtype.coe_mk]
                              rw [mem_facets_iff] at hsf
                              match hscard with 
                              | ⟨a, b, hab, hall⟩ => 
                                have hall' :  Finset.univ = @insert α (Finset α) 
                                    (@Finset.instInsertFinset α fun a b => propDecidable (a = b)) a {b}  := by 
                                    ext c 
                                    rw [hall]
                                    rw [Finset.mem_insert, @Finset.mem_insert _ (fun a b => propDecidable (a = b))]
                                by_cases ha : μ a ≥ 0 
                                . have hb : μ b < 0 := by 
                                    by_contra habs 
                                    have h : ∀ (x : α), μ x ≥ 0 := by
                                      intro x 
                                      cases Elements_pair a b hall' x with 
                                      | inl hxa => rw [hxa]; exact ha 
                                      | inr hxb => rw [hxb]; rw [lt_iff_not_le, not_not] at habs; exact habs 
                                    exact hpos h 
                                  have hseq : s ={{a}} := (WeightedComplex_of_pair μ hab hall' ha hb s).mp hsf.1 
                                  have hab' : r.lt a b := by 
                                    by_contra hba 
                                    rw [lt_iff_not_le, not_not] at hba
                                    rw [lt_iff_not_le] at hb 
                                    exact hb (le_trans ha (hmon hba))     
                                  rw [hseq, Finset.coe_singleton]
                                  exact Eq.symm (preorderToPowerset_of_pair r hab' hall)   
                                . rw [←lt_iff_not_le] at ha 
                                  have hb : μ b ≥ 0 := by 
                                    by_contra habs 
                                    rw [←lt_iff_not_le] at habs 
                                    have hneg : Finset.sum Finset.univ μ < 0 := by 
                                      apply Finset.sum_neg 
                                      . intro c hc 
                                        rw [hall] at hc 
                                        simp only [Finset.mem_singleton, Finset.mem_insert] at hc
                                        cases hc with 
                                        | inl hca => rw [hca]; exact ha 
                                        | inr hcb => rw [hcb]; exact habs 
                                      . exists a; exact Finset.mem_univ _ 
                                    rw [lt_iff_not_le] at hneg 
                                    exact hneg hsum 
                                  rw [Finset.pair_comm] at hall
                                  have hall' :  Finset.univ = @insert α (Finset α) 
                                    (@Finset.instInsertFinset α fun a b => propDecidable (a = b)) b {a}  := by 
                                    ext c 
                                    rw [hall]
                                    rw [Finset.mem_insert, @Finset.mem_insert _ (fun a b => propDecidable (a = b))]
                                  have hseq : s ={{b}} := (WeightedComplex_of_pair μ (Ne.symm hab) hall' hb ha s).mp hsf.1
                                  have hab' : r.lt b a := by 
                                    by_contra hab 
                                    rw [lt_iff_not_le, not_not] at hab 
                                    rw [lt_iff_not_le] at ha 
                                    exact ha (le_trans hb (hmon hab)) 
                                  rw [hseq, Finset.coe_singleton]
                                  exact Eq.symm (preorderToPowerset_of_pair r hab' hall)         
          . intro hsr 
            set t := FacetWeightedComplexofLinearOrder μ hsum hcard hmon with htdef 
            rw [hsr]
            exists t.2 
            rw [WeightedComplex_Pi0Facet] 
            apply Or.inl 
            rw [htdef]
            unfold FacetWeightedComplexofLinearOrder 
            simp only 
            rw [Set.Finite.coe_toFinset, Subtype.coe_mk, ←preorderToPowersetToPreorder]
        have hhom :  Set.Finite.toFinset (HomologyFacets_finite (WeightedComplex_is_decomposable μ hsum hmon) (WeightedComplex_is_finite μ)) = 
        ∅ := by 
          rw [Set.Finite.toFinset_eq_empty, Set.eq_empty_iff_forall_not_mem]
          intro s 
          unfold HomologyFacets
          simp only [Set.mem_setOf_eq, not_exists]
          intro hsf 
          rw [WeightedComplex_HomologyFacet, not_and_or]
          apply Or.inl 
          by_contra hdual 
          have heq : s = preorderToPowersetFinset ⟨(dual r).toPartialOrder.toPreorder, (AFLOPartitions_is_everything 
            (dual r).toPartialOrder.toPreorder).mp (dual r).le_total⟩ := by 
            rw [←Finset.coe_inj, Set.Finite.coe_toFinset, Subtype.coe_mk, ←hdual]
            apply Faces_powersetToPreordertoPowerset
            rw [mem_facets_iff] at hsf 
            exact WeightedComplex_subcomplex μ hsf.1 
          rw [mem_facets_iff, heq, Dual_linear_order_in_WeightedComplex μ hsum hmon hcard] at hsf 
          exact hpos hsf.1   
        rw [hpi, hhom, Finset.sum_empty, add_zero]
        simp only [Finset.card_singleton, Nat.cast_one]




end FiniteWeightedComplex       
