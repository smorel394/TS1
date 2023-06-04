import TS1.FiniteWeightedComplex 

set_option autoImplicit false

open Classical 

universe u

variable (α : Type u) [Fintype α]

open Preorder FiniteWeightedComplex FiniteCoxeterComplex AbstractSimplicialComplex 

namespace TS1 

noncomputable instance fintypeLinearOrderedPartitions : Fintype (LinearOrderedPartitions α) := 
Subtype.fintype _ 

variable {α}

noncomputable def fintypeAntisymmetrization (s : Preorder α) : Fintype (Antisymmetrization α s.le) := Quotient.fintype (AntisymmRel.setoid α s.le)

noncomputable def CardBlocksPartition (s : Preorder α) : ℕ := @Fintype.card (Antisymmetrization α s.le) (fintypeAntisymmetrization s)

lemma CardBlocksTrivialPreorder_nonempty (hne : Nonempty α) : CardBlocksPartition (trivialPreorder α) = 1 := by
  unfold CardBlocksPartition
  rw [@Fintype.card_eq_one_iff _ (fintypeAntisymmetrization (trivialPreorder α))] 
  set a := Classical.choice hne 
  exists toAntisymmetrization (trivialPreorder α).le a 
  intro x 
  rw [←(toAntisymmetrization_ofAntisymmetrization _ x)]
  apply Quotient.sound 
  generalize ofAntisymmetrization _ x = b 
  change AntisymmRel _ b a 
  unfold AntisymmRel trivialPreorder 
  simp only [and_self]

lemma CardBlocksTrivialPreorder_empty (he : IsEmpty α) : CardBlocksPartition (trivialPreorder α) = 0 := by 
  unfold CardBlocksPartition 
  rw [@Fintype.card_eq_zero_iff _ (fintypeAntisymmetrization _)]
  refine {false := fun x => he.false (ofAntisymmetrization (trivialPreorder α).le x)}


lemma CardBlocksPartition_vs_card_preorderToPowerset (hne : Nonempty α) {s : Preorder α} (htot : Total s.le) : 
CardBlocksPartition s = Fintype.card (preorderToPowerset s) + 1 := by 
  unfold CardBlocksPartition 
  haveI : Fintype (Antisymmetrization α s.le) := fintypeAntisymmetrization s 
  haveI : Fintype (Antisymmetrization_nonmaximal s) := inferInstance 
  rw [←(Fintype.card_congr (Equiv_Antisymmetrization_nonmaximal_to_PreorderToPowerset htot 
    (@Fintype.toLocallyFiniteOrder (Antisymmetrization α s.le) _ _ _ _)))]
  simp_rw [@FiniteAntisymmetrization_nonmaximal _ s htot inferInstance hne] 
  simp only [Finset.coe_sort_coe, Fintype.card_coe, ge_iff_le]
  rw [Finset.card_erase_of_mem ?_]
  . rw [@Finset.card_univ _ (@Fintype.ofFinite _ _)]
    apply Eq.symm
    rw [←Nat.succ_eq_add_one, ←Nat.pred_eq_sub_one]
    rw [@Fintype.card_congr' _ _ (fintypeAntisymmetrization s) (Fintype.ofFinite (Antisymmetrization α s.le)) rfl] 
    apply Nat.succ_pred   
    rw [←Nat.pos_iff_ne_zero, @Fintype.card_pos_iff _ (Fintype.ofFinite _)]
    apply Nonempty.intro 
    exact (toAntisymmetrization s.le (Classical.choice hne))
  . exact @Finset.mem_univ _ (Fintype.ofFinite (Antisymmetrization α s.le)) _    
 

lemma CardBlocksTwoStepPreorder {a b : α} (hab : a ≠ b) : CardBlocksPartition (twoStepPreorder a) = 2 := by 
  have hne : Nonempty α := Nonempty.intro a 
  rw [CardBlocksPartition_vs_card_preorderToPowerset hne (twoStepPreorder_IsTotal a)]
  have hcard : Fintype.card (preorderToPowerset (twoStepPreorder a)) = 1 := by 
    rw [Fintype.card_eq_one_iff]
    rw [preorderToPowerset_TwoStepPreorder hab]
    simp only [eq_iff_true_of_subsingleton, Subtype.forall, Set.mem_singleton_iff, implies_true, forall_const, exists_const]
  rw [hcard]


/- Positive linearly ordered partitions: this is AFLOPartitions_positive, but we can give a simpler definition since α is finite.-/

variable (μ : α → ℝ) {hsum : Finset.sum Finset.univ μ ≥ 0}

lemma AFLOPartitions_positive_eq : AFLOPartitions_positive μ = {s : Preorder α | Total s.le ∧ ∀ (a : α), 
@IsPositiveSet _ μ (@Set.Iic _ s a) (Subtype.finite)} := by  
  ext s 
  rw [AFLOPartitions_positive, Set.mem_setOf, Set.mem_setOf]
  constructor 
  . intro hs 
    match hs with 
    | ⟨hp, hs⟩ => 
      rw [AFLOPowerset_positive, Set.mem_setOf] at hs 
      match hs with
      | ⟨_, hs⟩ => 
        rw [and_iff_right hp.1]
        intro a 
        set X := @Set.Iic _ s a 
        by_cases hamax : ∃ (b : α), s.lt a b 
        . have hX : X ∈ preorderToPowersetFinset ⟨s, hp⟩ := by 
            rw  [Set.Finite.mem_toFinset, preorderToPowerset, Set.mem_setOf, Set.bot_eq_empty, Set.top_eq_univ,
            ←Set.nonempty_iff_ne_empty, Set.ne_univ_iff_exists_not_mem]
            constructor 
            . exists a; simp only [Set.mem_Iic, _root_.le_refl]
            . constructor 
              . match hamax with 
                | ⟨b, hab⟩ => exists b; simp only [Set.mem_Iic]; rw [TotalPreorder_lt_iff_not_le hp.1]; exact hab
              . exact isLowerSet_Iic _ 
          exact hs hX  
        . have hIic : Set.Finite.toFinset ((@Set.finite_coe_iff _ (@Set.Iic _ s a)).mp Subtype.finite) = Finset.univ := by 
            ext b 
            simp only [Set.Finite.toFinset_setOf, Finset.mem_univ, forall_true_left, Finset.mem_filter, true_and, iff_true]
            push_neg at hamax 
            have h := hamax b 
            rw [←(TotalPreorder_lt_iff_not_le hp.1), not_not] at h
            exact h  
          rw [IsPositiveSet, hIic]                              
          exact hsum 
  . intro hs 
    have hp : s ∈ AFLOPartitions α := by 
      rw [←AFLOPartitions_is_everything]
      exact hs.1
    exists hp 
    rw [AFLOPowerset_positive, Set.mem_setOf]
    have hE : preorderToPowersetFinset ⟨s, hp⟩ ∈ AFLOPowerset α := by 
      rw [←AFLOPowerset_is_everything]
      constructor 
      . intro ⟨X, hX⟩ ⟨Y, hY⟩
        rw [Set.Finite.mem_toFinset] at hX hY 
        exact preorderToPowerset_total_is_total hs.1 ⟨X, hX⟩ ⟨Y, hY⟩
      . intro X hX 
        rw [Set.Finite.mem_toFinset] at hX 
        exact ⟨hX.1, hX.2.1⟩
    exists hE 
    intro X hX 
    rw [Set.Finite.mem_toFinset] at hX 
    match TotalELFP_LowerSet_is_principal hs.1 (EssentiallyLocallyFinite_ofLocallyFinite (@Fintype.toLocallyFiniteOrder _ 
      s _ _ _)) hX with 
    | ⟨a, haX⟩ => simp_rw [haX]
                  exact hs.2 a 


lemma trivialPreorder_in_AFLOPartitions_positive : trivialPreorder α ∈ AFLOPartitions_positive μ := by
  rw [@AFLOPartitions_positive_eq _ _ μ hsum]
  simp only [Set.mem_setOf_eq]
  rw [and_iff_right (trivialPreorder_is_total α)]
  intro a 
  have hIic : Set.Finite.toFinset ((@Set.finite_coe_iff _ (@Set.Iic _ (trivialPreorder α) a)).mp Subtype.finite) = Finset.univ := by
    ext b 
    simp only [Set.Finite.toFinset_setOf, Finset.mem_univ, forall_true_left, Finset.mem_filter, true_and,
  iff_true]
    unfold trivialPreorder
    simp only 
  unfold IsPositiveSet 
  rw [hIic]
  exact hsum 


lemma AFLOPartitions_positive_of_empty (he : IsEmpty α) : AFLOPartitions_positive μ = {trivialPreorder α} := by 
  ext s 
  simp only [Set.mem_singleton_iff]
  constructor 
  . intro _ 
    ext a
    exfalso 
    exact he.false a 
  . exact fun hs => by rw [hs]; exact @trivialPreorder_in_AFLOPartitions_positive _ _ μ hsum 

lemma AFLOPartitions_positive_of_singleton {a : α} (hall : ∀ (b : α), b = a) : 
AFLOPartitions_positive μ = {trivialPreorder α} := by 
  ext s 
  simp only [Set.mem_singleton_iff]
  constructor 
  . intro _ 
    ext b c 
    unfold trivialPreorder 
    simp only [hall b, hall c, _root_.le_refl]
  . exact fun hs => by rw [hs]; exact @trivialPreorder_in_AFLOPartitions_positive _ _ μ hsum 


/- We want to compute the sum over all positive partitions s of (-1) to the number of blocks of s. We first define this sum.-/

noncomputable def Sum_of_signs_over_AFLOPartitions_positive : ℤ :=
Finset.sum (Set.Finite.toFinset ((@Set.finite_coe_iff _ (AFLOPartitions_positive μ)).mp inferInstance)) 
(fun s => (-1 : ℤ)^(CardBlocksPartition s)) 

lemma Sum_of_signs_eq : Sum_of_signs_over_AFLOPartitions_positive μ = if ∀ (a : α), μ a ≥ 0 then (-1 : ℤ)^(Fintype.card α) else 0 := by
  unfold Sum_of_signs_over_AFLOPartitions_positive 
  by_cases hne : Nonempty α
  . have heq := @Finset.sum_bij' ℤ (Preorder α) (Finset (Set α)) _ 
      (Set.Finite.toFinset ((@Set.finite_coe_iff _ (AFLOPartitions_positive μ)).mp inferInstance))
      (Set.Finite.toFinset ((@Set.finite_coe_iff _ (AFLOPowerset_positive μ)).mp inferInstance))
      (fun s => (-1 : ℤ)^(CardBlocksPartition s)) (fun s => (-1 : ℤ)^(Finset.card s + 1))
      (fun s hs => by rw [Set.Finite.mem_toFinset] at hs; exact preorderToPowersetFinset ⟨s, hs.1⟩)  
      (fun s hs => by rw [Set.Finite.mem_toFinset] at hs |- 
                      exact ((WeightedComplextoPositivePartitions μ).invFun ⟨s, hs⟩).2)
      (fun s hs => by simp only 
                      rw [Set.Finite.mem_toFinset] at hs  
                      rw [CardBlocksPartition_vs_card_preorderToPowerset hne hs.1.1]
                      unfold preorderToPowersetFinset
                      rw [Set.Finite.card_toFinset]) 
      (fun s _ => powersetToPreorder s)
      (fun s hs => by rw [Set.Finite.mem_toFinset] at hs |- 
                      exact ((WeightedComplextoPositivePartitions μ).toFun ⟨s, hs⟩).2)
      (fun s hs => by rw [Set.Finite.mem_toFinset] at hs
                      simp only 
                      unfold preorderToPowersetFinset 
                      rw [Set.Finite.coe_toFinset, Subtype.coe_mk]
                      exact Eq.symm (preorderToPowersetToPreorder s))
      (fun s hs => by rw [Set.Finite.mem_toFinset] at hs 
                      simp only 
                      unfold preorderToPowersetFinset 
                      rw [←Finset.coe_inj, Set.Finite.coe_toFinset, Subtype.coe_mk]
                      have heq : ⟨s, hs.1⟩ = (CoxeterComplextoPartitions α).invFun ((CoxeterComplextoPartitions α).toFun ⟨s, hs.1⟩) := by
                        simp only [Equiv.toFun_as_coe_apply, RelIso.coe_toEquiv, Equiv.invFun_as_coe, OrderIso.toEquiv_symm,
                        OrderIso.symm_apply_apply] 
                      rw [←SetCoe.ext_iff, Subtype.coe_mk] at heq 
                      unfold CoxeterComplextoPartitions preorderToPowersetFinset at heq 
                      simp only at heq 
                      rw [←Finset.coe_inj, Set.Finite.coe_toFinset] at heq  
                      exact Eq.symm heq)
    rw [heq] 
    have hunion : (Set.Finite.toFinset ((@Set.finite_coe_iff _ (AFLOPowerset_positive μ)).mp inferInstance)) = 
        (Set.Finite.toFinset ((@Set.finite_coe_iff _ (WeightedComplex μ).faces).mp inferInstance)) ∪ {∅} := by 
      ext s 
      rw [Set.Finite.mem_toFinset, Finset.mem_union, Set.Finite.mem_toFinset, Finset.mem_singleton, FacesWeightedComplex]
      constructor 
      . intro hs 
        by_cases hse : s = ∅ 
        . exact Or.inr hse 
        . exact Or.inl ⟨hs, hse⟩
      . intro hs 
        cases hs with 
        | inl hsne => exact hsne.1  
        | inr hse => rw [hse, AFLOPowerset_positive_iff]
                     constructor 
                     . intro ⟨_, hX⟩; exfalso; exact Finset.not_mem_empty _ hX  
                     . intro _ hX; exfalso; exact Finset.not_mem_empty _ hX 
    have hdisj : Disjoint (Set.Finite.toFinset ((@Set.finite_coe_iff _ (WeightedComplex μ).faces).mp inferInstance)) {∅} := by
      rw [Finset.disjoint_iff_ne]
      intro s hs t ht 
      rw [Set.Finite.mem_toFinset] at hs 
      rw [Finset.mem_singleton] at ht 
      rw [ht, ←Finset.nonempty_iff_ne_empty]
      exact (WeightedComplex μ).nonempty_of_mem hs  
    rw [←(Finset.disjUnion_eq_union _ _ hdisj)] at hunion 
    rw [hunion, Finset.sum_disjUnion hdisj]
    simp only [Finset.sum_singleton, Finset.card_empty, zero_add, pow_one]
    have hEP := EulerPoincareCharacteristic_WeightedComplex μ hsum hne
    unfold EulerPoincareCharacteristic at hEP  
    have heq := @Finset.sum_congr ℤ (Finset (Set α)) (FacesFinset (WeightedComplex_is_finite μ)) 
      (Set.Finite.toFinset ((@Set.finite_coe_iff _ (WeightedComplex μ).faces).mp inferInstance))
      (fun s => (-1)^(Finset.card s - 1)) (fun s => (-1)^(Finset.card s + 1)) _ 
      (by ext s; rw [FacesFinset, Set.Finite.mem_toFinset]) 
      (fun s hs => by simp only 
                      have heq : Finset.card s + 1 = Finset.card s - 1 + 2 := by 
                        rw [tsub_add_eq_add_tsub]
                        . simp only [ge_iff_le, Nat.succ_sub_succ_eq_sub, nonpos_iff_eq_zero, add_eq_zero, Finset.card_eq_zero,
                            and_false, tsub_zero]
                        . rw [Nat.succ_le, Nat.pos_iff_ne_zero]
                          rw [Set.Finite.mem_toFinset] at hs 
                          exact face_card_nonzero hs 
                      rw [heq, pow_add, neg_one_pow_two, mul_one]) 
    rw [←heq, hEP]
    by_cases hpos : ∀ (a : α), μ a ≥ 0 
    . simp only [ge_iff_le, hpos, forall_const, ite_true, add_neg_cancel_comm]
    . simp only [ge_iff_le, hpos, ite_false, add_right_neg]
  . rw [not_nonempty_iff] at hne
    simp_rw [@AFLOPartitions_positive_of_empty _ _ μ hsum hne] 
    rw [Set.Finite.toFinset_singleton, Finset.sum_singleton, CardBlocksTrivialPreorder_empty hne, pow_zero]
    have hpos : ∀ (a : α), μ a ≥ 0 := by 
      intro a 
      exfalso 
      exact hne.false a 
    simp only [ge_iff_le, hpos, IsEmpty.forall_iff, ite_true]
    rw [←Fintype.card_eq_zero_iff] at hne 
    rw [hne, pow_zero]



  
    



end TS1 



