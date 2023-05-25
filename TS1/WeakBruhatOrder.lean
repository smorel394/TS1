import TS1.ordered_partitions

universe u 

variable {α : Type u}

open LinearOrderedPartitions

namespace WeakBruhatOrder

/- We define the set of inversions between two relations r s on α. These are the pairs (a,b) of elements of α such that r a b and s b a hold.-/

def Inversions (r s : α → α → Prop) : Set (α × α) := {x | r x.1 x.2 ∧ s x.2 x.1}

lemma Inversions_def (r s : α → α → Prop) (a b : α) : (a,b) ∈ Inversions r s ↔ r a b ∧ s b a := by 
  unfold Inversions
  simp only [Set.mem_setOf_eq]

/- If r s are total preorders, then (a,b) is an inversions for r.lt and s.lt if and only if r.lt a b and ¬(s.le b a).-/ -- Is this useful ?

lemma Inversions_antitone (r : α → α → Prop) {s t : Preorder α} (hstot : Total s.le) (hst : s ≤ t) :
Inversions r t.lt ⊆ Inversions r s.lt := by 
  intro ⟨a,b⟩ hinv
  rw [Inversions_def, and_iff_right hinv.1] 
  rw [←(TotalPreorder_lt_iff_not_le hstot)]
  by_contra hsab 
  exact  not_lt_of_le (hst hsab) hinv.2 


/- Two linear orders are equal if and only if there are no inversions between them.-/

lemma LinearOrders_eq_iff_no_inversions {r r' : Preorder α} (hlinr : IsLinearOrder α r.le) (hlinr' : IsLinearOrder α r'.le) :
r = r' ↔ Inversions r.lt r'.lt = ∅ := by 
  constructor
  . intro hrr'
    rw [←hrr']
    apply Set.eq_empty_of_forall_not_mem
    intro ⟨a,b⟩ 
    rw [Inversions_def] 
    push_neg 
    exact fun hab => @not_lt_of_le _ r _ _ (@le_of_lt _ r _ _ hab) 
  . rw [Set.eq_empty_iff_forall_not_mem]
    intro hinv 
    ext a b 
    cases LinearPreorder_trichotomy hlinr a b with  
    | inl hab =>  simp only [@le_of_lt _ r _ _ hab, true_iff] 
                  have hinvab := hinv (a,b)
                  rw [Inversions_def] at hinvab 
                  push_neg at hinvab 
                  have hr'ab := hinvab hab 
                  rw [←(TotalPreorder_lt_iff_not_le hlinr'.toIsTotal.total), not_not] at hr'ab 
                  exact hr'ab 
    | inr hmed => cases hmed with 
                  | inl hba => simp only [@not_le_of_lt _ r _ _ hba, false_iff]
                               rw [TotalPreorder_lt_iff_not_le hlinr'.toIsTotal.total]
                               have hr'ba := hinv (b,a)
                               rw [Inversions_def] at hr'ba 
                               push_neg at hr'ba
                               have h := LinearPreorder_trichotomy hlinr' a b
                               rw [or_iff_right (hr'ba hba)] at h 
                               rw [or_iff_left (Ne.symm (@ne_of_lt _ r _ _ hba))] at h 
                               exact h
                  | inr heq => rw [heq]; simp only [r.le_refl b, le_refl]

/- Inversions vs LinearOrder_of_total_preorder_and_linear_order.-/

lemma Inversions_of_associated_linear_order (r : LinearOrder α) {s : Preorder α} (htot : Total s.le) :
Inversions r.lt s.lt = Inversions r.lt (LinearOrder_of_total_preorder_and_linear_order r s).lt := by 
ext ⟨a,b⟩
rw [Inversions_def, Inversions_def]
constructor
. intro ⟨hrab, hsba⟩
  rw [and_iff_right hrab]
  rw [←(@TotalPreorder_lt_iff_not_le _ (LinearOrder_of_total_preorder_and_linear_order r s) (LinearOrder_of_total_preorder_and_linear_order_is_total r htot))]
  by_contra hab
  rw [←(TotalPreorder_lt_iff_not_le htot)] at hsba 
  exact hsba (LinearOrder_of_total_preorder_and_linear_order_is_smaller r s hab)
. intro ⟨hrab, hba⟩ 
  rw [and_iff_right hrab]
  cases TotalPreorder_trichotomy htot a b with 
  | inl hsab => have hab : (LinearOrder_of_total_preorder_and_linear_order r s).le a b := Or.inl hsab 
                exfalso 
                exact @not_lt_of_le _ (LinearOrder_of_total_preorder_and_linear_order r s) _ _  hab hba
  | inr hmed => cases hmed with 
                | inr heq => have hab : (LinearOrder_of_total_preorder_and_linear_order r s).le a b := Or.inr ⟨heq, 
                                           @le_of_lt _ r.toPartialOrder.toPreorder _ _ hrab⟩ 
                             exfalso 
                             exact @not_lt_of_le _ (LinearOrder_of_total_preorder_and_linear_order r s) _ _  hab hba 
                | inl hsba => exact hsba 


/- Inversions vs the DescentPartition map. -/

lemma Inversions_of_descent_partition (r : LinearOrder α) {s : Preorder α} (htot : Total s.le) :
Inversions r.lt s.lt = Inversions r.lt (DescentPartition r htot).lt := by 
ext ⟨a,b⟩
rw [Inversions_def, Inversions_def]
constructor
. intro ⟨hrab, hsba⟩ 
  rw [and_iff_right hrab]
  rw [←(@TotalPreorder_lt_iff_not_le _ (DescentPartition r htot) (DescentPartition_is_total r htot))]
  change ¬(s.le a b ∨ (s.le b a ∧ ∀ (c d : α), s.le b c → s.le c d → s.le d a → (r.le b c ∧ r.le c d ∧ r.le d a)))
  rw [not_or, not_and]
  rw [TotalPreorder_lt_iff_not_le htot]
  rw [and_iff_right hsba]
  intro hsba' 
  by_contra habs
  exact @not_lt_of_le _ r.toPartialOrder.toPreorder _ _ (habs b b (s.le_refl b) (s.le_refl b) hsba').2.2 hrab    
. intro ⟨hrab, hba⟩ 
  rw [and_iff_right hrab]
  rw [←(@TotalPreorder_lt_iff_not_le _ (DescentPartition r htot) (DescentPartition_is_total r htot))] at hba 
  change ¬(s.le a b ∨ (s.le b a ∧ ∀ (c d : α), s.le b c → s.le c d → s.le d a → (r.le b c ∧ r.le c d ∧ r.le d a))) at hba
  rw [not_or] at hba
  rw [←(TotalPreorder_lt_iff_not_le htot)]
  exact hba.1 
  



--def WeakBruhatOrder


end WeakBruhatOrder 