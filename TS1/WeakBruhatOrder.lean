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


/- Inversions vs the AscentPartition map. -/

/-Depreceated.
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
 -/ 

lemma Inversions_of_AscentPartition (r : LinearOrder α) {s : Preorder α} (htot : Total s.le) :
Inversions r.lt s.lt = Inversions r.lt (AscentPartition r htot).lt := by 
ext ⟨a,b⟩
rw [Inversions_def, Inversions_def]
constructor
. intro ⟨hrab, hsba⟩ 
  rw [and_iff_right hrab]
  rw [←(@TotalPreorder_lt_iff_not_le _ (AscentPartition r htot) (AscentPartition_is_total r htot))]
  change ¬(s.le a b ∨ _)
  rw [not_or, not_and]
  rw [TotalPreorder_lt_iff_not_le htot]
  rw [and_iff_right hsba]
  intro hsba' 
  by_contra habs 
  refine @lt_irrefl _ r.toPartialOrder.toPreorder _ (@lt_trans _ r.toPartialOrder.toPreorder _ _ _ (habs ?_ ?_ hsba) hrab)   
  all_goals rw [Set.mem_Icc]
  . exact ⟨s.le_refl _, hsba'⟩
  . exact ⟨hsba', s.le_refl _⟩
. intro ⟨hrab, hba⟩ 
  rw [and_iff_right hrab]
  rw [←(@TotalPreorder_lt_iff_not_le _ (AscentPartition r htot) (AscentPartition_is_total r htot))] at hba 
  change ¬(s.le a b ∨ _) at hba
  rw [not_or] at hba
  rw [←(TotalPreorder_lt_iff_not_le htot)]
  exact hba.1 

/- The inversions between r and its dual are all the couples (a,b) such rthat r.lt a b. -/

lemma Inversions_dual_order (r : LinearOrder α) (a b : α) :
(a,b) ∈ Inversions r.lt (dual r).lt ↔ r.lt a b := by 
  constructor 
  . exact fun h => h.1 
  . exact fun h => ⟨h, h⟩


/- Two linear orders with the same inversions (with respect to a fixed r) are equal.-/

lemma Inversions_determine_linear_order_aux (r : LinearOrder α) {s₁ s₂ : Preorder α} (hlins₁ : IsLinearOrder α s₁.le) (hlins₂ : IsLinearOrder α s₂.le)
(heq : Inversions r.lt s₁.lt = Inversions r.lt s₂.lt) : s₁ ≤ s₂ := by 
  intro a b h1ab 
  cases lt_trichotomy a b with 
  | inl hrab => have hinv : (a,b) ∉ Inversions r.lt s₁.lt := by 
                  by_contra habs 
                  change _ ∧ _ at habs 
                  rw [and_iff_right hrab] at habs 
                  exact @not_le_of_lt _ s₁ _ _ habs h1ab
                rw [heq] at hinv 
                change ¬(_ ∧ _) at hinv
                rw [not_and_or] at hinv
                rw [or_iff_right (not_not_intro hrab)] at hinv
                rw [←(TotalPreorder_lt_iff_not_le hlins₂.toIsTotal.total), not_not] at hinv
                exact hinv      
  | inr hmed => cases hmed with 
                | inl heq => rw [heq]
                | inr hrba => have h1ab' : s₁.lt a b := by 
                                by_contra habs 
                                rw [←(TotalPreorder_lt_iff_not_le hlins₁.toIsTotal.total), not_not] at habs
                                have heq := hlins₁.toIsPartialOrder.toIsAntisymm.antisymm _ _ h1ab habs 
                                rw [heq] at hrba 
                                exact @lt_irrefl _ r.toPartialOrder.toPreorder b hrba 
                              have hinv : (b,a) ∈ Inversions r.lt s₁.lt := ⟨hrba, h1ab'⟩
                              rw [heq] at hinv 
                              exact le_of_lt hinv.2  

lemma Inversions_determine_linear_order (r : LinearOrder α) {s₁ s₂ : Preorder α} (hlins₁ : IsLinearOrder α s₁.le) (hlins₂ : IsLinearOrder α s₂.le)
(heq : Inversions r.lt s₁.lt = Inversions r.lt s₂.lt) : s₁ = s₂ := 
le_antisymm (Inversions_determine_linear_order_aux r hlins₁ hlins₂ heq) (Inversions_determine_linear_order_aux r hlins₂ hlins₁ (Eq.symm heq))


/- Definition of the weak Bruhat order (with basis r): it is the partial order on the set of linear orders on α given by s ≤ s' if and only 
Inversions r s ⊆ Inversions r s'.-/

def WeakBruhatOrder (r : LinearOrder α): PartialOrder {s : Preorder α | IsLinearOrder α s.le} :=
PartialOrder.lift (fun s => Inversions r.lt s.1.lt) (fun s₁ s₂ heq => by have h:= Inversions_determine_linear_order r s₁.2 s₂.2 heq
                                                                         rw [SetCoe.ext_iff] at h; exact h)



lemma WeakBruhatOrder_iff (r : LinearOrder α) {s₁ s₂ : Preorder α} (hlins₁ : IsLinearOrder α s₁.le) (hlins₂ : IsLinearOrder α s₂.le) :
(WeakBruhatOrder r).le ⟨s₁, hlins₁⟩ ⟨s₂, hlins₂⟩ ↔ Inversions s₁.lt s₂.lt = Inversions r.lt s₂.lt \ Inversions r.lt s₁.lt := by
  change Inversions r.lt s₁.lt ⊆ Inversions r.lt s₂.lt ↔ _ 
  constructor 
  . intro hsub 
    ext ⟨a,b⟩
    simp only [Set.mem_diff]
    unfold Inversions at hsub |- 
    simp only [Set.mem_setOf_eq, not_and]
    simp only [Set.setOf_subset_setOf, and_imp, Prod.forall] at hsub
    constructor 
    . intro hinv12 
      constructor 
      . rw [and_iff_left hinv12.2]
        cases lt_trichotomy a b with 
        | inl hrab => exact hrab 
        | inr hmed => cases hmed with 
                      | inl heq => exfalso
                                   rw [heq] at hinv12 
                                   exact @lt_irrefl _ s₂ b hinv12.2 
                      | inr hrba => exfalso 
                                    exact @lt_irrefl _ s₂ _ (@lt_trans _ s₂ _ _ _ (hsub b a hrba hinv12.1).2 hinv12.2)   
      . intro _ 
        by_contra h1ba 
        exact @lt_irrefl _ s₁ _ (@lt_trans _ s₁ _ _ _ hinv12.1 h1ba) 
    . intro h 
      rw [and_iff_left h.1.2]
      cases LinearPreorder_trichotomy hlins₁ a b with 
      | inl h1ab => exact h1ab 
      | inr hmed => cases hmed with 
                    | inr heq => exfalso 
                                 rw [heq] at h 
                                 exact @lt_irrefl _ s₂ _ h.1.2  
                    | inl h1ba => exfalso; exact h.2 h.1.1 h1ba 
  . intro hinv 
    unfold Inversions
    simp only [Set.setOf_subset_setOf, and_imp, Prod.forall]
    intro a b hrab h1ba 
    rw [and_iff_right hrab]
    cases LinearPreorder_trichotomy hlins₂ a b with 
    | inl h2ab => exfalso 
                  have hinvba : (b,a) ∈ Inversions s₁.lt s₂.lt := ⟨h1ba, h2ab⟩ 
                  rw [hinv] at hinvba 
                  unfold Inversions at hinvba 
                  simp only [Set.mem_diff, Set.mem_setOf_eq, not_and] at hinvba
                  exact @lt_irrefl _ r.toPartialOrder.toPreorder _ (@lt_trans _ r.toPartialOrder.toPreorder _ _ _ hrab hinvba.1.1) 
    | inr hmed => cases hmed with 
                  | inl h2ba => exact h2ba 
                  | inr heq => exfalso
                               rw [heq] at h1ba 
                               exact @lt_irrefl _ s₁ _ h1ba 





end WeakBruhatOrder 