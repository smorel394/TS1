import TS1.ordered_partitions
import Mathlib.Order.Cover



set_option autoImplicit false

universe u 

variable {α : Type u}

open LinearOrderedPartitions

open Classical

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




/- Smallest and biggest elements for the weak Bruhat order (i.e. the fixed linear order r and its dual).-/

lemma WeakBruhatOrder_smallest (r : LinearOrder α) {s : Preorder α} (hlins : IsLinearOrder α s.le) :
(WeakBruhatOrder r).le ⟨r.toPartialOrder.toPreorder, @instIsLinearOrderLeToLEToPreorderToPartialOrder _ r⟩ ⟨s, hlins⟩ := by 
  intro ⟨a,b⟩ hab 
  exfalso 
  rw [Inversions_def] at hab 
  exact @lt_irrefl _ r.toPartialOrder.toPreorder _ (@lt_trans _ r.toPartialOrder.toPreorder _ _ _ hab.1 hab.2)


lemma WeakBruhatOrder_greatest (r : LinearOrder α) {s : Preorder α} (hlins : IsLinearOrder α s.le) :
(WeakBruhatOrder r).le  ⟨s, hlins⟩ ⟨(dual r).toPartialOrder.toPreorder, @instIsLinearOrderLeToLEToPreorderToPartialOrder _ (dual r)⟩ := by 
  intro ⟨a,b⟩ hab 
  rw [Inversions_dual_order]
  rw [Inversions_def] at hab 
  exact hab.1 


/- If s and t are linear orders such that s ≤ t for the weak Bruhat order and Inversions s t is finite, then we can find a chain of linear orders
s₀ = s ≤ s₁ ≤ ... ≤ sₙ = t  such that each order covers the preceding one (for the weak Bruhat order). Here we will construct s₁ and show that
s₁ covers s₀ and that Inversions s₁ t is strictly contained in Inversions s t.-/

/-The first step is to show that there exists an element (a,b) of Inversions s t such that b covers a. Then s₁ will be the composition of s and of the
transposition (a,b).-/

lemma Finite_inversions_exists_elementary_inversion_rec (n : ℕ) {s t : Preorder α} (hlins : IsLinearOrder α s.le) (hlint : IsLinearOrder α t.le) :
∀ (A : Finset α), (Finset.card A ≤ n) → (∀ (a b c : α), a ∈ A → b ∈ A → s.le a c → s.le c b → c ∈ A) → 
(∃ (a b : α), a ∈ A ∧ b ∈ A ∧ (a,b) ∈ Inversions s.lt t.lt) → ∃ (a b : α), a ∈ A ∧ b ∈ A ∧ (a,b) ∈ Inversions s.lt t.lt ∧ 
@Covby _ s.toLT a b := by 
  induction' n with d hd 
  . intro A hcard _ hinv 
    exfalso 
    match hinv with 
    | ⟨a, _, ⟨ha,_,_⟩⟩ => rw [Nat.le_zero, Finset.card_eq_zero] at hcard  
                          rw [hcard] at ha 
                          exact Finset.not_mem_empty a ha                          
  . intro A hcard hA hinv 
    match hinv with 
    | ⟨a, b, ⟨haA, hbA, hab⟩⟩ => 
        by_cases hcov : @Covby _ s.toLT a b 
        . exists a; exists b 
        . change ¬(_ ∧ _) at hcov 
          rw [Inversions_def] at hab 
          rw [not_and_or, or_iff_right (Decidable.not_not.mpr hab.1)] at hcov 
          push_neg at hcov 
          cases hcov with 
          | intro c hsc => cases LinearPreorder_trichotomy hlint c a with 
                           | inl htca => set B := ↑A ∩ @Set.Icc _ s a c with hBdef 
                                         have hfin : B.Finite := 
                                           Set.Finite.subset (Finset.finite_toSet A) (Set.inter_subset_left _ _)
                                         have hBcard : Finset.card (Set.Finite.toFinset hfin) ≤ d := by 
                                           rw [←Nat.lt_succ]
                                           refine lt_of_lt_of_le ?_ hcard 
                                           apply Finset.card_lt_card 
                                           rw [Set.Finite.toFinset_ssubset]
                                           rw [Set.ssubset_iff_of_subset (Set.inter_subset_left _ _)]
                                           exists b 
                                           rw [Finset.mem_coe, and_iff_right hbA, Set.mem_inter_iff, not_and]
                                           intro _ 
                                           rw [@Set.mem_Icc α s, not_and_or]
                                           apply Or.inr 
                                           rw [TotalPreorder_lt_iff_not_le hlins.toIsTotal.total]
                                           exact hsc.2 
                                         have haB : a ∈ (Set.Finite.toFinset hfin) := by 
                                           rw [Set.Finite.mem_toFinset, Set.mem_inter_iff, Finset.mem_coe, @Set.mem_Icc _ s]
                                           exact ⟨haA, ⟨s.le_refl a, @le_of_lt _ s _ _ hsc.1⟩⟩                                           
                                         have hcB : c ∈ (Set.Finite.toFinset hfin) := by 
                                           rw [Set.Finite.mem_toFinset, Set.mem_inter_iff, Finset.mem_coe, @Set.mem_Icc _ s]
                                           rw [and_iff_left ⟨@le_of_lt _ s _ _ hsc.1, s.le_refl c⟩]
                                           exact hA a b c haA hbA (@le_of_lt _ s _ _ hsc.1) (@le_of_lt _ s _ _ hsc.2)
                                         match hd (Set.Finite.toFinset hfin) hBcard 
                                           (fun d e f hdB heB hdf hfe => by rw [Set.Finite.mem_toFinset, hBdef, Set.mem_inter_iff] at hdB heB |- 
                                                                            constructor 
                                                                            . rw [Finset.mem_coe] at hdB heB |- 
                                                                              exact hA d e f hdB.1 heB.1 hdf hfe 
                                                                            . rw [@Set.mem_Icc _ s] at hdB heB |- 
                                                                              exact ⟨s.le_trans _ _ _ hdB.2.1 hdf, s.le_trans _ _ _ hfe heB.2.2⟩)
                                           (by exists a; exists c
                                               rw [and_iff_right haB, and_iff_right hcB, Inversions_def]
                                               exact ⟨hsc.1, htca⟩
                                           ) with
                                         | ⟨d, e, ⟨hdB, heB, hinvde, hcovde⟩⟩ => rw [Set.Finite.mem_toFinset, Set.mem_inter_iff, Finset.mem_coe] at hdB heB 
                                                                                 exists d; exists e 
                                                                                 exact ⟨hdB.1, heB.1, hinvde, hcovde⟩
                           | inr hmed => cases hmed with 
                                         | inr heq => exfalso
                                                      rw [heq] at hsc
                                                      exact @lt_irrefl _ s _ hsc.1  
                                         | inl htac => have htbc : t.lt b c := by 
                                                         by_contra htcb 
                                                         rw [←(TotalPreorder_lt_iff_not_le hlint.toIsTotal.total), not_not] at htcb
                                                         exact @lt_irrefl _ t a (@lt_trans _ t _ _ _ (@lt_of_lt_of_le _ t _ _ _ htac htcb) hab.2)  
                                                       set B := ↑A ∩ @Set.Icc _ s c b with hBdef 
                                                       have hfin : B.Finite := 
                                                         Set.Finite.subset (Finset.finite_toSet A) (Set.inter_subset_left _ _)
                                                       have hBcard : Finset.card (Set.Finite.toFinset hfin) ≤ d := by 
                                                         rw [←Nat.lt_succ]
                                                         refine lt_of_lt_of_le ?_ hcard 
                                                         apply Finset.card_lt_card 
                                                         rw [Set.Finite.toFinset_ssubset]
                                                         rw [Set.ssubset_iff_of_subset (Set.inter_subset_left _ _)]
                                                         exists a 
                                                         rw [Finset.mem_coe, and_iff_right haA, Set.mem_inter_iff, not_and]
                                                         intro _ 
                                                         rw [@Set.mem_Icc α s, not_and_or] 
                                                         apply Or.inl
                                                         rw [TotalPreorder_lt_iff_not_le hlins.toIsTotal.total]
                                                         exact hsc.1 
                                                       have hbB : b ∈ (Set.Finite.toFinset hfin) := by 
                                                        rw [Set.Finite.mem_toFinset, Set.mem_inter_iff, Finset.mem_coe, @Set.mem_Icc _ s]
                                                        exact ⟨hbA, ⟨@le_of_lt _ s _ _ hsc.2, s.le_refl b⟩⟩                                           
                                                       have hcB : c ∈ (Set.Finite.toFinset hfin) := by 
                                                         rw [Set.Finite.mem_toFinset, Set.mem_inter_iff, Finset.mem_coe, @Set.mem_Icc _ s]
                                                         rw [and_iff_left ⟨s.le_refl c, @le_of_lt _ s _ _ hsc.2⟩]
                                                         exact hA a b c haA hbA (@le_of_lt _ s _ _ hsc.1) (@le_of_lt _ s _ _ hsc.2)
                                                       match hd (Set.Finite.toFinset hfin) hBcard 
                                                        (fun d e f hdB heB hdf hfe => by rw [Set.Finite.mem_toFinset, hBdef, Set.mem_inter_iff] at hdB heB |- 
                                                                                         constructor 
                                                                                         . rw [Finset.mem_coe] at hdB heB |- 
                                                                                           exact hA d e f hdB.1 heB.1 hdf hfe 
                                                                                         . rw [@Set.mem_Icc _ s] at hdB heB |- 
                                                                                           exact ⟨s.le_trans _ _ _ hdB.2.1 hdf, s.le_trans _ _ _ hfe heB.2.2⟩)
                                                        (by exists c; exists b
                                                            rw [and_iff_right hcB, and_iff_right hbB, Inversions_def]
                                                            exact ⟨hsc.2, htbc⟩
                                                        ) with
                                         | ⟨d, e, ⟨hdB, heB, hinvde, hcovde⟩⟩ => rw [Set.Finite.mem_toFinset, Set.mem_inter_iff, Finset.mem_coe] at hdB heB 
                                                                                 exists d; exists e 
                                                                                 exact ⟨hdB.1, heB.1, hinvde, hcovde⟩

lemma Finite_inversions_finite_inversion_interval {s t : Preorder α} (hlins : IsLinearOrder α s.le) (hlint : IsLinearOrder α t.le) 
(hfin : (Inversions s.lt t.lt).Finite) {a b : α} (hinv : (a,b) ∈ Inversions s.lt t.lt) : (@Set.Icc _ s a b).Finite := by 
  rw [←Set.finite_coe_iff] at hfin |- 
  rw [Inversions_def] at hinv 
  set f : @Set.Icc _ s a b → Option (Inversions s.lt t.lt) := by
    intro ⟨c, hc⟩ 
    rw [@Set.mem_Icc _ s] at hc 
    by_cases hsac : s.lt a c
    . by_cases hscb : s.lt c b 
      . by_cases htca : t.lt c a 
        . have hac : (a,c) ∈ Inversions s.lt t.lt := by 
            rw [Inversions_def]
            exact ⟨hsac, htca⟩
          exact some ⟨(a,c), hac⟩
        . by_cases htbc : t.lt b c 
          . have hcb : (c,b) ∈ Inversions s.lt t.lt := by 
              rw [Inversions_def]
              exact ⟨hscb, htbc⟩
            exact some ⟨(c,b), hcb⟩
          . exact none
      . exact none 
    . exact some ⟨(a,b), hinv⟩ 
  apply @Finite.of_injective _ _ (@Fintype.finite _ (@instFintypeOption _ (@Fintype.ofFinite _ hfin))) f  
  intro ⟨c,hc⟩ ⟨d,hd⟩ heq 
  rw [@Set.mem_Icc _ s] at hc hd 
  simp only [Subtype.mk.injEq]
  by_cases hsac : s.lt a c 
  . simp only [hsac, dite_true] at heq
    by_cases hscb : s.lt c b 
    . simp only [hscb, dite_true] at heq
      by_cases htca : t.lt c a 
      . simp only [htca, dite_true] at heq
        by_cases hsad : s.lt a d 
        . simp only [hsad, dite_true] at heq
          by_cases hsdb : s.lt d b 
          . simp only [hsdb, dite_true] at heq
            by_cases htda : t.lt d a 
            . simp only [htda, dite_true, Option.some.injEq, Subtype.mk.injEq, Prod.mk.injEq, true_and] at heq 
              exact heq 
            . simp only [htda, dite_false] at heq
              by_cases htbd : t.lt b d 
              . simp only [htbd, dite_true, Option.some.injEq, Subtype.mk.injEq, Prod.mk.injEq] at heq
                exfalso 
                rw [heq.2] at hscb 
                exact @lt_irrefl _ s _ hscb 
              . simp only [htbd, dite_false] at heq
          . simp only [hsdb, dite_false] at heq 
        . simp only [hsad, dite_false, Option.some.injEq, Subtype.mk.injEq, Prod.mk.injEq, true_and] at heq
          exfalso 
          rw [heq] at hscb 
          exact @lt_irrefl _ s _ hscb 
      . simp only [htca, dite_false] at heq
        by_cases htbc : t.lt b c 
        . simp only [htbc, dite_true] at heq
          by_cases hsad : s.lt a d 
          . simp only [hsad, dite_true] at heq
            by_cases hsdb : s.lt d b
            . simp only [hsdb, dite_true] at heq
              by_cases htda : t.lt d a 
              . simp only [htda, dite_true, Option.some.injEq, Subtype.mk.injEq, Prod.mk.injEq] at heq
                exfalso 
                rw [heq.1] at hsac
                exact @lt_irrefl _ s _ hsac 
              . simp only [htda, dite_false] at heq
                by_cases htbd : t.lt b d 
                . simp only [htbd, dite_true, Option.some.injEq, Subtype.mk.injEq, Prod.mk.injEq, and_true] at heq
                  exact heq 
                . simp only [htbd, dite_false] at heq
            . simp only [hsdb, dite_false] at heq 
          . simp only [hsad, dite_false, Option.some.injEq, Subtype.mk.injEq, Prod.mk.injEq, and_true] at heq
            exfalso
            rw [heq] at hsac 
            exact @lt_irrefl _ s _ hsac 
        . exfalso 
          rw [←(TotalPreorder_lt_iff_not_le hlint.toIsTotal.total), not_not] at htca htbc
          exact @lt_irrefl _ t _ (@lt_of_le_of_lt _ t _ _ _ (t.le_trans _ _ _ htca htbc) hinv.2) 
    . simp only [hscb, dite_false] at heq
      by_cases hsad : s.lt a d
      . simp only [hsad, dite_true] at heq
        by_cases hsdb : s.lt d b 
        . simp only [hsdb, dite_false] at heq  
          by_cases htda : t.lt d a 
          . simp only [htda, dite_false, dite_true] at heq
          . simp only [htda, dite_false, dite_true] at heq
            by_cases htbd : t.lt b d 
            . simp only [htbd, dite_true] at heq
            . simp only [htbd, dite_false] at heq
              exfalso 
              rw [←(TotalPreorder_lt_iff_not_le hlint.toIsTotal.total), not_not] at htda htbd
              exact @lt_irrefl _ t _ (@lt_of_le_of_lt _ t _ _ _ (t.le_trans _ _ _ htda htbd) hinv.2)  
        . simp only [hsdb, dite_false] at heq 
          rw [←(TotalPreorder_lt_iff_not_le hlins.toIsTotal.total), not_not] at hscb 
          rw [←(TotalPreorder_lt_iff_not_le hlins.toIsTotal.total), not_not] at hsdb 
          have heqbc := hlins.toIsPartialOrder.toIsAntisymm.antisymm _ _ hscb hc.2
          have heqbd := hlins.toIsPartialOrder.toIsAntisymm.antisymm _ _ hsdb hd.2
          rw [←heqbc, ←heqbd]  
      . simp only [hsad, dite_false] at heq 
  . simp only [hsac, dite_false] at heq
    by_cases hsad : s.lt a d 
    . simp only [hsad, dite_true] at heq
      by_cases hsdb : s.lt d b 
      . simp only [hsdb, dite_true] at heq 
        by_cases htda : t.lt d a 
        . simp only [htda, dite_true, Option.some.injEq, Subtype.mk.injEq, Prod.mk.injEq, true_and] at heq
          exfalso 
          rw [heq] at hsdb 
          exact @lt_irrefl _ s _ hsdb 
        . simp only [htda, dite_false] at heq
          by_cases htbd : t.lt b d 
          . simp only [htbd, dite_true, Option.some.injEq, Subtype.mk.injEq, Prod.mk.injEq, and_true] at heq
            exfalso 
            rw [heq] at hsad 
            exact @lt_irrefl _ s _ hsad 
          . simp only [htbd, dite_false] at heq
      . simp only [hsdb, dite_false] at heq 
    . simp only [hsad, dite_false] at heq
      rw [←(TotalPreorder_lt_iff_not_le hlins.toIsTotal.total), not_not] at hsac hsad 
      have heqac := hlins.toIsPartialOrder.toIsAntisymm.antisymm _ _ hc.1 hsac 
      have heqad := hlins.toIsPartialOrder.toIsAntisymm.antisymm _ _ hd.1 hsad 
      rw [←heqac, ←heqad]

lemma Finite_inversions_exists_elementary_inversion {s t : Preorder α} (hlins : IsLinearOrder α s.le) (hlint : IsLinearOrder α t.le) 
(hinvne : (Inversions s.lt t.lt).Nonempty) (hinvfin : (Inversions s.lt t.lt).Finite) :
∃ x : α × α, x ∈ Inversions s.lt t.lt ∧ @Covby _ s.toLT x.1 x.2 := by 
  match hinvne with 
  | ⟨⟨a, b⟩, hab⟩ => set A := @Set.Icc _ s a b 
                     have haA : a ∈ A := by 
                       rw [@Set.mem_Icc _ s]
                       exact ⟨s.le_refl _, @le_of_lt _ s _ _ hab.1⟩
                     have hbA :  b ∈ A := by
                       rw [@Set.mem_Icc _ s]
                       exact ⟨@le_of_lt _ s _ _ hab.1, s.le_refl _⟩
                     have hAfin : A.Finite := Finite_inversions_finite_inversion_interval hlins hlint hinvfin hab 
                     match Finite_inversions_exists_elementary_inversion_rec (Finset.card (Set.Finite.toFinset hAfin)) hlins hlint 
                       (Set.Finite.toFinset hAfin) (le_refl _) (fun c d e hcA hdA hce hed => by rw [Set.Finite.mem_toFinset] at hcA hdA |- 
                                                                                                rw [@Set.mem_Icc _ s] at hcA hdA |- 
                                                                                                constructor 
                                                                                                . exact s.le_trans _ _ _ hcA.1 hce  
                                                                                                . exact s.le_trans _ _ _ hed hdA.2)
                       (by exists a; exists b; rw [Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]; exact ⟨haA, hbA, hab⟩) with 
                     | ⟨a, b, ⟨_, _, h1, h2⟩⟩ => exists (a,b) 


/- If s < t for the weak Bruhat order (relative to r) and Inversions s t is finite, we get an element of [s, t] covering s by composing s with the
transposition (a,b), where (a,b) is an element of Inversions s t such that b covers a for s. So we need to define the transposition (it might be in
Mathlib already, I didn't find it.)-/

noncomputable def Transposition (a b : α) : α → α := by 
  intro x 
  by_cases x = a 
  . exact b
  . by_cases x = b
    . exact a
    . exact x


lemma Transposition_is_involutive (a b x : α) : Transposition a b (Transposition a b x) = x := by 
  unfold Transposition 
  by_cases ha : x = a
  . simp only [ha, dite_eq_ite, ite_self, ite_true, ite_eq_right_iff, imp_self]
  . by_cases hb : x = b 
    . simp only [hb, eq_self_iff_true, dite_eq_ite, if_true, ite_eq_right_iff, imp_self]
    . simp only [ha, hb, dite_eq_ite, if_false]


lemma Transposition_is_injective (a b  : α) : Function.Injective (Transposition a b) := by 
  intro x y hxy
  apply_fun (Transposition a b) at hxy
  rw [Transposition_is_involutive, Transposition_is_involutive] at hxy 
  exact hxy  

/- Now we have the transposition, we introduce the transposed preorder.-/

noncomputable def TransposedPreorder (s : Preorder α) (a b : α) := @Preorder.lift _ _ s (Transposition a b)

noncomputable def Transposed_of_linear_is_linear {s : Preorder α} (hlin : IsLinearOrder α s.le) (a b  : α) :
IsLinearOrder α (TransposedPreorder s a b).le := by 
  refine {toIsPartialOrder := ?_, toIsTotal := ?_} 
  . refine {toIsPreorder := @instIsPreorderLeToLE α (TransposedPreorder s a b), toIsAntisymm := ?_}
    refine {antisymm := fun x y hxy hyx => Transposition_is_injective _ _ (hlin.toIsPartialOrder.toIsAntisymm.antisymm _ _ hxy hyx)}
  . refine {total := fun x y => hlin.toIsTotal.total _ _}


/- Construction of a covering element of s (for the weak Bruhat order) if we are given a t such that s ≤ t and Inversions s t is finite.-/

noncomputable def CoveringElementBruhatOrder {s t : Preorder α} (hlins : IsLinearOrder α s.le) (hlint : IsLinearOrder α t.le) 
(hinvne : (Inversions s.lt t.lt).Nonempty) (hinvfin : (Inversions s.lt t.lt).Finite) : Preorder α := by
  set x := Classical.choose (Finite_inversions_exists_elementary_inversion hlins hlint hinvne hinvfin)
  exact TransposedPreorder s x.1 x.2 

noncomputable def CoveringElementBruhatOrder_is_linear {s t : Preorder α} (hlins : IsLinearOrder α s.le) (hlint : IsLinearOrder α t.le) 
(hinvne : (Inversions s.lt t.lt).Nonempty) (hinvfin : (Inversions s.lt t.lt).Finite) : 
IsLinearOrder α (CoveringElementBruhatOrder hlins hlint hinvne hinvfin).le := Transposed_of_linear_is_linear hlins _ _ 

/- Properties of the covering element: inversions with respect to s and t.-/

lemma CoveringElementBruhatOrder_Inversions1 {s t : Preorder α} (hlins : IsLinearOrder α s.le) (hlint : IsLinearOrder α t.le) 
(hinvne : (Inversions s.lt t.lt).Nonempty) (hinvfin : (Inversions s.lt t.lt).Finite) :
Inversions s.lt (CoveringElementBruhatOrder hlins hlint hinvne hinvfin).lt = 
{Classical.choose (Finite_inversions_exists_elementary_inversion hlins hlint hinvne hinvfin)} := by 
  set x := Classical.choose (Finite_inversions_exists_elementary_inversion hlins hlint hinvne hinvfin)
  have hx := Classical.choose_spec (Finite_inversions_exists_elementary_inversion hlins hlint hinvne hinvfin)
  ext ⟨a,b⟩
  constructor 
  . intro hinv 
    rw [Inversions_def] at hx hinv 
    rw [Set.mem_singleton_iff, Prod.ext_iff]
    change _ ∧ s.lt (Transposition _ _ _) (Transposition _ _ _) at hinv 
    unfold Transposition at hinv 
    by_cases ha : a = x.1 
    . simp only [ha, dite_eq_ite, ite_self, ite_true] at hinv
      by_cases hb : b = x.2
      . exact ⟨ha, hb⟩
      . simp only [hb, ite_false] at hinv
        have hb' : b ≠ x.1 := by 
          by_contra habs 
          rw [habs] at hinv
          exact @lt_irrefl _ s _ hinv.1
        simp only [hb', ite_false] at hinv
        exfalso
        exact hx.2.2 hinv.1 hinv.2   
    . simp only [dite_eq_ite, ha, ite_false] at hinv
      by_cases hb : b = x.1 
      . simp only [hb, ite_self, ite_true] at hinv
        by_cases ha' : a = x.2 
        . simp only [ha', ite_true, and_self] at hinv
          exfalso 
          exact @lt_irrefl _ s _ (@lt_trans _ s _ _ _ hinv hx.1.1) 
        . simp only [ha', ite_false] at hinv
          exfalso 
          exact @lt_irrefl _ s _ (@lt_trans _ s _ _ _ (@lt_trans _ s _ _ _ hinv.1 hx.1.1) hinv.2)  
      . simp only [hb, ite_false] at hinv
        by_cases hb' : b = x.2 
        . simp only [hb', ite_true] at hinv
          have ha' : a ≠ x.2 := by 
            by_contra habs 
            rw [habs] at hinv 
            exact @lt_irrefl _ s _ hinv.1 
          simp only [ha', ite_false] at hinv
          exfalso 
          exact hx.2.2 hinv.2 hinv.1 
        . simp only [hb', ite_false] at hinv
          by_cases ha' : a = x.2 
          . simp only [ha', ite_true] at hinv
            exfalso 
            exact @lt_irrefl _ s _ (@lt_trans _ s _ _ _ hx.1.1 (@lt_trans _ s _ _ _ hinv.1 hinv.2)) 
          . simp only [ha', ite_false] at hinv
            exfalso 
            exact @lt_irrefl _ s _ (@lt_trans _ s _ _ _ hinv.1 hinv.2)  
  . intro heq 
    rw [Set.mem_singleton_iff, Prod.ext_iff] at heq
    simp only at heq  
    rw [Inversions_def] at hx |-
    rw [heq.1, heq.2, and_iff_right hx.1.1]
    change s.lt (Transposition _ _ _) (Transposition _ _ _)
    unfold Transposition
    simp only [Ne.symm (@ne_of_lt _ s _ _ hx.1.1), dite_eq_ite, ite_true, ite_false, ite_self]
    exact hx.1.1 
    


lemma CoveringElementBruhatOrder_Inversions2 {s t : Preorder α} (hlins : IsLinearOrder α s.le) (hlint : IsLinearOrder α t.le) 
(hinvne : (Inversions s.lt t.lt).Nonempty) (hinvfin : (Inversions s.lt t.lt).Finite) :
Inversions (CoveringElementBruhatOrder hlins hlint hinvne hinvfin).lt t.lt= 
Inversions s.lt t.lt \ {Classical.choose (Finite_inversions_exists_elementary_inversion hlins hlint hinvne hinvfin)} := by 
  set x := Classical.choose (Finite_inversions_exists_elementary_inversion hlins hlint hinvne hinvfin)
  have hx := Classical.choose_spec (Finite_inversions_exists_elementary_inversion hlins hlint hinvne hinvfin)
  ext ⟨a,b⟩
  simp only [Set.mem_diff, Set.mem_singleton_iff]
  rw [Inversions_def, Inversions_def]
  change (s.lt (Transposition _ _ _) (Transposition _ _ _) ∧ _) ↔ _
  unfold Transposition 
  by_cases ha1 : a = x.1 
  . simp only [ha1, dite_eq_ite, ite_self, ite_true]
    by_cases hb1 : b = x.1 
    . simp only [hb1, ite_self, ite_true, lt_self_iff_false, and_false, false_and]
    . simp only [hb1, ite_false]
      by_cases hb2 : b = x.2 
      . simp only [hb2, ite_true, Prod.mk.eta, not_true, and_false, iff_false, not_and]
        intro habs
        exfalso 
        exact @lt_irrefl _ s _ (@lt_trans _ s _ _ _ hx.1.1 habs) 
      . simp only [hb2, ite_false]
        constructor 
        . intro h 
          rw [and_iff_right (@lt_trans _ s _ _ _ hx.1.1 h.1), and_iff_right h.2]
          by_contra habs 
          apply_fun (fun x => x.2) at habs 
          simp only at habs 
          rw [←habs] at h 
          exact @lt_irrefl _ s _ h.1 
        . intro h 
          rw [and_iff_left h.1.2]
          cases LinearPreorder_trichotomy hlins b x.2 with
          | inl hbx =>  exfalso; exact hx.2.2 h.1.1 hbx  
          | inr hmed => cases hmed with 
                        | inl hxb => exact hxb 
                        | inr heq => exfalso 
                                     rw [heq] at h
                                     exact h.2 rfl         
  . simp only [ha1, dite_eq_ite, ite_false]
    by_cases ha2 : a = x.2 
    . simp only [ha2, ite_true]
      by_cases hb1 : b = x.1 
      . simp only [hb1, ite_self, ite_true]
        constructor 
        . intro h 
          exfalso 
          exact @lt_irrefl _ t _ (@lt_trans _ t _ _ _ h.2 hx.1.2) 
        . intro h 
          exfalso 
          exact @lt_irrefl _ s _ (@lt_trans _ s _ _ _ h.1.1 hx.1.1)
      . simp only [hb1, ite_false]
        by_cases hb2 : b = x.2 
        . simp only [hb2, ite_true, lt_self_iff_false, and_false, false_and]
        . simp only [hb2, ite_false]
          constructor 
          . intro h 
            constructor 
            . rw [and_iff_left h.2]
              cases LinearPreorder_trichotomy hlins b x.2 with 
              | inl hbx => exfalso; exact hx.2.2 h.1 hbx               
              | inr hmed => cases hmed with 
                            | inl hxb => exact hxb  
                            | inr heq => exfalso; exact hb2 heq 
            . by_contra habs 
              apply_fun (fun y => y.2) at habs  
              exact hb2 habs 
          . intro h 
            rw [and_iff_left h.1.2]
            exact @lt_trans _ s _ _ _ hx.1.1 h.1.1 
    . simp only [ha2, ite_false]
      by_cases hb1 : b = x.1 
      . simp only [hb1, ite_self, ite_true]
        constructor 
        . intro h 
          constructor 
          . rw [and_iff_left h.2]
            cases LinearPreorder_trichotomy hlins a x.1 with 
            | inl hax => exact hax 
            | inr hmed => cases hmed with 
                          | inl hxa => exfalso; exact hx.2.2 hxa h.1 
                          | inr heq => exfalso; exact ha1 heq 
          . by_contra habs 
            apply_fun (fun y => y.1) at habs 
            exact ha1 habs 
        . intro h 
          rw [and_iff_left h.1.2]
          exact @lt_trans _ s _ _ _ h.1.1 hx.1.1 
      . simp only [hb1, ite_false]
        by_cases hb2 : b = x.2 
        . simp only [hb2, ite_true]
          constructor 
          . intro h 
            constructor 
            . rw [and_iff_left h.2]
              exact @lt_trans _ s _ _ _ h.1 hx.1.1  
            . by_contra habs 
              apply_fun (fun y => y.1) at habs 
              exact ha1 habs 
          . intro h 
            rw [and_iff_left h.1.2]
            cases LinearPreorder_trichotomy hlins a x.1 with 
            | inl hax => exact hax 
            | inr hmed => cases hmed with 
                          | inl hxa => exfalso; exact hx.2.2 hxa h.1.1  
                          | inr heq => exfalso; exact ha1 heq 
        . simp only [hb2, ite_false, iff_self_and, and_imp]
          intro _ _ habs 
          apply_fun (fun y => y.1) at habs 
          exact ha1 habs 


lemma CoveringElementBruhatOrder_Inversions3 {s t : Preorder α} (hlins : IsLinearOrder α s.le) (hlint : IsLinearOrder α t.le) 
(hinvne : (Inversions s.lt t.lt).Nonempty) (hinvfin : (Inversions s.lt t.lt).Finite) :
Inversions (CoveringElementBruhatOrder hlins hlint hinvne hinvfin).lt t.lt ⊂ Inversions s.lt t.lt := by 
  rw [CoveringElementBruhatOrder_Inversions2]
  simp only [Set.diff_singleton_sSubset]
  exact (Classical.choose_spec (Finite_inversions_exists_elementary_inversion hlins hlint hinvne hinvfin)).1 
  

/- More properties of the covering element: if, for a fixed linear order r, we have s ≤ t for teh weak Bruhat order with respect to r
(and if Inversions s t is finite, as before), then the covering element is a covering element of s, and it is ≤ t. -/

lemma CoveringElementBruhatOrder_covering (r : LinearOrder α) {s t : Preorder α} (hlins : IsLinearOrder α s.le) (hlint : IsLinearOrder α t.le) 
(hinvne : (Inversions s.lt t.lt).Nonempty) (hinvfin : (Inversions s.lt t.lt).Finite) (hwB : (WeakBruhatOrder r).le ⟨s, hlins⟩ ⟨t, hlint⟩) :
@Covby _ (WeakBruhatOrder r).toLT ⟨s, hlins⟩ ⟨CoveringElementBruhatOrder hlins hlint hinvne hinvfin, CoveringElementBruhatOrder_is_linear hlins hlint
hinvne hinvfin⟩ := sorry 


lemma CoveringElementBruhatOrder_smaller (r : LinearOrder α) {s t : Preorder α} (hlins : IsLinearOrder α s.le) (hlint : IsLinearOrder α t.le) 
(hinvne : (Inversions s.lt t.lt).Nonempty) (hinvfin : (Inversions s.lt t.lt).Finite) (hwB : (WeakBruhatOrder r).le ⟨s, hlins⟩ ⟨t, hlint⟩) :
(WeakBruhatOrder r).le ⟨CoveringElementBruhatOrder hlins hlint hinvne hinvfin, CoveringElementBruhatOrder_is_linear hlins hlint hinvne hinvfin⟩
⟨t, hlint⟩ := sorry


end WeakBruhatOrder