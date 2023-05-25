import TS1.general_preorder_stuff

universe u 

variable {α : Type u}

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
    by_cases hrab : r.lt a b 
    . simp only [@le_of_lt _ r _ _ hrab, true_iff]
      have hinvab := hinv (a,b)
      rw [Inversions_def] at hinvab 
      push_neg at hinvab 
      have hr'ab := hinvab hrab 
      rw [←(TotalPreorder_lt_iff_not_le hlinr'.toIsTotal.total), not_not] at hr'ab
      exact hr'ab 
    . sorry 



--def WeakBruhatOrder


end WeakBruhatOrder 