import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum

--open Classical 

universe u 

variable (α : Type u) [DecidableEq (Finset α)]


lemma alternating_sum_powerset_aux (s : Finset α) (j : ℕ) :
(Finset.powersetLen j s).sum (fun (t : Finset α) => (-1 : ℤ) ^ t.card) = (-1 : ℤ)^j *
(s.card.choose j) := by 
  rw [@Finset.sum_congr _ _ (Finset.powersetLen j s) (Finset.powersetLen j s) (fun t => (-1 : ℤ)^(t.card))
    (fun _ => (-1 :ℤ)^j) _ rfl ?_]
  . rw [Finset.sum_const, Finset.card_powersetLen]
    simp only [nsmul_eq_mul, mul_comm]
  . intro x hx 
    rw [Finset.mem_powersetLen] at hx 
    simp [hx.2]


lemma alternating_sum_powerset (s : Finset α) :
Finset.sum (Finset.powerset s) (fun (t : Finset α) => (-1 : ℤ)^(t.card)) =
ite (s = ∅) 1 0 := by 
  rw [Finset.sum_powerset]
  rw [@Finset.sum_congr _ _ (Finset.range (s.card + 1)) (Finset.range (s.card + 1))
    (fun (n : ℕ) => (Finset.powersetLen n s).sum (fun t => (-1 : ℤ)^(t.card))) 
    (fun (n : ℕ) => (-1)^n * (s.card.choose n)) _ rfl ?_]
  . simp_rw [←Finset.card_eq_zero]
    exact @Int.alternating_sum_range_choose s.card 
  . exact fun n _ => alternating_sum_powerset_aux α s n 




lemma AlternatingSumPowerset {s : Finset α} (hsne : s.Nonempty) :
Finset.sum (Finset.powerset s) (fun (t : Finset α) => (-1 : ℤ)^(t.card)) = 0 := by
  have h := Finset.sum_pow_mul_eq_add_pow (-1 : ℤ) (1 : ℤ) s 
  rw [←Finset.card_pos] at hsne 
  simp only [zero_pow hsne, one_pow, mul_one, add_left_neg] at h 
  exact h 
