import Mathlib.Tactic
import Mathlib.Init.Algebra.Order

variable {α : Type _}

example (r : LinearOrder α) (s : Preorder α) (a b : α) : ¬(s.lt a b → r.lt a b) := by 
  push_neg -- now the goal is s.lt a b ∧ s.le b a ! 

/- Error message:
application type mismatch
  id
    (Eq.trans (Mathlib.Tactic.PushNeg.not_implies_eq (a < b) (a < b))
      (congrArg (And (a < b)) (Mathlib.Tactic.PushNeg.not_lt_eq a b)))
argument has type
  (¬(a < b → a < b)) = (a < b ∧ b ≤ a)
but function has type
  (¬(a < b → a < b)) = (a < b ∧ b ≤ a) → (¬(a < b → a < b)) = (a < b ∧ b ≤ a)
-/
  
