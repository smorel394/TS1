import Mathlib.Tactic
import Mathlib.Init.Algebra.Order
import Mathlib.Order.SuccPred.Basic


open Classical 

variable {α : Type _}

def powersetToPreorder (E : Set (Set α)) : Preorder α  where
le :=  fun a b => ∀ ⦃X : Set α⦄, X ∈ E → b ∈ X → a ∈ X 
le_refl := fun _ => fun _ _ h => h
le_trans :=  fun _ _ _ hab hbc => fun X hXE hXc => hab hXE (hbc hXE hXc)


def successeur1 (s : Preorder α) (hsucc : @SuccOrder α s) (a : α) : α := hsucc.succ a 


def successeur2 (E : Set (Set α)) (hsucc : @SuccOrder α (powersetToPreorder E)) (a : α) : α := by
  letI : Preorder α := powersetToPreorder E
  exact hsucc.succ a  

