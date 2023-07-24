import Mathlib.Tactic 
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.CategoryTheory.ConcreteCategory.Bundled
import Mathlib.CategoryTheory.ConcreteCategory.BundledHom
import Mathlib.CategoryTheory.FintypeCat


universe u 

open Classical 

lemma stupid (S : Type u) (hSfin : Fintype S) :
↑(@FintypeCat.of S hSfin) = S := by 
  tauto 



