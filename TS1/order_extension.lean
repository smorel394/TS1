import Mathlib.Tactic
import Mathlib.Init.Algebra.Order
import Mathlib.Order.Antisymmetrization
import Mathlib.Order.Zorn
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Extension.Linear
import Mathlib.Data.Sum.Order







open Classical 

variable {α : Type _}

/- The order extension principle is in mathlib ! 
See: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Extension/Linear.html -/

/- In this file we prove a version of the extension principle where we extend the partial order while preserving a lower set.-/

namespace Preorder 


lemma extension_principle_with_lowerset (s : PartialOrder α) {I : Set α} (hI : @IsLowerSet α {le := s.le} I) :
∃ (t : LinearOrder α), (∀ (a b : α), s.le a b → t.le a b) ∧ @IsLowerSet α {le := t.le} I := by
  set t₁ := @instLinearOrderLinearExtension I (@PartialOrder.lift I α s (fun (a : I) => ↑a) Subtype.coe_injective)
  set t₂ := @instLinearOrderLinearExtension I.compl (@PartialOrder.lift I.compl α s (fun (a : I.compl) => ↑a) Subtype.coe_injective)
  set t':= @Sum.Lex.linearOrder (LinearExtension ↑I) (LinearExtension ↑I.compl) t₁ t₂ 
  set f : α → Lex ((LinearExtension ↑I) ⊕ (LinearExtension ↑I.compl)) := 
      fun a => by by_cases ha : a ∈ I
                  . exact toLex (Sum.inl (toLinearExtension.toFun ⟨a,ha⟩))  
                  . exact toLex (Sum.inr (toLinearExtension.toFun ⟨a,ha⟩))
      with hfdef
  have hinj : Function.Injective f := fun a b hab => by rw [hfdef] at hab 
                                                        by_cases ha : a ∈ I
                                                        . simp only [ha, dite_true] at hab 
                                                          by_cases hb : b ∈ I
                                                          . simp only [hb, dite_true, 
                                                            EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq] at hab
                                                            apply_fun (fun s => s.val) at hab
                                                            simp only at hab 
                                                            exact hab                                                        
                                                          . simp only [hb, dite_false, EmbeddingLike.apply_eq_iff_eq] at hab
                                                        . simp only [ha, dite_false] at hab
                                                          by_cases hb : b ∈ I
                                                          . simp only [hb, dite_true, EmbeddingLike.apply_eq_iff_eq] at hab
                                                          . simp only [hb, dite_false, EmbeddingLike.apply_eq_iff_eq, 
                                                            Sum.inr.injEq] at hab
                                                            apply_fun (fun s => s.val) at hab
                                                            simp only at hab
                                                            exact hab
  set t:= @LinearOrder.lift' _ _  t' f hinj
  exists t
  constructor
  . intro a b hab
    change t'.le (f a) (f b)
    rw [hfdef]
    by_cases ha : a ∈ I
    . simp only [ha, dite_true]
      by_cases hb : b ∈ I
      . simp only [hb, dite_true, Sum.Lex.toLex_le_toLex, Sum.lex_inl_inl]
        exact toLinearExtension.map_rel' hab  
      . simp only [hb, dite_false, Sum.Lex.toLex_le_toLex, Sum.Lex.sep]
    . simp only [ha, dite_false]
      by_cases hb : b ∈ I
      . simp only [hb, dite_true, Sum.Lex.toLex_le_toLex, Sum.lex_inr_inl]
        exact ha (hI hab hb)
      . simp only [hb, dite_false, Sum.Lex.toLex_le_toLex, Sum.lex_inr_inr]
        exact toLinearExtension.map_rel' hab
  . intro b a hab hb
    change t'.le (f a) (f b) at hab
    by_contra ha
    simp only [ha, dite_false, hb, dite_true, Sum.Lex.toLex_le_toLex, Sum.lex_inr_inl] at hab



                                                                                     


end Preorder



