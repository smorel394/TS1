import TS1.ordered_partitions 

set_option autoImplicit false

universe u

variable (α : Type u) 

/- We introduce "almost finite linearly ordered partitions" (AFLO partitions). These are linearly ordered partitions, i.e. total preorders, that have
finitely many blocks and all of whose blocks are finite, except for maybe the last one. Another way to say this is that all initial intervals are
finite or equal to α and that any two "big enough" elements are equivalent : this condition is clearly necessary, we prove below that it is sufficient.-/


def AFLOPartitions : Set (Preorder α) := {s | Total s.le ∧ (∀ (a : α), @Set.Iic α s a ≠ ⊤ → (@Set.Iic α s a).Finite) ∧
∃ (M : α), (@Set.Iic α s M).Finite ∧ ∀ (a b : α), s.lt M a → s.lt M b → s.le a b}

lemma AFLO_has_finite_antisymmetrization (p : AFLOPartitions α) : Finite (Antisymmetrization α p.1.le) := by 
  letI : Preorder α := p.1 
  match p.2.2.2 with 
  | ⟨M, ⟨hMf, hM⟩⟩ => set R := WithTop (Set.Iic M) 
                      have hRfin : Finite R :=  by
                        change (Finite (Option (Set.Iic M)))
                        rw [←Set.finite_coe_iff] at hMf
                        haveI := hMf 
                        haveI := Fintype.ofFinite (Set.Iic M)
                        exact Finite.of_fintype _  
                      set f : R → Antisymmetrization α p.1.le := 
                        fun x => match x with 
                                 | some a => toAntisymmetrization p.1.le a.1 
                                 | none => by by_cases htop : ∃ (a : α), p.1.lt M a 
                                              . exact toAntisymmetrization p.1.le (Classical.choose htop) 
                                              . exact toAntisymmetrization p.1.le M
                                              with hfdef  
                      have hsur : Function.Surjective f := by
                        intro x 
                        by_cases hxM : x ≤ toAntisymmetrization p.1.le M 
                        . set a := ofAntisymmetrization p.1.le x 
                          have haM :  a ≤ M := by rw[←(toAntisymmetrization_ofAntisymmetrization p.1.le x)] at hxM
                                                  rw [toAntisymmetrization_le_toAntisymmetrization_iff] at hxM
                                                  exact hxM
                          exists some ⟨a, haM⟩
                          rw [hfdef]
                          simp only [toAntisymmetrization_ofAntisymmetrization]
                        . rw [←(toAntisymmetrization_ofAntisymmetrization p.1.le x)] at hxM
                          rw [toAntisymmetrization_le_toAntisymmetrization_iff] at hxM
                          rw [TotalPreorder_lt_iff_not_le p.2.1] at hxM 
                          exists none 
                          rw [hfdef]
                          have hE : ∃ (a : α), M < a := ⟨ofAntisymmetrization p.1.le x, hxM⟩
                          simp only [hE, dite_true]
                          rw [←(toAntisymmetrization_ofAntisymmetrization p.1.le x)]
                          apply Quotient.sound
                          change AntisymmRel p.1.le _ _ 
                          have hxa := hM (ofAntisymmetrization p.1.le x) (Classical.choose hE) hxM (Classical.choose_spec hE)
                          have hax := hM (Classical.choose hE) (ofAntisymmetrization p.1.le x) (Classical.choose_spec hE) hxM 
                          exact ⟨hax, hxa⟩
                      exact  Finite.of_surjective f hsur 


/- Let's assume α finite for now.-/
variable [Fintype α]









