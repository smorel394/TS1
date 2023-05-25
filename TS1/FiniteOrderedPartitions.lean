import TS1.ordered_partitions 

set_option autoImplicit false

open Preorder 
open Classical 

universe u

variable {α : Type u} 


/- We introduce "almost finite linearly ordered partitions" (AFLO partitions). These are linearly ordered partitions, i.e. total preorders, that have
finitely many blocks and all of whose blocks are finite, except for maybe the last one. Another way to say this is that all initial intervals are
finite or equal to α and that any two "big enough" elements are equivalent : this condition is clearly necessary, we prove below that it is sufficient.-/

/-Old definition.

def AFLOPartitions (α : Type u) : Set (Preorder α) := {s | Total s.le ∧ (∀ (a : α), @Set.Iic α s a ≠ ⊤ → (@Set.Iic α s a).Finite) ∧
∃ (M : α), (@Set.Iic α s M).Finite ∧ ∀ (a b : α), s.lt M a → s.lt M b → s.le a b}

instance AFLOPartitions.PartialOrder : PartialOrder (LinearOrderedPartitions α) :=
Subtype.partialOrder _ 


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


lemma AFLO_has_finite_blocks (p : AFLOPartitions α) {x : Antisymmetrization α p.1.le} 
(hnonmax : ∃ (y : Antisymmetrization α p.1.le), x < y) : Finite {a : α | toAntisymmetrization p.1.le a = x} := by 
  letI : Preorder α := p.1 
  match p.2.2.2 with 
  | ⟨M, ⟨hMf, hM⟩⟩ => rw [←Set.finite_coe_iff] at hMf 
                      match hnonmax with 
                      | ⟨y, hxy⟩ => have hxM : ofAntisymmetrization p.1.le x ≤ M := by 
                                      by_contra habs
                                      rw [TotalPreorder_lt_iff_not_le p.2.1] at habs 
                                      rw [←(toAntisymmetrization_ofAntisymmetrization p.1.le x), ←(toAntisymmetrization_ofAntisymmetrization p.1.le y)] at hxy
                                      rw [toAntisymmetrization_lt_toAntisymmetrization_iff] at hxy
                                      have hyx := hM _ _ (lt_trans habs hxy) habs
                                      rw [←(TotalPreorder_lt_iff_not_le p.2.1)] at hxy
                                      exact hxy hyx   
                                    haveI := hMf 
                                    apply Finite.Set.subset (Set.Iic M)
                                    intro a hax 
                                    simp only [Set.mem_setOf_eq] at hax
                                    rw [←(toAntisymmetrization_ofAntisymmetrization p.1.le x)] at hax
                                    have hax' := le_of_eq hax 
                                    rw [toAntisymmetrization_le_toAntisymmetrization_iff] at hax'
                                    exact le_trans hax' hxM  

-/

def AFLOPartitions (α : Type u) : Set (Preorder α) := {s | Total s.le ∧ (∀ (a : α), @Set.Iic α s a ≠ ⊤ → (@Set.Iic α s a).Finite) ∧
Finite (Antisymmetrization α s.le)}

instance AFLOPartitions.PartialOrder : PartialOrder (LinearOrderedPartitions α) :=
Subtype.partialOrder _ 




lemma AFLO_has_finite_blocks (p : AFLOPartitions α) {x : Antisymmetrization α p.1.le} 
(hnonmax : ∃ (y : Antisymmetrization α p.1.le), x < y) : Finite {a : α | toAntisymmetrization p.1.le a = x} := by 
  letI : Preorder α := p.1 
  match hnonmax with 
  | ⟨y, hxy⟩ => rw [←(toAntisymmetrization_ofAntisymmetrization p.1.le x), ←(toAntisymmetrization_ofAntisymmetrization p.1.le y)] at hxy
                rw [toAntisymmetrization_lt_toAntisymmetrization_iff] at hxy 
                have hax : {a : α | toAntisymmetrization p.1.le a =x} ⊆ Set.Iic (ofAntisymmetrization p.1.le x) := by 
                  intro a ha 
                  simp only [Set.mem_setOf_eq] at ha
                  rw [←(toAntisymmetrization_ofAntisymmetrization p.1.le x)] at ha 
                  rw [Set.mem_Iic, ←toAntisymmetrization_le_toAntisymmetrization_iff, ha]
                refine @Finite.Set.subset _ _ _ ?_ hax  
                rw [Set.finite_coe_iff]
                refine p.2.2.1 (ofAntisymmetrization p.1.le x) ?_ 
                rw [Set.top_eq_univ, Set.ne_univ_iff_exists_not_mem]
                exists ofAntisymmetrization p.1.le y 
                exact not_le_of_lt hxy 

/- We deduce from the first result above that ALFO preorders are essentially locally finite.-/

noncomputable def AFLOPartition_is_ELF (p : AFLOPartitions α) : EssentiallyLocallyFinitePreorder p.1 := by 
  haveI := p.2.2.2
  haveI := Fintype.ofFinite 
  apply LocallyFiniteOrder.ofFiniteIcc (fun x y => by rw [←Set.finite_coe_iff]; exact inferInstance)


/- We define what will be the corresponding sets of ideals. Because these will be the faces of a simplicial complex, we make them Finsets of ideals
already.-/

def AFLOPowerset (α : Type u): Set (Finset (Set α)) := {E | Total (fun (X : E) => fun (Y : E) => X.1 ⊆ Y.1) ∧ ∀ (X : Set α), X ∈ E → (X ≠ ⊥ ∧ X ≠ ⊤) ∧ Finite X}


/- An AFLO partition goes to an AFLO set of ideals.-/

lemma AFLO_preorderToPowerset_finite (p : AFLOPartitions α) : Finite (preorderToPowerset p.1) := by 
  haveI := p.2.2.2 
  apply Finite.of_surjective (Equiv_Antisymmetrization_nonmaximal_to_PreorderToPowerset p.2.1 (AFLOPartition_is_ELF p)).toFun 
     (Equiv_Antisymmetrization_nonmaximal_to_PreorderToPowerset p.2.1 (AFLOPartition_is_ELF p)).surjective 


@[reducible] noncomputable def preorderToPowersetFinset (p : AFLOPartitions α) := Set.Finite.toFinset (Set.finite_coe_iff.mp (AFLO_preorderToPowerset_finite p))


lemma AFLO_preorderToPowerset (p : AFLOPartitions α) : preorderToPowersetFinset p ∈ AFLOPowerset α := by
  constructor
  . intro ⟨X, hXE⟩ ⟨Y, hYE⟩
    rw [Set.Finite.mem_toFinset] at hXE hYE  
    exact preorderToPowerset_total_is_total p.2.1 ⟨X, hXE⟩ ⟨Y, hYE⟩ 
  intro X hXE 
  . constructor
    . rw [Set.Finite.mem_toFinset] at hXE
      exact ⟨hXE.1, hXE.2.1⟩
    . rw [Set.Finite.mem_toFinset] at hXE 
      match TotalELFP_LowerSet_is_principal p.2.1 (AFLOPartition_is_ELF p) hXE with 
      | ⟨a, haX⟩ => rw [haX, Set.finite_coe_iff]
                    have hXnt := hXE.2.1 
                    rw [haX] at hXnt 
                    exact p.2.2.1 a hXnt 

/- An AFLO set of ideals goes to an AFLO partition.-/

lemma AFLO_powersetToPreorder (E : AFLOPowerset α) : powersetToPreorder (E.1 : Set (Set α)) ∈ AFLOPartitions α := by 
  have htot : Total (powersetToPreorder (E.1 : Set (Set α))).le := by  
    apply powersetToPreorder_total_is_total 
    intro ⟨X, hXE⟩  ⟨Y, hYE⟩  
    rw [Finset.mem_coe] at hXE hYE 
    exact E.2.1 ⟨X, hXE⟩ ⟨Y,hYE⟩ 
  constructor
  . exact htot
  . constructor 
    . intro a hafin 
      rw [Set.top_eq_univ, Set.ne_univ_iff_exists_not_mem] at hafin
      match hafin with 
      | ⟨b, hab⟩ => rw [@Set.mem_Iic _ (powersetToPreorder (E.1 : Set (Set α))) _ _] at hab  
                    change ¬(∀ (X : Set α), X ∈ (E.1 : Set (Set α)) → a ∈ X → b ∈ X) at hab
                    push_neg at hab 
                    match hab with 
                    | ⟨X, ⟨hXE, haX, _⟩⟩ => rw [←Set.finite_coe_iff]
                                            have haX : @Set.Iic _ (powersetToPreorder (E.1 : Set (Set α))) a ⊆ X := by 
                                              intro c hca 
                                              rw [@Set.mem_Iic _ (powersetToPreorder (E.1 : Set (Set α)))] at hca 
                                              exact hca X hXE haX 
                                            haveI := (E.2.2 X hXE).2   
                                            exact Finite.Set.subset X haX  
    . set s := powersetToPreorder (E.1 : Set (Set α))
      by_cases he : IsEmpty (Antisymmetrization α s.le)
      . exact @Finite.of_fintype _ (@Fintype.ofIsEmpty _ he)
      . rw [not_isEmpty_iff] at he 
        set x := Classical.choice he 
        set A := Finset.biUnion E (fun (X : Set α) => by by_cases hXE : X ∈ E.1 
                                                         . exact Set.Finite.toFinset (Set.finite_coe_iff.mp (E.2.2 X hXE).2)  
                                                         . exact ∅)
        have hAtot : ∀ (X : Set α), X ∈ E.1 → X ⊆ A := by 
          intro X hXE 
          have := Finset.subset_biUnion_of_mem (fun (X : Set α) => by by_cases hXE : X ∈ E.1 
                                                                      . exact Set.Finite.toFinset (Set.finite_coe_iff.mp (E.2.2 X hXE).2)  
                                                                      . exact ∅) hXE 
          simp only [hXE, dite_true] at this 
          rw [Set.Finite.toFinset_subset] at this 
          exact this 
        set f : WithTop A → Antisymmetrization α s.le := 
                        fun z => match z with 
                                 | some a => toAntisymmetrization s.le a.1 
                                 | none => by by_cases htop : ∃ (b : α), b ∉ A  
                                              . exact toAntisymmetrization s.le (Classical.choose htop) 
                                              . exact x 
                                              with hfdef  
        have hsur : Function.Surjective f := by 
          intro y 
          by_cases hyA : ofAntisymmetrization s.le y ∈ A
          . exists some ⟨ofAntisymmetrization s.le y, hyA⟩ 
            rw [hfdef]
            simp only [toAntisymmetrization_ofAntisymmetrization]
          . exists none
            have hAnt : ∃ (b : α), b ∉ A := ⟨ofAntisymmetrization s.le y, hyA⟩ 
            rw [hfdef]
            simp only [hAnt, if_true, dite_true]
            rw [←(toAntisymmetrization_ofAntisymmetrization s.le y)]
            apply Quotient.sound
            constructor
            . intro X hXE hyX 
              exfalso
              exact hyA (hAtot X hXE hyX)  
            . intro X hXE hX 
              exfalso 
              exact Classical.choose_spec hAnt (hAtot X hXE hX)  
        have hfin : Finite (WithTop A) :=  by
          change Finite (Option A)
          have hAfin := Finset.finite_toSet A 
          rw [←Set.finite_coe_iff] at hAfin 
          haveI := hAfin 
          haveI := Fintype.ofFinite A 
          exact Finite.of_fintype _  
        exact Finite.of_surjective f hsur 


/- The descent partitions sends an AFLO partition to an AFLO partition.-/

/- Let's assume α finite for now.-/
variable [Fintype α]









