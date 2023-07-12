import Mathlib.Tactic
import Mathlib.Init.Algebra.Order
import Mathlib.Order.Ideal
import Mathlib.Order.Zorn


universe u 

variable (α : Type u) [Preorder α]

def IsNoetherianPoset : Prop := WellFounded (fun (a b : α) => b < a)




lemma Order.Ideal.generated_by_maximal_element (I : Order.Ideal α) {a : α} (ha : a ∈ I ∧ ∀ (b : α), b ∈ I → a ≤ b → b ≤ a) : 
I = Order.Ideal.principal a := by 
  rw [←Order.Ideal.principal_le_iff] at ha
  refine le_antisymm ?_ ha.1 
  intro b hbI 
  erw [Order.Ideal.mem_principal] 
  cases I.directed a (by rw [Order.Ideal.principal_le_iff] at ha; exact ha.1) b hbI with
  | intro c hc => exact le_trans hc.2.2 (ha.2 c hc.1 hc.2.1)


lemma Noetherian_iff_every_ideal_is_principal_aux (hprin : ∀ (I : Order.Ideal α), ∃ (a : α), I = Order.Ideal.principal a) (s : Set α) 
(c : Set α) (hcs : c ⊆ s) (hchain : IsChain (fun a b => a ≤ b) c) (a : α) (hac : a ∈ c) : 
∃ (m : α), m ∈ s ∧ ∀ (b : α), b ∈ c → b ≤ m := by 
  set J := ⋃ (a : c), ((Order.Ideal.principal a.1).carrier : Set α) with hJdef
  have hJdef : ∀ (a : α), a ∈ c → ((Order.Ideal.principal a).toLowerSet.carrier : Set α) ⊆ J := by 
    intro a hac 
    rw [hJdef]
    refine Set.subset_iUnion (fun (a : c) => ((Order.Ideal.principal a.1).toLowerSet.carrier : Set α)) ⟨a, hac⟩    
  have hJne : J.Nonempty := by exists a
                               refine (hJdef a hac) ?_  
                               erw [Order.Ideal.mem_principal]
  have hJls : IsLowerSet J := by 
    intro b d hdb hbJ 
    rw [Set.mem_iUnion] at hbJ |-
    cases hbJ with 
    | intro e he => exists e; erw [Order.Ideal.mem_principal] at he |-; exact le_trans hdb he  
  have hJdo : DirectedOn (fun b d => b ≤ d) J := by 
    intro b hbJ d hdJ 
    rw [Set.mem_iUnion] at hbJ hdJ 
    cases hbJ with 
    | intro e he => cases hdJ with
                    | intro f hd => cases IsChain.total hchain e.2 f.2 with 
                                    | inl hef => exists f
                                                 have hfJ := hJdef f.1 f.2
                                                 rw [and_iff_right (hfJ (by have hff := le_refl ↑f; rw [←Order.Ideal.mem_principal] at hff; exact hff))]
                                                 erw [Order.Ideal.mem_principal] at hd he
                                                 exact ⟨le_trans he hef, hd⟩
                                    | inr hfe => exists e
                                                 have heJ := hJdef e.1 e.2
                                                 rw [and_iff_right (heJ (by have hee := le_refl ↑e; rw [←Order.Ideal.mem_principal] at hee; exact hee))]
                                                 erw [Order.Ideal.mem_principal] at hd he
                                                 exact ⟨he, le_trans hd hfe⟩
  cases hprin (Order.IsIdeal.toIdeal {IsLowerSet := hJls, Nonempty := hJne, Directed := hJdo}) with
  | intro b hb => apply_fun (fun I => I.carrier) at hb 
                  change J = _ at hb 
                  have hbmax : ∀ (d : α), d ∈ c → d ≤ b := by 
                    intro d hdc 
                    have hdJ : d ∈ J := by rw [Set.mem_iUnion]
                                           exists ⟨d,hdc⟩
                                           erw [Order.Ideal.mem_principal]
                    erw [hb, Order.Ideal.mem_principal] at hdJ
                    exact hdJ
                  have hbJ : b ∈ J := by erw [hb, Order.Ideal.mem_principal] 
                  rw [Set.mem_iUnion] at hbJ
                  cases hbJ with 
                  | intro d hbd => erw [Order.Ideal.mem_principal] at hbd 
                                   exists d 
                                   rw [and_iff_right (hcs d.2)]
                                   intro e hec 
                                   exact le_trans (hbmax e hec) hbd  


lemma Noetherian_iff_every_ideal_is_principal : IsNoetherianPoset α  ↔ ∀ (I : Order.Ideal α), ∃ (a : α), I = Order.Ideal.principal a := by
  constructor
  . intro hNoeth I 
    exists WellFounded.min hNoeth I I.nonempty
    apply Order.Ideal.generated_by_maximal_element 
    erw [and_iff_right (WellFounded.min_mem hNoeth I I.nonempty)] 
    intro b hbI hab 
    have hnlt := WellFounded.not_lt_min hNoeth I I.nonempty hbI
    rw [lt_iff_le_not_le] at hnlt
    push_neg at hnlt 
    exact hnlt hab    
  . intro hprin
    unfold IsNoetherianPoset
    rw [WellFounded.wellFounded_iff_has_min]
    intro s hsne 
    cases hsne with
    | intro a has => cases zorn_nonempty_preorder₀ s 
                       (fun c hcs hchain b hbc => @Noetherian_iff_every_ideal_is_principal_aux α _ hprin s c hcs hchain b hbc) 
                       a has with  
                     | intro m hm => exists m 
                                     rw [and_iff_right hm.1]
                                     exact fun b hbs => by rw [lt_iff_le_not_le]; push_neg; exact hm.2.2 b hbs

