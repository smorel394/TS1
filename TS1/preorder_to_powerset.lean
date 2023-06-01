import TS1.general_preorder_stuff

set_option autoImplicit false

open Classical 

namespace Preorder 

universe u 

variable {α : Type u}

/- The goal is to describe a map from Preorder α to Set (Set α), sending a preorder to the set of its nontrivial lower sets
(here "nontrivial" means different from ⊥ and ⊥). This map reverses the order and it is injective. We will prove in another file
that,  if α is finite, its image is closed under taking subsets (so it will define an abstract simplicial complex on Set α). -/

/- We start with the definition of the map from Preorder α to Set (Set α). -/


def preorderToPowerset (s : Preorder α) : Set (Set α) := {β : Set α | β ≠ ⊥ ∧ β ≠ ⊤ ∧ (@IsLowerSet α {le := s.le} β)}


/- One important example of calculation.-/
lemma preorderToPowerset_TrivialPreorder_is_empty : preorderToPowerset (trivialPreorder α) = ∅ := by
  by_contra habs
  change _ ≠ ∅ at habs
  rw [←Set.nonempty_iff_ne_empty] at habs
  cases habs with
  | intro β hβ => unfold preorderToPowerset at hβ
                  simp only [Set.bot_eq_empty, ne_eq, Set.top_eq_univ, Set.mem_setOf_eq] at hβ
                  change _ ≠ ∅ ∧ _ at hβ
                  rw [←Set.nonempty_iff_ne_empty] at hβ
                  cases hβ.1 with
                  | intro a ha => have htop : β = Set.univ := by ext b
                                                                 simp only [Set.mem_univ, iff_true]
                                                                 exact hβ.2.2 (by triv) ha 
                                  exact hβ.2.1 htop 


/- Another important example: if s is the two-step preorder associated to a ∈ α (i.e. it makes a the smallest element and all the other elements
equivalent), and if s is nontrivial (i.e. if there exists b in α such that b ≠ a), then preorderToPowerset s is the singleton {{a}}.-/

lemma preorderToPowerset_TwoStepPreorder {a b : α} (hab : a ≠ b) :
preorderToPowerset (twoStepPreorder a) = {{a}} := by 
  ext X 
  simp only [Set.mem_singleton_iff]
  unfold preorderToPowerset 
  simp only [Set.bot_eq_empty, Set.top_eq_univ, Set.mem_setOf_eq]
  rw [←Set.nonempty_iff_ne_empty, Set.ne_univ_iff_exists_not_mem]
  constructor 
  . intro hX 
    match hX.1 with 
  | ⟨c, hcX⟩ => 
    have haX := hX.2.2 (twoStepPreorder_smallest a c) hcX
    ext b 
    simp only [Set.mem_singleton_iff]
    constructor 
    . intro hbX 
      match hX.2.1 with 
      | ⟨d, hdX⟩ => 
        by_contra hba 
        have hdb : (twoStepPreorder a).le d b := by 
          unfold twoStepPreorder 
          simp only [dite_eq_ite, hba, ite_false, ite_self]
        exact hdX (hX.2.2 hdb hbX) 
    . exact fun hba => by rw [hba]; exact haX   
  . intro hX 
    rw [hX, and_iff_right ⟨a, Set.mem_singleton _⟩, and_iff_right ⟨b, by rw [Set.mem_singleton_iff]; exact Ne.symm hab⟩]
    intro c d hdc 
    simp only [Set.mem_singleton_iff]
    intro hc 
    rw [hc] at hdc 
    unfold twoStepPreorder at hdc 
    by_cases hd : d = a 
    . exact hd  
    . exfalso; simp only [dite_eq_ite, hd, ite_true, ite_false] at hdc


/- If s is total, then its image is totally ordered by inclusion.-/

lemma preorderToPowerset_total_is_total {s : Preorder α} (htot : Total s.le) : Total (fun (X : (preorderToPowerset s)) => 
fun (Y : preorderToPowerset s) => X.1 ⊆ Y.1) := by 
  intro X Y 
  simp only
  by_cases hXY : X.1 ⊆ Y.1
  . exact Or.inl hXY 
  . rw [Set.not_subset] at hXY
    match hXY with 
    | ⟨a, ⟨haX, haY⟩⟩ => apply Or.inr 
                         intro b hbY 
                         cases htot a b with 
                         | inl hab =>  exfalso; exact haY (Y.2.2.2 hab hbY)  
                         | inr hba => exact X.2.2.2 hba haX 




/- Antitonicity.-/

lemma preorderToPowerset_antitone {s t : Preorder α} (hst : s ≤ t) : preorderToPowerset t ⊆ preorderToPowerset s := by
  rw [Set.subset_def]
  exact fun β hβ => by constructor
                       . exact hβ.1
                       . constructor
                         . exact hβ.2.1
                         . exact fun b a hab hb => hβ.2.2 (hst hab) hb




/- Now we introduce a left inverse, called powersetToPreorder (and prove that it is a left inverse). -/

def powersetToPreorder (E : Set (Set α)) : Preorder α :=
{le := fun a b => (∀ (β : Set α), β ∈ E → b ∈ β → a ∈ β),
 le_refl := fun _ _ _ h => h,
 le_trans := fun _ _ _ hab hbc β hβ hcβ => hab β hβ (hbc β hβ hcβ)
 } 


/- This map is also antitone. -/

lemma powersetToPreorder_antitone {E F : Set (Set α)} (hEF : E ⊆ F) : powersetToPreorder F ≤ powersetToPreorder E := 
fun _ _ hab β hβ hbβ => hab β (hEF hβ) hbβ

/- If E is totally ordered by inclusion, then its image is total.-/

lemma powersetToPreorder_total_is_total {E : Set (Set α)} (hEtot : Total (fun (X : E) => fun (Y : E) => X.1 ⊆ Y.1)) : 
Total (powersetToPreorder E).le := by 
  intro a b 
  letI : Preorder α := powersetToPreorder E 
  by_cases hab : a ≤ b  
  . exact Or.inl hab 
  . change ¬(∀ (Y : Set α), Y ∈ E → b ∈ Y → a ∈ Y) at hab
    push_neg at hab
    match hab with
    | ⟨Y, ⟨hYE, hbY, haY⟩⟩ => apply Or.inr 
                              intro Z hZE haZ 
                              cases hEtot ⟨Y, hYE⟩ ⟨Z, hZE⟩ with 
                              | inl hYZ => exact hYZ hbY
                              | inr hZY => exfalso; exact haY (hZY haZ) 
  


/- We prove that powersetToPreorder is a left inverse of preorderToPowerset. -/

lemma preorderToPowersetToPreorder (s : Preorder α) : s = powersetToPreorder (preorderToPowerset s) := by
  apply Preorder.ext
  intro a b 
  constructor
  . exact fun hab β hβ hbβ => hβ.2.2 hab hbβ
  . by_cases hab : s.le a b
    . exact fun _ => hab
    . set β := @Set.Iic α s b
      have hβ : β ∈ preorderToPowerset s  := by constructor
                                                . rw [Set.bot_eq_empty, ←Set.nonempty_iff_ne_empty]
                                                  exact ⟨b, s.le_refl _⟩
                                                . constructor
                                                  . simp only [Set.top_eq_univ, ne_eq, Set.eq_univ_iff_forall, 
                                                               Set.mem_Iic, not_forall]
                                                    exact ⟨a, hab⟩
                                                  . exact isLowerSet_Iic b 
      exact fun h => by exfalso; exact hab (h β hβ (s.le_refl _))


/- We deduce that preorderToPowerset is injective.-/

lemma preorderToPowerset_injective : Function.Injective (@preorderToPowerset α) := 
fun s t hst => by apply_fun powersetToPreorder at hst

                  rw [←preorderToPowersetToPreorder, ←preorderToPowersetToPreorder] at hst
                  exact hst


/- This in turn implies that preorderToPowerset of s is empty if and only if s is the trivial preorder. -/

lemma preorderToPowerset_is_empty_iff_TrivialPreorder (s : Preorder α) : preorderToPowerset s = ∅ ↔ s = trivialPreorder α := by
  constructor
  . exact fun h => by rw [←preorderToPowerset_TrivialPreorder_is_empty] at h; exact preorderToPowerset_injective h
  . exact fun h => by rw [h]; exact preorderToPowerset_TrivialPreorder_is_empty 


/- In the other direction, we only get an inclusion in general.-/

lemma powersetToPreorderToPowerset (E : Set (Set α)) {β : Set α} (hβ : β ∈ E) :
β ≠ ⊥ → β ≠ ⊤ → β ∈ preorderToPowerset (powersetToPreorder E) := 
fun hne hnuniv => ⟨hne, ⟨hnuniv, fun _ _ hab hbβ => hab β hβ hbβ⟩⟩


/- Under some conditions we have equality (up to ⊥ and ⊤). The condition I first wanted to use is "s is total, locally (i.e. in
each closed interval) s.gt is well-founded and there is a successor function." But this is actually equivalent to the fact that,
in every closed interval, s.gt and s.lt are well-founded:
(1) If the latter condition is true, then we get a successor function in the following way: Let a be an element of α. If a is 
maximal, we set succ a = a. If not, then there exists b such that a < b. We set succ a to be a minimal element of the set
{s : α | a < c ∧ c ≤ b}, which is nonempty subset of the closed interval [a,b]. 
(2) In the other direction, let a and b be elements of α such that a ≤ b. We want to show that s.lt is well-founded on the closed
interval [a,b], so let S be a nonempty closed subset of [a,b]. If there exists c in S such that c ≤ a, then this c is minimal.
Otherwise, the set M of elements of [a,b] that are stricly smaller than every element of S is nonempty (because is contains a).
Let b be a maximal element of M, and let c = succ b. We have b < c because b is not maximal in α, so c ∉  M, so there exists d in S 
such that d ≤ c. I claim that d is a minimal element of S. Indeed, let e be an element of S. If e < d, then e < c, so e ≤ b (by
the properties of the successor function), and this is a contradiction; so ¬(e < d).

On the other, if s is a total preorder such that s.lt and s.gt are well-founded, then the antisymmetrization of s is finite. Indeed,
going to the antisymmetrization, we may assume that s is a partial order, hence a linear order, hence a well-order whose dual
is also a well-order. As every well-order is isomorphic to an ordinal, we may assume that α is an ordinal (and s is its canonical
order). Then if α were infinite, it would contain the ordinal ω as an initial segment, and ω has no greatest element, so the dual
of s would not be a well-order.
  
So in conclusion, the conclusion I wanted to impose is equivalent to the fact that the antisymmetrization partial order of s is
locally finite. I will call this "essentially locally finite", and it is proved in the file "general_preorder_stuff.lean" that
total essentially finite preorder form an upper set.

I think that this condition is also stable the other relevant operations (taking the associated linear order and taking the descent 
preorder), as long as the auxiliary linear order we use for the last two is a locally finite well-order, i.e. isomorphic to ω.
-/


lemma TotalELFP_LowerSet_is_principal {s : Preorder α} (htot : Total s.le) (hELF : EssentiallyLocallyFinitePreorder s) {β : Set α} 
(hβ : β ∈ preorderToPowerset s) : ∃ (a : α), β = @Set.Iic α s a := by 
  unfold preorderToPowerset at hβ
  simp only [Set.bot_eq_empty, Set.top_eq_univ, Set.mem_setOf_eq] at hβ
  rw [←Set.nonempty_iff_ne_empty, ne_eq, Set.eq_univ_iff_forall] at hβ
  push_neg at hβ
  match hβ with 
  | And.intro ⟨a,ha⟩ (And.intro ⟨b,hb⟩  h) => have hab : s.le a b := by cases (htot a b) with
                                                                        | inl hab => exact hab
                                                                        | inr hba => exfalso; exact hb (h hba ha) 
                                              cases (ELFP_is_locally_WellFounded hELF a b {c : α | s.le a c ∧ s.le c b ∧ c ∈ β}
                                                ⟨a, ⟨s.le_refl a, hab, ha⟩⟩ (fun _ hc => ⟨hc.1, hc.2.1⟩)) with
                                              | intro c hc => exists c
                                                              ext x
                                                              simp only [Set.mem_setOf_eq, Set.coe_setOf, Subtype.coe_lt_coe, Set.mem_Iic]
                                                              constructor 
                                                              . intro hx
                                                                cases (htot a x) with
                                                                | inr hxa => exact s.le_trans _ _ _ hxa hc.1.1
                                                                | inl hax => cases (htot x b) with
                                                                             | inl hxb => have halmost := (hc.2 x ⟨hax, hxb, hx⟩)
                                                                                          rw [←(TotalPreorder_lt_iff_not_le htot)] at halmost
                                                                                          exact of_not_not halmost 
                                                                             | inr hbx => exfalso; exact hb (h hbx hx) 
                                                              . intro hx
                                                                exact h hx hc.1.2.2 
                                     
  

lemma TotalELFP_powersetToPreorderToPowerset (E : Set (Set α)) (htot : Total (powersetToPreorder E).le) 
(hELF : EssentiallyLocallyFinitePreorder (powersetToPreorder E)) : preorderToPowerset (powersetToPreorder E) ⊆ E := by
  rw [Set.subset_def]
  intro β hβ
  cases (TotalELFP_LowerSet_is_principal htot hELF hβ) with
  | intro a haβ => letI : Preorder α := powersetToPreorder E  -- have to do this so hsucc will know which preorder I am talking about 
                   set b : α := (TotalELFP_SuccOrder htot hELF).succ a  
                   have hnle : ¬((powersetToPreorder E).le b a) := by 
                      by_contra habs
                      have htop : β = ⊤ := by 
                        rw [Set.top_eq_univ]
                        ext x
                        simp only [Set.mem_univ, iff_true]
                        rw [haβ]
                        cases (htot x a) with
                        | inl hxa => exact hxa
                        | inr hax => exact ((TotalELFP_SuccOrder htot hELF).max_of_succ_le habs) hax
                      exact hβ.2.1 htop                                
                   change ¬(∀ (X : Set α), X ∈ E → a ∈ X → b ∈ X) at hnle
                   push_neg at hnle
                   match hnle with
                   | ⟨X,⟨hXE,haX,hbX⟩⟩ =>  have hX : X ∈ preorderToPowerset (powersetToPreorder E) := by
                                             apply powersetToPreorderToPowerset E hXE 
                                             rw [Set.bot_eq_empty, ←Set.nonempty_iff_ne_empty]
                                             exact ⟨a,haX⟩
                                             rw [Set.top_eq_univ, ne_eq, Set.eq_univ_iff_forall]
                                             push_neg
                                             exact ⟨b, hbX⟩
                                           have heq : X = β := by 
                                            ext x
                                            rw [haβ]
                                            simp only [Set.mem_Iic]
                                            constructor
                                            . exact fun h => by by_contra habs 
                                                                rw [TotalPreorder_lt_iff_not_le htot] at habs  
                                                                exact hbX (hX.2.2 ((TotalELFP_SuccOrder htot hELF).succ_le_of_lt habs) h) 
                                            . exact fun h => hX.2.2 h haX 
                                           rw [heq] at hXE
                                           exact hXE 


/- We deduce that, is s is total and essentially locally finite, then every subset of preorderToPowerset s is in the image of 
preorderToPowerset. -/

lemma preorderToPowersets_down_closed {s : Preorder α}  (htot : Total s.le) (hELF : EssentiallyLocallyFinitePreorder s)
{E : Set (Set α)} (hE : E ⊆ preorderToPowerset s) : 
E = preorderToPowerset (powersetToPreorder E) := by
  have hEs : s ≤ powersetToPreorder E  := by rw [preorderToPowersetToPreorder s]; exact powersetToPreorder_antitone hE  
  have hEtot : Total (powersetToPreorder E).le :=  Total_IsUpperSet hEs htot 
  have hEELF := TotalELPF_IsUpperSet htot hELF hEs   
  ext β  
  simp only [Set.mem_setOf_eq]
  constructor
  . intro hβ
    unfold preorderToPowerset at hE 
    constructor
    . by_contra habs
      rw [habs] at hβ
      have habs' := hE hβ
      simp only [Set.bot_eq_empty, ne_eq, Set.mem_setOf_eq, not_true, false_and] at habs'  
    . constructor
      . by_contra habs
        rw [habs] at hβ
        have habs' := hE hβ
        simp only [Set.top_eq_univ, ne_eq, Set.mem_setOf_eq, Set.univ_eq_empty_iff, not_isEmpty_iff, not_true, false_and, and_false] at habs' 
      . exact fun _ _ hab ha => hab β hβ ha
  . intro hβ
    apply Set.mem_of_subset_of_mem (TotalELFP_powersetToPreorderToPowerset E hEtot hEELF)
    exact hβ

                  



/- If s is a total essentially locally finite preorder (in fact, we just need total and locally dually well-founded) and α is nonempty, 
then preorderToPowerset s is in order-preserving bijection with the quotient of α by the antisymmetrization of s if that quotient has
a biggest element, and with the complement of the biggest element otherwise.-/

/- A remark: Maximal elements of the antisymmetrization correspond to maximal elements of α, and a total preorder is dually well-founded if and
only it is locally dually well-founded and has a biggest element. Indeed, if s is dually well-founded (and α is not empty), then s has a 
biggest element and is locally dually well-founded. Conversely, suppose that s is locally dually well-founded and has a biggest element, and 
let β be a nonempty subset of α. Let a be a biggest element of α and b be an element of β. Then β ∩ [b,a] is nonempty (it contains b), so it has 
a biggest element, which is also a biggest element of β.
-/

/- This is old code from when I used the condition "fun a b => s.lt b a well-founded" instead of "total ELFP".-/
/-noncomputable def Antisymmetrization_greatest (hne : Nonempty α) {s : Preorder α} (hwf : WellFounded (fun a b => s.lt b a)) :
Antisymmetrization α s.le := toAntisymmetrization s.le (WellFounded.min hwf Set.univ (@Set.univ_nonempty _ hne))

                     
lemma Antisymmetrization_greatest_is_greatest (hne : Nonempty α) {s : Preorder α} (hwf : WellFounded (fun a b => s.lt b a)) 
(htot : Total s.le) (x : Antisymmetrization α s.le) : x ≤ Antisymmetrization_greatest hne hwf := by
  unfold Antisymmetrization_greatest
  rw [←(toAntisymmetrization_ofAntisymmetrization s.le x)]
  rw [toAntisymmetrization_le_toAntisymmetrization_iff]
  generalize ofAntisymmetrization s.le x = a
  have hlt := WellFounded.not_lt_min hwf Set.univ (@Set.univ_nonempty _ hne) (Set.mem_univ a)
  rw [lt_iff_le_not_le] at hlt
  push_neg at hlt
  cases (htot a (WellFounded.min hwf Set.univ (@Set.univ_nonempty _ hne))) with
  | inl ham => exact ham
  | inr hma => exact hlt hma  

noncomputable def Antisymmetrization_minus_greatest (hne : Nonempty α) {s : Preorder α} (hwf : WellFounded (fun a b => s.lt b a)) :
Set (Antisymmetrization α s.le) := {x | x ≠ Antisymmetrization_greatest hne hwf}-/

/- Now we introduce directly the set "antisymmetrization minus maximal elements". And if the antisymmetrization is finite, we
prove the existence of the biggest element. -/

def Preorder_nonmaximal (s : Preorder α) : Set α := {b : α | ∃ (c : α), s.lt b c}

def Antisymmetrization_nonmaximal (s : Preorder α) := Preorder_nonmaximal (@PartialOrder.toPreorder _
(@instPartialOrderAntisymmetrizationLeToLEInstIsPreorderLeToLE α s)) 


lemma Antisymmetrization_nonmaximal_prop1 {s : Preorder α} (hnonmax : ∀ (a : α), ∃ (b : α), s.lt a b) :
Antisymmetrization_nonmaximal s = @Set.univ (@Antisymmetrization α s.le (@instIsPreorderLeToLE α s)) := by
  unfold Antisymmetrization_nonmaximal
  unfold Preorder_nonmaximal
  ext x 
  simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
  cases (hnonmax (ofAntisymmetrization s.le x)) with
  | intro c hc => exists (toAntisymmetrization s.le c)
                  rw [←(toAntisymmetrization_ofAntisymmetrization s.le x), toAntisymmetrization_lt_toAntisymmetrization_iff]
                  exact hc 

lemma Antisymmetrization_nonmaximal_prop2 {s : Preorder α} (htot : Total s.le) {a : α} (hamax : ∀ (b : α), ¬(s.lt a b)) :
Antisymmetrization_nonmaximal s = {x | x ≠ toAntisymmetrization s.le a} := by
  unfold Antisymmetrization_nonmaximal
  unfold Preorder_nonmaximal
  ext x 
  simp only [Set.mem_setOf_eq, ne_eq]
  letI : Preorder α := s 
  constructor
  . intro hx
    cases hx with
    | intro y hy => rw [←ofAntisymmetrization_lt_ofAntisymmetrization_iff] at hy
                    by_contra habs
                    have hax : a ≤ ofAntisymmetrization s.le x := by
                      rw [←toAntisymmetrization_le_toAntisymmetrization_iff, toAntisymmetrization_ofAntisymmetrization, ←habs]
                    exact hamax _ (lt_of_le_of_lt hax hy)  
  . intro hx 
    exists toAntisymmetrization s.le a
    have hxa : x ≤ toAntisymmetrization s.le a := by
      rw [←(toAntisymmetrization_ofAntisymmetrization s.le x), toAntisymmetrization_le_toAntisymmetrization_iff]
      apply of_not_not 
      rw [TotalPreorder_lt_iff_not_le htot]
      exact hamax _ 
    rw [lt_iff_le_and_ne]
    exact ⟨hxa, hx⟩ 

lemma FiniteAntisymmetrization_exists_maximal (s : Preorder α) (hfin : Finite (Antisymmetrization α s.le)) (hne : Nonempty α) : 
∃ (a : α), ∀ (b : α), ¬(s.lt a b) := by 
  letI : Preorder α := s 
  have hane : (@Set.univ (Antisymmetrization α s.le)).Nonempty := by 
    exists toAntisymmetrization s.le (Classical.choice hne)
  exists ofAntisymmetrization s.le (WellFounded.min (@Finite.Preorder.wellFounded_gt _ hfin _) _ hane)
  intro b 
  rw [←toAntisymmetrization_lt_toAntisymmetrization_iff, toAntisymmetrization_ofAntisymmetrization]  
  exact WellFounded.not_lt_min (@Finite.Preorder.wellFounded_gt _ hfin _) _ hane (Set.mem_univ (toAntisymmetrization s.le b)) 

lemma FiniteAntisymmetrization_nonmaximal {s : Preorder α} (htot : Total s.le) (hfin : Finite (Antisymmetrization α s.le)) (hne : Nonempty α) : 
Antisymmetrization_nonmaximal s = 
Finset.erase (@Finset.univ (Antisymmetrization α s.le) (@Fintype.ofFinite _ hfin)) 
(toAntisymmetrization s.le (Classical.choose (FiniteAntisymmetrization_exists_maximal s hfin hne))) := by 
  rw [Antisymmetrization_nonmaximal_prop2 htot (Classical.choose_spec (FiniteAntisymmetrization_exists_maximal s hfin hne))]
  ext x 
  simp only [ne_eq, Set.mem_setOf_eq, Finset.coe_erase, Finset.mem_coe, Set.mem_diff, Set.mem_singleton_iff, iff_and_self]
  exact fun  _ => @Finset.mem_univ _ (@Fintype.ofFinite _ hfin) _  

/- We define the map from the antisymmetrization (minus biggest element) to preorderToPowerset. -/

def Antisymmetrization_to_powerset (s : Preorder α) (x : Antisymmetrization α s.le) : Set α :=
{a : α | toAntisymmetrization s.le a ≤ x}

lemma Antisymmetrization_to_powerset_in_PreorderToPowerset {s : Preorder α}  (htot : Total s.le) {x : Antisymmetrization α s.le} 
(hxnonmax : x ∈ Antisymmetrization_nonmaximal s) : 
Antisymmetrization_to_powerset s x ∈ preorderToPowerset s := by
  unfold Antisymmetrization_nonmaximal at hxnonmax 
  unfold Preorder_nonmaximal at hxnonmax 
  simp only [Set.mem_setOf_eq] at hxnonmax 
  unfold Antisymmetrization_to_powerset
  constructor
  . rw [Set.bot_eq_empty, ←Set.nonempty_iff_ne_empty]
    exists ofAntisymmetrization s.le x
    simp only [Set.mem_setOf_eq, toAntisymmetrization_ofAntisymmetrization, _root_.le_refl]
  . constructor
    . by_contra habs
      cases hxnonmax with
      | intro y hy => have hnle : ¬(y ≤ x) := by 
                        rw [←ofAntisymmetrization_le_ofAntisymmetrization_iff, TotalPreorder_lt_iff_not_le htot]
                        rw [←ofAntisymmetrization_lt_ofAntisymmetrization_iff] at hy 
                        exact hy 
                      have hyuniv : ofAntisymmetrization s.le y ∈ Set.univ := Set.mem_univ _ 
                      rw [Set.top_eq_univ] at habs
                      rw [←habs] at hyuniv 
                      simp only [Set.mem_setOf_eq, toAntisymmetrization_ofAntisymmetrization] at hyuniv 
                      exact hnle hyuniv 
    . intro b a hab hb
      rw [←(@toAntisymmetrization_le_toAntisymmetrization_iff α s _ _)] at hab 
      exact le_trans _ _ _ hab hb


/- It is (strictly) compatible with the partial orders. -/

lemma Antisymmetrization_to_powerset_preserves_order (s : Preorder α) (x y : Antisymmetrization α s.le) :
x ≤ y ↔ Antisymmetrization_to_powerset s x ⊆ Antisymmetrization_to_powerset s y := by
  unfold Antisymmetrization_to_powerset
  rw [Set.subset_def]
  constructor
  . exact fun hxy a ha => le_trans (toAntisymmetrization s.le a) _ _ ha hxy 
  . exact fun hxy => by have halmost := hxy (ofAntisymmetrization s.le x) (by simp only [Set.mem_setOf_eq, 
                            toAntisymmetrization_ofAntisymmetrization, _root_.le_refl])  
                        simp only [Set.mem_setOf_eq, toAntisymmetrization_ofAntisymmetrization] at halmost
                        exact halmost

/- Hence it is injective. -/

lemma Antisymmetrization_to_powerset_injective (s : Preorder α) : Function.Injective (Antisymmetrization_to_powerset s) := by
  intro x y heq
  have hxy : Antisymmetrization_to_powerset s x ⊆ Antisymmetrization_to_powerset s y := by rw [heq]
  have hyx : Antisymmetrization_to_powerset s y ⊆ Antisymmetrization_to_powerset s x := by rw [heq]
  rw [←Antisymmetrization_to_powerset_preserves_order] at hxy hyx
  exact le_antisymm hxy hyx 

/- We prove surjectivity onto preorderToPowerset, assuming that s is total essentially locally finite preorder. -/

lemma Nonempty_of_mem_PreorderToPowerset {s : Preorder α} {β : Set α} (hβ : β ∈ preorderToPowerset s) : Nonempty α := by
  unfold preorderToPowerset at hβ
  simp only [Set.bot_eq_empty, Set.top_eq_univ, Set.mem_setOf_eq] at hβ
  rw [←Set.nonempty_iff_ne_empty] at hβ
  cases hβ.1 with
  | intro a _ => exact ⟨a⟩

lemma Antisymmetrization_to_powerset_surjective {s : Preorder α} (htot : Total s.le) (hELF : EssentiallyLocallyFinitePreorder s)
{β : Set α} (hβ : β ∈ preorderToPowerset s) : ∃ (x : Antisymmetrization α s.le), 
x ∈ Antisymmetrization_nonmaximal s ∧ Antisymmetrization_to_powerset s x = β:= by
  cases TotalELFP_LowerSet_is_principal htot hELF hβ with
  | intro a ha => exists toAntisymmetrization s.le a 
                  constructor
                  . unfold Antisymmetrization_nonmaximal
                    unfold Preorder_nonmaximal
                    have hβnuniv := hβ.2.1
                    rw [Set.top_eq_univ, ne_eq, Set.eq_univ_iff_forall] at hβnuniv
                    push_neg at hβnuniv
                    cases hβnuniv with
                    | intro b hb => exists toAntisymmetrization s.le b 
                                    rw [toAntisymmetrization_lt_toAntisymmetrization_iff]
                                    rw [ha] at hb
                                    simp only [Set.mem_Iic] at hb
                                    rw [TotalPreorder_lt_iff_not_le htot] at hb 
                                    exact hb 
                  . rw [ha]
                    unfold Antisymmetrization_to_powerset 
                    ext b 
                    simp only [toAntisymmetrization_le_toAntisymmetrization_iff, Set.mem_setOf_eq, Set.mem_Iic]



/- The equivalence between Antisymmetrization_minus_greatest and preorderToPowerset. -/

noncomputable def Equiv_Antisymmetrization_nonmaximal_to_PreorderToPowerset
{s : Preorder α} (htot : Total s.le) (hELF : EssentiallyLocallyFinitePreorder s):
Equiv (Antisymmetrization_nonmaximal s) (preorderToPowerset s) :=
  Equiv.ofBijective 
    (fun x => ⟨Antisymmetrization_to_powerset s ↑x, Antisymmetrization_to_powerset_in_PreorderToPowerset htot x.2⟩)
    (by constructor
        . exact fun x y heq => by simp only [Subtype.mk.injEq] at heq
                                  rw [←Subtype.coe_inj]
                                  exact Antisymmetrization_to_powerset_injective s heq 
        . intro ⟨β,hβ⟩
          simp only [Subtype.mk.injEq, Subtype.exists, exists_prop]
          exact Antisymmetrization_to_powerset_surjective htot hELF hβ)

/- And now the order isomorphism. -/


noncomputable def OrderIso_Antisymmetrization_minus_greatest_to_PreorderToPowerset
{s : Preorder α} (htot : Total s.le) (hELF : EssentiallyLocallyFinitePreorder s):
OrderIso (Antisymmetrization_nonmaximal s) (preorderToPowerset s) where  
__ := Equiv_Antisymmetrization_nonmaximal_to_PreorderToPowerset htot hELF 
map_rel_iff':= by simp only [Equiv.toFun_as_coe, Equiv.invFun_as_coe, Equiv.coe_fn_mk, Subtype.forall, Subtype.mk_le_mk]
                  unfold Equiv_Antisymmetrization_nonmaximal_to_PreorderToPowerset
                  simp only [Equiv.ofBijective_apply, Subtype.mk_le_mk, Set.le_eq_subset]
                  exact fun x _ y _ => Iff.symm (Antisymmetrization_to_powerset_preserves_order s x y)

                 

end Preorder