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
See: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Extension/Linear.html 
So I can comment almost everything that follows. -/

/-

/- The goal is to show the following: for any preorder s on α, there exists a total preorder t greater than s and such that s and t have
the same antisymmetrization relation. As a preorder is a partial order if and only if its antisymmetrization relation is the
diagonal this implies in particular that any partial order is refined by a linear order. -/


/- The proof uses Zorn's lemma on the set of preorders that are greater than or equal to s and have the same antisymmetrization
relation as s. First we prove that a maximal element of this set has to be total (or rather we prove the contraposition of this.)
So we take a preorder s and elements a and b of α that are not comparable, and we construct a preorder strictly greater than s,
with the same antisymmetrization relation, for which a is smaller than b.-/



lemma ne_of_noncomp (s : Preorder α) {a b : α} (hab : ¬(s.le a b)) : a ≠ b := by
  by_contra heq
  rw [heq] at hab
  exact hab (s.le_refl b)

def oneStepUpAux (s : Preorder α) (a b : α) : α → α → Prop := by 
  intro x y
  by_cases x=a
  . by_cases y=b
    . exact True
    . exact (s.le a y) ∨ (s.le b y)
  . by_cases x=b
    . by_cases y=a
      . exact False 
      . exact s.le b y 
    . by_cases y=b
      . exact s.le x a ∨ s.le x b
      . exact s.le x y ∨ (s.le x a ∧ s.le b y)

lemma oneStepUpAux_refl (s : Preorder α) (a b : α) (x : α) : oneStepUpAux s a b x x := by
  rw [oneStepUpAux]
  by_cases hxa : x=a
  . simp only [hxa, _root_.le_refl, true_or, dite_eq_ite, ite_self, ite_true, true_and]
  . simp only [hxa, dite_eq_ite, ite_false, _root_.le_refl, true_or]
    by_cases hxb : x=b
    . simp only [hxb, _root_.le_refl, or_true, ite_self]
    . simp only [hxb, ite_false]

lemma oneStepUpAux_trans (s : Preorder α) {a b : α} (hab : ¬(s.le a b) ∧ ¬(s.le b a)) (x y z : α) :
oneStepUpAux s a b x y → oneStepUpAux s a b y z → oneStepUpAux s a b x z := by
  unfold oneStepUpAux
  by_cases hxa : x=a
  . simp only [hxa, dite_eq_ite, _root_.le_refl, true_or, true_and, ite_true]
    by_cases hya : y=a
    . simp only [hya, _root_.le_refl, true_or, ite_self, true_and, ite_true, imp_self, forall_true_left]
    . simp only [hya, ite_false]
      by_cases hyb : y=b
      . simp only [hyb, _root_.le_refl, or_true, ite_self, ite_true, forall_true_left]
        by_cases hza : z=a
        . simp only [hza, ite_true, _root_.le_refl, true_or, ite_self, IsEmpty.forall_iff]
        . simp only [hza, ite_false]
          by_cases hzb : z=b
          . simp only [hzb, _root_.le_refl, or_true, ite_self, forall_true_left]
          . simp only [hzb, ite_false]
            exact fun h => Or.inr h
      . simp only [hyb, ite_false]
        by_cases hzb : z=b
        . simp only [hzb, _root_.le_refl, and_true, ite_true, or_true, ite_self, implies_true]
        . simp only [hzb, ite_false]
          intro h h'
          cases h' with
          | inr hyz => exact Or.inr hyz.2
          | inl hyz => cases h with
                       | inl hay => exact Or.inl (s.le_trans _ _ _ hay hyz)
                       | inr hby => exact Or.inr (s.le_trans _ _ _ hby hyz)
  . simp only [hxa, dite_eq_ite, ite_false]
    by_cases hxb : x=b
    . simp only [hxb, _root_.le_refl, or_true, ite_true]
      by_cases hya : y=a
      . simp only [hya, ite_true, _root_.le_refl, true_or, true_and, IsEmpty.forall_iff]
      . simp only [hya, ite_false]
        by_cases hyb : y=b
        . simp only [hyb, _root_.le_refl, or_true, ite_true, imp_self, forall_true_left]
        . simp only [hyb, ite_false]
          by_cases hzb : z=b
          . simp only [hzb, _root_.le_refl, and_true, ite_true]
            exact fun _ _ => by simp only [ne_of_noncomp s hab.2, ite_false]
          . simp only [hzb, ite_false]
            by_cases hza : z=a
            . simp only [hza, ite_true]
              exact fun h h' => by cases h' with
                                   | inl hya => exact hab.2 (s.le_trans _ _ _ h hya)
                                   | inr hby => exact hab.2 hby.2  
            . simp only [hza, ite_false]
              exact fun h h' => by cases h' with
                                   | inl hyz => exact s.le_trans _ _ _ h hyz
                                   | inr hyz => exact hyz.2 
    . simp only [hxb, ite_false]
      by_cases hyb : y=b
      . simp only [hyb, _root_.le_refl, and_true, ite_true, or_true]
        by_cases hzb : z=b
        . simp only [hzb, _root_.le_refl, or_true, ite_self, and_true, ite_true]
          exact fun h _ => h
        . simp only [ne_of_noncomp s hab.2, hzb, ite_false]
          by_cases hza : z=a
          . simp only [hza, ite_true, IsEmpty.forall_iff, implies_true]
          . simp only [hza, ite_false]
            exact fun h h' => by cases h with
                                 | inl hxa => exact Or.inr ⟨hxa,h'⟩
                                 | inr hxb => exact Or.inl (s.le_trans _ _ _ hxb h')
      . simp only [hyb, ite_false]
        by_cases hya : y=a
        . simp only [hya, _root_.le_refl, true_or, true_and, ite_self]
          by_cases hzb : z=b
          . simp only [hzb, _root_.le_refl, or_true, ite_self, and_true, ite_true, forall_true_left]
            exact fun h => by cases h with
                              | inl hxa => exact Or.inl hxa
                              | inr hxa => exact Or.inl hxa.1
          . simp only [hzb, ite_false]
            exact fun h => by cases h with
                              | inl hxa => exact fun h' => by cases h' with
                                                              | inl haz => exact Or.inl (s.le_trans _ _ _ hxa haz)
                                                              | inr hbz => exact Or.inr ⟨hxa,hbz⟩
                              | inr hxa => exact fun h' => by cases h' with
                                                              | inl haz => exact Or.inl (s.le_trans _ _ _ hxa.1 haz)
                                                              | inr hbz => exact Or.inr ⟨hxa.1,hbz⟩
        . simp only [hya, ite_false]
          by_cases hzb : z=b
          . simp only [hzb, _root_.le_refl, and_true, ite_true]
            exact fun h => by cases h with
                              | inl hxy => exact fun h' => by cases h' with
                                                              | inl hya => exact Or.inl (s.le_trans _ _ _ hxy hya)
                                                              | inr hyb => exact Or.inr (s.le_trans _ _ _ hxy hyb)
                              | inr hxy => exact fun _ => Or.inl hxy.1
          . simp only [hzb, ite_false]
            exact fun h => by cases h with
                              | inl hxy => exact fun h' => by cases h' with
                                                              | inl hyz => exact Or.inl (s.le_trans _ _ _ hxy hyz) 
                                                              | inr hyz => exact Or.inr ⟨s.le_trans _ _ _ hxy hyz.1, hyz.2⟩
                              | inr hxy => exact fun h' => by cases h' with
                                                              | inl hyz => exact Or.inr ⟨hxy.1, s.le_trans _ _ _ hxy.2 hyz⟩ 
                                                              | inr hyz => exact Or.inr ⟨hxy.1, hyz.2⟩



lemma oneStepUpAux_AntisymmRel (s : Preorder α) {a b : α} (hab : ¬(s.le a b) ∧ ¬(s.le b a)) (x y : α) :
AntisymmRel s.le x y ↔ AntisymmRel (oneStepUpAux s a b) x y := by
  unfold oneStepUpAux
  unfold AntisymmRel
  have hne := ne_of_noncomp s hab.1
  by_cases hxa : x=a
  . simp only [hxa, dite_eq_ite, _root_.le_refl, true_or, true_and, ite_true, ite_self]
    by_cases hya : y=a
    . simp only [hya, _root_.le_refl, and_self, true_or, ite_self, true_and, ite_true]
    . simp only [hya, ite_false]
      by_cases hyb : y=b
      . simp only [hyb, _root_.le_refl, or_true, ite_self, and_self, or_self, ite_true, and_false, iff_false, not_and]
        exact fun _ => hab.2
      . simp only [hyb, ite_false, hne]
        constructor
        . exact fun h => ⟨Or.inl h.1, Or.inl h.2⟩
        . exact fun h => by match h with
                            | ⟨Or.inl hay, Or.inl hya⟩ => exact ⟨hay,hya⟩
                            | ⟨Or.inl hay, Or.inr hya⟩ => exact ⟨hay, hya.1⟩
                            | ⟨Or.inr hby, Or.inl hya⟩ => by_contra; exact hab.2 (s.le_trans _ _ _ hby hya)
                            | ⟨Or.inr _, Or.inr hya⟩ => by_contra; exact hab.2 hya.2
  . simp only [hxa, dite_eq_ite, ite_false]
    by_cases hxb : x=b
    . simp only [hxb, _root_.le_refl, or_true, ite_true, ite_self, and_true]
      by_cases hya : y=a
      . simp only [hya, ite_true, _root_.le_refl, true_or, ite_self, and_true, iff_false, not_and]
        exact fun _ => hab.1
      . simp only [hya, ite_false, and_congr_right_iff]
        by_cases hyb : y=b
        . simp only [hyb, _root_.le_refl, or_true, ite_self, forall_true_left]
        . simp only [hyb, ite_false]
          exact fun h => by constructor
                            . exact fun h' => Or.inr h'
                            . exact fun h' => by cases h' with
                                                 | inl hya => by_contra; exact hab.2 (s.le_trans _ _ _ h hya)
                                                 | inr hyb => exact hyb
    . simp only [hxb, ite_false]
      by_cases hya : y=a
      . simp only [hya, hne, hab.2, and_false, or_false, ite_false, _root_.le_refl, true_and, ite_self,
          and_congr_right_iff]
        exact fun h => by constructor
                          . exact fun h' => Or.inl h'
                          . exact fun h' => by cases h' with 
                                               | inl hax => exact hax
                                               | inr hbx => by_contra; exact hab.2 (s.le_trans _ _ _ hbx h)
      . simp only [hya, ite_false]
        by_cases hyb : y=b
        . simp only [hyb, _root_.le_refl, and_true, ite_true, and_congr_left_iff]
          exact fun h => by constructor
                            . exact fun h' => Or.inr h'
                            . exact fun h' => by cases h' with
                                                 | inl hxa => by_contra; exact hab.2 (s.le_trans _ _ _ h hxa)
                                                 | inr hxb => exact hxb
        . simp only [hyb, ite_false]
          constructor
          . exact fun h => ⟨Or.inl h.1, Or.inl h.2⟩
          . exact fun h => by match h with
                              | ⟨Or.inl hxy, Or.inl hyx⟩ => exact ⟨hxy, hyx⟩
                              | ⟨Or.inl hxy, Or.inr hyx⟩ => by_contra; exact hab.2 (s.le_trans _ _ _ hyx.2 (s.le_trans _ _ _ hxy hyx.1))
                              | ⟨Or.inr hxy, Or.inl hyx⟩ => by_contra; exact hab.2 (s.le_trans _ _ _ hxy.2 (s.le_trans _ _ _ hyx hxy.1))
                              | ⟨Or.inr hxy, Or.inr hyx⟩ => by_contra; exact hab.2 (s.le_trans _ _ _ hxy.2 hyx.1)



def oneStepUp (s : Preorder α) {a b : α} (hab : ¬(s.le a b) ∧ ¬(s.le b a)) : Preorder α where
le := fun x y => oneStepUpAux s a b x y
lt := fun x y => (oneStepUpAux s a b x y) ∧ ¬(oneStepUpAux s a b y x)
le_refl:= oneStepUpAux_refl s a b 
le_trans := oneStepUpAux_trans s hab
lt_iff_le_not_le := fun x y => by rfl


lemma oneStepUp_AntisymmRel (s : Preorder α) {a b : α} (hab : ¬(s.le a b) ∧ ¬(s.le b a)):
AntisymmRel s.le = AntisymmRel (oneStepUp s hab).le  := by
  ext x y
  exact oneStepUpAux_AntisymmRel s hab x y


/- We prove that oneStepUp s is indeed greater than s. -/

lemma oneStepUp_is_greater (s : Preorder α) {a b : α} (hab : ¬(s.le a b) ∧ ¬(s.le b a)) :
s < (oneStepUp s hab) :=by 
  rw [lt_iff_le_and_ne]
  constructor
  . intro x y hsxy
    change oneStepUpAux s a b x y
    unfold oneStepUpAux
    by_cases hxa : x=a
    . simp only [hxa, dite_eq_ite, _root_.le_refl, true_or, true_and, ite_true]
      by_cases hyb : y=b
      . simp only [hyb, _root_.le_refl, or_true, ite_self]
      . simp only [hyb, ite_false]
        rw [hxa] at hsxy; exact Or.inl hsxy
    . simp only [hxa, dite_eq_ite, ite_false]
      by_cases hxb : x=b
      . simp only [hxb, _root_.le_refl, or_true, ite_true]
        by_cases hya : y=a
        . simp only [hya, ite_true]
          rw [hxb, hya] at hsxy; exact hab.2 hsxy
        . simp only [hya, ite_false]
          rw [hxb] at hsxy; exact hsxy
      . simp only [hxb, ite_false]
        by_cases hyb : y=b
        . simp only [hyb, _root_.le_refl, and_true, ite_true]
          rw [hyb] at hsxy; exact Or.inr hsxy
        . simp only [hyb, ite_false]
          exact Or.inl hsxy
  . have hle : (oneStepUp s hab).le a b := by 
      change oneStepUpAux s a b a b
      unfold oneStepUpAux
      simp only [_root_.le_refl, or_true, dite_eq_ite, true_or, and_self, ite_true]
    by_contra heq
    rw [←heq] at hle
    exact hab.1 hle 


/- We introduce the set of preorders that are greater than or equal to s and have the same antisymmetrization and prove that 
a maximal element of that set is necessarily total. -/

def greaterSameAntisymmRel (s : Preorder α) : Set (Preorder α) := {r : Preorder α | s ≤ r ∧ AntisymmRel s.le = AntisymmRel r.le}

lemma self_is_in_GreaterSameAntisymmRel (s : Preorder α) : s ∈ greaterSameAntisymmRel s := ⟨le_refl s, rfl⟩

lemma greaterSameAntisymmRel_trans {s t u : Preorder α} (hst : t ∈ greaterSameAntisymmRel s) 
(htu : u ∈ greaterSameAntisymmRel t) : u ∈ greaterSameAntisymmRel s := 
⟨@le_trans (Preorder α) _ _ _ _ hst.1 htu.1, Eq.trans hst.2 htu.2⟩

lemma oneStepUp_is_in_GreaterSameAntisymmRel (s : Preorder α) {a b : α} (hab : ¬(s.le a b) ∧ ¬(s.le b a)) :
oneStepUp s hab ∈ greaterSameAntisymmRel s :=
⟨le_of_lt (oneStepUp_is_greater s hab), oneStepUp_AntisymmRel s hab⟩

lemma maximal_element_of_GreaterSameAntisymmRel_is_total {s t : Preorder α} (hst : t ∈ greaterSameAntisymmRel s)
(hmax : ∀ (u : Preorder α), u ∈ greaterSameAntisymmRel s → t ≤ u → u=t) : Total t.le := by
  unfold Total
  by_contra habs
  push_neg at habs
  match habs with
  | ⟨a,b,hab⟩ => have hsu := greaterSameAntisymmRel_trans hst (oneStepUp_is_in_GreaterSameAntisymmRel t hab)
                 have hlt := oneStepUp_is_greater t hab
                 exact (Ne.symm (ne_of_lt hlt)) (hmax (oneStepUp t hab) hsu (le_of_lt hlt))


/- Now we prove that the set greaterSameAntisymmRel s is inductive (i.e. every chain is bounded).-/

/- We introduce what will be the upper bound of a chain c. -/

def upperBoundChain_greaterSameAntisymmRel_aux (c : Set (Preorder α)) : α → α → Prop :=
fun a b => (∃ (p : Preorder α), p ∈ c ∧ p.le a b)


lemma upperBoundChain_greaterSameAntisymmRel_aux_refl {c : Set (Preorder α)} (hne : c.Nonempty) (a : α) : 
upperBoundChain_greaterSameAntisymmRel_aux c a a := by
  cases hne with
  | intro p hp => exact ⟨p,⟨hp, p.le_refl a⟩⟩


lemma upperBoundChain_greaterSameAntisymmRel_aux_trans {c : Set (Preorder α)} (hchain : IsChain LE.le c) (x y z : α) : 
upperBoundChain_greaterSameAntisymmRel_aux c x y → upperBoundChain_greaterSameAntisymmRel_aux c y z → 
upperBoundChain_greaterSameAntisymmRel_aux c x z := by
  intro hab hbc
  match hab, hbc with
  | ⟨p,hp⟩, ⟨q,hq⟩ => by_cases heq : p=q
                      . exists p
                        rw [←heq] at hq
                        exact ⟨hp.1, p.le_trans _ _ _ hp.2 hq.2⟩
                      . cases (hchain hp.1 hq.1 heq) with
                        | inl hpq => exact ⟨q, ⟨hq.1, q.le_trans _ _ _ (hpq _ _ hp.2) hq.2⟩⟩
                        | inr hqp => exact ⟨p, ⟨hp.1, p.le_trans _ _ _ hp.2 (hqp _ _ hq.2)⟩⟩


lemma upperBoundChain_greaterSameAntisymmRel_aux_AntisymmRel (s : Preorder α) {c : Set (Preorder α)} 
(hc : c ⊆ greaterSameAntisymmRel s)
(hchain : IsChain LE.le c) (hne : c.Nonempty) (a b : α) :
AntisymmRel s.le a b ↔ AntisymmRel (upperBoundChain_greaterSameAntisymmRel_aux c) a b := by
  constructor
  . intro hs
    unfold AntisymmRel
    cases hne with
    | intro p hp => rw [(hc hp).2] at hs
                    constructor
                    . exact ⟨p, ⟨hp, hs.1⟩⟩ 
                    . exact ⟨p, ⟨hp, hs.2⟩⟩
  . intro hupc
    match hupc.1, hupc.2 with
    | ⟨p,hp⟩, ⟨q,hq⟩ => by_cases heq : p=q
                        . rw [←heq] at hq
                          rw [(hc hp.1).2]
                          exact ⟨hp.2, hq.2⟩
                        . cases (hchain hp.1 hq.1 heq) with
                          | inl hpq => rw [(hc hq.1).2]
                                       exact ⟨hpq _ _ hp.2, hq.2⟩
                          | inr hqp => rw [(hc hp.1).2]
                                       exact ⟨hp.2, hqp _ _ hq.2⟩

def upperBoundChain_greaterSameAntisymmRel {c : Set (Preorder α)} (hchain : IsChain LE.le c) (hne : c.Nonempty) : Preorder α where
le := fun x y => upperBoundChain_greaterSameAntisymmRel_aux c x y
lt := fun x y => (upperBoundChain_greaterSameAntisymmRel_aux c x y) ∧ ¬(upperBoundChain_greaterSameAntisymmRel_aux c y x)
le_refl:= upperBoundChain_greaterSameAntisymmRel_aux_refl hne
le_trans := upperBoundChain_greaterSameAntisymmRel_aux_trans hchain
lt_iff_le_not_le := fun x y => by rfl

lemma upperBoundChain_greaterSameAntisymmRel_AntisymmRel (s : Preorder α) {c : Set (Preorder α)}
(hc : c ⊆ greaterSameAntisymmRel s) (hchain : IsChain LE.le c) (hne : c.Nonempty) :
AntisymmRel s.le = AntisymmRel (upperBoundChain_greaterSameAntisymmRel hchain hne).le := by
  ext a b
  exact upperBoundChain_greaterSameAntisymmRel_aux_AntisymmRel s hc hchain hne a b

lemma upperBoundChain_greaterSameAntisymmRel_greater (s : Preorder α) {c : Set (Preorder α)}
(hc : c ⊆ greaterSameAntisymmRel s) (hchain : IsChain LE.le c) (hne : c.Nonempty) :
s ≤ upperBoundChain_greaterSameAntisymmRel hchain hne := by
  intro a b hsab
  cases hne with
  |intro p hp => exact ⟨p, ⟨hp, (hc hp).1 _ _ hsab⟩⟩

lemma upperBoundChain_greaterSameAntisymmRel_member (s : Preorder α) {c : Set (Preorder α)}
(hc : c ⊆ greaterSameAntisymmRel s) (hchain : IsChain LE.le c) (hne : c.Nonempty) :
upperBoundChain_greaterSameAntisymmRel hchain hne  ∈ greaterSameAntisymmRel s :=
⟨upperBoundChain_greaterSameAntisymmRel_greater s hc hchain hne,
 upperBoundChain_greaterSameAntisymmRel_AntisymmRel s hc hchain hne⟩

lemma upperBoundChain_greaterSameAntisymmRel_maximal {c : Set (Preorder α)} (hchain : IsChain LE.le c) (hne : c.Nonempty) :
∀ (t : Preorder α), t ∈ c → t ≤ upperBoundChain_greaterSameAntisymmRel hchain hne := fun t htc _ _  ht => ⟨t, ⟨htc, ht⟩⟩

lemma greaterSameAntisymmRel_inductive (s : Preorder α) : ∀ (c : Set (Preorder α)), (c ⊆ greaterSameAntisymmRel s) →
IsChain (fun s t => s ≤ t) c → ∃ (ub : Preorder α), (ub ∈ greaterSameAntisymmRel s) ∧ ∀ (t : Preorder α), t ∈ c → t ≤ ub := by
  intro c hc hchain
  by_cases hne : c.Nonempty
  . exact ⟨upperBoundChain_greaterSameAntisymmRel hchain hne, ⟨upperBoundChain_greaterSameAntisymmRel_member s hc hchain hne,
      upperBoundChain_greaterSameAntisymmRel_maximal hchain hne⟩⟩
  . exists s, self_is_in_GreaterSameAntisymmRel s
    intro t htc
    exfalso
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne] at htc
    rw [Set.mem_empty_iff_false] at htc
    exact htc 



/- Finally we prove the preorder extension principle, by applying Zorn's lemma. -/

lemma extension_principle (s : Preorder α) : ∃ (t : Preorder α), t ∈ greaterSameAntisymmRel s ∧ Total t.le := by
  cases (zorn_partialOrder₀ (greaterSameAntisymmRel s) (greaterSameAntisymmRel_inductive s)) with
  | intro t ht => exact ⟨t, ⟨ht.1, maximal_element_of_GreaterSameAntisymmRel_is_total ht.1 ht.2⟩⟩


/- We deduce the preorder extension principle, by first proving that a preorder is a partial if and only if its associated
AntisymmRel is equality.-/

lemma AntisymmRel_eq_Eq_iff_antisymm (r : α → α → Prop) (hrefl : ∀  (a : α), r a a) :
AntisymmRel r = Eq  ↔ IsAntisymm α r := by
  constructor
  . intro hr
    exact {antisymm := fun a b hab hba => by have hra : AntisymmRel r a b := ⟨hab, hba⟩
                                             rw [hr] at hra
                                             exact hra}
  . intro hr
    ext a b
    unfold AntisymmRel
    constructor
    . exact fun hab => hr.antisymm _ _ hab.1 hab.2
    . exact fun hab => by rw [hab]; exact ⟨hrefl _, hrefl _⟩

lemma extension_principle_partialOrder (s : PartialOrder α) : ∃ (t : LinearOrder α), 
--@PartialOrder.toPreorder α s ≤ @PartialOrder.toPreorder α (@LinearOrder.toPartialOrder α t) := by
∀ (a b : α), s.le a b → t.le a b := by
 cases (extension_principle (@PartialOrder.toPreorder α s)) with
 | intro r hr => have hra := (AntisymmRel_eq_Eq_iff_antisymm s.le s.le_refl).mpr {antisymm := s.le_antisymm} 
                 unfold greaterSameAntisymmRel at hr
                 simp only [Set.mem_setOf_eq] at hr
                 rw [hra] at hr
                 have hranti := (AntisymmRel_eq_Eq_iff_antisymm r.le r.le_refl).mp (Eq.symm hr.1.2)
                 set p : PartialOrder α := {r with le_antisymm := hranti.antisymm}
                 have hptot : IsTotal α p.le := {total := hr.2}
                 set t:= @AsLinearOrder.linearOrder α p hptot
                 exact ⟨t, hr.1.1⟩
-/


/- We prove a version of the extension principle where we extend the partial order while preserving a lower set.-/

namespace Preorder 

lemma extension_principle_with_lowerset (s : PartialOrder α) {I : Set α} (hI : @IsLowerSet α {le := s.le} I) :
∃ (t : LinearOrder α), (∀ (a b : α), s.le a b → t.le a b) ∧ @IsLowerSet α {le := t.le} I := by
  set t₁ := @instLinearOrderLinearExtension I (@PartialOrder.lift I α s (fun (a : I) => ↑a) Subtype.coe_injective)
  set t₂ := @instLinearOrderLinearExtension I.compl (@PartialOrder.lift I.compl α s (fun (a : I.compl) => ↑a) Subtype.coe_injective)
  set t':= @Sum.Lex.linearOrder (LinearExtension ↑I) (LinearExtension ↑I.compl) t₁ t₂ 
  set f : α → Lex ((LinearExtension ↑I) ⊕ (LinearExtension ↑I.compl)) := 
      fun a => by by_cases ha : a ∈ I
                  . exact toLex (Sum.inl (toLinearExtension ⟨a,ha⟩))  
                  . exact toLex (Sum.inr (toLinearExtension ⟨a,ha⟩))
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



