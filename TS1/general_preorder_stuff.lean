import Mathlib.Tactic 
import Mathlib.Init.Algebra.Order
import Mathlib.Order.Antisymmetrization
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Extension.Linear
import Mathlib.Data.Sum.Order
import Mathlib.Order.WellFounded
import Mathlib.Order.RelIso.Basic
import Mathlib.Order.SuccPred.Basic
import Mathlib.Order.LocallyFinite
import Mathlib.Order.SuccPred.LinearLocallyFinite
import Mathlib.Data.Set.Image
import Mathlib.Order.PFilter
import Mathlib.Order.Zorn 



set_option autoImplicit false


open Classical 

universe u 

variable {α : Type u}


/- Some lemmas for total preorders. -/

lemma TotalPreorder_trichotomy {s : Preorder α} (htot : Total s.le) (a b : α) :
s.lt a b ∨ s.lt b a ∨ AntisymmRel s.le a b := by
  by_cases hltab : s.lt a b
  . exact Or.inl hltab
  . by_cases hltba : s.lt b a 
    . exact Or.inr (Or.inl hltba)
    . rw [s.lt_iff_le_not_le] at hltab hltba
      push_neg at hltab hltba
      cases (htot a b) with
      | inl hab => exact Or.inr (Or.inr ⟨hab, hltab hab⟩)
      | inr hba => exact Or.inr (Or.inr ⟨hltba hba, hba⟩)


lemma LinearPreorder_trichotomy {s : Preorder α} (hlin : IsLinearOrder α s.le) (a b : α) :
s.lt a b ∨ s.lt b a ∨ a=b := by
  have halmost := TotalPreorder_trichotomy hlin.toIsTotal.total a b
  rw [@antisymmRel_iff_eq α s.le {refl := s.le_refl} hlin.toIsPartialOrder.toIsAntisymm a b] at halmost 
  exact halmost 


lemma TotalPreorder_lt_iff_not_le {s : Preorder α} (htot : Total s.le) {a b : α} : ¬(s.le a b) ↔ s.lt b a := by
  rw [s.lt_iff_le_not_le]
  simp only [iff_and_self]
  intro hnab
  cases (htot a b) with
  | inl hab => exfalso; exact hnab hab  
  | inr hba => exact hba 


/- For s a preorder, we have a SuccOrder on s if and only if we have one on the antisymmetrization of s. (Same for PredOrders, but
I'm not sure I have the courage to do battle with duality.)-/

noncomputable def SuccOrdertoAntisymmetrization {s : Preorder α} (hsucc : @SuccOrder α s) : @SuccOrder (Antisymmetrization α s.le)
(@PartialOrder.toPreorder _ (@instPartialOrderAntisymmetrizationLeToLEInstIsPreorderLeToLE α s)) where
succ := fun x => toAntisymmetrization s.le (hsucc.succ (ofAntisymmetrization s.le x))
le_succ := fun x => by rw [←(toAntisymmetrization_ofAntisymmetrization s.le x), toAntisymmetrization_le_toAntisymmetrization_iff]
                       rw [toAntisymmetrization_ofAntisymmetrization]
                       exact hsucc.le_succ _ 
max_of_succ_le := fun hx => by rename_i x
                               intro y hyx
                               rw [←(toAntisymmetrization_ofAntisymmetrization s.le x)] at hyx hx |-
                               rw [←(toAntisymmetrization_ofAntisymmetrization s.le y)] at hyx |-
                               rw [toAntisymmetrization_le_toAntisymmetrization_iff] at hyx hx |-
                               rw [toAntisymmetrization_ofAntisymmetrization] at hx 
                               exact hsucc.max_of_succ_le hx hyx 
succ_le_of_lt := fun hxy => by rename_i x y
                               rw [←(toAntisymmetrization_ofAntisymmetrization s.le x), ←(toAntisymmetrization_ofAntisymmetrization s.le y)]
                                 at hxy |-
                               rw [toAntisymmetrization_le_toAntisymmetrization_iff]
                               rw [toAntisymmetrization_lt_toAntisymmetrization_iff] at hxy
                               rw [toAntisymmetrization_ofAntisymmetrization]
                               exact hsucc.succ_le_of_lt hxy
le_of_lt_succ := fun hxy => by rename_i x y 
                               rw [←(toAntisymmetrization_ofAntisymmetrization s.le x)] at hxy |- 
                               rw [←(toAntisymmetrization_ofAntisymmetrization s.le y)]
                               rw [toAntisymmetrization_le_toAntisymmetrization_iff]  
                               rw [toAntisymmetrization_lt_toAntisymmetrization_iff] at hxy 
                               exact hsucc.le_of_lt_succ hxy 

noncomputable def SuccOrderofAntisymmetrization {s : Preorder α} (hsucc : @SuccOrder (Antisymmetrization α s.le)
(@PartialOrder.toPreorder _ (@instPartialOrderAntisymmetrizationLeToLEInstIsPreorderLeToLE α s))) : @SuccOrder α s where 
succ := fun a => ofAntisymmetrization s.le (hsucc.succ (toAntisymmetrization s.le a))
le_succ := fun a => by rw [←(toAntisymmetrization_le_toAntisymmetrization_iff), toAntisymmetrization_ofAntisymmetrization]
                       exact hsucc.le_succ (toAntisymmetrization s.le a) 
max_of_succ_le := fun ha => by intro b hba 
                               rw [←(toAntisymmetrization_le_toAntisymmetrization_iff)] at hba ha |- 
                               rw [toAntisymmetrization_ofAntisymmetrization] at ha 
                               exact hsucc.max_of_succ_le ha hba  
succ_le_of_lt := fun hab => by rw [←toAntisymmetrization_le_toAntisymmetrization_iff]
                               rw [←toAntisymmetrization_lt_toAntisymmetrization_iff] at hab 
                               rw [toAntisymmetrization_ofAntisymmetrization]
                               exact hsucc.succ_le_of_lt hab 
le_of_lt_succ := fun hab => by rw [←toAntisymmetrization_le_toAntisymmetrization_iff]
                               rw [←toAntisymmetrization_lt_toAntisymmetrization_iff] at hab
                               rw [toAntisymmetrization_ofAntisymmetrization] at hab 
                               exact hsucc.le_of_lt_succ hab 

/- We define essentially locally finite preorders; these are preorders whose antisymmetrization is locally finite.-/

def EssentiallyLocallyFinitePreorder (s : Preorder α) := @LocallyFiniteOrder _ 
(@PartialOrder.toPreorder _ (@instPartialOrderAntisymmetrizationLeToLEInstIsPreorderLeToLE α s))

/- For any preorder s,  "locally finite" implies "essentially locally finite" (Of course, if s is a partial order then they are
equivalent. )-/

noncomputable def EssentiallyLocallyFinite_ofLocallyFinite {s : Preorder α} (hLF : @LocallyFiniteOrder α s) : 
EssentiallyLocallyFinitePreorder s := by
  letI : Preorder α := s 
  have hIfin : ∀ (x y : Antisymmetrization α s.le), (Set.Icc x y).Finite := by
    intro x y
    have himage : Set.Icc x y = Set.image (toAntisymmetrization s.le) (Set.Icc (ofAntisymmetrization s.le x) (ofAntisymmetrization s.le y)) := by
      ext z 
      simp only [ge_iff_le, gt_iff_lt, Set.mem_Icc, ofAntisymmetrization_le_ofAntisymmetrization_iff,
          ofAntisymmetrization_lt_ofAntisymmetrization_iff, Set.mem_image]
      constructor
      . intro hz 
        exists ofAntisymmetrization s.le z 
        rw [ofAntisymmetrization_le_ofAntisymmetrization_iff, ofAntisymmetrization_le_ofAntisymmetrization_iff,
             toAntisymmetrization_ofAntisymmetrization]
        exact ⟨hz, by rfl⟩
      . intro hz
        match hz with 
        | ⟨a,⟨⟨hxa, hay⟩, haz⟩⟩ => rw [←toAntisymmetrization_le_toAntisymmetrization_iff, toAntisymmetrization_ofAntisymmetrization,
                                        haz] at hxa hay  
                                   exact ⟨hxa, hay⟩
    rw [himage, ←Set.finite_coe_iff]
    apply Finite.Set.finite_image _ (toAntisymmetrization s.le) 
  set finsetIcc := fun x y => Set.Finite.toFinset (hIfin x y) 
  unfold EssentiallyLocallyFinitePreorder
  apply LocallyFiniteOrder.ofIcc' _ finsetIcc 
  intro x y z 
  simp only [ge_iff_le, gt_iff_lt, Set.Finite.mem_toFinset, Set.mem_Icc]
  


/- A total essentially locally finite preorder is a SuccOrder (and also a PredOrder, but I didn't write it). This us because the
antisymmetrization partial order is a linear locally finite order. -/

noncomputable def TotalELFP_SuccOrder {s : Preorder α} (htot : Total s.le) (ELPF : EssentiallyLocallyFinitePreorder s) : @SuccOrder α s := 
SuccOrderofAntisymmetrization (@LinearLocallyFiniteOrder.instSuccOrderToPreorderToPartialOrderToSemilatticeInfToLatticeInstDistribLattice _ 
  (@instLinearOrderAntisymmetrizationLeToLEInstIsPreorderLeToLE α s _ _ {total := htot}) ELPF) 


/- Essentially locally finite preorders are also (dually) well-founded on bounded intervals. I could deduce this from the fact that the
antisymmetrization is, but I don't want to mess around showing that the antisymmetrization of an interval is an interval in the
antisymmetrization and playing with saturations, so I'll just do it directly using the "existence of max" criterion. -/

lemma ELFP_is_locally_WellFounded {s : Preorder α} (ELPF : EssentiallyLocallyFinitePreorder s) (a b : α) :
∀ (E : Set α), Set.Nonempty E → (∀ (c : α), c ∈ E → (s.le a c ∧ s.le c b)) → ∃ (m : α), m ∈ E ∧ ∀ (c : α), c ∈ E → ¬(s.lt m c) := by
  intro E hEne hEboun 
  have hfin : Finite (Set.image (toAntisymmetrization s.le) E) := by  
    set I := ELPF.finsetIcc (toAntisymmetrization s.le a) (toAntisymmetrization s.le b) with hIdef 
    have hinc : Set.image (toAntisymmetrization s.le) E ⊆ ↑I := by rw [Set.subset_def]
                                                                   intro x hx 
                                                                   rw [hIdef]
                                                                   rw [Finset.mem_coe, ELPF.finset_mem_Icc]
                                                                   simp only [Set.mem_image] at hx
                                                                   cases hx with
                                                                   | intro c hc => rw [←hc.2, toAntisymmetrization_le_toAntisymmetrization_iff,
                                                                                        toAntisymmetrization_le_toAntisymmetrization_iff]
                                                                                   exact hEboun c hc.1
    refine Finite.of_injective (fun x => (⟨x.1, hinc x.2⟩ : ↑I)) (fun x y hxy => by simp only [Subtype.mk.injEq] at hxy
                                                                                    rw [Subtype.mk.injEq]
                                                                                    exact hxy)
  have hne : Nonempty (Set.image (toAntisymmetrization s.le) E) := by
    rw [Set.nonempty_coe_sort, Set.nonempty_image_iff] 
    exact hEne 
  set x:= WellFounded.min ((@Finite.Preorder.wellFounded_gt _ hfin (@Subtype.preorder _ (@PartialOrder.toPreorder _ 
     (@instPartialOrderAntisymmetrizationLeToLEInstIsPreorderLeToLE α s)) _))) Set.univ (@Set.univ_nonempty _ hne)
  have hxE := x.2 
  simp only [Set.mem_image] at hxE
  cases hxE with
  | intro c hc => exists c 
                  constructor
                  . exact hc.1
                  . exact fun d hdE => by rw [←toAntisymmetrization_lt_toAntisymmetrization_iff]
                                          have hdE' : toAntisymmetrization s.le d ∈ Set.image (toAntisymmetrization s.le) E := by
                                            simp only [Set.mem_image]
                                            exists d 
                                          rw [hc.2] 
                                          exact @WellFounded.not_lt_min _ _ ((@Finite.Preorder.wellFounded_gt _ hfin (@Subtype.preorder _ 
                                            (@PartialOrder.toPreorder _ (@instPartialOrderAntisymmetrizationLeToLEInstIsPreorderLeToLE α s)) 
                                            _))) Set.univ (@Set.univ_nonempty _ hne) ⟨toAntisymmetrization s.le d, hdE'⟩ (Set.mem_univ _)



/- Let's define a partial order on preorders (we just lift the existing partial order on relations). Maybe this
is already in mathlib somewhere ? -/

instance instPreorder.le : LE (Preorder α) :=
  ⟨fun r s =>  ∀ ⦃a b : α⦄, r.le a b → s.le a b⟩

instance Preorder.PartialOrder : PartialOrder (Preorder α) where
le := (. ≤ .)
lt r s := r ≤ s ∧ ¬(s ≤ r)
le_refl r := fun _ _ h => h  
le_trans r s t := fun hrs hst => fun _ _ h => hst (hrs h) 
lt_iff_le_not_le _ _ := Iff.rfl 
le_antisymm r s := fun hrs hsr => by apply Preorder.ext; 
                                     exact fun _ _ => ⟨fun h => hrs h, fun h => hsr h⟩  





namespace Preorder 

/- We give a name to the biggest element of this partial order, which is the trivial preorder on α (i.e. any
two elements are comparable).-/

def trivialPreorder (α : Type _): Preorder α where
le := fun _ _ => True
lt := fun _ _ => False
le_refl := fun _ => trivial 
le_trans := fun _ _ _ _ _ => trivial 
lt_iff_le_not_le := fun _ _ => by simp

lemma trivialPreorder_is_greatest (s : Preorder α) : s ≤ trivialPreorder α := by
  intro a b 
  unfold trivialPreorder
  simp only [le_Prop_eq, implies_true]

lemma nontrivial_preorder_iff_exists_not_le (s : Preorder α) :
(s ≠ trivialPreorder α) ↔ (∃ (a b : α), ¬(s.le a b)) := by
  constructor
  . contrapose!
    exact fun hs => by ext a b; exact ⟨(fun _ => by triv), fun _ => hs a b⟩
  . contrapose!
    exact fun hs => by rw [hs]; exact fun _ _ => by triv


/- If we have preorders r,s such that r ≤ s, then AntisymmRel r ≤ AntisymmRel s.-/

lemma AntisymmRel_monotone {r s : Preorder α} (hrs : r ≤ s) : ∀ {a b : α},
AntisymmRel r.le a b → AntisymmRel s.le a b :=
fun hab => ⟨hrs hab.1, hrs hab.2⟩

/- So we get a function from the antisymmetrization of r to that of s by sending x to toAntisymmetrization s.le (ofAntisymmetrization r.le x).-/

noncomputable def AntisymmetrizationtoAntisymmetrization (r s : Preorder α) : 
@Antisymmetrization α r.le (@instIsPreorderLeToLE α r) → @Antisymmetrization α s.le (@instIsPreorderLeToLE α s) :=
fun x => @toAntisymmetrization α s.le (@instIsPreorderLeToLE α s) (@ofAntisymmetrization α r.le (@instIsPreorderLeToLE α r) x) 

lemma AntisymmetrizationtoAntisymmetrization_lift {r s : Preorder α} (hrs : r ≤ s) (a : α) :
@toAntisymmetrization α s.le (@instIsPreorderLeToLE α s) a = AntisymmetrizationtoAntisymmetrization r s (@toAntisymmetrization α r.le 
(@instIsPreorderLeToLE α r) a) := by
  unfold AntisymmetrizationtoAntisymmetrization 
  apply Quotient.sound 
  apply AntisymmRel_monotone hrs 
  letI : Preorder α := r 
  rw [←AntisymmRel.setoid_r] 
  apply Quotient.exact 
  change toAntisymmetrization r.le a = toAntisymmetrization r.le (ofAntisymmetrization r.le (toAntisymmetrization r.le a))
  rw [toAntisymmetrization_ofAntisymmetrization]

lemma AntisymmetrizationtoAntisymmetrization_surjective {r s : Preorder α} (hrs : r ≤ s) : 
Function.Surjective (AntisymmetrizationtoAntisymmetrization r s) := by
  intro x 
  exists @toAntisymmetrization α r.le (@instIsPreorderLeToLE α r) (@ofAntisymmetrization α s.le (@instIsPreorderLeToLE α s) x)
  rw [←AntisymmetrizationtoAntisymmetrization_lift, toAntisymmetrization_ofAntisymmetrization]
  exact hrs 

lemma AntisymmetrizationtoAntisymmetrization_monotone {r s : Preorder α} (hrs : r ≤ s) : 
@Monotone _ _ (@PartialOrder.toPreorder _ (@instPartialOrderAntisymmetrizationLeToLEInstIsPreorderLeToLE α r)) 
(@PartialOrder.toPreorder _ (@instPartialOrderAntisymmetrizationLeToLEInstIsPreorderLeToLE α s)) 
(AntisymmetrizationtoAntisymmetrization r s) := by
  intro x y hxy 
  rw [←(@toAntisymmetrization_ofAntisymmetrization α r.le (@instIsPreorderLeToLE α r) x)]
  rw [←(@toAntisymmetrization_ofAntisymmetrization α r.le (@instIsPreorderLeToLE α r) y)]
  rw [←(AntisymmetrizationtoAntisymmetrization_lift hrs), ←(AntisymmetrizationtoAntisymmetrization_lift hrs)]
  rw [toAntisymmetrization_le_toAntisymmetrization_iff]
  rw [←(@ofAntisymmetrization_le_ofAntisymmetrization_iff α r x y)] at hxy 
  exact hrs hxy
  


lemma AntisymmetrizationtoAntisymmetrization_image_interval {r s : Preorder α} (hrs : r ≤ s) (hrtot : Total r.le) {a b : α} (hrab : r.le a b) :
Set.image (AntisymmetrizationtoAntisymmetrization r s) 
(@Set.Icc _ (@PartialOrder.toPreorder _ (@instPartialOrderAntisymmetrizationLeToLEInstIsPreorderLeToLE α r)) 
(@toAntisymmetrization α r.le (@instIsPreorderLeToLE α r) a) (@toAntisymmetrization α r.le (@instIsPreorderLeToLE α r) b)) =
(@Set.Icc _ (@PartialOrder.toPreorder _ (@instPartialOrderAntisymmetrizationLeToLEInstIsPreorderLeToLE α s)) 
(@toAntisymmetrization α s.le (@instIsPreorderLeToLE α s) a) (@toAntisymmetrization α s.le (@instIsPreorderLeToLE α s) b)) := by
  ext z 
  constructor
  . simp only [Set.mem_image, ge_iff_le, toAntisymmetrization_le_toAntisymmetrization_iff, gt_iff_lt,
      toAntisymmetrization_lt_toAntisymmetrization_iff, Set.mem_Icc, forall_exists_index, and_imp]
    intro t ht hzt 
    unfold Set.Icc at ht
    simp only [Set.mem_setOf_eq] at ht
    rw [←hzt]
    rw [AntisymmetrizationtoAntisymmetrization_lift hrs a, AntisymmetrizationtoAntisymmetrization_lift hrs b]
    exact ⟨AntisymmetrizationtoAntisymmetrization_monotone hrs ht.1, AntisymmetrizationtoAntisymmetrization_monotone hrs ht.2⟩ 
  . simp only [ge_iff_le, toAntisymmetrization_le_toAntisymmetrization_iff, gt_iff_lt,
      toAntisymmetrization_lt_toAntisymmetrization_iff, Set.mem_Icc, Set.mem_image, and_imp]
    intro haz hzb
    set c := @ofAntisymmetrization α s.le (@instIsPreorderLeToLE α s) z with hcdef 
    have hsac : s.le a c := by 
      rw [←(toAntisymmetrization_ofAntisymmetrization s.le z), ←hcdef, toAntisymmetrization_le_toAntisymmetrization_iff] at haz
      exact haz
    have hscb : s.le c b := by 
      rw [←(toAntisymmetrization_ofAntisymmetrization s.le z), ←hcdef, toAntisymmetrization_le_toAntisymmetrization_iff] at hzb
      exact hzb
    cases (hrtot a c) with 
    | inr hca => have hsym : AntisymmRel s.le a c := ⟨hsac, hrs hca⟩
                 exists @toAntisymmetrization α r.le (@instIsPreorderLeToLE α r) a
                 constructor
                 . unfold Set.Icc
                   simp only [Set.mem_setOf_eq]
                   rw [and_iff_right ((@instPartialOrderAntisymmetrizationLeToLEInstIsPreorderLeToLE α r).le_refl _)]
                   rw [@ toAntisymmetrization_le_toAntisymmetrization_iff α r _ _]
                   exact hrab
                 . rw [←(AntisymmetrizationtoAntisymmetrization_lift hrs)]
                   rw [←(toAntisymmetrization_ofAntisymmetrization s.le z), ←hcdef]
                   apply Quotient.sound 
                   rw [←AntisymmRel.setoid_r] at hsym
                   exact hsym  
    | inl hac => . cases (hrtot c b) with
                   | inr hbc => have hsym : AntisymmRel s.le b c := ⟨hrs hbc, hscb⟩
                                exists @toAntisymmetrization α r.le (@instIsPreorderLeToLE α r) b
                                constructor
                                . unfold Set.Icc
                                  simp only [Set.mem_setOf_eq]
                                  rw [and_iff_left ((@instPartialOrderAntisymmetrizationLeToLEInstIsPreorderLeToLE α r).le_refl _)]
                                  rw [@ toAntisymmetrization_le_toAntisymmetrization_iff α r _ _]
                                  exact hrab
                                . rw [←(AntisymmetrizationtoAntisymmetrization_lift hrs)]
                                  rw [←(toAntisymmetrization_ofAntisymmetrization s.le z), ←hcdef]
                                  apply Quotient.sound 
                                  rw [←AntisymmRel.setoid_r] at hsym
                                  exact hsym   
                   | inl hcb => exists @toAntisymmetrization α r.le (@instIsPreorderLeToLE α r) c 
                                constructor 
                                . unfold Set.Icc
                                  simp only [Set.mem_setOf_eq]
                                  rw [←hcdef]
                                  rw [@toAntisymmetrization_le_toAntisymmetrization_iff α r, 
                                      @toAntisymmetrization_le_toAntisymmetrization_iff α r]
                                  exact ⟨hac, hcb⟩
                                . rw [←(AntisymmetrizationtoAntisymmetrization_lift hrs), hcdef, toAntisymmetrization_ofAntisymmetrization]
  


/- We prove that total preorders form an upper set. -/

lemma Total_IsUpperSet : IsUpperSet {s : Preorder α | Total s.le} := by
  intro s t hst hstot a b
  cases (hstot a b) with
  | inl hsab => exact Or.inl (hst hsab)
  | inr hsba => exact Or.inr (hst hsba) 

/- And so do total essentially locally finite preorders. -/

noncomputable def TotalELPF_IsUpperSet {r s : Preorder α} (htot : Total r.le) (hELF : EssentiallyLocallyFinitePreorder r)
(hrs : r ≤ s) : EssentiallyLocallyFinitePreorder s := by
  have hIfin : ∀ (x y : @Antisymmetrization α s.le (@instIsPreorderLeToLE α s)), (@Set.Icc _ 
       (@PartialOrder.toPreorder _ (@instPartialOrderAntisymmetrizationLeToLEInstIsPreorderLeToLE α s)) x y).Finite := by
    intro x y
    letI : Preorder α := r
    cases htot (@ofAntisymmetrization α s.le (@instIsPreorderLeToLE α s) x) (@ofAntisymmetrization α s.le (@instIsPreorderLeToLE α s) y)
      with
      | inl  hrxy =>  rw [←Set.finite_coe_iff]
                      rw [←(@toAntisymmetrization_ofAntisymmetrization α s.le (@instIsPreorderLeToLE α s) x)]
                      rw [←(@toAntisymmetrization_ofAntisymmetrization α s.le (@instIsPreorderLeToLE α s) y)]
                      rw [←(AntisymmetrizationtoAntisymmetrization_image_interval hrs)]
                      have finI : Finite (Set.Icc (@toAntisymmetrization α r.le (@instIsPreorderLeToLE α r) (@ofAntisymmetrization α s.le 
                         (@instIsPreorderLeToLE α s) x)) (@toAntisymmetrization α r.le (@instIsPreorderLeToLE α r) (@ofAntisymmetrization α s.le 
                         (@instIsPreorderLeToLE α s) y))) := by
                        rw [←(@Finset.coe_Icc _ _ hELF)]
                        rw [Set.finite_coe_iff]
                        exact Finset.finite_toSet _  
                      exact @Finite.Set.finite_image _ _ _ _ finI  
                      exact htot
                      exact hrxy
      | inr hryx => by_cases hsxy : s.le (@ofAntisymmetrization α s.le (@instIsPreorderLeToLE α s) x)
                       (@ofAntisymmetrization α s.le (@instIsPreorderLeToLE α s) y)
                    . have hsym : AntisymmRel s.le  (@ofAntisymmetrization α s.le (@instIsPreorderLeToLE α s) x)
                        (@ofAntisymmetrization α s.le (@instIsPreorderLeToLE α s) y) := ⟨hsxy, hrs hryx⟩
                      have heq : x = y := by 
                        rw [←(@toAntisymmetrization_ofAntisymmetrization α s.le (@instIsPreorderLeToLE α s) x)]
                        rw [←(@toAntisymmetrization_ofAntisymmetrization α s.le (@instIsPreorderLeToLE α s) y)]
                        apply Quotient.sound
                        exact hsym 
                      rw [heq]
                      rw [@Set.Icc_self _ (@instPartialOrderAntisymmetrizationLeToLEInstIsPreorderLeToLE α s) y]
                      simp only [Set.finite_singleton]
                    . rw [TotalPreorder_lt_iff_not_le (Total_IsUpperSet hrs htot)] at hsxy
                      rw [@ofAntisymmetrization_lt_ofAntisymmetrization_iff _ s] at hsxy 
                      have he := @Set.Icc_eq_empty_of_lt _ (@PartialOrder.toPreorder _ 
                         (@instPartialOrderAntisymmetrizationLeToLEInstIsPreorderLeToLE α s)) _ _ hsxy 
                      rw [he]
                      exact Set.finite_empty 
  set finsetIcc := fun x y => Set.Finite.toFinset (hIfin x y) 
--    apply Nonempty.intro 
  apply LocallyFiniteOrder.ofIcc' _ finsetIcc 
  intro x y z 
  rw [Set.Finite.mem_toFinset]
  simp only [ge_iff_le, gt_iff_lt, Set.mem_Icc]


end Preorder

/- A preorder is called Noetherian if it has no infinite ascending chain.-/


def IsNoetherianPoset (α : Type u) [s : Preorder α] : Prop := WellFounded (fun a b => s.lt b a)
 

/- We introduce "maximal nonproper" order ideals, i.e. order ideals that are maximal among all
order ideals (not just the proper ones). This is only interesting when α is not known to be directed,
so ⊤ might not be an order ideal.-/

section

variable [Preorder α]


@[mk_iff]
class Order.Ideal.IsMaximalNonProper (I : Order.Ideal α) : Prop where
maximal_nonproper : ∀ ⦃J : Order.Ideal α⦄, I ≤ J → I = J 


/- Every order ideal is contained in a maximal nonproper order ideal. -/


lemma OrderIdeals_inductive_set : ∀ (c : Set (Order.Ideal α)), IsChain (fun I J => I ≤ J) c → ∀ (I : Order.Ideal α), 
I ∈ c → ∃ (ub : Order.Ideal α), ∀ (J : Order.Ideal α), J ∈ c → J ≤ ub := by 
  intro c hchain I hIc 
  set J := ⋃ (K : c), (K.1.carrier : Set α)  
  have hJdef : ∀ (K : Order.Ideal α), K ∈ c → (K : Set α) ⊆ J := by 
    intro K hKc 
    exact Set.subset_iUnion (fun (K : c) => (K : Set α)) ⟨K, hKc⟩   
  have hJne : J.Nonempty := by cases I.nonempty' with
                               | intro a haI => exists a; exact (hJdef I hIc) haI 
  have hJls : IsLowerSet J := by 
    intro s t hts hsJ 
    rw [Set.mem_iUnion] at hsJ |-
    cases hsJ with 
    | intro K hK => exists K; exact K.1.toLowerSet.lower' hts hK 
  have hJdo : DirectedOn (fun s t => s ≤ t) J := by 
    intro s hsJ t htJ 
    rw [Set.mem_iUnion] at hsJ htJ 
    cases hsJ with 
    | intro K hsK => cases htJ with
                    | intro L htL => cases IsChain.total hchain K.2 L.2 with 
                                     | inl hKL => have hsL : s ∈ (L : Set α) := hKL hsK 
                                                  cases L.1.directed' s hsL t htL with 
                                                  | intro u hu => exists u 
                                                                  constructor
                                                                  . rw [Set.mem_iUnion]
                                                                    exists L 
                                                                    exact hu.1
                                                                  . exact hu.2    
                                     | inr hLK => have htK : t ∈ (K : Set α) := hLK htL 
                                                  cases K.1.directed' s hsK t htK with 
                                                  | intro u hu => exists u 
                                                                  constructor
                                                                  . rw [Set.mem_iUnion]
                                                                    exists K 
                                                                    exact hu.1
                                                                  . exact hu.2    
  exists Order.IsIdeal.toIdeal {IsLowerSet := hJls, Nonempty := hJne, Directed := hJdo}
  


lemma Order.Ideal.contained_in_maximal_nonproper (I : Order.Ideal α): ∃ (J : Order.Ideal α), Order.Ideal.IsMaximalNonProper J ∧ I ≤ J := by 
  cases @zorn_nonempty_partialOrder₀ (Order.Ideal α) _ Set.univ 
    (fun c _ hchain J hJc => by cases @OrderIdeals_inductive_set α _ c hchain J hJc with 
                                | intro ub hub => exists ub) I (Set.mem_univ _)  with 
  | intro J hJ => exists J  
                  erw [and_iff_left hJ.2.1, Order.Ideal.IsMaximalNonProper_iff]
                  exact fun K hJK => Eq.symm (hJ.2.2 K (Set.mem_univ _) hJK) 


lemma Order.Ideal.generated_by_maximal_element (I : Order.Ideal α) {a : α} (ha : a ∈ I ∧ ∀ (b : α), b ∈ I → a ≤ b → b ≤ a) : 
I = Order.Ideal.principal a := by 
  rw [←Order.Ideal.principal_le_iff] at ha
  refine le_antisymm ?_ ha.1 
  intro b hbI 
  erw [Order.Ideal.mem_principal] 
  cases I.directed a (by rw [Order.Ideal.principal_le_iff] at ha; exact ha.1) b hbI with
  | intro c hc => exact le_trans hc.2.2 (ha.2 c hc.1 hc.2.1)

lemma Order.PFilter.generated_by_minimal_element (F : Order.PFilter α) {a : α} (ha : a ∈ F ∧ ∀ (b : α), b ∈ F → b ≤ a → a ≤ b) : 
F = Order.PFilter.principal a := by 
  suffices hdual : F.dual = @Order.Ideal.principal αᵒᵈ _ a by  
    unfold Order.PFilter.principal 
    erw [←hdual]
  apply Order.Ideal.generated_by_maximal_element F.dual
  change a ∈ F.dual ∧ _ at ha
  rw [and_iff_right ha.1]
  exact fun b hbF hab => ha.2 b hbF hab   



/- The preodered set α is Noetherian if and only if every ideal of α is principal.-/

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



end 

/- For a partial order, the order embedding from α to order ideals of α. -/

section 
variable [PartialOrder α]

def Elements_to_Ideal : OrderEmbedding α (Order.Ideal α) where 
toFun := fun a => Order.Ideal.principal a 
inj' := by intro a b heq; simp only at heq
           refine le_antisymm ?_ ?_ 
           rw [←Order.Ideal.mem_principal, ←heq, Order.Ideal.mem_principal]
           rw [←Order.Ideal.mem_principal, heq, Order.Ideal.mem_principal]
map_rel_iff' := by intro a b
                   simp only [Function.Embedding.coeFn_mk, Order.Ideal.principal_le_iff, Order.Ideal.mem_principal]

end 


/- Locally finite and locally finite with bot instance on Finset α.-/

lemma FinsetIic_is_finite (s : Finset α) : (Set.Iic s).Finite := by
  rw [←Set.finite_coe_iff]
  apply Finite.of_injective (fun (t : Set.Iic s) => ({a : s | a.1 ∈ t.1} : Set s))
  intro t u htu
  simp only at htu 
  rw [←SetCoe.ext_iff]
  ext a 
  constructor 
  . exact fun ha => by have has : a ∈ s := t.2 ha 
                       set a' := (⟨a, has⟩ : {a : α | a ∈ s})
                       have hat : a' ∈ {a : s| a.1 ∈ t.1} := by simp only [Finset.setOf_mem, Finset.coe_sort_coe, Set.mem_setOf_eq]; exact ha
                       rw [htu] at hat 
                       exact hat 
  . exact fun ha => by have has : a ∈ s := u.2 ha
                       set a' := (⟨a,has⟩ : {a : α | a ∈ s})
                       have hau : a' ∈ {a : s| a.1 ∈ u.1} := by simp only [Finset.setOf_mem, Finset.coe_sort_coe, Set.mem_setOf_eq]; exact ha
                       rw [←htu] at hau 
                       exact hau 


lemma FinsetIcc_is_finite (s t : Finset α) : (Set.Icc s t).Finite := 
Set.Finite.subset (FinsetIic_is_finite t) (by rw [Set.subset_def]; simp only [ge_iff_le, gt_iff_lt, Set.mem_Icc, Set.mem_Iic, and_imp, imp_self, 
implies_true, Subtype.forall, forall_const])

noncomputable instance FinsetLFB : LocallyFiniteOrderBot (Finset α) :=
LocallyFiniteOrderTop.ofIic (Finset α) (fun s => Set.Finite.toFinset (FinsetIic_is_finite s)) 
  (fun a s => by simp only [Set.Finite.mem_toFinset, Set.mem_Iic]) 

noncomputable instance FacePosetLF : LocallyFiniteOrder (Finset α) :=
LocallyFiniteOrder.ofIcc (Finset α) (fun s t => Set.Finite.toFinset (FinsetIcc_is_finite s t)) 
  (fun a s t => by simp only [ge_iff_le, gt_iff_lt, Set.Finite.mem_toFinset, Set.mem_Icc]) 
