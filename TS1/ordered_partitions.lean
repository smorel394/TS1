import TS1.preorder_to_powerset  
import Mathlib.Order.Extension.Well
import Init.WF


open Classical Preorder 


variable {α : Type _}

/- Sending a linear order to a preorder in one step. -/

def PreorderofLinearOrder (r : LinearOrder α) : Preorder α := r.toPartialOrder.toPreorder

/- Dual of a linear order. -/

def dual (r : LinearOrder α) := @OrderDual.linearOrder α r 


/- The set of linearly ordered partitions on α is the set of total preorders on α. (We get the corresponding partition by looking at
the equivalence classes of the antisymmetrization.) They are partially ordered by the partial order on preorders. -/

def LinearOrderedPartitions (α : Type _) := {s : Preorder α | Total s.le}

instance LinearOrderedPartitions.PartialOrder : PartialOrder (LinearOrderedPartitions α) :=
Subtype.partialOrder (fun (s : Preorder α) => Total s.le) 


namespace LinearOrderedPartitions 

/- LinearOrderedPartitions has a greatest element, which is given by the trivial preorder. -/


lemma trivialPreorder_is_total : Total (trivialPreorder α).le := 
fun _ _ => by change True ∨ True; simp only

lemma trivialPreorder_is_greatest_partition (p : LinearOrderedPartitions α) : p ≤ ⟨trivialPreorder α, TrivialPreorder_is_total⟩ := by
  change ↑p ≤ trivialPreorder α  
  exact trivialPreorder_is_greatest _ 

/- The minimal elements are exactly the linear orders. First we prove that they are minimal. We could write a version of this
with IsMin, using ordered partitions. (Maybe we should at some point.)-/

lemma linearOrder_is_minimal_partition {s : Preorder α} (hlin : IsLinearOrder α s.le) {t : Preorder α} (ht : Total t.le) :
t ≤ s → t = s := by
  intro hts 
  apply Preorder.ext
  intro a b 
  constructor
  . exact fun htab => hts htab
  . exact fun hsab => by cases (ht a b) with
                         | inl htab => exact htab
                         | inr htba => rw [hlin.toIsPartialOrder.toIsAntisymm.antisymm a b hsab (hts htba)]
                                      


/- Now we should that minimal partitions are necessarily linear orders. This basically says that every total preorder s dominates a linear
order, so that is what we first show; the idea is that we take an auxiliary linear r order on α, and we use r to order the elements
of α that are equivalent for s. This construction will be useful again later (to construct the "smallest facet" map.)-/

def LinearOrder_of_total_preorder_and_linear_order_aux (r : LinearOrder α) (s : Preorder α) : α → α → Prop :=
fun a b => s.lt a b ∨ (AntisymmRel s.le a b ∧ r.le a b)

lemma LinearOrder_of_total_preorder_and_linear_order_aux_refl (r : LinearOrder α) (s : Preorder α) (a : α) :
LinearOrder_of_total_preorder_and_linear_order_aux r s a a := Or.inr ⟨antisymmRel_refl s.le a, r.le_refl a⟩

lemma LinearOrder_of_total_preorder_and_linear_order_aux_trans (r : LinearOrder α) (s : Preorder α) (a b c : α) 
(hab : LinearOrder_of_total_preorder_and_linear_order_aux r s a b) (hbc : LinearOrder_of_total_preorder_and_linear_order_aux r s b c) :
LinearOrder_of_total_preorder_and_linear_order_aux r s a c := by
  cases hab with
  | inl hab => cases hbc with
               | inl hbc => exact Or.inl (lt_trans hab hbc)
               | inr hbc => exact Or.inl (lt_of_lt_of_le hab hbc.1.1)
  | inr hab => cases hbc with
               | inl hbc => exact Or.inl (lt_of_le_of_lt hab.1.1 hbc)
               | inr hbc => apply Or.inr
                            constructor
                            . exact AntisymmRel.trans hab.1 hbc.1
                            . exact r.le_trans _ _ _ hab.2 hbc.2

lemma LinearOrder_of_total_preorder_and_linear_order_aux_antisymm (r : LinearOrder α) (s : Preorder α) (a b : α) 
(hab : LinearOrder_of_total_preorder_and_linear_order_aux r s a b) (hba : LinearOrder_of_total_preorder_and_linear_order_aux r s b a) :
a =b := by
  cases hab with
  | inl hab => cases hba with
               | inl hba => exfalso; exact not_lt_of_lt hab hba 
               | inr hba => exfalso; exact not_lt_of_le hba.1.1 hab 
  | inr hab => cases hba with
               | inl hba => exfalso; exact not_lt_of_le hab.1.1 hba 
               | inr hba => exact r.le_antisymm _ _ hab.2 hba.2 



lemma LinearOrder_of_total_preorder_and_linear_order_aux_total (r : LinearOrder α) {s : Preorder α} (htot : Total s.le) :
Total (LinearOrder_of_total_preorder_and_linear_order_aux r s) := by
  intro a b 
  cases (TotalPreorder_trichotomy htot a b) with
  | inl hltab => exact Or.inl (Or.inl hltab)
  | inr hmed => cases hmed with
                | inl hltba => exact Or.inr (Or.inl hltba)
                | inr heqab => cases (r.le_total a b) with
                               | inl hrab => exact Or.inl (Or.inr ⟨heqab, hrab⟩)
                               | inr hrba => exact Or.inr (Or.inr ⟨AntisymmRel.symm heqab, hrba⟩)


def LinearOrder_of_total_preorder_and_linear_order (r : LinearOrder α) (s : Preorder α) : Preorder α where
  le := LinearOrder_of_total_preorder_and_linear_order_aux r s
  le_refl a := LinearOrder_of_total_preorder_and_linear_order_aux_refl r s a
  le_trans a b c := LinearOrder_of_total_preorder_and_linear_order_aux_trans r s a b c 
  lt := fun a b => (LinearOrder_of_total_preorder_and_linear_order_aux r s a b) ∧ ¬(LinearOrder_of_total_preorder_and_linear_order_aux r s b a)
  lt_iff_le_not_le := fun a b => by triv

lemma LinearOrder_of_total_preorder_and_linear_order_is_total (r : LinearOrder α) {s : Preorder α} (htot : Total s.le) :
Total (LinearOrder_of_total_preorder_and_linear_order r s).le := LinearOrder_of_total_preorder_and_linear_order_aux_total r htot 

lemma LinearOrder_of_total_preorder_and_linear_order_is_linear (r : LinearOrder α) {s : Preorder α} (htot : Total s.le) :
IsLinearOrder α (LinearOrder_of_total_preorder_and_linear_order r s).le where
refl := LinearOrder_of_total_preorder_and_linear_order_aux_refl r s
trans := LinearOrder_of_total_preorder_and_linear_order_aux_trans r s
antisymm := LinearOrder_of_total_preorder_and_linear_order_aux_antisymm r s 
total := LinearOrder_of_total_preorder_and_linear_order_aux_total r htot 

lemma LinearOrder_of_total_preorder_and_linear_order_is_smaller (r : LinearOrder α) (s : Preorder α) :
LinearOrder_of_total_preorder_and_linear_order r s ≤ s := by
  intro a b hab
  cases hab with
  | inl hlt => exact le_of_lt hlt
  | inr heq => exact heq.1.1

/- On the blocks of s, the linear orders LO(s) and r coincide.-/

lemma LinearOrder_vs_fixed_LinearOrder (r : LinearOrder α) {s : Preorder α} (htot : Total s.le) {a b : α} (hab : AntisymmRel s.le a b) :
r.le a b ↔  (LinearOrder_of_total_preorder_and_linear_order r s).le a b := by 
  constructor
  . exact fun hrab => Or.inr ⟨hab, hrab⟩
  . intro hsab 
    cases hsab with 
    | inl hlt => exfalso
                 rw [←(TotalPreorder_lt_iff_not_le htot)] at hlt 
                 exact hlt hab.2
    | inr heq => exact heq.2 

/- Formal consequence of the fact that LO(s) ≤ s and the preorders are total.-/

lemma LinearOrder_of_total_preorder_and_linear_order_lt (r : LinearOrder α) {s : Preorder α} (htot : Total s.le) {a b : α}
(hab : s.lt a b) : (LinearOrder_of_total_preorder_and_linear_order r s).lt a b := by 
  rw [←(TotalPreorder_lt_iff_not_le htot)] at hab 
  rw [←(@TotalPreorder_lt_iff_not_le _ (LinearOrder_of_total_preorder_and_linear_order r s) (LinearOrder_of_total_preorder_and_linear_order_is_total r htot))]
  by_contra habs
  exact hab (LinearOrder_of_total_preorder_and_linear_order_is_smaller r s habs)


/- Sanity check. -/

lemma LinearOrder_of_linear_order_and_linear_order_is_self (r : LinearOrder α) {s : Preorder α} (hlin : IsLinearOrder α s.le) :
LinearOrder_of_total_preorder_and_linear_order r s =s := 
@linearOrder_is_minimal_partition α s hlin (LinearOrder_of_total_preorder_and_linear_order r s) 
      (LinearOrder_of_total_preorder_and_linear_order_is_total r hlin.toIsTotal.total) 
      (LinearOrder_of_total_preorder_and_linear_order_is_smaller r s)
  

/- We can now prove that minimal ordered partitions are linear orders. -/

lemma minimal_partition_is_linear_order (p : LinearOrderedPartitions α) (hmin : ∀ (q : LinearOrderedPartitions α), q ≤ p → q = p) :
IsLinearOrder α p.1.le := by
  set r := WellFounded.wellOrderExtension (@emptyWf α).wf 
  have heq := hmin ⟨LinearOrder_of_total_preorder_and_linear_order r p.1, LinearOrder_of_total_preorder_and_linear_order_is_total r p.2⟩
      (LinearOrder_of_total_preorder_and_linear_order_is_smaller r p.1)
  rw [←Subtype.coe_inj] at heq
  change LinearOrder_of_total_preorder_and_linear_order r p.1 = p.1 at heq 
  rw [←heq]
  exact LinearOrder_of_total_preorder_and_linear_order_is_linear r p.2 

 
/- We already introduced what will correspond to the "smallest facet" map on the abstract simplicial complex side (when α is finite).
We now introduce what will be the "restriction" map of the shelling, which we call the "descent partition"; as before, we need an 
auxiliary linear order r on α. The idea is that, for a total preorder s, the equivalence classes of its descent partition are
the maximal connected (for s) sets on which s and r agree, and then these classes are ordered using s. -/


def DescentPartition_aux (r : LinearOrder α) (s : Preorder α) : α → α → Prop :=
fun a b => s.le a b ∨ (s.le b a ∧ ∀ (c d : α), s.le b c → s.le c d → s.le d a → (r.le b c ∧ r.le c d ∧ r.le d a))

lemma DescentPartition_aux_refl (r : LinearOrder α) (s : Preorder α) (a : α) : DescentPartition_aux r s a a :=
Or.inl (s.le_refl a)



lemma DescentPartition_aux_trans (r : LinearOrder α) {s : Preorder α} (htot : Total s.le) (a b c : α) (hab : DescentPartition_aux r s a b)
(hbc : DescentPartition_aux r s b c) : DescentPartition_aux r s a c := by 
  cases hab with
  | inl hab => cases hbc with
               | inl hbc => exact Or.inl (s.le_trans _ _ _ hab hbc)
               | inr hcb => cases (htot a c) with
                            | inl hac => exact Or.inl hac
                            | inr hca => apply Or.inr
                                         constructor
                                         . exact hca
                                         . intro d e hcd hde hea 
                                           have h1 := hcb.2 d e hcd hde (s.le_trans _ _ _ hea hab)
                                           have h2 := hcb.2 e a (s.le_trans _ _ _ hcd hde) hea hab
                                           exact ⟨h1.1, h1.2.1, h2.2.1⟩                                           
  | inr hba => cases hbc with
               | inl hbc => cases (htot a c) with
                            | inl hac => exact Or.inl hac 
                            | inr hca => apply Or.inr
                                         rw [and_iff_right hca]
                                         intro d e hcd hde hea 
                                         have h1 := hba.2 d e (s.le_trans _ _ _ hbc hcd) hde hea 
                                         have h2 := hba.2 c d hbc hcd (s.le_trans _ _ _ hde hea)
                                         exact ⟨h2.2.1, h1.2.1, h1.2.2⟩  

               | inr hcb => apply Or.inr 
                            rw [and_iff_right (s.le_trans _ _ _ hcb.1 hba.1)]
                            intro d e hcd hde hea 
                            have hrab := (hba.2 a a hba.1 (s.le_refl a) (s.le_refl a)).1
                            have hrcb := (hcb.2 c c (s.le_refl c) (s.le_refl c) hcb.1).2.2
                            cases (htot e b) with
                            | inl heb => have h := hcb.2 d e hcd hde heb 
                                         exact ⟨h.1, h.2.1, r.le_trans _ _ _ h.2.2 hrab⟩
                            | inr hbe => cases (htot d b) with
                                         | inl hdb => have h1 := hcb.2 d d hcd (s.le_refl d) hdb 
                                                      have h2 := hba.2 e e hbe (s.le_refl e) hea 
                                                      exact ⟨h1.1, r.le_trans _ _ _ h1.2.2 h2.1, h2.2.2⟩
                                         | inr hbd => have h:= hba.2 d e hbd hde hea 
                                                      exact ⟨r.le_trans _ _ _  hrcb h.1, h.2.1, h.2.2⟩

lemma DescentPartition_aux_total (r: LinearOrder α) {s : Preorder α} (htot : Total s.le) (a b : α) :
DescentPartition_aux r s a b ∨ DescentPartition_aux r s b a := by
  cases (htot a b) with
  | inl hab => exact Or.inl (Or.inl hab) 
  | inr hba => exact Or.inr (Or.inl hba) 


def DescentPartition (r: LinearOrder α) {s : Preorder α} (htot : Total s.le) : Preorder α where 
le := DescentPartition_aux r s 
lt := fun a b => DescentPartition_aux r s a b ∧ ¬(DescentPartition_aux r s b a)
le_refl := DescentPartition_aux_refl r s 
le_trans := DescentPartition_aux_trans r htot 
lt_iff_le_not_le := fun a b => by triv 

lemma DescentPartition_is_total (r: LinearOrder α) {s : Preorder α} (htot : Total s.le) :
Total (DescentPartition r htot).le := DescentPartition_aux_total r htot 

lemma DescentPartition_is_greater (r : LinearOrder α) {s: Preorder α} (htot : Total s.le) : 
s ≤ DescentPartition r htot := by
  intro a b hsab 
  change DescentPartition_aux r s a b  
  exact Or.inl hsab 


def AscentPartition_aux (r : LinearOrder α) (s : Preorder α) : α → α → Prop :=
fun a b => s.le a b ∨ (s.le b a ∧ @StrictMonoOn α α s r.toPartialOrder.toPreorder (fun x => x) (@Set.Icc α s b a))


lemma AscentPartition_aux_refl (r : LinearOrder α) (s : Preorder α) (a : α) : AscentPartition_aux r s a a :=
Or.inl (s.le_refl a)


lemma AscentPartition_aux_trans (r : LinearOrder α) {s : Preorder α} (htot : Total s.le) (a b c : α) (hab : AscentPartition_aux r s a b)
(hbc : AscentPartition_aux r s b c) : AscentPartition_aux r s a c := by 
  cases hab with
  | inl hab => cases hbc with
               | inl hbc => exact Or.inl (s.le_trans _ _ _ hab hbc)
               | inr hcb => cases (htot a c) with
                            | inl hac => exact Or.inl hac
                            | inr hca => apply Or.inr 
                                         rw [and_iff_right hca]
                                         intro d hd e he hde  
                                         refine hcb.2 ?_ ?_ hde 
                                         . rw [Set.mem_Icc] at hd |- 
                                           exact ⟨hd.1, s.le_trans _ _ _ hd.2 hab⟩ 
                                         . rw [Set.mem_Icc] at he |- 
                                           exact ⟨he.1, s.le_trans _ _ _ he.2 hab⟩                       
  | inr hba => cases hbc with
               | inl hbc => cases (htot a c) with
                            | inl hac => exact Or.inl hac 
                            | inr hca => apply Or.inr
                                         rw [and_iff_right hca]
                                         intro d hd e he hde 
                                         refine hba.2 ?_ ?_ hde 
                                         . rw [Set.mem_Icc] at hd |-
                                           exact ⟨s.le_trans _ _ _ hbc hd.1, hd.2⟩
                                         . rw [Set.mem_Icc] at he |- 
                                           exact ⟨s.le_trans _ _ _ hbc he.1, he.2⟩
               | inr hcb => apply Or.inr 
                            rw [and_iff_right (s.le_trans _ _ _ hcb.1 hba.1)]
                            intro d hd e he hde 
                            rw [Set.mem_Icc] at hd he
                            cases htot d b with 
                            | inr hbd => refine hba.2 ?_ ?_ hde 
                                         all_goals rw [Set.mem_Icc]
                                         . exact ⟨hbd, hd.2⟩
                                         . exact ⟨le_trans hbd (le_of_lt hde) , he.2⟩
                            | inl hdb => cases htot b e with 
                                         | inr heb => refine hcb.2 ?_ ?_ hde 
                                                      all_goals rw [Set.mem_Icc]
                                                      . exact ⟨hd.1, hdb⟩
                                                      . exact ⟨he.1, heb⟩
                                         | inl hbe => by_cases hdblt : s.lt d b 
                                                      . by_cases hbelt : s.lt b e 
                                                        . refine @lt_trans _ r.toPartialOrder.toPreorder _ _ _ (hcb.2 ?_ ?_ hdblt) (hba.2 ?_ ?_ hbelt)
                                                          all_goals rw [Set.mem_Icc]
                                                          . exact ⟨hd.1, hdb⟩
                                                          . exact ⟨hcb.1, s.le_refl b⟩
                                                          . exact ⟨s.le_refl b, hba.1⟩
                                                          . exact ⟨hbe, he.2⟩
                                                        . rw [←(TotalPreorder_lt_iff_not_le htot), not_not] at hbelt
                                                          refine hcb.2 ?_ ?_ hde 
                                                          all_goals rw [Set.mem_Icc]
                                                          . exact ⟨hd.1, hdb⟩
                                                          . exact ⟨he.1, hbelt⟩
                                                      . rw [←(TotalPreorder_lt_iff_not_le htot), not_not] at hdblt 
                                                        refine hba.2 ?_ ?_ hde 
                                                        all_goals rw [Set.mem_Icc]
                                                        . exact ⟨hdblt, hd.2⟩
                                                        . exact ⟨hbe, he.2⟩
                            

lemma AscentPartition_aux_total (r: LinearOrder α) {s : Preorder α} (htot : Total s.le) (a b : α) :
AscentPartition_aux r s a b ∨ AscentPartition_aux r s b a := by
  cases (htot a b) with
  | inl hab => exact Or.inl (Or.inl hab) 
  | inr hba => exact Or.inr (Or.inl hba) 



def AscentPartition (r: LinearOrder α) {s : Preorder α} (htot : Total s.le) : Preorder α where 
le := AscentPartition_aux r s 
lt := fun a b => AscentPartition_aux r s a b ∧ ¬(AscentPartition_aux r s b a)
le_refl := AscentPartition_aux_refl r s 
le_trans := AscentPartition_aux_trans r htot 
lt_iff_le_not_le := fun a b => by triv 


lemma AscentPartition_is_total (r: LinearOrder α) {s : Preorder α} (htot : Total s.le) :
Total (AscentPartition r htot).le := AscentPartition_aux_total r htot 


lemma AscentPartition_is_greater (r : LinearOrder α) {s: Preorder α} (htot : Total s.le) : 
s ≤ AscentPartition r htot := by
  intro a b hsab 
  change AscentPartition_aux r s a b  
  exact Or.inl hsab 


/- Interaction between the two maps.-/

lemma AscentPartition_comp (r : LinearOrder α) {s: Preorder α} (htot : Total s.le) : 
AscentPartition r htot = @AscentPartition _ r (LinearOrder_of_total_preorder_and_linear_order r s)
(LinearOrder_of_total_preorder_and_linear_order_is_total r htot) := by 
  ext a b 
  constructor 
  . intro hab 
    by_cases hloab : (LinearOrder_of_total_preorder_and_linear_order r s).le a b
    . exact Or.inl hloab 
    . rw [@TotalPreorder_lt_iff_not_le _ (LinearOrder_of_total_preorder_and_linear_order r s) 
       (LinearOrder_of_total_preorder_and_linear_order_is_total r htot)] at hloab 
      apply Or.inr 
      rw [and_iff_right (@le_of_lt _ (LinearOrder_of_total_preorder_and_linear_order r s) _ _ hloab)]
      intro d hd e he hde 
      rw [@Set.mem_Icc _ (LinearOrder_of_total_preorder_and_linear_order r s)] at hd he 
      by_cases hsab : s.le a b 
      . have heqde : AntisymmRel s.le d e := by 
          constructor
          . apply LinearOrder_of_total_preorder_and_linear_order_is_smaller r 
            exact @le_of_lt _ (LinearOrder_of_total_preorder_and_linear_order r s) _ _ hde 
          . refine s.le_trans e a d ?_ (s.le_trans a b d hsab ?_)
            all_goals apply LinearOrder_of_total_preorder_and_linear_order_is_smaller r 
            . exact he.2
            . exact hd.1  
        apply lt_of_le_of_ne 
        . rw [LinearOrder_vs_fixed_LinearOrder r htot heqde]
          exact @le_of_lt _ (LinearOrder_of_total_preorder_and_linear_order r s) _ _ hde 
        . exact @ne_of_lt _ (LinearOrder_of_total_preorder_and_linear_order r s) _ _ hde 
      . cases hab with 
        | inl hab => exfalso; exact hsab hab 
        | inr hba => by_cases hsde : s.lt d e 
                     . refine hba.2 ?_ ?_ hsde 
                       all_goals rw [Set.mem_Icc]
                       . constructor 
                         all_goals apply LinearOrder_of_total_preorder_and_linear_order_is_smaller r
                         . exact hd.1 
                         . exact hd.2  
                       . constructor 
                         all_goals apply LinearOrder_of_total_preorder_and_linear_order_is_smaller r 
                         . exact he.1 
                         . exact he.2 
                     . have heqde : AntisymmRel s.le d e :=  by
                         constructor 
                         . apply LinearOrder_of_total_preorder_and_linear_order_is_smaller r 
                           exact @le_of_lt _ (LinearOrder_of_total_preorder_and_linear_order r s) d e hde                          
                         . rw [←(TotalPreorder_lt_iff_not_le htot), not_not] at hsde
                           exact hsde 
                       apply lt_of_le_of_ne 
                       . rw [LinearOrder_vs_fixed_LinearOrder r htot heqde]
                         exact @le_of_lt _ (LinearOrder_of_total_preorder_and_linear_order r s) d e hde 
                       . exact @ne_of_lt _ (LinearOrder_of_total_preorder_and_linear_order r s) d e hde 
  . intro hab 
    cases hab with 
    | inl hloab => exact Or.inl (LinearOrder_of_total_preorder_and_linear_order_is_smaller r s hloab) 
    | inr hloba => by_cases hsab : s.le a b 
                   . exact Or.inl hsab 
                   . apply Or.inr 
                     rw [TotalPreorder_lt_iff_not_le htot] at hsab
                     rw [and_iff_right (le_of_lt hsab)]
                     intro d hd e he hde 
                     rw [Set.mem_Icc] at hd he 
                     by_cases hbd : (LinearOrder_of_total_preorder_and_linear_order r s).le b d 
                     . by_cases hea : (LinearOrder_of_total_preorder_and_linear_order r s).le e a 
                       . refine hloba.2 ?_ ?_ (LinearOrder_of_total_preorder_and_linear_order_lt r htot hde)
                         all_goals rw [@Set.mem_Icc _ (LinearOrder_of_total_preorder_and_linear_order r s)]
                         . constructor
                           . exact hbd 
                           . exact (LinearOrder_of_total_preorder_and_linear_order r s).le_trans _ _ _ (Or.inl hde) hea 
                         . constructor 
                           . exact (LinearOrder_of_total_preorder_and_linear_order r s).le_trans _ _ _ hbd  (Or.inl hde)
                           . exact hea 
                       . change ¬(s.lt e a ∨ (AntisymmRel s.le e a ∧ r.le e a)) at hea 
                         rw [not_or, not_and, ←(TotalPreorder_lt_iff_not_le htot), not_not] at hea
                         have hrea := hea.2 ⟨he.2, hea.1⟩
                         rw [←lt_iff_not_le] at hrea 
                         refine @lt_trans _ r.toPartialOrder.toPreorder d a e ?_ hrea
                         have hda : (LinearOrder_of_total_preorder_and_linear_order r s).lt d a := by
                           apply LinearOrder_of_total_preorder_and_linear_order_lt r htot
                           exact @lt_of_lt_of_le _ s d e a hde he.2  
                         refine hloba.2 ?_ ?_ hda 
                         all_goals rw [@Set.mem_Icc _ (LinearOrder_of_total_preorder_and_linear_order r s)]
                         . exact ⟨hbd, @le_of_lt _ (LinearOrder_of_total_preorder_and_linear_order r s) _ _ hda⟩
                         . exact ⟨Or.inl hsab, (LinearOrder_of_total_preorder_and_linear_order r s).le_refl _⟩
                     . change ¬(s.lt b d ∨ (AntisymmRel s.le b d ∧ r.le b d)) at hbd
                       rw [not_or, not_and, ←(TotalPreorder_lt_iff_not_le htot), not_not] at hbd
                       have hrbd := hbd.2 ⟨hd.1, hbd.1⟩
                       rw [←lt_iff_not_le] at hrbd 
                       refine @lt_trans _ r.toPartialOrder.toPreorder d b e hrbd ?_
                       by_cases hea : (LinearOrder_of_total_preorder_and_linear_order r s).le e a 
                       . have hbe : (LinearOrder_of_total_preorder_and_linear_order r s).lt b e := by
                           apply LinearOrder_of_total_preorder_and_linear_order_lt r htot 
                           exact @lt_of_le_of_lt _ s _ _ _ hd.1 hde 
                         refine hloba.2 ?_ ?_ hbe 
                         all_goals rw [@Set.mem_Icc _ (LinearOrder_of_total_preorder_and_linear_order r s)]
                         . exact ⟨(LinearOrder_of_total_preorder_and_linear_order r s).le_refl _, Or.inl hsab⟩ 
                         . exact ⟨@le_of_lt _ (LinearOrder_of_total_preorder_and_linear_order r s) _ _ hbe, hea⟩
                       . change ¬(s.lt e a ∨ (AntisymmRel s.le e a ∧ r.le e a)) at hea 
                         rw [not_or, not_and, ←(TotalPreorder_lt_iff_not_le htot), not_not] at hea
                         have hrea := hea.2 ⟨he.2, hea.1⟩
                         rw [←lt_iff_not_le] at hrea 
                         refine @lt_trans _ r.toPartialOrder.toPreorder b a e ?_ hrea
                         have hba : (LinearOrder_of_total_preorder_and_linear_order r s).lt b a := by
                           apply LinearOrder_of_total_preorder_and_linear_order_lt r htot
                           exact @lt_of_lt_of_le _ s b e a (@lt_of_le_of_lt _ s b d e hd.1 hde) he.2
                         refine hloba.2 ?_ ?_ hba 
                         all_goals rw [@Set.mem_Icc _ (LinearOrder_of_total_preorder_and_linear_order r s)]
                         . exact ⟨(LinearOrder_of_total_preorder_and_linear_order r s).le_refl _, @le_of_lt _ 
                             (LinearOrder_of_total_preorder_and_linear_order r s) _ _ hba⟩  
                         . exact ⟨@le_of_lt _ (LinearOrder_of_total_preorder_and_linear_order r s) _ _ hba, 
                             (LinearOrder_of_total_preorder_and_linear_order r s).le_refl _⟩ 


lemma LinearOrder_of_AscentPartition (r : LinearOrder α) {s : Preorder α} (hstot : Total s.le) :
LinearOrder_of_total_preorder_and_linear_order r s = LinearOrder_of_total_preorder_and_linear_order r (AscentPartition r hstot) := by 
  ext a b 
  constructor
  . intro hab 
    cases hab with 
    | inl hsltab => by_cases hapab : (AscentPartition r hstot).lt a b 
                    . exact Or.inl hapab 
                    . rw [←(@TotalPreorder_lt_iff_not_le _ (AscentPartition r hstot) (AscentPartition_is_total r hstot)), not_not] at hapab
                      set hapab' := hapab
                      rw [←(TotalPreorder_lt_iff_not_le hstot)] at hsltab 
                      change s.le b a ∨ _ at hapab 
                      rw [or_iff_right hsltab] at hapab
                      rw [TotalPreorder_lt_iff_not_le hstot] at hsltab
                      have hrab : r.lt a b := by 
                        refine hapab.2 ?_ ?_   hsltab 
                        all_goals rw [Set.mem_Icc]
                        . exact ⟨s.le_refl a, le_of_lt hsltab⟩
                        . exact ⟨le_of_lt hsltab, s.le_refl b⟩
                      apply Or.inr 
                      rw [and_iff_left (@le_of_lt _ r.toPartialOrder.toPreorder _ _ hrab)]
                      unfold AntisymmRel
                      rw [and_iff_left hapab'] 
                      exact Or.inl (le_of_lt hsltab)                     
    | inr hrab => apply Or.inr 
                  rw [and_iff_left hrab.2]
                  constructor 
                  . exact AscentPartition_is_greater r hstot hrab.1.1
                  . exact AscentPartition_is_greater r hstot hrab.1.2
  . intro hab 
    cases hab with 
    | inl hltab => rw [←(@TotalPreorder_lt_iff_not_le _ (AscentPartition r hstot) (AscentPartition_is_total r hstot))] at hltab 
                   change ¬(s.le b a ∨ _) at hltab 
                   rw [not_or, TotalPreorder_lt_iff_not_le hstot] at hltab 
                   exact Or.inl hltab.1
    | inr heq => have hsab : s.le a b := by 
                   by_contra habs  
                   unfold AntisymmRel at heq 
                   change ((s.le a b ∨ _) ∧ _) ∧ _ at heq
                   rw [or_iff_right habs] at heq
                   rw [TotalPreorder_lt_iff_not_le hstot] at habs
                   have hrba : r.lt b a := by 
                     refine heq.1.1.2 ?_ ?_ habs 
                     all_goals rw [Set.mem_Icc]
                     . exact ⟨s.le_refl _, le_of_lt habs⟩ 
                     . exact ⟨le_of_lt habs, s.le_refl _⟩ 
                   exact @not_le_of_lt _ r.toPartialOrder.toPreorder _ _ hrba heq.2 
                 by_cases hsltab : s.lt a b 
                 . exact Or.inl hsltab 
                 . rw [←(TotalPreorder_lt_iff_not_le hstot), not_not] at hsltab 
                   apply Or.inr 
                   exact ⟨⟨hsab, hsltab⟩, heq.2⟩ 
                   

/- One of the big goals: LinearOrder_of_total_preorder_and_linear_order r s is equal to s' if and only s is in the interval
[s', AscentPartition r s'], if and only if AscentPartition r s = AscentPartition r s'. So the intervals [s', AscentPartition r s']
for s' a linear order are the fibers of the map LinearOrder_etc and also of the map AscentPartition.-/

/-We do the easy part first, i.e. the fact that LinearOrder_etc is constant on any interval [s, AscentPartition r s].-/

lemma LinearOrder_of_total_preorder_and_linear_order_is_constant_on_intervals_aux (r : LinearOrder α) {s t u : Preorder α}
(httot : Total t.le) (hutot : Total u.le) (hst : s ≤ t) (htu : t ≤ u)
(heq : LinearOrder_of_total_preorder_and_linear_order r s = LinearOrder_of_total_preorder_and_linear_order r u) :
LinearOrder_of_total_preorder_and_linear_order r s ≤ LinearOrder_of_total_preorder_and_linear_order r t := by 
  intro a b hab 
  by_cases htab : t.lt a b 
  . exact Or.inl htab 
  . rw [←(TotalPreorder_lt_iff_not_le httot), not_not] at htab
    have htab' : t.le a b := by 
      apply hst 
      exact LinearOrder_of_total_preorder_and_linear_order_is_smaller r s hab 
    have huab : ¬(u.lt a b) := by
      rw [←(TotalPreorder_lt_iff_not_le hutot), not_not]
      exact htu htab
    rw [heq] at hab
    change u.lt a b ∨ _ at hab 
    rw [or_iff_right huab] at hab 
    exact Or.inr ⟨⟨htab', htab⟩, hab.2⟩



lemma LinearOrder_of_total_preorder_and_linear_order_is_constant_on_intervals (r : LinearOrder α) {s t u : Preorder α}
(hstot : Total s.le) (httot : Total t.le) (hutot : Total u.le) (hst : s ≤ t) (htu : t ≤ u)
(heq : LinearOrder_of_total_preorder_and_linear_order r s = LinearOrder_of_total_preorder_and_linear_order r u) :
LinearOrder_of_total_preorder_and_linear_order r s = LinearOrder_of_total_preorder_and_linear_order r t := by 
  apply le_antisymm
  . exact LinearOrder_of_total_preorder_and_linear_order_is_constant_on_intervals_aux r httot hutot hst htu heq  
  . intro a b htab 
    cases LinearOrder_of_total_preorder_and_linear_order_is_total r hstot a b with 
    | inl hsab => exact hsab 
    | inr hsba => have htba := LinearOrder_of_total_preorder_and_linear_order_is_constant_on_intervals_aux r httot hutot hst htu heq hsba 
                  have heq := LinearOrder_of_total_preorder_and_linear_order_aux_antisymm r t _ _ htab htba 
                  rw [heq]
                  exact (LinearOrder_of_total_preorder_and_linear_order r s).le_refl _ 


lemma LinearOrder_of_total_preorder_and_linear_order_on_ascent_interval (r : LinearOrder α) {s t : Preorder α} (hstot : Total s.le)
(httot : Total t.le) (hst : s ≤ t) (hts : t ≤ AscentPartition r hstot) :
LinearOrder_of_total_preorder_and_linear_order r s = LinearOrder_of_total_preorder_and_linear_order r t := 
@LinearOrder_of_total_preorder_and_linear_order_is_constant_on_intervals _ r s t (AscentPartition r hstot) hstot httot 
(AscentPartition_is_total r hstot) hst hts (LinearOrder_of_AscentPartition r hstot)

/- And a corollary when s is a linear order.-/

lemma LinearOrder_of_total_preorder_and_linear_order_on_ascent_interval' (r : LinearOrder α) {s t : Preorder α} 
(hslin : IsLinearOrder α s.le) (httot : Total t.le) (hst : s ≤ t) (hts : t ≤ AscentPartition r hslin.toIsTotal.total) :
s = LinearOrder_of_total_preorder_and_linear_order r t := by 
  rw [←(LinearOrder_of_linear_order_and_linear_order_is_self r hslin)]
  exact LinearOrder_of_total_preorder_and_linear_order_on_ascent_interval r hslin.toIsTotal.total httot hst hts  


/- We show that the fibers of the LinearOrder_etc map are the ascent intervals.-/

lemma LinearOrder_of_total_preorder_and_linear_order_fibers (r : LinearOrder α) {s t : Preorder α}
(hslin : IsLinearOrder α s.le) (httot : Total t.le) (him : LinearOrder_of_total_preorder_and_linear_order r t = s) :
s ≤ t ∧ t ≤ (AscentPartition r hslin.toIsTotal.total) := by 
  constructor 
  . rw [←him]
    exact LinearOrder_of_total_preorder_and_linear_order_is_smaller r t 
  . simp_rw [←him]
    rw [←AscentPartition_comp] 
    exact AscentPartition_is_greater r httot 

/- Now we show that the fibers of the AscentPartition map are the same intervals.-/

lemma AscentPartition_fibers (r : LinearOrder α) {s t : Preorder α} (hslin : IsLinearOrder α s.le) (httot : Total t.le) :
AscentPartition r hslin.toIsTotal.total = AscentPartition r httot ↔ t ≤ AscentPartition r hslin.toIsTotal.total ∧ s ≤ t := by
  constructor 
  . intro heq 
    constructor 
    . rw [heq]
      exact AscentPartition_is_greater r httot  
    . rw [←(LinearOrder_of_linear_order_and_linear_order_is_self r hslin)] 
      rw [LinearOrder_of_AscentPartition r hslin.toIsTotal.total, heq]
      rw [←(LinearOrder_of_AscentPartition r httot)]
      exact LinearOrder_of_total_preorder_and_linear_order_is_smaller r t 
  . intro hineq 
    simp_rw [LinearOrder_of_total_preorder_and_linear_order_on_ascent_interval' r hslin httot hineq.2 hineq.1] 
    rw [←AscentPartition_comp]

lemma AscentPartition_fibers' (r : LinearOrder α) {s t : Preorder α} (hslin : IsLinearOrder α s.le) (httot : Total t.le) :
AscentPartition r hslin.toIsTotal.total = AscentPartition r httot ↔ s = LinearOrder_of_total_preorder_and_linear_order r t := by 
  rw [AscentPartition_fibers r hslin httot]
  constructor
  . exact fun hineq => LinearOrder_of_total_preorder_and_linear_order_on_ascent_interval' r hslin httot hineq.2 hineq.1 
  . exact fun heq => And.symm (LinearOrder_of_total_preorder_and_linear_order_fibers r hslin httot (Eq.symm heq))



/- We want some conditions on ordered partitions that will be respected by LinearOrder_of_total_preorder_and_linear_order and
DescentPartition. At first I though that it would be okay if I took r to be a locally finite well-order (i.e isomorphic to ω)
and the set of total essentially locally finite preorders. But no, because if I take α = ℕ and s to the preorder with two
equivalence classes {0,2,4,6,...} and {1,3,5,7,...} (in that order), then s is total essentially locally finite but
the associated linear order is 0,2,4,6,...,1,3,5,7,..., which is not. So I think that the correct condition is to take r as
before and to consider only partition that have one block containing an interval [a,->] (for r). This forces the partition
to have a finite number of blocks (so it is essentially locally finite), and all the blocks but at most one are finite.  We will
get the Coxeter complexes of the finite symmetric groups and of the infinite symmetric group. Let's call this condition
"eventually trivial".

Also, the easiest way to phrase condition on r is ti say that it should be a linear order with a "locally finite with bot" 
structure (as that is already in mathlib). -/


def EventuallyTrivialLinearOrderedPartitions (r : LinearOrder α): Set (Preorder α) := {s : Preorder α | Total s.le ∧ ∃ (a : α), 
∀ (b c : α), r.le a b → r.le a c → s.le b c}

lemma EventuallyTrivial_is_finite {r : LinearOrder α} (hLF : @LocallyFiniteOrderBot α (PreorderofLinearOrder r)) {s : Preorder α} 
(hs : s ∈ EventuallyTrivialLinearOrderedPartitions r) : Finite (Antisymmetrization α s.le) := by
  letI : Preorder α := PreorderofLinearOrder r 
  cases hs.2 with
  | intro a ha => set f : hLF.finsetIic a → @Antisymmetrization α s.le (@instIsPreorderLeToLE α s) := 
                    fun b => @toAntisymmetrization α s.le (@instIsPreorderLeToLE α s) b.1    
                  apply Finite.of_surjective f 
                  intro x 
                  cases r.le_total (@ofAntisymmetrization α s.le (@instIsPreorderLeToLE α s) x) a with 
                  | inl hxa => have hmem : @ofAntisymmetrization α s.le (@instIsPreorderLeToLE α s) x ∈ hLF.finsetIic a := by
                                 rw [hLF.finset_mem_Iic]
                                 exact hxa 
                               exists ⟨@ofAntisymmetrization α s.le (@instIsPreorderLeToLE α s) x, hmem⟩
                               exact @toAntisymmetrization_ofAntisymmetrization α s.le (@instIsPreorderLeToLE α s) x 
                  | inr hax => have hamem : a ∈ hLF.finsetIic a := by rw [hLF.finset_mem_Iic]
                               existsi ⟨a, hamem⟩
                               simp only 
                               rw [←(@toAntisymmetrization_ofAntisymmetrization α s.le (@instIsPreorderLeToLE α s) x)]
                               apply Quotient.sound
                               exact ⟨ha a _ (r.le_refl a) hax, ha _ a hax (r.le_refl _)⟩ 

lemma EventuallyTrivial_IsUpperSet (r : LinearOrder α) : IsUpperSet (EventuallyTrivialLinearOrderedPartitions r) := by 
  intro r s hrs hr
  constructor
  . exact Total_IsUpperSet hrs hr.1 
  . cases (hr.2) with
    | intro a ha => exact ⟨a, fun b c hab hac => hrs (ha b c hab hac)⟩


/- If α is finite (and nonempty), then everything is eventually trivial.-/

lemma Finite_is_EventuallyTrivial [Fintype α] [Nonempty α] (r : LinearOrder α) (s : Preorder α) : ∃ (a : α), ∀ (b c : α), 
r.le a b → r.le a c → s.le b c := by
  set a:= (WellFounded.min (@Finite.Preorder.wellFounded_gt α (Finite.of_fintype α) (PreorderofLinearOrder r)) Set.univ Set.univ_nonempty)
  exists a
  intro b c hab hac 
  have habeq : a = b := by
    apply r.le_antisymm a b hab
    exact @WellFounded.min_le α (dual r) (@Finite.Preorder.wellFounded_gt α (Finite.of_fintype α) (PreorderofLinearOrder r)) b Set.univ 
      (Set.mem_univ b) Set.univ_nonempty 
  have haceq : a = c := by 
    apply r.le_antisymm a c hac
    exact @WellFounded.min_le α (dual r) (@Finite.Preorder.wellFounded_gt α (Finite.of_fintype α) (PreorderofLinearOrder r)) c Set.univ 
      (Set.mem_univ b) Set.univ_nonempty 
  rw [←habeq, ←haceq]
  


/- We will have to modify the "smallest facet" map, as linear orders are not eventually trivial (unless α is finite). The target of the new
map will be preorders that are linear except for the last block, i.e. where all blocks except one have size one.-/




/- Now we do some calculations. -/
/- Calculation: if we take the Descent partitition of the fixed linear order r itself, then we get the trivial preorder. -/

lemma DescentPartition_fixed_linear_order (r : LinearOrder α) : 
@DescentPartition α r (PreorderofLinearOrder r) r.le_total = trivialPreorder α := by
  apply Preorder.ext
  intro a b 
  change DescentPartition_aux r (PreorderofLinearOrder r) a b ↔ True 
  simp only [iff_true]
  cases (r.le_total a b) with
  | inl hab => exact Or.inl hab 
  | inr hba => apply Or.inr 
               rw [and_iff_right hba]
               exact fun c d => by tauto 

/- Conversely, the only linear order with trivial Descent partition is r itself.-/

lemma Preorder_lt_and_DescentPartition_ge_implies_LinearOrder_le (r : LinearOrder α) {s : Preorder α} (htot : Total s.le) {a b : α}
(hlt : s.lt a b) (hge : (DescentPartition r htot).le  b a) : r.le a b := by
  change DescentPartition_aux r s b a at hge
  unfold DescentPartition_aux at hge
  rw [or_iff_right (not_le_of_lt hlt)] at hge
  exact (hge.2 a a (s.le_refl a) (s.le_refl a) (le_of_lt hlt)).2.2

lemma DescentPartition_trivial_implies_fixed_linear_order (r : LinearOrder α) {s : Preorder α} (hlin : IsLinearOrder α s.le)
(htriv : DescentPartition r hlin.toIsTotal.total = trivialPreorder α) : s = PreorderofLinearOrder r := by
  apply Preorder.ext 
  intro a b 
  cases (LinearPreorder_trichotomy hlin a b) with 
  | inl hab => simp only [le_of_lt hab, true_iff]
               have hdba : (DescentPartition r hlin.toIsTotal.total).le b a := by rw [htriv]; triv  
               exact Preorder_lt_and_DescentPartition_ge_implies_LinearOrder_le r hlin.toIsTotal.total hab hdba 
  | inr hmid => cases hmid with
                | inl hba => simp only [not_le_of_lt hba, false_iff, not_le]
                             have hdab : (DescentPartition r hlin.toIsTotal.total).le a b := by rw [htriv]; triv  
                             have hrba := Preorder_lt_and_DescentPartition_ge_implies_LinearOrder_le r hlin.toIsTotal.total hba hdab 
                             rw [lt_iff_le_and_ne, and_iff_right hrba]
                             exact ne_of_lt hba
                | inr heq => rw [heq]; simp only [_root_.le_refl, true_iff]; exact r.le_refl _ 

/- Second calculation: the descent partition of the dual of the fixed linear order r is equal to r itself. -/

lemma DescentPartition_dual_fixed_linear_order (r : LinearOrder α) : 
@DescentPartition α r (PreorderofLinearOrder (dual r)) (dual r).le_total = PreorderofLinearOrder (dual r) := by 
  apply Preorder.ext 
  intro a b 
  change DescentPartition_aux r (PreorderofLinearOrder (dual r)) a b ↔ _  
  unfold DescentPartition_aux 
  simp only [or_iff_left_iff_imp]
  exact fun ⟨hba, h⟩ => (h b b ((dual r).le_refl b) ((dual r).le_refl b) hba).2.2  


/- Conversely, we would like to say that if the descent partition of a linear order s is equal to itself, then s has to be the dual of r.
But this is not true in general, for example if r is the usual order on ℕ and s is the linear order
.....6,4,2,0,....,5,3,1. So we need a condition on s, which is that s is locally finite (i.e. bounded intervals are finite).-/

lemma DescentPartition_linear_implies_dual_linear_order (r : LinearOrder α) {s : Preorder α} (hlin : IsLinearOrder α s.le)
(heq : DescentPartition r hlin.toIsTotal.total = s) : s = PreorderofLinearOrder (dual r) := by sorry  







end LinearOrderedPartitions