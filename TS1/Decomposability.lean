import TS1.AbstractSimplicialComplex 
import TS1.FacePoset
import TS1.OrderOnFacets 

set_option autoImplicit false

universe u 

variable {α : Type u} {K : AbstractSimplicialComplex α}

/- An abstract simplicial K is called decomposable if there exists a map R (for "restriction") to K.facets to K.faces ∪ {∅} (which we will write as a map
from K.facets to Finset α) such that K.faces is the disjoint union of the intervals [R(s),s]. (If R(s) is empty, then [R(s),s] is by convention the
half-infinite interval [<-,s].) For every face s of K, there is then a unique facet t such that s ∈ [R(t),t]; we write t = DF(s) (for "distinguished
facet"). We will actually define decomposability using the maps R and DF rather than the disjoint union decomposition. Note that the map R is not
uniquely determined by the decomposition, only the intervals [R(s),s] are. (If s is a vertex, then [s,s]=[∅,s]). -/

namespace AbstractSimplicialComplex 

/- Definition of decomposability. -/


def IsDecomposition (R : K.facets → Finset α)  (DF : K.faces → K.facets) : Prop := 
(∀ (s : K.facets), R s ⊆ s.1) ∧ (∀ (s : K.faces) (t : K.facets), (R t ⊆ s.1 ∧ s.1 ⊆ t.1) ↔ t = DF s)

lemma Decomposition_DF_bigger_than_source {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF) (s : K.faces) :
s.1 ⊆ (DF s).1 := ((hdec.2 s (DF s)).mpr rfl).2  

lemma Decomposition_is_union {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF) (s : K.faces) : 
∃ (t : K.facets), R t ⊆ s.1 ∧ s.1 ⊆ t.1 := ⟨DF s, (hdec.2 s (DF s)).mpr rfl⟩

lemma Decomposition_is_disjoint {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF) (s : K.faces) 
{t₁ t₂ : K.facets} (hst₁ : R t₁ ⊆ s.1 ∧ s.1⊆ t₁.1) (hst₂ : R t₂ ⊆ s.1 ∧ s.1 ⊆ t₂.1) : t₁ = t₂ := by 
  erw [hdec.2 s t₁] at hst₁  
  erw [hdec.2 s t₂] at hst₂
  exact Eq.trans hst₁ (Eq.symm hst₂)

lemma Decomposition_DF_of_a_facet {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF) (s : K.facets) :
 s = DF ⟨s.1, facets_subset s.2⟩ := (hdec.2 ⟨s.1, facets_subset s.2⟩ s).mp ⟨hdec.1 s, by simp only [subset_refl]⟩


lemma Decomposition_image_of_R {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF) {s : K.facets}
(hne : R s ≠ ∅) : R s ∈ K.faces := 
K.down_closed (facets_subset s.2) (hdec.1 s) (by rw [←Finset.nonempty_iff_ne_empty] at hne; exact hne) 

lemma Decomposition_image_of_R' {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF) (s : K.facets) :
R s = ∅ ∨ R s ∈ K.faces := by
  by_cases he : R s = ∅
  . exact Or.inl he 
  . exact Or.inr (Decomposition_image_of_R hdec he)


lemma Decomposition_SF_composed_with_R {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF) {s : K.facets} 
(hne : R s ≠ ∅) : s = DF (⟨R s, Decomposition_image_of_R hdec hne⟩ : K.faces) := by 
  rw [←(hdec.2)]
  simp only [Finset.Subset.refl, Finset.le_eq_subset, true_and]
  exact hdec.1 s 


lemma Decomposition_R_determines_DF {R : K.facets → Finset α}  {DF₁ : K.faces → K.facets} {DF₂ : K.faces → K.facets} 
(hdec₁ : IsDecomposition R DF₁) (hdec₂ : IsDecomposition R DF₂) : DF₁ = DF₂ := by 
  funext s 
  rw [←(hdec₂.2 s (DF₁ s))]
  rw [hdec₁.2 s (DF₁ s)]

open Classical 

noncomputable def Interval {s t : Finset α} (hs : s = ∅ ∨ s ∈ K.faces) (ht : t ∈ K.faces) : 
Finset (K.faces) := by 
  by_cases hse : s = ∅ 
  . exact Finset.Iic ⟨t, ht⟩  
  . rw [or_iff_right hse] at hs  
    exact Finset.Icc ⟨s, hs⟩ ⟨t, ht⟩  

@[reducible] noncomputable def DecompositionInterval {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF) 
(s : K.facets) := Interval (Decomposition_image_of_R' hdec s) (facets_subset s.2)

lemma DecompositionInterval_def {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF) (s : K.facets)
(t : K.faces) : t ∈ DecompositionInterval hdec s ↔ R s ≤ t ∧ t.1 ⊆ s.1 := by 
  unfold DecompositionInterval
  unfold Interval
  by_cases he : R s = ∅
  . simp only [he, gt_iff_lt, Subtype.mk_lt_mk, Finset.lt_eq_subset, Finset.not_ssubset_empty, dite_true, Finset.mem_Iic, 
      Finset.le_eq_subset, Finset.empty_subset, true_and]
    tauto
  . simp only [he, gt_iff_lt, Subtype.mk_lt_mk, Finset.lt_eq_subset, dite_false, Finset.mem_Icc, Finset.le_eq_subset]
    tauto

lemma DecompositionInterval_eq {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF) (s : K.facets)
(t : K.faces) : t ∈ DecompositionInterval hdec s ↔ s = DF t := by 
  unfold DecompositionInterval
  unfold Interval 
  by_cases he : R s = ∅ 
  . simp only [he, dite_true, Finset.mem_Iic]
    rw [←(hdec.2 t s), he]
    simp only [Finset.empty_subset, Finset.le_eq_subset, true_and]
    tauto
  . rw [←(hdec.2 t s)]
    simp only [he, gt_iff_lt, Subtype.mk_lt_mk, Finset.lt_eq_subset, dite_false, Finset.mem_Icc, Finset.le_eq_subset]
    tauto 


lemma Decomposition_DF_determines_R_intervals {R₁ : K.facets → Finset α}  {R₂ : K.facets → Finset α} {DF : K.faces → K.facets} 
(hdec₁ : IsDecomposition R₁ DF) (hdec₂ : IsDecomposition R₂ DF) (s : K.facets) : 
Interval (Decomposition_image_of_R' hdec₁ s) (facets_subset s.2) = Interval (Decomposition_image_of_R' hdec₂ s) (facets_subset s.2) := by
  ext t 
  rw [DecompositionInterval_eq hdec₁, DecompositionInterval_eq hdec₂]


/- The goal is to prove that if a linear order on the faces of K is compatible with a given decomposition, then it is a shelling order (provided it
is also well-founded). Here "compatible" means that, for a face s, the facet DF s is the smallest facet containing s. We will phrase this condition as:
for every face s and every facet t, is s is contained in t, then DF s is smaller than t for the order on the facets. It also makes sense for a partial
order on the facets, and is inherited by any linear order refining that partial order; we phrase it in that generality because the natural order on
the facets of the Coxeter complex is partial (and it satisfies the compatibility condition).-/


@[reducible] def CompatibleOrder (DF : K.faces → K.facets) (r : PartialOrder K.facets) : Prop :=
∀ (s : K.faces) (t : K.facets), s.1 ⊆ t.1 → r.le (DF s) t  


lemma OldFacesCompatibleOrder {DF : K.faces → K.facets} {r : PartialOrder K.facets} (hcomp : CompatibleOrder DF r) {s : K.facets}
{t : K.faces} (hts : t.1 ⊆ s.1) (hDFt : t.1 ⊆ (DF t).1) :
t.1 ∉ OldFaces r s ↔ DF t = s := by 
  rw [OldFaces_mem]
  push_neg
  constructor 
  . intro ht 
    apply eq_of_le_of_not_lt (hcomp t s hts)
    have h := ht t.2 hts (DF t) 
    rw [imp_not_comm] at h 
    exact h hDFt 
  . intro ht _ _ u hus htu 
    have h := @lt_of_le_of_lt _ (@PartialOrder.toPreorder _ r) _ _ _ (hcomp t u htu) hus   
    rw [ht] at h 
    exact (@ne_of_lt _ (@PartialOrder.toPreorder _ r) _ _ h) rfl 

lemma OldFacesDecomposition {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF)
{r : PartialOrder K.facets} (hcomp : CompatibleOrder DF r) {s : K.facets} {t : K.faces} (hts : t.1 ⊆ s.1) :
t.1 ∉ OldFaces r s ↔ t ∈ DecompositionInterval hdec s := by 
  rw [OldFacesCompatibleOrder hcomp hts (Decomposition_DF_bigger_than_source hdec t)]
  rw [DecompositionInterval_eq]
  tauto

lemma OldFacesDecomposition' {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF)
{r : PartialOrder K.facets} (hcomp : CompatibleOrder DF r) {s : K.facets} {t : K.faces} (hts : t.1 ⊆ s.1) :
t.1 ∉ OldFaces r s ↔ R s ≤ t := by 
  rw [OldFacesDecomposition hdec hcomp hts, DecompositionInterval_def]
  simp only [Finset.le_eq_subset, hts, and_true]

lemma OldFacesDecomposition_faces {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF)
{r : PartialOrder K.facets} (hcomp : CompatibleOrder DF r) {s : K.facets} {t : K.faces} (hts : t.1 ⊆ s.1) :
t.1 ∈ OldFaces r s ↔ ¬(R s ≤ t) := iff_not_comm.mp (Iff.symm (OldFacesDecomposition' hdec hcomp hts))



/- The complex of old faces is empty (i.e. s is π0 facet) if and only if the interval [R s, s] is equal to the half-infinite
interval [<-, s].-/

lemma OldFacesDecomposition_empty_iff {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF)
{r : PartialOrder K.facets} (hcomp : CompatibleOrder DF r) (s : K.facets) :
(OldFaces r s).faces = ∅ ↔ DecompositionInterval hdec s = Finset.Iic ⟨s.1, facets_subset s.2⟩ := by 
  constructor
  . intro he 
    ext t 
    rw [DecompositionInterval_def, Finset.mem_Iic] 
    constructor 
    .  exact fun ht => ht.2
    . intro hts
      erw [and_iff_left hts]
      rw [←(@OldFacesDecomposition' _ _ _ _ hdec _ hcomp s t hts)]
      change ¬(t.1 ∈ (OldFaces r s).faces)
      rw [he]
      simp only [Set.mem_empty_iff_false, not_false_eq_true]
  . intro hint 
    by_contra hne 
    rw [←ne_eq, ←Set.nonempty_iff_ne_empty] at hne 
    match hne with 
    | ⟨t, ht⟩ => have ht' := (OldFaces_mem r s t).mp ht
                 erw [@OldFacesDecomposition_faces _ _ _ _ hdec _ hcomp s ⟨t, ht'.1⟩ ht'.2.1] at ht  
                 have htint : (⟨t, ht'.1⟩ : K.faces) ∈ Finset.Iic ⟨s.1, facets_subset s.2⟩ := by
                   rw [Finset.mem_Iic]
                   exact ht'.2.1 
                 rw [←hint, DecompositionInterval_def] at htint
                 exact ht htint.1 
                  

/- The facets of the complex of old faces all have cardinality equal to card s - 1. -/

lemma OldFacesDecompositionDimensionFacets {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF)
{r : PartialOrder K.facets} (hcomp : CompatibleOrder DF r) (s : K.facets) (t : (OldFaces r s).facets) :
Finset.card t.1 = Finset.card s.1 - 1 := by 
  have htf := facets_subset t.2 
  have htf' := (OldFaces_mem r s t.1).mp htf 
  erw [@OldFacesDecomposition_faces _ _ _ _ hdec _ hcomp s ⟨t.1, htf'.1⟩ htf'.2.1, Finset.not_subset] at htf 
  match htf with 
  | ⟨a, ⟨has, hat⟩⟩ => set u := s.1 \ {a}
                       have hus : u ⊆ s.1 := Finset.sdiff_subset _ _ 
                       have htu : t.1 ⊆ u := by rw [Finset.subset_sdiff, Finset.disjoint_singleton_right]
                                                exact ⟨htf'.2.1, hat⟩
                       have hune : u.Nonempty := by match K.nonempty_of_mem htf'.1 with | ⟨a, ha⟩ => exact ⟨a, htu ha⟩                             
                       have huK : u ∈ K.faces := K.down_closed (facets_subset s.2) hus hune 
                       have huof : u ∈ (OldFaces r s).faces := by 
                         erw [@OldFacesDecomposition_faces _ _ _ _ hdec _ hcomp s ⟨u, huK⟩ hus, Finset.not_subset] 
                         exists a
                         rw [and_iff_right has]
                         apply Finset.not_mem_sdiff_of_mem_right
                         exact Finset.mem_singleton_self _ 
                       have has' : {a} ⊆ s.1 := by
                         rw [Finset.singleton_subset_iff]
                         exact (hdec.1 s) has 
                       rw [((mem_facets_iff (OldFaces r s) t.1).mp t.2).2 huof htu, Finset.card_sdiff has']     
                       rw [Finset.card_singleton]


/- The complex of old faces is pure. -/

lemma OldFacesDecompositionIsPure {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF)
{r : PartialOrder K.facets} (hcomp : CompatibleOrder DF r) (s : K.facets) : Pure (OldFaces r s) := 
Dimension_of_Noetherian_pure (Finite_implies_Noetherian (OldFacesFinite r s)) 
(fun t u htf huf => by rw [OldFacesDecompositionDimensionFacets hdec hcomp s ⟨t, htf⟩, OldFacesDecompositionDimensionFacets hdec hcomp s ⟨u, huf⟩])

/- If it is not empty, the complex of old faces has dimension card s - 2.-/

lemma OldFacesDecompositionDimension {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF)
{r : PartialOrder K.facets} (hcomp : CompatibleOrder DF r) (s : K.facets) (hne : (OldFaces r s).faces.Nonempty) :
dimension (OldFaces r s) = Finset.card s.1 - 2 := by 
  match (Noetherian_nonempty_implies_facets_exist (Finite_implies_Noetherian (OldFacesFinite r s)) hne) with
  | ⟨t, htf⟩ => rw [←((OldFacesDecompositionIsPure hdec hcomp s) htf), OldFacesDecompositionDimensionFacets hdec hcomp s ⟨t, htf⟩]
                erw [←ENat.coe_sub, WithTop.coe_eq_coe, Nat.cast_inj, Nat.sub_succ]
                

/- We define π₀ and homology facets without reference to an order on the facets (if the decomposition is compatible with a shelling order,
we will recover the usual notion). π₀ facets are the facets s such that the corresponding decomposition interval is Set.Iic s, and homology
facets are non-π₀ facets s such that the corresponding decomposition interval is reduced to s.-/
                
def IsPi0Facet {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF) (s : K.facets) : Prop :=
DecompositionInterval hdec s = Finset.Iic ⟨s.1, facets_subset s.2⟩ 

def IsHomologyFacet {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF) (s : K.facets) : Prop :=
¬(IsPi0Facet hdec s) ∧ DecompositionInterval hdec s = {⟨s.1, facets_subset s.2⟩}





end AbstractSimplicialComplex
