import TS1.FacePoset
import TS1.FintypeNECat
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.Order.Category.PartOrdCat
import Mathlib.Tactic
import Mathlib.AlgebraicTopology.SimplexCategory
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Functor.Category



set_option autoImplicit false

universe u 

open AbstractSimplicialComplex Classical SimplicialMap 

namespace CategoryTheory

@[nolint checkUnivs]
def AbstractSimplicialComplexCat :=
  Bundled AbstractSimplicialComplex.{u}


namespace AbstractSimplicialComplexCat

instance : CoeSort AbstractSimplicialComplexCat (Type u) where coe := Bundled.α

/-- Construct a bundled `AbstractSimplicialComplexCat` from the underlying type and the typeclass. -/
def of (V : Type u) (K : AbstractSimplicialComplex V) : AbstractSimplicialComplexCat.{u} :=
  @Bundled.of _ V K 

/-Not used.
lemma complex_of (α : Type u) (K : AbstractSimplicialComplex α) : (of α K).2 = K := sorry 
-/

instance : Inhabited AbstractSimplicialComplexCat :=
  ⟨AbstractSimplicialComplexCat.of Empty (@AbstractSimplicialComplex.Bot Empty).1⟩


/-- Morphisms. --/
protected def Hom (C D : AbstractSimplicialComplexCat) :=
  C.2 →ₛ D.2  

/-- Make a morphism from a simplicial map. -/
def mk {C D : AbstractSimplicialComplexCat} (f : C.2 →ₛ D.2) : AbstractSimplicialComplexCat.Hom C D :=
  f

/-- Category structure on `AbstractSimplicialComplexCat` -/
noncomputable instance category : LargeCategory.{u} AbstractSimplicialComplexCat.{u}
    where
  Hom C D := AbstractSimplicialComplexCat.Hom C D 
  id C := SimplicialMap.id C.2 
  comp F G := SimplicialMap.comp G F  




/- Forgetful functor to types (sends an abstract simplicial complex on α to the set of its vertices).-/

@[simps]
noncomputable def forget : AbstractSimplicialComplexCat.{u} ⥤ Type u 
    where
  obj C := C.2.vertices 
  map F := F.vertex_map 


/- Functor sending an abstract simplicial complex to its poset of faces.-/


@[simps]
noncomputable def FacePoset : AbstractSimplicialComplexCat.{u} ⥤ PartOrdCat.{u}
    where
  obj C := PartOrdCat.of C.2.faces 
  map F := SimplicialMap.toFaceMapOrderHom F  
  map_id := fun C => by simp only; unfold SimplicialMap.toFaceMapOrderHom 
                        apply OrderHom.ext 
                        simp only 
                        change SimplicialMap.toFaceMap (SimplicialMap.id C.2) = _ 
                        rw [id_toFaceMap]
                        aesop        
  map_comp := fun f g => by simp only; unfold SimplicialMap.toFaceMapOrderHom  
                            apply OrderHom.ext 
                            erw [OrderHom.comp_coe] 
                            simp only [PartOrdCat.coe_of] 
                            exact SimplicialMap.toFaceMap_comp f g  



/- The category of abstract simplicial complexes is equivalent to a full sucategory of the category of presheaves on the category
of finite nonempty sets FintypeNECat. We first construct the functor from FintypeNECat to AbstractSimplicialComplexCat, then the
fully faithful embedding will be the composition of the Yoneda embedding and of this functor.-/


noncomputable def FintypeNEtoAbstractSimplicialComplex : FintypeNECat ⥤ AbstractSimplicialComplexCat where 
  obj α := @AbstractSimplicialComplexCat.of α (Simplex α)  
  map f := by simp only; apply AbstractSimplicialComplexCat.mk; exact MapSimplex f   
  map_id := by aesop
  map_comp := by aesop  


noncomputable def AbstractSimplicialComplextoPresheaf : AbstractSimplicialComplexCat ⥤ FintypeNECatᵒᵖ ⥤ Type u := by
  apply curry.obj 
  refine (Prod.swap _ _) ⋙ ?_ 
  refine ?_ ⋙ (Functor.hom AbstractSimplicialComplexCat)
  refine Functor.prod ?_ (Functor.id _)
  exact Functor.op FintypeNEtoAbstractSimplicialComplex 


lemma AbstractSimplicialComplextoPresheaf_calculation_map1 {K L : AbstractSimplicialComplexCat} (f : K ⟶ L)
(S : FintypeNECatᵒᵖ) :
(AbstractSimplicialComplextoPresheaf.map f).app S = (fun g => f.comp g) := by 
  unfold AbstractSimplicialComplextoPresheaf 
  simp only [curry_obj_obj_obj, Functor.comp_obj, Prod.swap_obj, Functor.prod_obj, Functor.op_obj,
  Functor.id_obj, Functor.hom_obj, Opposite.unop_op, curry_obj_map_app, Functor.comp_map, Prod.swap_map,
  Functor.prod_map, Functor.op_map, unop_id, Functor.map_id, op_id, Functor.id_map]
  tauto 



lemma AbstractSimplicialComplextoPresheaf_calculation_map2 (K : AbstractSimplicialComplexCat) {S T : FintypeNECatᵒᵖ}
(f : S ⟶ T) : (AbstractSimplicialComplextoPresheaf.obj K).map f = fun g => g.comp (MapSimplex f.unop) := by 
  ext g 
  unfold AbstractSimplicialComplextoPresheaf 
  simp only [curry_obj_obj_obj, Functor.comp_obj, Prod.swap_obj, Functor.prod_obj, Functor.op_obj,
  Functor.id_obj, Functor.hom_obj, Opposite.unop_op, curry_obj_obj_map, Functor.comp_map, Prod.swap_map,
  Functor.prod_map, Functor.op_map, Functor.id_map, Functor.hom_map, Quiver.Hom.unop_op, Category.comp_id]
  unfold FintypeNEtoAbstractSimplicialComplex 
  simp only [id_eq]
  tauto 



/- We need a more explicit description of this functor.-/

def HomTypetoAbstractSimplicialComplex (α : Type u) {β : Type u} (K : AbstractSimplicialComplex β) :
Type u := {f : α → β | ∀ (S : Finset α), S.Nonempty → Finset.image f S ∈ K.faces}

/-A morphism from Simplex α to K defines an element of HomTypetoAbstractSimplicialComplex α K.-/
def HomSimplexTypetoAbstractSimplicialComplex {α β : Type u} {K : AbstractSimplicialComplex β} 
(f : Simplex α →ₛ K) : HomTypetoAbstractSimplicialComplex α K := by 
  set g : α → β := by 
    intro a 
    have hav : a ∈ (Simplex α).vertices := by
      rw [vertices_Simplex]
      simp only [Set.top_eq_univ, Set.mem_univ]
    exact (f.vertex_map ⟨a, hav⟩).1
  refine ⟨g, ?_⟩
  intro S hSne 
  have hSf : S ∈ (Simplex α).faces := by rw [←faces_Simplex]; exact hSne 
  have heq : Finset.image g S = (f.toFaceMap ⟨S, hSf⟩).1 := by 
    unfold toFaceMap 
    ext b 
    simp only [Finset.mem_image, Subtype.exists]
    constructor 
    . intro hb  
      match hb with 
      | ⟨a, haS, hab⟩ => 
        exists a 
        have hav : a ∈ (Simplex α).vertices := by rw [vertices_Simplex]; simp only [Set.top_eq_univ, Set.mem_univ]
        exists hav 
        rw [face_to_finset_vertices_mem']
        exact ⟨haS, hab⟩
    . intro hb 
      match hb with 
      | ⟨a, hav, haS, hab⟩ => 
        exists a 
        rw [face_to_finset_vertices_mem'] at haS 
        rw [and_iff_right haS]
        exact hab 
  rw [heq]
  exact (f.toFaceMap ⟨S, hSf⟩).2

lemma HomTypetoAbstractSimplicialComplex_image {α β : Type u} {K : AbstractSimplicialComplex β}
(f : HomTypetoAbstractSimplicialComplex α K) (a : α) : f.1 a ∈ K.vertices := by 
  rw [mem_vertices, ←Finset.image_singleton]
  exact f.2 _ (Finset.singleton_nonempty _)

def HomTypetoAbstractSimplicialComplex_func1 {α α' : Type u} (f : α → α') {β : Type u} (K : AbstractSimplicialComplex β) :
HomTypetoAbstractSimplicialComplex α' K → HomTypetoAbstractSimplicialComplex α K := by 
  intro g 
  refine ⟨g.1 ∘ f, ?_⟩
  intro S hSne 
  have heq : Finset.image (g.1 ∘ f) S = Finset.image g.1 (Finset.image f S) := by
    rw [←Finset.coe_inj, Finset.coe_image, Finset.coe_image, Finset.coe_image, Set.image_comp]
  rw [heq]
  apply g.2 
  simp only [Finset.Nonempty.image_iff]
  exact hSne 

lemma HomTypetoAbstractSimplicialComplex_func1_id (α : Type u) {β : Type u} (K : AbstractSimplicialComplex β) : 
HomTypetoAbstractSimplicialComplex_func1 (@id α) K = @_root_.id (HomTypetoAbstractSimplicialComplex α K) := by 
  ext f
  unfold HomTypetoAbstractSimplicialComplex_func1 
  simp only [Set.mem_setOf_eq, Function.comp.right_id, Subtype.coe_eta, id_eq]


lemma HomTypetoAbstractSimplicialComplex_func1_comp {α α' α'' : Type u} (f : α → α') (g : α' → α'')
{β : Type u} (K : AbstractSimplicialComplex β) : 
HomTypetoAbstractSimplicialComplex_func1 (g ∘ f) K = (HomTypetoAbstractSimplicialComplex_func1 f K) ∘ 
(HomTypetoAbstractSimplicialComplex_func1 g K) := by 
  ext h 
  unfold HomTypetoAbstractSimplicialComplex_func1 
  rw [←SetCoe.ext_iff]
  simp only [Set.mem_setOf_eq, Function.comp_apply]
  rfl 

def HomTypetoAbstractSimplicialComplex_func2 (α : Type u) {β β' : Type u} {K : AbstractSimplicialComplex β}
{L : AbstractSimplicialComplex β'} (f : K →ₛ L) :
HomTypetoAbstractSimplicialComplex α K → HomTypetoAbstractSimplicialComplex α L := by
  intro g 
  refine ⟨fun a => (f.vertex_map ⟨g.1 a, HomTypetoAbstractSimplicialComplex_image g a⟩).1, ?_⟩
  intro S hSne 
  set T := Finset.image g.1 S 
  have hTf : T ∈ K.faces := g.2 S hSne 
  have hTeq : (f.toFaceMap ⟨T, hTf⟩).1 = Finset.image (fun a => (f.vertex_map ⟨g.1 a, 
    HomTypetoAbstractSimplicialComplex_image g a⟩).1) S := by 
    ext b
    unfold toFaceMap 
    simp only [Set.mem_setOf_eq, Finset.mem_image, Subtype.exists]
    constructor 
    . intro hb 
      match hb with 
      | ⟨a, hav, haS, hab⟩ => 
        rw [face_to_finset_vertices_mem'] at haS 
        simp only [Finset.mem_image] at haS
        match haS with 
        | ⟨x, hxS, hxa⟩ => 
          exists x 
          rw [and_iff_right hxS]
          simp_rw [hxa]
          exact hab 
    . intro hb 
      match hb with 
      | ⟨a, haS, hab⟩ => 
        simp_rw [face_to_finset_vertices_mem']
        exists (g.1 a)
        have hav : g.1 a ∈ K.vertices := by 
          rw [mem_vertices_iff]
          exists ⟨T, hTf⟩
          simp only [Set.mem_setOf_eq, Finset.mem_image]
          exists a 
        exists hav
        rw [and_iff_right (Finset.mem_image_of_mem _ haS)]
        exact hab  
  rw [←hTeq]
  exact (f.toFaceMap ⟨T, hTf⟩).2

def HomTypetoAbstractSimplicialComplex_func1_func2 {α α' : Type u} (g : α → α') {β β' : Type u} {K : AbstractSimplicialComplex β}
{L : AbstractSimplicialComplex β'} (f : K →ₛ L) :
(HomTypetoAbstractSimplicialComplex_func2 α f) ∘ (HomTypetoAbstractSimplicialComplex_func1 g K) =
(HomTypetoAbstractSimplicialComplex_func1 g L) ∘ (HomTypetoAbstractSimplicialComplex_func2 α' f) := by 
  ext h 
  unfold HomTypetoAbstractSimplicialComplex_func1 HomTypetoAbstractSimplicialComplex_func2 
  simp only [Set.mem_setOf_eq, Function.comp_apply]
  rw [←SetCoe.ext_iff]
  simp only 
  ext a 
  simp only [Function.comp_apply]

/- Conversely, an element of HomTypetoAbstractSimplicialComplex α K defines a moprhism of abstract simplicial complexes
from Simplex α to K.-/

noncomputable def HomTypetoAbstractSimplicialComplextoSimplicialMap {α β : Type u} {K : AbstractSimplicialComplex β}
(f : HomTypetoAbstractSimplicialComplex α K) : Simplex α →ₛ K := by
  apply SimplicialMapofMap f.1 
  intro s hsf 
  rw [←faces_Simplex] at hsf 
  exact f.2 s hsf  



/- We finally introduce the functor that will be isomorphic to AbstractSimplicialComplextoPresheaf.-/

def AbstractSimplicialComplextoPresheaf_obj {α : Type u} (K : AbstractSimplicialComplex α) : FintypeNECatᵒᵖ ⥤ Type u 
    where
  obj S := HomTypetoAbstractSimplicialComplex S.1 K  
  map f := HomTypetoAbstractSimplicialComplex_func1 f.1 K 
  map_id := fun S => HomTypetoAbstractSimplicialComplex_func1_id S.1 K  
  map_comp := fun f g => HomTypetoAbstractSimplicialComplex_func1_comp g.1 f.1 K 

def AbstractSimplicialComplextoPresheaf_map {α β : Type u} {K : AbstractSimplicialComplex α} {L : AbstractSimplicialComplex β}
(f : K →ₛ L) : AbstractSimplicialComplextoPresheaf_obj K ⟶ AbstractSimplicialComplextoPresheaf_obj L 
    where 
  app S := HomTypetoAbstractSimplicialComplex_func2 S.1 f   
  naturality _ _ g := HomTypetoAbstractSimplicialComplex_func1_func2 g.1 f  

lemma AbstractSimplicialComplextoPresheaf_map_id {α : Type u} (K : AbstractSimplicialComplex α) :
AbstractSimplicialComplextoPresheaf_map (SimplicialMap.id K) = NatTrans.id (AbstractSimplicialComplextoPresheaf_obj K) := by 
  ext S f  
  unfold AbstractSimplicialComplextoPresheaf_map AbstractSimplicialComplextoPresheaf_obj SimplicialMap.id 
  simp only [NatTrans.id_app', types_id_apply]
  unfold HomTypetoAbstractSimplicialComplex_func2 
  simp only [Set.mem_setOf_eq, Subtype.coe_eta]

lemma AbstractSimplicialComplextoPresheaf_map_comp {α β γ : Type u} {K : AbstractSimplicialComplex α} 
{L : AbstractSimplicialComplex β} {M : AbstractSimplicialComplex γ} (f : K →ₛ L) (g : L →ₛ M) :
AbstractSimplicialComplextoPresheaf_map (g.comp f) = 
(AbstractSimplicialComplextoPresheaf_map f) ≫ (AbstractSimplicialComplextoPresheaf_map g) := by 
  unfold AbstractSimplicialComplextoPresheaf_map 
  ext S h 
  simp only [FunctorToTypes.comp]
  unfold HomTypetoAbstractSimplicialComplex_func2 SimplicialMap.comp 
  simp only [Set.mem_setOf_eq, Function.comp_apply, Subtype.coe_eta]

noncomputable def AbstractSimplicialComplextoPresheaf2 : AbstractSimplicialComplexCat ⥤ FintypeNECatᵒᵖ ⥤ Type u where 
  obj K := AbstractSimplicialComplextoPresheaf_obj K.2  
  map f := AbstractSimplicialComplextoPresheaf_map f 
  map_id K := AbstractSimplicialComplextoPresheaf_map_id K.2
  map_comp f g := AbstractSimplicialComplextoPresheaf_map_comp f g 


/- We need to compare the two definitions, i.e. to define an isomorphism of functors between them.-/

def AbstractSimplicialComplextoPresheaf_comp_app_aux (K : AbstractSimplicialComplexCat) (S : FintypeNECatᵒᵖ) :
(AbstractSimplicialComplextoPresheaf.obj K).obj S → (AbstractSimplicialComplextoPresheaf2.obj K).obj S := 
fun f => HomSimplexTypetoAbstractSimplicialComplex f 

lemma AbstractSimplicialComplextoPresheaf_comp_app_aux_natural (K : AbstractSimplicialComplexCat.{u})
{S T : FintypeNECat.{u}ᵒᵖ} (f : S ⟶ T) :
((AbstractSimplicialComplextoPresheaf.obj K).map f) ≫ (AbstractSimplicialComplextoPresheaf_comp_app_aux K T) = 
CategoryTheory.types.comp (AbstractSimplicialComplextoPresheaf_comp_app_aux K S)
((AbstractSimplicialComplextoPresheaf2.obj K).map f) := by 
  ext g 
  rw [AbstractSimplicialComplextoPresheaf_calculation_map2]
  simp only [Prod.swap_obj, Functor.prod_obj, Functor.op_obj, Functor.id_obj, Opposite.unop_op,
  types_comp_apply]
  unfold AbstractSimplicialComplextoPresheaf_comp_app_aux
  simp only [eq_mpr_eq_cast, cast_eq]
  unfold AbstractSimplicialComplextoPresheaf2 AbstractSimplicialComplextoPresheaf_obj AbstractSimplicialComplextoPresheaf_map
  simp only 
  unfold HomTypetoAbstractSimplicialComplex_func1  
  rw [←SetCoe.ext_iff]
  simp only [Set.mem_setOf_eq]
  unfold HomSimplexTypetoAbstractSimplicialComplex 
  simp only 
  ext a 
  unfold comp
  simp only [Function.comp_apply]
  unfold MapSimplex 
  simp only 
  tauto 
  

def AbstractSimplicialComplextoPresheaf_comp_app (K : AbstractSimplicialComplexCat) :
AbstractSimplicialComplextoPresheaf.obj K ⟶ AbstractSimplicialComplextoPresheaf2.obj K 
    where 
  app S := AbstractSimplicialComplextoPresheaf_comp_app_aux K S  
  naturality _ _ f := AbstractSimplicialComplextoPresheaf_comp_app_aux_natural K f 


noncomputable def AbstractSimplicialComplextoPresheaf_comp_app_inv_aux (K : AbstractSimplicialComplexCat) (S : FintypeNECatᵒᵖ) :
(AbstractSimplicialComplextoPresheaf2.obj K).obj S → (AbstractSimplicialComplextoPresheaf.obj K).obj S :=  
  fun g => HomTypetoAbstractSimplicialComplextoSimplicialMap g 

  lemma AbstractSimplicialComplextoPresheaf_comp_app_inv_aux_natural (K : AbstractSimplicialComplexCat.{u})
{S T : FintypeNECat.{u}ᵒᵖ} (f : S ⟶ T) :
((AbstractSimplicialComplextoPresheaf2.obj K).map f) ≫ (AbstractSimplicialComplextoPresheaf_comp_app_inv_aux K T) = 
CategoryTheory.types.comp (AbstractSimplicialComplextoPresheaf_comp_app_inv_aux K S)
((AbstractSimplicialComplextoPresheaf.obj K).map f) := by tauto 
  

noncomputable def AbstractSimplicialComplextoPresheaf_comp_app_inv (K : AbstractSimplicialComplexCat) :
AbstractSimplicialComplextoPresheaf2.obj K ⟶ AbstractSimplicialComplextoPresheaf.obj K 
    where 
  app S := AbstractSimplicialComplextoPresheaf_comp_app_inv_aux K S 
  naturality _ _ f := AbstractSimplicialComplextoPresheaf_comp_app_inv_aux_natural K f 

noncomputable def AbstractSimplicialComplextoPresheaf_comp_app_equiv (K : AbstractSimplicialComplexCat) :
AbstractSimplicialComplextoPresheaf.obj K ≅ AbstractSimplicialComplextoPresheaf2.obj K 
    where 
  hom := AbstractSimplicialComplextoPresheaf_comp_app K  
  inv := AbstractSimplicialComplextoPresheaf_comp_app_inv K 
  hom_inv_id := by tauto  
  inv_hom_id := by tauto 


lemma AbstractSimplicialComplextoPresheaf_comp_naturality {K L : AbstractSimplicialComplexCat} (f : K ⟶ L) :
(AbstractSimplicialComplextoPresheaf.map f) ≫ (AbstractSimplicialComplextoPresheaf_comp_app L) =
(AbstractSimplicialComplextoPresheaf_comp_app K) ≫ (AbstractSimplicialComplextoPresheaf2.map f) := by 
  ext S g 
  unfold AbstractSimplicialComplextoPresheaf2 AbstractSimplicialComplextoPresheaf_map AbstractSimplicialComplextoPresheaf_obj 
  simp only [FunctorToTypes.comp]
  rw [AbstractSimplicialComplextoPresheaf_calculation_map1]
  rw [←SetCoe.ext_iff]
  unfold HomTypetoAbstractSimplicialComplex_func2 
  simp only [Set.mem_setOf_eq, Prod.swap_obj, Functor.prod_obj, Functor.op_obj, Functor.id_obj,
  Opposite.unop_op]
  ext a 
  simp only 
  unfold AbstractSimplicialComplextoPresheaf_comp_app AbstractSimplicialComplextoPresheaf_comp_app_aux 
  simp only [eq_mpr_eq_cast, cast_eq]
  tauto 


def AbstractSimplicialComplextoPresheaf_comp : AbstractSimplicialComplextoPresheaf ⟶ AbstractSimplicialComplextoPresheaf2 
    where 
  app := AbstractSimplicialComplextoPresheaf_comp_app
  naturality _ _ f := AbstractSimplicialComplextoPresheaf_comp_naturality f 


noncomputable def AbstractSimplicialComplextoPresheaf_comp_inv : 
AbstractSimplicialComplextoPresheaf2 ⟶ AbstractSimplicialComplextoPresheaf 
    where 
  app := AbstractSimplicialComplextoPresheaf_comp_app_inv
  naturality _ _ f := by tauto 

noncomputable def AbstractSimplicialComplextoPresheaf_comp_equiv :
AbstractSimplicialComplextoPresheaf ≅ AbstractSimplicialComplextoPresheaf2 
    where 
  hom := AbstractSimplicialComplextoPresheaf_comp 
  inv := AbstractSimplicialComplextoPresheaf_comp_inv 
  hom_inv_id := by tauto 
  inv_hom_id := by tauto 


/- We construct a left adjoint of AbstractSimplicialComplexPresheaf2. -/

def ElementtoMap {S : FintypeNECat.{u}ᵒᵖ} (a : S.unop.1) : S ⟶ (Opposite.op (FintypeNECat.of PUnit)) := by 
  apply Quiver.Hom.op 
  exact fun _ => a 


def PresheafMap (F : FintypeNECat.{u}ᵒᵖ ⥤ Type u) {S : FintypeNECatᵒᵖ} (e : F.obj S) : 
S.unop.1 → F.obj (Opposite.op (FintypeNECat.of PUnit)) :=  
fun a => F.map (ElementtoMap a) e  

def PresheafFaces (F : FintypeNECat.{u}ᵒᵖ ⥤ Type u) :=
{s : Finset (F.obj (Opposite.op (FintypeNECat.of PUnit))) | ∃ (S : FintypeNECatᵒᵖ) (e : F.obj S), s = Finset.image (PresheafMap F e) ⊤} 

lemma PresheafFaces_down_closed {F : FintypeNECat.{u}ᵒᵖ ⥤ Type u} {s t : Finset (F.obj (Opposite.op (FintypeNECat.of PUnit)))}
(hsf : s ∈ PresheafFaces F) (hts : t ⊆ s) (htne : Finset.Nonempty t) : t ∈ PresheafFaces F := by 
  match hsf with 
  | ⟨S, e, hSs⟩ => 
      set T' := @Finset.filter S.unop.1 (fun a => PresheafMap F e a ∈ t) _ ⊤ 
      letI htfin : Fintype T' := Finset.fintypeCoeSort _ 
      letI htne : Nonempty T' := by 
        simp only [Finset.top_eq_univ, Finset.mem_univ, forall_true_left, Finset.mem_filter, true_and,
  nonempty_subtype]
        cases htne with
        | intro a hat => 
          have has := hts hat
          rw [hSs] at has 
          simp only [Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ, true_and] at has
          cases has with 
          | intro x hxa => 
            exists x; rw [hxa]; exact hat
      letI : FintypeNE T' := {htfin with Nonempty := htne}  
      set T := Opposite.op (FintypeNECat.of T') 
      set f : S ⟶ T := by 
        apply Quiver.Hom.op 
        exact fun ⟨a, _⟩ => a 
      set e' := F.map f e 
      exists T; exists e' 
      ext a 
      constructor 
      . intro hat 
        have has := hts hat 
        rw [hSs] at has 
        simp only [Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ, true_and] at has
        match has with 
        | ⟨x, hxa⟩ => 
          have hxT : x ∈ T' := by 
            simp only [Finset.top_eq_univ, Finset.mem_univ, forall_true_left, Finset.mem_filter, hxa, hat, and_self]
          have hxa' : a = PresheafMap F e' ⟨x, hxT⟩ := by 
            rw [←hxa]
            unfold PresheafMap ElementtoMap
            simp only [Finset.top_eq_univ, Opposite.unop_op]
            change _ = ((F.map _) ≫ (F.map _)) _ 
            rw [←F.map_comp] 
            tauto
          rw [hxa']
          simp only [Finset.top_eq_univ, Opposite.unop_op, Finset.mem_image, Finset.mem_univ, true_and,
  exists_apply_eq_apply]
      . intro hat 
        simp only [Finset.top_eq_univ, Opposite.unop_op, Finset.mem_image, Finset.mem_univ, true_and] at hat
        match hat with 
        | ⟨⟨x, hxT⟩, hxa⟩ => 
          simp only [Finset.mem_univ, forall_true_left, Finset.mem_filter, true_and] at hxT
          have haT' : a = PresheafMap F e x := by 
            rw [←hxa]
            unfold PresheafMap ElementtoMap 
            change ((F.map _) ≫ (F.map _)) _ = _
            rw [←F.map_comp]
            tauto  
          rw [haT']; exact hxT 



def PresheaftoAbstractSimplicialComplex_obj (F : FintypeNECat.{u}ᵒᵖ ⥤ Type u) : AbstractSimplicialComplexCat.{u} := by
  apply AbstractSimplicialComplexCat.of (F.obj (Opposite.op (FintypeNECat.of PUnit)))
  refine {faces := PresheafFaces F, nonempty_of_mem := ?_, down_closed := PresheafFaces_down_closed}
  intro s hsf 
  unfold PresheafFaces at hsf 
  simp only [Finset.top_eq_univ, Set.mem_setOf_eq] at hsf
  match hsf with 
  | ⟨S, e, hSs⟩ => 
    rw [hSs]
    simp only [Finset.Nonempty.image_iff]
    rw [Finset.univ_nonempty_iff]
    exact S.unop.2.2


noncomputable def PresheaftoAbstractSimplicialComplex_map {F : FintypeNECat.{u}ᵒᵖ ⥤ Type u} 
{G : FintypeNECat.{u}ᵒᵖ ⥤ Type u} (u : F ⟶ G) :
PresheaftoAbstractSimplicialComplex_obj F ⟶ PresheaftoAbstractSimplicialComplex_obj G := by
  set f : (F.obj (Opposite.op (FintypeNECat.of PUnit))) → (G.obj (Opposite.op (FintypeNECat.of PUnit))) := u.app _  
  apply SimplicialMapofMap f 
  intro s hsf 
  match hsf with 
  | ⟨S, e, hSs⟩ => 
    exists S 
    exists u.app S e 
    simp only 
    rw [hSs, Finset.image_image] 
    unfold PresheafMap 
    ext a 
    simp only [Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ, Function.comp_apply, true_and]
    constructor 
    . intro ha  
      cases ha with 
      | intro x hxa => 
        change ((F.map _) ≫ (u.app _)) _ = _ at hxa
        rw [u.naturality] at hxa 
        exists x  
    . intro ha 
      cases ha with 
      | intro x hxa => 
        change ((u.app _) ≫ (G.map _)) _ = _ at hxa 
        rw [←u.naturality] at hxa 
        exists x     


lemma PresheaftoAbstractSimplicialComplex_map_id (F : FintypeNECat.{u}ᵒᵖ ⥤ Type u) :
PresheaftoAbstractSimplicialComplex_map (CategoryStruct.id F) = SimplicialMap.id (PresheaftoAbstractSimplicialComplex_obj F).2 := 
by tauto

lemma PresheaftoAbstractSimplicialComplex_map_comp {F : FintypeNECat.{u}ᵒᵖ ⥤ Type u} {G : FintypeNECat.{u}ᵒᵖ ⥤ Type u} 
{H : FintypeNECat.{u}ᵒᵖ ⥤ Type u} (u : F ⟶ G) (v : G ⟶ H) :
PresheaftoAbstractSimplicialComplex_map (u ≫ v) = 
(PresheaftoAbstractSimplicialComplex_map u) ≫ (PresheaftoAbstractSimplicialComplex_map v) := by tauto 


noncomputable def PresheaftoAbstractSimplicialComplex : (FintypeNECat.{u}ᵒᵖ ⥤ Type u) ⥤ AbstractSimplicialComplexCat.{u} where 
  obj F := PresheaftoAbstractSimplicialComplex_obj F    
  map u := PresheaftoAbstractSimplicialComplex_map u 
  map_id F := PresheaftoAbstractSimplicialComplex_map_id F
  map_comp u v := PresheaftoAbstractSimplicialComplex_map_comp u v  


/- Now we need the unit and counit of the adjunction. -/

/- Unit.-/

noncomputable def Unit.PresheaftoAbstractSimplicialComplex_app (K : AbstractSimplicialComplexCat.{u}) :
K ⟶ PresheaftoAbstractSimplicialComplex.obj (AbstractSimplicialComplextoPresheaf2.obj K) := by
  set L := PresheaftoAbstractSimplicialComplex.obj (AbstractSimplicialComplextoPresheaf2.obj K)
  set f : K.2.vertices → L.1 := by 
    intro ⟨a, hav⟩ 
    change ((AbstractSimplicialComplextoPresheaf2.obj K).obj (Opposite.op (FintypeNECat.of PUnit)))
    unfold AbstractSimplicialComplextoPresheaf2 AbstractSimplicialComplextoPresheaf_obj 
      HomTypetoAbstractSimplicialComplex
    simp only [Opposite.unop_op, Set.coe_setOf]
    refine ⟨fun _ => a, ?_⟩ 
    intro s hsne 
    simp only [Opposite.unop_op] at s
    have heq : Finset.image (fun _ => a) s = {a} := sorry 
    rw [heq]
    erw [←mem_vertices]
    exact hav 
  have hf : ∀ {a : K.1} (hav : a ∈ K.2.vertices), f ⟨a, hav⟩ ∈ L.2.vertices := sorry
  set f' : K.2.vertices → L.2.vertices := fun a => ⟨f a, hf a.2⟩  
  refine {vertex_map := f', face :=?_}
  sorry 


#exit 

noncomputable def Unit.PresheaftoAbstractSimplicialComplex : 𝟭 AbstractSimplicialComplexCat.{u} ⟶
AbstractSimplicialComplextoPresheaf2 ⋙ PresheaftoAbstractSimplicialComplex where
  app := sorry 
  naturality := sorry


/- Counit. -/

noncomputable def Counit.PresheaftoAbstractSimplicialComplex : 
PresheaftoAbstractSimplicialComplex ⋙ AbstractSimplicialComplextoPresheaf2 ⟶ 
(𝟭 (FintypeNECat.{u}ᵒᵖ ⥤ Type u)) where 
  app := sorry 
  naturality := sorry 



/- We prove that the functors AbstractSimplicialComplextoPresheaf(2) are fully faithful.-/

lemma AbstractSimplicialComplextoPresheaf2_faithful_aux {K L : AbstractSimplicialComplexCat} (f : K ⟶ L)
{S : FintypeNECatᵒᵖ} (h : (AbstractSimplicialComplextoPresheaf2.obj K).obj S) (a : S.unop)
(hav : h.1 a ∈ K.2.vertices) :
f.vertex_map ⟨h.1 a, hav⟩ = ((AbstractSimplicialComplextoPresheaf2.map f).app S h).1 a := by 
  unfold AbstractSimplicialComplextoPresheaf2 AbstractSimplicialComplextoPresheaf_map
  simp only [Set.mem_setOf_eq]
  unfold HomTypetoAbstractSimplicialComplex_func2
  simp only [Set.mem_setOf_eq]
  

lemma AbstractSimplicialComplextoPresheaf2_faithful : Faithful AbstractSimplicialComplextoPresheaf2 where
map_injective := by
  intro K L f g heq
  change _ = (_ : SimplicialMap K.2 L.2)
  ext ⟨a, hav⟩
  set S:= Opposite.op (FintypeNECat.of PUnit.{u_1+1}) 
  set h : (AbstractSimplicialComplextoPresheaf2.obj K).obj S := by 
    refine ⟨fun _ => a, ?_⟩
    simp only [Opposite.unop_op, Set.mem_setOf_eq]
    intro s hsne 
    have hs : s = {PUnit.unit} := by 
      simp only [Opposite.unop_op] at s
      unfold FintypeNECat.of Bundled.of at s 
      simp only at s
      ext a 
      simp only [Opposite.unop_op, Finset.mem_singleton, iff_true]
      match hsne with 
      | ⟨b, hbs⟩ => have hab : a = b := by simp 
                    rw [hab]; exact hbs 
    simp only [hs, Opposite.unop_op, Finset.image_singleton]
    rw [mem_vertices] at hav 
    exact hav 
  rw [AbstractSimplicialComplextoPresheaf2_faithful_aux f h PUnit.unit, 
    AbstractSimplicialComplextoPresheaf2_faithful_aux g h PUnit.unit, heq]
  

lemma AbstractSimplicialComplextoPresheaf2_full : Full AbstractSimplicialComplextoPresheaf2 where
  preimage := by 
    intro K L F 
    sorry  
  witness := sorry 


lemma AbstractSimplicialComplextoPresheaf_faithful : Faithful AbstractSimplicialComplextoPresheaf := 
@Faithful.of_iso _ _ _ _ _ _ AbstractSimplicialComplextoPresheaf2_faithful AbstractSimplicialComplextoPresheaf_comp_equiv.symm  



lemma AbstractSimplicialComplextoPresheaf_full : Full AbstractSimplicialComplextoPresheaf := 
@Full.ofIso _ _ _ _ _ _ AbstractSimplicialComplextoPresheaf2_full AbstractSimplicialComplextoPresheaf_comp_equiv.symm  


end AbstractSimplicialComplexCat 

end CategoryTheory
