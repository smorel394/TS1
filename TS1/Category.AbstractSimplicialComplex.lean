import TS1.FacePoset 
import TS1.FintypeNECat
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.Order.Category.PartOrdCat
import Mathlib.Tactic
import Mathlib.AlgebraicTopology.SimplexCategory
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Adjunction.Reflective








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
                        tauto
  map_comp := fun f g => by simp only; unfold SimplicialMap.toFaceMapOrderHom  
                            apply OrderHom.ext 
                            erw [OrderHom.comp_coe] 
                            simp only [PartOrdCat.coe_of] 
                            tauto


/- The category of abstract simplicial complexes is equivalent to a full sucategory of the category of presheaves on the category
of finite nonempty sets FintypeNECat. We first construct the functor from FintypeNECat to AbstractSimplicialComplexCat, then the
fully faithful embedding will be the composition of the Yoneda embedding and of this functor.-/


noncomputable def FintypeNEtoAbstractSimplicialComplex : FintypeNECat ⥤ AbstractSimplicialComplexCat where 
  obj α := @AbstractSimplicialComplexCat.of α (Simplex α)  
  map f := by simp only; apply AbstractSimplicialComplexCat.mk; exact MapSimplex f   
  map_id := by intro S; simp only [id_eq]
               change MapSimplex (fun x => x) = _ 
               rw [MapSimplex.id]
               tauto  
  map_comp := by intro S T U f g; simp only [id_eq]
                 change MapSimplex (g ∘ f) = _ 
                 rw [←MapSimplex.comp]
                 tauto 



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
  have heq : Finset.image g S = (f.face_map ⟨S, hSf⟩).1 := by  
    ext b 
    simp only [Finset.mem_image, Subtype.exists]
    constructor 
    . intro hb  
      match hb with 
      | ⟨a, haS, hab⟩ => 
        rw [←hab,  f.compatibility_face_vertex]
        exists a; exists haS 
    . intro hb 
      rw [f.compatibility_face_vertex] at hb 
      match hb with 
      | ⟨a, has, hab⟩ => 
        exists a
  rw [heq]
  exact (f.face_map ⟨S, hSf⟩).2


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
  have hTeq : (f.face_map ⟨T, hTf⟩).1 = Finset.image (fun a => (f.vertex_map ⟨g.1 a, 
    HomTypetoAbstractSimplicialComplex_image g a⟩).1) S := by 
    ext b
    simp only [Set.mem_setOf_eq, Finset.mem_image, Subtype.exists]
    constructor 
    . intro hb; rw [f.compatibility_face_vertex] at hb  
      match hb with 
      | ⟨a, haS, hab⟩ =>
         simp only [Finset.mem_image] at haS
         match haS with
         | ⟨c, hcS, hca⟩ =>
           exists c
           rw [and_iff_right hcS]
           simp_rw [hca, hab] 
    . intro hb 
      match hb with 
      | ⟨a, haS, hab⟩ => 
        rw [f.compatibility_face_vertex]
        exists g.1 a
        have h : g.1 a ∈ Finset.image g.1 S := by
          simp only [Set.mem_setOf_eq, Finset.mem_image]
          exists a
        exists h 
  rw [←hTeq]
  exact (f.face_map ⟨T, hTf⟩).2


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
((AbstractSimplicialComplextoPresheaf.obj K).map f) := by 
  ext g 
  apply SimplicialMap.ext_vertex 
  tauto


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
  hom_inv_id := by 
    ext g 
    apply SimplicialMap.ext_vertex 
    tauto 
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
  naturality _ _ f := by 
    ext g 
    apply SimplicialMap.ext_vertex
    tauto


noncomputable def AbstractSimplicialComplextoPresheaf_comp_equiv :
AbstractSimplicialComplextoPresheaf ≅ AbstractSimplicialComplextoPresheaf2 
    where 
  hom := AbstractSimplicialComplextoPresheaf_comp 
  inv := AbstractSimplicialComplextoPresheaf_comp_inv 
  hom_inv_id := by ext g; apply SimplicialMap.ext_vertex; tauto  
  inv_hom_id := by tauto 


/- We construct a left adjoint of AbstractSimplicialComplexPresheaf2. -/

def ElementtoMap {S : FintypeNECat.{u}ᵒᵖ} (a : S.unop.1) : S ⟶ (Opposite.op (FintypeNECat.of PUnit)) := by 
  apply Quiver.Hom.op 
  exact fun _ => a 

lemma ElementtoMap_naturality {S T : FintypeNECat.{u}ᵒᵖ} (f : S ⟶ T) (a : T.unop.1) :
ElementtoMap (f.unop a) = f ≫ (ElementtoMap a) := by tauto

lemma ElementtoMap_PUnit (a : (Opposite.op (FintypeNECat.of.{u} PUnit)).unop.1) :
ElementtoMap a = CategoryTheory.CategoryStruct.id _ := by 
  unfold ElementtoMap 
  apply Quiver.Hom.unop_inj 
  simp only [Opposite.unop_op, Quiver.Hom.unop_op, unop_id]
  change _ = fun x => x 
  ext x 
  exact PUnit.ext a x 


def PresheafMap (F : FintypeNECat.{u}ᵒᵖ ⥤ Type u) {S : FintypeNECatᵒᵖ} (e : F.obj S) : 
S.unop.1 → F.obj (Opposite.op (FintypeNECat.of PUnit)) :=  
fun a => F.map (ElementtoMap a) e  

lemma PresheafMap_self (P : FintypeNECat.{u}ᵒᵖ ⥤ Type u) (a : P.obj (Opposite.op (FintypeNECat.of PUnit))) :
∀ x, PresheafMap P a x = a := by 
  intro x 
  unfold PresheafMap 
  rw [ElementtoMap_PUnit x]
  simp only [FunctorToTypes.map_id_apply]

lemma PresheafMap_naturality1 (F : FintypeNECat.{u}ᵒᵖ ⥤ Type u) {S T : FintypeNECatᵒᵖ} (f : S ⟶ T)
(e : F.obj S) : PresheafMap F (F.map f e) = (PresheafMap F e) ∘ f.unop := by 
  ext a 
  unfold PresheafMap 
  rw [←(@Function.comp_apply _ _ _ (F.map (ElementtoMap a)) (F.map f) e)]
  change ((F.map f) ≫ _) e = _ 
  rw [←F.map_comp, ←ElementtoMap_naturality]
  simp only [Function.comp_apply]

lemma PresheafMap_naturality2 {P Q : FintypeNECat.{u}ᵒᵖ ⥤ Type u} (f : P ⟶ Q) {S : FintypeNECatᵒᵖ} (u : P.obj S) :
PresheafMap Q (f.app S u) = (f.app (Opposite.op (FintypeNECat.of PUnit))) ∘ (PresheafMap P u) := by 
  unfold PresheafMap 
  ext a 
  rw [←(@Function.comp_apply _ _ _ (Q.map (ElementtoMap a)) (f.app S) u)]
  change ((f.app _) ≫ (Q.map _)) u = _ 
  rw [←f.naturality] 
  tauto


noncomputable def PresheafMap_factorization {P : FintypeNECat.{u}ᵒᵖ ⥤ Type u} {T : FintypeNECat.{u}ᵒᵖ} (e : P.obj T)
{s : Finset (P.obj (Opposite.op (FintypeNECat.of PUnit)))} (hsne : s.Nonempty) (heq : s = Finset.image (PresheafMap P e) ⊤) :  
T ⟶ (Opposite.op (@FintypeNECat.of s {FinsetCoe.fintype s with Nonempty := Finset.Nonempty.to_subtype hsne})) := by 
  apply Quiver.Hom.op 
  intro a 
  have has := a.2 
  simp_rw [heq, Finset.mem_image] at has 
  exact Classical.choose has 


lemma PresheafMap_factorization_prop1 {P : FintypeNECat.{u}ᵒᵖ ⥤ Type u} {T : FintypeNECat.{u}ᵒᵖ} (e : P.obj T) 
{s : Finset (P.obj (Opposite.op (FintypeNECat.of PUnit)))} (hsne : s.Nonempty) 
(heq : s = Finset.image (PresheafMap P e) ⊤) : 
∀ (a : s), PresheafMap P e ((PresheafMap_factorization e hsne heq).unop a) = a := by 
  intro a 
  have has := a.2 
  simp_rw [heq, Finset.mem_image] at has 
  exact (Classical.choose_spec has).2 


lemma PresheafMap_factorization_prop2 {P : FintypeNECat.{u}ᵒᵖ ⥤ Type u} {T : FintypeNECat.{u}ᵒᵖ} (e : P.obj T) 
{s : Finset (P.obj (Opposite.op (FintypeNECat.of PUnit)))} (hsne : s.Nonempty) 
{g : T ⟶ (Opposite.op (@FintypeNECat.of s {FinsetCoe.fintype s with Nonempty := Finset.Nonempty.to_subtype hsne}))}
(hg : ∀ (a : s), PresheafMap P e (g.unop a) = a) :
PresheafMap P (P.map g e) = fun a => a.1 := by 
  rw [PresheafMap_naturality1]
  ext a 
  simp only [Finset.coe_sort_coe, Opposite.unop_op, Function.comp_apply]
  exact hg a 
  

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
PresheaftoAbstractSimplicialComplex_map (CategoryStruct.id F) = SimplicialMap.id (PresheaftoAbstractSimplicialComplex_obj F).2 := by
  apply SimplicialMap.ext_vertex 
  tauto 


lemma PresheaftoAbstractSimplicialComplex_map_comp {F : FintypeNECat.{u}ᵒᵖ ⥤ Type u} {G : FintypeNECat.{u}ᵒᵖ ⥤ Type u} 
{H : FintypeNECat.{u}ᵒᵖ ⥤ Type u} (u : F ⟶ G) (v : G ⟶ H) :
PresheaftoAbstractSimplicialComplex_map (u ≫ v) = 
(PresheaftoAbstractSimplicialComplex_map u) ≫ (PresheaftoAbstractSimplicialComplex_map v) := by 
  apply SimplicialMap.ext_vertex; tauto 


noncomputable def PresheaftoAbstractSimplicialComplex : (FintypeNECat.{u}ᵒᵖ ⥤ Type u) ⥤ AbstractSimplicialComplexCat.{u} where 
  obj F := PresheaftoAbstractSimplicialComplex_obj F    
  map u := PresheaftoAbstractSimplicialComplex_map u 
  map_id F := PresheaftoAbstractSimplicialComplex_map_id F
  map_comp u v := PresheaftoAbstractSimplicialComplex_map_comp u v  


/- A simpler characterization of the faces of PresheaftoAbstractSimplicialComplex.obj P.-/

lemma PresheaftoAbstractSimplicialComplex_mem_faces (P : FintypeNECat.{u}ᵒᵖ ⥤ Type u) 
(s : Finset (P.obj (Opposite.op (FintypeNECat.of PUnit)))) (hsne : s.Nonempty) :
s ∈ (PresheaftoAbstractSimplicialComplex.obj P).2.faces ↔ 
(∃ (e : P.obj (Opposite.op (@FintypeNECat.of s {FinsetCoe.fintype s with Nonempty := Finset.Nonempty.to_subtype hsne}))),
PresheafMap P e = fun a => a.1) := by 
  constructor 
  . intro hsf
    match hsf with 
    | ⟨S, e, hSs⟩ => 
      exists (P.map (PresheafMap_factorization e hsne hSs) e)
      exact PresheafMap_factorization_prop2 e hsne (PresheafMap_factorization_prop1 e hsne hSs)
  . intro hs 
    match hs with 
    | ⟨e, hes⟩ => 
      exists (Opposite.op (@FintypeNECat.of s {FinsetCoe.fintype s with Nonempty := Finset.Nonempty.to_subtype hsne}))
      exists e 
      rw [hes]
      ext a 
      simp only [Finset.coe_sort_coe, Opposite.unop_op, Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ,
        true_and]
      constructor 
      . exact fun has => by exists ⟨a, has⟩ 
      . intro ha 
        match ha with 
        | ⟨b, hba⟩ => rw [←hba]; exact b.2

/- Now we need the unit and counit of the adjunction. -/

/- Unit.-/

noncomputable def Unit.PresheaftoAbstractSimplicialComplex_app_app (P : FintypeNECat.{u}ᵒᵖ ⥤ Type u) (S : FintypeNECatᵒᵖ) :
P.obj S ⟶ ((PresheaftoAbstractSimplicialComplex ⋙ AbstractSimplicialComplextoPresheaf2).obj P).obj S := by 
  intro u 
  simp only [Functor.comp_obj]
  unfold AbstractSimplicialComplextoPresheaf2 AbstractSimplicialComplextoPresheaf_obj 
    HomTypetoAbstractSimplicialComplex
  simp only [Set.coe_setOf]
  refine ⟨PresheafMap P u, ?_⟩
  intro s hsne 
  unfold PresheaftoAbstractSimplicialComplex PresheaftoAbstractSimplicialComplex_obj PresheafFaces 
  change ∃ _ _, _ 
  have hsfin : Fintype s := FinsetCoe.fintype s 
  letI : FintypeNE s := {hsfin with Nonempty := Finset.Nonempty.to_subtype hsne}  
  exists Opposite.op (FintypeNECat.of s) 
  set f : S ⟶ Opposite.op (FintypeNECat.of s) := by 
    apply Quiver.Hom.op 
    exact fun a => a.1  
  exists P.map f u 
  have heq : PresheafMap P (P.map f u) = (PresheafMap P u) ∘ (fun a => a.1) := by 
    rw [PresheafMap_naturality1]
    simp only [Opposite.unop_op, Quiver.Hom.unop_op]
  have hseq : (s : Finset ↑S.unop) = Finset.image (fun (a : ↑(Opposite.op (FintypeNECat.of { x // x ∈ s })).unop) => a.1) ⊤ := by 
    simp only [Opposite.unop_op, Finset.top_eq_univ]
    ext a 
    simp only [Finset.mem_image, Finset.mem_univ, true_and] 
    constructor 
    . exact fun has => by exists ⟨a, has⟩  
    . intro has 
      match has with 
      | ⟨b, hba⟩ => rw [←hba]; exact b.2
  rw [heq, ←Finset.image_image, ←hseq]
  
lemma Unit.PresheaftoAbstractSimplicialComplex_app_naturality (P : FintypeNECat.{u}ᵒᵖ ⥤ Type u) {S T : FintypeNECatᵒᵖ}
(f : S ⟶ T) :
(P.map f) ≫ (PresheaftoAbstractSimplicialComplex_app_app P T)  = 
(PresheaftoAbstractSimplicialComplex_app_app P S) ≫
((PresheaftoAbstractSimplicialComplex ⋙ AbstractSimplicialComplextoPresheaf2).obj P).map f := by 
  ext u 
  unfold PresheaftoAbstractSimplicialComplex_app_app
  simp only [Functor.comp_obj, Set.coe_setOf, id_eq, types_comp_apply]
  unfold PresheaftoAbstractSimplicialComplex AbstractSimplicialComplextoPresheaf2 AbstractSimplicialComplextoPresheaf_obj 
  rw [←SetCoe.ext_iff]
  simp only 
  rw [PresheafMap_naturality1]
  tauto


noncomputable def Unit.PresheaftoAbstractSimplicialComplex_app (P : FintypeNECat.{u}ᵒᵖ ⥤ Type u) :
P ⟶ (PresheaftoAbstractSimplicialComplex ⋙ AbstractSimplicialComplextoPresheaf2).obj P where
  app := Unit.PresheaftoAbstractSimplicialComplex_app_app P  
  naturality _ _ := Unit.PresheaftoAbstractSimplicialComplex_app_naturality P 

lemma Unit.PresheaftoAbstractSimplicialComplex_naturality {P Q : FintypeNECat.{u}ᵒᵖ ⥤ Type u}  
(f : P ⟶ Q) :
f ≫ (Unit.PresheaftoAbstractSimplicialComplex_app Q) = (Unit.PresheaftoAbstractSimplicialComplex_app P) ≫
(PresheaftoAbstractSimplicialComplex ⋙ AbstractSimplicialComplextoPresheaf2).map f := by 
  ext S u 
  unfold PresheaftoAbstractSimplicialComplex_app PresheaftoAbstractSimplicialComplex_app_app 
  rw [←SetCoe.ext_iff]
  simp only [Set.mem_setOf_eq, Functor.comp_obj, Set.coe_setOf, id_eq, FunctorToTypes.comp, Functor.comp_map]
  rw [PresheafMap_naturality2]
  tauto



noncomputable def Unit.PresheaftoAbstractSimplicialComplex : 
(𝟭 (FintypeNECat.{u}ᵒᵖ ⥤ Type u))  ⟶
PresheaftoAbstractSimplicialComplex ⋙ AbstractSimplicialComplextoPresheaf2 
where 
  app := Unit.PresheaftoAbstractSimplicialComplex_app 
  naturality _ _ := Unit.PresheaftoAbstractSimplicialComplex_naturality 


/- Counit. -/

noncomputable def Counit.PresheaftoAbstractSimplicialComplex_app_aux (K : AbstractSimplicialComplexCat.{u}) :
((AbstractSimplicialComplextoPresheaf2 ⋙ PresheaftoAbstractSimplicialComplex).obj K).1 → K.1 := by 
  intro f 
  apply f.1 
  simp only [Opposite.unop_op]
  unfold FintypeNECat.of Bundled.of
  simp only 
  exact PUnit.unit
  

noncomputable def Counit.PresheaftoAbstractSimplicialComplex_app (K : AbstractSimplicialComplexCat.{u}) :
((AbstractSimplicialComplextoPresheaf2 ⋙ PresheaftoAbstractSimplicialComplex).obj K) ⟶ K := by 
  apply SimplicialMapofMap (Counit.PresheaftoAbstractSimplicialComplex_app_aux K)
  intro s hsf 
  simp only [Functor.comp_obj] at hsf
  unfold PresheaftoAbstractSimplicialComplex 
  simp only at hsf 
  match hsf with 
  | ⟨S, f, hSs⟩ => 
    have heq : (PresheaftoAbstractSimplicialComplex_app_aux K) ∘ (PresheafMap (AbstractSimplicialComplextoPresheaf2.obj K) f) = 
        fun a => f.1 a := by 
      ext a 
      unfold PresheaftoAbstractSimplicialComplex_app_aux AbstractSimplicialComplextoPresheaf2 AbstractSimplicialComplextoPresheaf_obj
        PresheafMap ElementtoMap HomTypetoAbstractSimplicialComplex HomTypetoAbstractSimplicialComplex_func1 
      simp only [Set.coe_setOf, Set.mem_setOf_eq, Functor.comp_obj, Opposite.unop_op, id_eq, Function.comp_apply]
      rfl
    erw [hSs, Finset.image_image, heq]
    apply f.2 
    simp only [Finset.top_eq_univ]
    rw [Finset.univ_nonempty_iff]
    exact S.unop.2.2
  
lemma Counit.PresheaftoAbstractSimplicialComplex_naturality {K L : AbstractSimplicialComplexCat.{u}} (f : K ⟶ L) :
((AbstractSimplicialComplextoPresheaf2 ⋙ PresheaftoAbstractSimplicialComplex).map f) ≫ 
(Counit.PresheaftoAbstractSimplicialComplex_app L) = (Counit.PresheaftoAbstractSimplicialComplex_app K) ≫ f := by 
  apply SimplicialMap.ext_vertex 
  tauto 


noncomputable def Counit.PresheaftoAbstractSimplicialComplex : 
AbstractSimplicialComplextoPresheaf2 ⋙ PresheaftoAbstractSimplicialComplex ⟶ 𝟭 AbstractSimplicialComplexCat.{u} where
  app := Counit.PresheaftoAbstractSimplicialComplex_app  
  naturality _ _ := Counit.PresheaftoAbstractSimplicialComplex_naturality 


/- Now we define the adjunction.-/

lemma coeur_LT_aux1 (P : FintypeNECat.{u}ᵒᵖ ⥤ Type u) (a : P.obj (Opposite.op (FintypeNECat.of PUnit)))  
(f : ((PresheaftoAbstractSimplicialComplex ⋙ AbstractSimplicialComplextoPresheaf2).obj P).obj (Opposite.op (FintypeNECat.of PUnit)))  
(hfa : ∀ x, f.1 x = a) 
(hfv : f ∈ ((PresheaftoAbstractSimplicialComplex ⋙ AbstractSimplicialComplextoPresheaf2 
⋙ PresheaftoAbstractSimplicialComplex).obj P).2.vertices) : 
((Counit.PresheaftoAbstractSimplicialComplex.app (PresheaftoAbstractSimplicialComplex.obj P)).vertex_map ⟨f, hfv⟩).1 = a := by 
  have x : (Opposite.op (FintypeNECat.of.{u} PUnit)).unop.1 := by 
    simp only [Opposite.unop_op]
    exact PUnit.unit
  rw [←(hfa x)]
  apply SimplicialMapofMap.vertex_map 


lemma coeur_LT_aux2 (P : FintypeNECat.{u}ᵒᵖ ⥤ Type u) (a : P.obj (Opposite.op (FintypeNECat.of PUnit))) 
(hav : a ∈ (PresheaftoAbstractSimplicialComplex.obj P).2.vertices) : ∀ x,
((PresheaftoAbstractSimplicialComplex.map (Unit.PresheaftoAbstractSimplicialComplex.app P)).vertex_map ⟨a, hav⟩).1.1 x = a := by 
  intro x 
  unfold PresheaftoAbstractSimplicialComplex PresheaftoAbstractSimplicialComplex_obj PresheaftoAbstractSimplicialComplex_map
  unfold Unit.PresheaftoAbstractSimplicialComplex Unit.PresheaftoAbstractSimplicialComplex_app Unit.PresheaftoAbstractSimplicialComplex_app_app
  simp only [Opposite.unop_op, Set.mem_setOf_eq, Functor.comp_obj, Functor.id_obj, Set.coe_setOf, id_eq]
  rw [SimplicialMapofMap.vertex_map]
  exact PresheafMap_self P a _ 

noncomputable def Coeur : CategoryTheory.Adjunction.CoreUnitCounit PresheaftoAbstractSimplicialComplex.{u}
AbstractSimplicialComplextoPresheaf2.{u} where 
unit := Unit.PresheaftoAbstractSimplicialComplex 
counit := Counit.PresheaftoAbstractSimplicialComplex 
left_triangle := by 
  ext P 
  apply SimplicialMap.ext_vertex 
  ext ⟨a, hav⟩
  simp only [Functor.comp_obj, Functor.id_obj, NatTrans.comp_app, whiskerRight_app, Functor.associator_hom_app,
  whiskerLeft_app, Category.id_comp, NatTrans.id_app']
  change _ = a 
  simp only [Functor.comp_obj, Functor.id_obj] at hav 
  rw [@SetCoe.ext_iff _ _ _ ⟨a, hav⟩]
  change SimplicialMap.vertex_map (SimplicialMap.comp _ _) ⟨a, hav⟩ = _
  unfold SimplicialMap.comp 
  simp only [Functor.comp_obj, Functor.id_obj, Function.comp_apply]
  rw [←SetCoe.ext_iff]
  change _ = a 
  apply coeur_LT_aux1 
  apply coeur_LT_aux2 
right_triangle := by tauto 

noncomputable def Adjunction.PresheaftoAbstractSimplicialComplex : CategoryTheory.Adjunction
PresheaftoAbstractSimplicialComplex AbstractSimplicialComplextoPresheaf2 := CategoryTheory.Adjunction.mkOfUnitCounit Coeur 

/- We show that the functor AbstractSimplicialComplextoPresheaf2 is reflective. This means that it is fully faithful, and we
prove this by proving that the counit of the adjunction is an isomorphism.-/

/- The inverse of the counit.-/

noncomputable def InverseCounit.PresheaftoAbstractSimplicialComplex_app_aux (K : AbstractSimplicialComplexCat.{u}) 
(a : K.1) (hav : a ∈ K.2.vertices) : (AbstractSimplicialComplextoPresheaf2.obj K).obj (Opposite.op (FintypeNECat.of PUnit)) := by
  set f : PUnit → K.1 := fun _ => a 
  set g : (AbstractSimplicialComplextoPresheaf2.obj K).obj (Opposite.op (FintypeNECat.of PUnit)) := by 
    refine ⟨f, ?_⟩
    simp only [Opposite.unop_op, Set.mem_setOf_eq]
    intro s hsne 
    have heq : Finset.image (fun _ => a) s = {a} := by 
      ext b 
      simp only [Opposite.unop_op, Finset.mem_image, exists_and_right, Finset.mem_singleton]
      constructor 
      . exact fun h => Eq.symm h.2 
      . intro h 
        rw [h]
        simp only [and_true]
        exact hsne 
    erw [heq]
    exact hav 
  exact g 

noncomputable def InverseCounit.PresheaftoAbstractSimplicialComplex_app (K : AbstractSimplicialComplexCat.{u}) :
K ⟶ ((AbstractSimplicialComplextoPresheaf2 ⋙ PresheaftoAbstractSimplicialComplex).obj K) where 
vertex_map := by 
  intro a 
  refine ⟨InverseCounit.PresheaftoAbstractSimplicialComplex_app_aux K a.1 a.2, ?_⟩
  rw [mem_vertices]
  unfold PresheaftoAbstractSimplicialComplex PresheaftoAbstractSimplicialComplex_obj
  simp only [Functor.comp_obj]
  change ∃ _, _ 
  exists (Opposite.op (FintypeNECat.of PUnit))
  exists InverseCounit.PresheaftoAbstractSimplicialComplex_app_aux K a.1 a.2  
face_map := by
  intro ⟨s, hsf⟩ 
  set t := Finset.image (fun (a : s) => InverseCounit.PresheaftoAbstractSimplicialComplex_app_aux K ↑a 
    (by rw [mem_vertices_iff]; exists ⟨s, hsf⟩; exact a.2)) ⊤ 
  refine ⟨t, ?_⟩
  change ∃ _, _ 
  have hsfin : Fintype s := by 
    exact FinsetCoe.fintype s  
  have hsne : Nonempty s := by 
    simp only [nonempty_subtype]
    exact K.2.nonempty_of_mem hsf 
  haveI : FintypeNE s := {hsfin with Nonempty := hsne}
  exists (Opposite.op (FintypeNECat.of s)) 
  set f : s → K.1 := fun a => ↑a 
  exists ⟨f, ?_⟩
  .  simp only [Opposite.unop_op, Set.mem_setOf_eq]
     intro S hSne 
     simp only [Opposite.unop_op] at S
     apply K.2.down_closed hsf 
     . intro a ha 
       simp only [Finset.mem_image] at ha
       match ha with 
       | ⟨b, _, hab⟩ => rw [←hab]; exact b.2 
     . simp only [Finset.Nonempty.image_iff, hSne]
  . ext b 
    simp only [Finset.top_eq_univ, Finset.univ_eq_attach, Finset.mem_image, Finset.mem_attach, true_and,
      Subtype.exists, Opposite.unop_op, Set.mem_setOf_eq, Finset.mem_univ]
    constructor 
    . intro hb 
      match hb with 
      | ⟨a, has, _, hab⟩ => 
        exists ⟨a, has⟩
    . intro hb 
      match hb with 
      | ⟨⟨a, has⟩, hab⟩ => 
        exists a; exists has  
        constructor 
        . rw [@Finset.top_eq_univ _ (Finset.Subtype.fintype s)]
          apply @Finset.mem_univ _ (Finset.Subtype.fintype s)
        . tauto 
compatibility_vertex_face := by tauto  
compatibility_face_vertex := by 
  intro s b 
  simp only [Functor.comp_obj, Finset.top_eq_univ, Finset.univ_eq_attach]
  erw [Finset.mem_image]
  constructor 
  . intro hb 
    match hb with 
    | ⟨a, _, hab⟩ => 
      exists a.1; exists a.2   
  . intro hb 
    match hb with 
    | ⟨a, has, hab⟩ => 
    exists ⟨a, has⟩
    simp only [Finset.mem_attach, true_and]
    exact hab 

lemma InverseCounit.PresheaftoAbstractSimplicialComplex_naturality {K L : AbstractSimplicialComplexCat}
(f : K ⟶ L) : 
f ≫ (InverseCounit.PresheaftoAbstractSimplicialComplex_app L) = (InverseCounit.PresheaftoAbstractSimplicialComplex_app K) ≫
((AbstractSimplicialComplextoPresheaf2 ⋙ PresheaftoAbstractSimplicialComplex).map f) := by
  apply SimplicialMap.ext_vertex 
  tauto

noncomputable def InverseCounit.PresheaftoAbstractSimplicialComplex :
𝟭 AbstractSimplicialComplexCat.{u} ⟶ AbstractSimplicialComplextoPresheaf2 ⋙ PresheaftoAbstractSimplicialComplex  where
  app := InverseCounit.PresheaftoAbstractSimplicialComplex_app  
  naturality _ _ := InverseCounit.PresheaftoAbstractSimplicialComplex_naturality 


noncomputable def IsIsoCounit.PresheaftoAbstractSimplicialComplex :
IsIso Counit.PresheaftoAbstractSimplicialComplex where 
out := by 
  exists InverseCounit.PresheaftoAbstractSimplicialComplex 
  constructor 
  . ext K 
    apply SimplicialMap.ext_vertex 
    tauto
  . ext K 
    apply SimplicialMap.ext_vertex 
    tauto 

/- We deduce that the right adjoint AbstractSimplicialComplextoPresheaf2 is fully faithful.-/

noncomputable def AbstractSimplicialComplextoPresheaf2_full : Full AbstractSimplicialComplextoPresheaf2 := 
@rFullOfCounitIsIso _ _ _ _ _ _ Adjunction.PresheaftoAbstractSimplicialComplex IsIsoCounit.PresheaftoAbstractSimplicialComplex 

lemma AbstractSimplicialComplextoPresheaf2_faithful : Faithful AbstractSimplicialComplextoPresheaf2 := 
@R_faithful_of_counit_isIso _ _ _ _ _ _ Adjunction.PresheaftoAbstractSimplicialComplex IsIsoCounit.PresheaftoAbstractSimplicialComplex

/- We finally deduce that AbstractSimplicialComplextoPresheaf2 is reflective.-/

noncomputable instance AbstractSimplicialComplextoPresheaf2_reflective : Reflective AbstractSimplicialComplextoPresheaf2 where
toFull := AbstractSimplicialComplextoPresheaf2_full
toFaithful := AbstractSimplicialComplextoPresheaf2_faithful
toIsRightAdjoint := {left := PresheaftoAbstractSimplicialComplex, adj := Adjunction.PresheaftoAbstractSimplicialComplex}


/- We identify the essential image of AbstractSimplicialComplextoPResheaf2: it is the full subcategory of concrete presheaves,
i.e. presheaves P such that P(S) -> (Hom(*,S) -> P(*)) is injective for every S. As the functor is reflective, we know
that P is in its essential if and only if the unit of the adjunction is an isomorphism at P, so we first prove that this is
the one if and only if P is concrete.-/

def IsConcretePresheaf (P : FintypeNECatᵒᵖ ⥤ Type u) := ∀ (S : FintypeNECatᵒᵖ),
Function.Injective (fun (e : P.obj S) => PresheafMap P e)



lemma IsConcretePresheaf.unit_IsIso_inv {P : FintypeNECat.{u}ᵒᵖ ⥤ Type u} {S : FintypeNECatᵒᵖ} 
(f : ((PresheaftoAbstractSimplicialComplex ⋙ AbstractSimplicialComplextoPresheaf2).obj P).obj S) :
∃ (e : P.obj S), PresheafMap P e = f.1 := by 
  set T := Finset.image f.1 ⊤ 
  have hTf : T ∈ (PresheaftoAbstractSimplicialComplex.obj P).2.faces := by 
    refine f.2 ⊤ ?_ 
    rw [Finset.top_eq_univ, Finset.univ_nonempty_iff]
    exact S.unop.2.2
  have hTne := ((PresheaftoAbstractSimplicialComplex.obj P).2.nonempty_of_mem hTf)
  rw [PresheaftoAbstractSimplicialComplex_mem_faces P T hTne] at hTf 
  set e := Classical.choose hTf 
  set g : Opposite.op (@FintypeNECat.of T {FinsetCoe.fintype T with Nonempty := Finset.Nonempty.to_subtype hTne}) ⟶ S := by 
    apply Quiver.Hom.op 
    intro a 
    refine ⟨f.1 a, ?_⟩
    simp only [Set.mem_setOf_eq, Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ, true_and,
      exists_apply_eq_apply, hTne]
  exists P.map g e 
  rw [PresheafMap_naturality1, Classical.choose_spec hTf] 
  ext a 
  simp only [Set.mem_setOf_eq, Finset.top_eq_univ, Finset.coe_sort_coe, Opposite.unop_op, Quiver.Hom.unop_op,
    Function.comp_apply]


lemma IsConcretePresheaf.unit_IsIso {P : FintypeNECat.{u}ᵒᵖ ⥤ Type u} (hconc : IsConcretePresheaf P) :
IsIso (Unit.PresheaftoAbstractSimplicialComplex.app P) := by 
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ (Unit.PresheaftoAbstractSimplicialComplex.app P) ?_ 
  intro S 
  refine {out := ?_}
  set I : ((PresheaftoAbstractSimplicialComplex ⋙ AbstractSimplicialComplextoPresheaf2).obj P).obj S → P.obj S := 
    fun f => Classical.choose (IsConcretePresheaf.unit_IsIso_inv f)
  exists I 
  simp only [Functor.id_obj, Functor.comp_obj, Set.mem_setOf_eq]
  constructor 
  . ext a 
    simp only [types_comp_apply, types_id_apply]
    apply hconc S  
    simp only 
    rw [Classical.choose_spec (IsConcretePresheaf.unit_IsIso_inv ((Unit.PresheaftoAbstractSimplicialComplex.app P).app S a))]
    tauto
  . ext f 
    have hI := Classical.choose_spec (IsConcretePresheaf.unit_IsIso_inv f)
    simp only [types_comp_apply, types_id_apply]
    unfold Unit.PresheaftoAbstractSimplicialComplex Unit.PresheaftoAbstractSimplicialComplex_app
      Unit.PresheaftoAbstractSimplicialComplex_app_app 
    simp only [Functor.comp_obj, Set.coe_setOf, id_eq]
    rw [←SetCoe.ext_iff]
    simp only 
    exact hI 



lemma IsConcretePresheaf_of_unit_IsIso {P : FintypeNECat.{u}ᵒᵖ ⥤ Type u}
(hiso : IsIso (Unit.PresheaftoAbstractSimplicialComplex.app P)) : IsConcretePresheaf P := by 
  intro S u v huv 
  set eta := Unit.PresheaftoAbstractSimplicialComplex.app P
  simp only [Functor.id_obj, Functor.comp_obj] at eta
  have heq : eta.app S u = eta.app S v := by 
    simp only 
    unfold Unit.PresheaftoAbstractSimplicialComplex Unit.PresheaftoAbstractSimplicialComplex_app 
      Unit.PresheaftoAbstractSimplicialComplex_app_app 
    simp only [Functor.comp_obj, Set.coe_setOf, id_eq]
    rw [←SetCoe.ext_iff]
    exact huv 
  set eta' := (@CategoryTheory.inv _ _ _ _ eta hiso) 
  apply_fun (eta'.app S) at heq
  rw [←(@Function.comp_apply _ _ _ (eta'.app S) (eta.app S) u), ←(@Function.comp_apply _ _ _ (eta'.app S) (eta.app S) v)] at heq
  change ((eta.app S) ≫ _) u = ((eta.app S) ≫ _) v at heq 
  rw [←NatTrans.vcomp_app] at heq   
  simp only [NatTrans.vcomp_eq_comp, IsIso.hom_inv_id, NatTrans.id_app, types_id_apply] at heq
  exact heq 

lemma IsConcretePresheaf_iff_essImage (P : FintypeNECat.{u}ᵒᵖ ⥤ Type u) :
P ∈ Functor.essImage AbstractSimplicialComplextoPresheaf2 ↔ IsConcretePresheaf P := by 
  constructor 
  . exact fun h => IsConcretePresheaf_of_unit_IsIso (Functor.essImage.unit_isIso h)   
  . exact fun h => @mem_essImage_of_unit_isIso _ _ _ _ _ _ P (IsConcretePresheaf.unit_IsIso h)

lemma IsConcretePresheaf_iff_essImage' (P : FintypeNECat.{u}ᵒᵖ ⥤ Type u) :
P ∈ Functor.essImage AbstractSimplicialComplextoPresheaf ↔ IsConcretePresheaf P := by 
  rw [←IsConcretePresheaf_iff_essImage, Functor.essImage_eq_of_natIso AbstractSimplicialComplextoPresheaf_comp_equiv]


/- The geometric realization: we define it on FintypeNECat by sending S to the standard simplex on S, extend it to
FintypeNECatᵒᵖ ⥤ Type u  by left Kan extension along Yoneda, and then restrict it to AbstractSimplicialComplexCat via
the reflective functor AbstractSimplicialComplextoPresheaf2.-/




end AbstractSimplicialComplexCat 

end CategoryTheory
