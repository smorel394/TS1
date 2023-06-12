import TS1.FacePoset
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.Order.Category.PartOrdCat
import Mathlib.Tactic


set_option autoImplicit false

universe u 

open AbstractSimplicialComplex Classical 

namespace CategoryTheory

@[nolint checkUnivs]
def AbstractSimplicialComplexCat :=
  Bundled AbstractSimplicialComplex.{u}


namespace AbstractSimplicialComplexCat

instance : CoeSort AbstractSimplicialComplexCat (Type u) where coe := Bundled.α

/-- Construct a bundled `AbstractSimplicialComplexCat` from the underlying type and the typeclass. -/
def of (V : Type u) (K : AbstractSimplicialComplex V) : AbstractSimplicialComplexCat.{u} :=
  @Bundled.of _ V K 


instance : Inhabited AbstractSimplicialComplexCat :=
  ⟨AbstractSimplicialComplexCat.of Empty (@AbstractSimplicialComplex.Bot Empty).1⟩


/-- Category structure on `AbstractSimplicialComplexCat` -/
instance category : LargeCategory.{u} AbstractSimplicialComplexCat.{u}
    where
  Hom C D := SimplicialMap C.2 D.2  
  id C := SimplicialMap.id C.2 
  comp F G := SimplicialMap.comp G F  


/- Forgetful functor to types (sends an abstract simplicial complex on α to α).-/

@[simps]
def forget : AbstractSimplicialComplexCat.{u} ⥤ Type u 
    where
  obj C := C.1 
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
                        unfold SimplicialMap.toFaceMap 
                        ext s a 
                        simp
                        constructor 
                        . intro h; match h with | ⟨b, hb⟩ => unfold SimplicialMap.vertex_map at hb; simp at hb; sorry 
                        . sorry 
  map_comp := fun f g => by simp only; unfold SimplicialMap.toFaceMapOrderHom 
                            apply OrderHom.ext 
                            erw [OrderHom.comp_coe]
                            simp only [PartOrdCat.coe_of]
                            exact SimplicialMap.toFaceMap_comp f g  
                          

end AbstractSimplicialComplexCat 

end CategoryTheory
