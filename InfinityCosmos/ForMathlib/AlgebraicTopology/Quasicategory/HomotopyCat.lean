import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.Homotopy
import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat

universe u

abbrev CategoryTheory.SSet.OneTruncation (S : SSet.{u}) :=
  OneTruncation₂ <| (SSet.truncation 2).obj S

namespace SSet.Quasicategory
open CategoryTheory Limits Functor Opposite SSet Simplicial

def HoRel {S : SSet.{u}} (X Y : OneTruncation S) (f g : X ⟶ Y) : Prop :=
  HomotopicL f.val g.val

variable (A : SSet.{u}) [Quasicategory A]

noncomputable instance ho_cat : Category (OneTruncation A) where
  Hom X Y := Quot <| HoRel X Y
  id X := Quot.mk _ <| 𝟙rq X
  comp {X Y Z} hf hg := by
    refine Quot.liftOn hf (fun f ↦ Quot.liftOn hg (fun g ↦ Quot.mk _ ?_) ?_) ?_
    · refine ⟨?_, ?_⟩
      · apply truncation 2 |>.obj A |>.map (δ₂ 1).op
        refine A.yonedaEquiv [2] ?_
        refine Classical.choose <| hornFilling (i := 1) (by simp) (by simp [Fin.last]) ?_
        sorry
      · sorry
    · sorry
    · sorry

end SSet.Quasicategory
