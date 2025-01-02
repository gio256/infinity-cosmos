import Mathlib.AlgebraicTopology.SimplicialSet.Basic

universe v u

namespace SSet

open CategoryTheory Simplicial SimplexCategory Limits

open Fintype in
lemma not_surjective_of_card_lt {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (h : card α < card β) : ¬Function.Surjective f :=
  Nat.lt_le_asymm h ∘ card_le_of_surjective f

open Fintype in
lemma not_injective_of_card_lt {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (h : card β < card α) : ¬Function.Injective f :=
  Nat.lt_le_asymm h ∘ card_le_of_injective f

lemma δ_not_surjective {n : ℕ} (i : Fin (n + 2)) :
    ¬Function.Surjective (δ i).toOrderHom :=
  not_surjective_of_card_lt _ (by simp)

lemma σ_not_injective {n : ℕ} (i : Fin (n + 1)) :
    ¬Function.Injective (σ i).toOrderHom :=
  not_injective_of_card_lt _ (by simp)

namespace boundary

noncomputable def skips {n : ℕ} {m : SimplexCategoryᵒᵖ} (α : ∂Δ[n].obj m) :
    Fin (n + 1) := Classical.choose <| not_forall.mp α.property

lemma skips_spec {n : ℕ} {m : SimplexCategoryᵒᵖ} (α : ∂Δ[n].obj m) :
    ∀ k : Fin (m.unop.len + 1), asOrderHom α.1 k ≠ skips α :=
  not_exists.mp <| Classical.choose_spec <| not_forall.mp α.2

end boundary

section PredAbove
open Fin
variable {n : ℕ}

lemma predAbove_eq_lt_iff {p j : Fin n} (h : j < p) (i : Fin (n + 1)) :
    p.predAbove i = j ↔ i = j.castSucc := by
  by_cases hi : p.castSucc < i
  · apply Iff.intro <;> rintro rfl
    · rw [predAbove_of_castSucc_lt _ _ hi] at h
      exact False.elim <| not_lt.mpr ((le_pred_iff _).mpr hi) h
    · exact False.elim <| not_le.mpr hi <| le_of_lt h
  · rw [predAbove_of_le_castSucc _ _ (not_lt.mp hi)]
    apply castPred_eq_iff_eq_castSucc

lemma predAbove_eq_iff (p : Fin n) (i : Fin (n + 1)) :
    p.predAbove i = p ↔ i = p.castSucc ∨ i = p.succ := by
  apply Iff.intro
  · intro hp
    by_cases hi : p.castSucc < i
    · rw [predAbove_of_castSucc_lt _ _ hi] at hp
      simp only [← hp, succ_pred, or_true]
    · rw [predAbove_of_le_castSucc _ _ (not_lt.mp hi)] at hp
      simp only [← hp, castSucc_castPred, true_or]
  · rintro (rfl | rfl)
    · rw [predAbove_castSucc_self]
    · rw [predAbove_succ_self]

lemma predAbove_eq_gt_iff {p j : Fin n} (h : p < j) (i : Fin (n + 1)) :
    p.predAbove i = j ↔ i = j.succ := by
  by_cases hi : p.castSucc < i
  . rw [predAbove_of_castSucc_lt _ _ hi]
    apply pred_eq_iff_eq_succ
  · apply Iff.intro <;> rintro rfl
    · rw [predAbove_of_le_castSucc _ _ (not_lt.mp hi)] at h
      exact False.elim <| hi <| lt_castPred_iff _ |>.mp h
    · exact False.elim <| lt_asymm h <| succ_le_castSucc_iff.mp <| not_lt.mp hi

lemma predAbove_le_predAbove {n : ℕ} (p : Fin n) {i j : Fin (n + 1)}
    (h : i ≤ j) : p.predAbove i ≤ p.predAbove j := by
  by_cases hi : p.castSucc < i
  · rw [predAbove_of_castSucc_lt _ _ (lt_of_lt_of_le hi h),
      predAbove_of_castSucc_lt _ _ hi]
    exact pred_le_pred_iff.mpr h
  · have hi := not_lt.mp hi
    rw [predAbove_of_le_castSucc _ _ hi]
    by_cases hj : p.castSucc < j
    · rw [predAbove_of_castSucc_lt _ _ hj]
      exact castPred_le_pred_iff _ _ |>.mpr (lt_of_le_of_lt hi hj)
    · rw [predAbove_of_le_castSucc _ _ (not_lt.mp hj)]
      exact h

lemma predAbove_le {n : ℕ} (p : Fin n) (i : Fin (n + 1)) :
    (p.predAbove i).castSucc ≤ i := by
  by_cases h : p.castSucc < i
  · rw [predAbove_of_castSucc_lt _ _ h, castSucc_pred_eq_pred_castSucc]
    exact le_of_lt <| pred_castSucc_lt _
  · rw [predAbove_of_le_castSucc _ _ (not_lt.mp h), castSucc_castPred]

lemma predAbove_lt_iff_lt_castSucc (p : Fin n) (i : Fin (n + 1)) :
    p.predAbove i < p ↔ i < p.castSucc := by
  apply Iff.intro
  · intro h
    by_cases hi : p.castSucc < i
    · rw [predAbove_of_castSucc_lt _ _ hi] at h
      exact False.elim <| not_lt.mpr ((le_pred_iff _).mpr hi) h
    · rw [predAbove_of_le_castSucc _ _ (not_lt.mp hi)] at h
      exact h
  · intro h
    rw [predAbove_of_le_castSucc _ _ (le_of_lt h)]
    exact h

lemma lt_predAbove_iff_succ_lt (p : Fin n) (i : Fin (n + 1)) :
    p < p.predAbove i ↔ p.succ < i := by
  apply Iff.intro
  · intro h
    by_cases hi : p.castSucc < i
    · rw [predAbove_of_castSucc_lt _ _ hi] at h
      exact lt_pred_iff (ne_zero_of_lt hi) |>.mp h
    · rw [predAbove_of_le_castSucc _ _ (not_lt.mp hi)] at h
      exact False.elim <| hi h
  · intro h
    rw [predAbove_of_succ_le _ _ (le_of_lt h)]
    exact lt_pred_iff (ne_zero_of_lt h) |>.mpr h

end PredAbove

section SuccAbove
open Fin
variable {n : ℕ} {p : Fin (n + 1)}

lemma succAbove_eq_lt_iff {j : Fin (n + 1)} (h : j < p) (i : Fin n) :
    p.succAbove i = j ↔ i.castSucc = j := by
  by_cases hi : i.castSucc < p
  · rw [succAbove_of_castSucc_lt _ _ hi]
  · apply Iff.intro <;> rintro rfl
    · rw [succAbove_of_le_castSucc _ _ (not_lt.mp hi)] at h
      exact False.elim <| hi <| lt_succ |>.trans h
    · exact False.elim <| hi h

lemma succAbove_eq_gt_iff {j : Fin (n + 1)} (h : p < j) (i : Fin n) :
    p.succAbove i = j ↔ i.succ = j := by
  by_cases hi : i.castSucc < p
  · apply Iff.intro <;> rintro rfl
    · rw [succAbove_of_castSucc_lt _ _ hi] at h
      exact False.elim <| lt_asymm hi h
    · exact False.elim <| (not_lt.mpr (castSucc_lt_iff_succ_le.mp hi)) h
  · rw [succAbove_of_le_castSucc _ _ (not_lt.mp hi)]

end SuccAbove

open Fin in
@[reassoc]
lemma σ_predAbove_comp_σ_predAbove {n : ℕ} {p : Fin (n + 1)} {i j : Fin (n + 2)}
    (h : i ≤ j) (hp : p.castSucc = i ∨ p.castSucc ≠ j) :
    σ (p.castSucc.predAbove j.succ) ≫ σ (p.predAbove i) =
      σ (p.predAbove i).castSucc ≫ σ (p.predAbove j) := by
  rw [σ_comp_σ (predAbove_le_predAbove p h)]
  rcases hp with (rfl | hp)
  · rw [predAbove_castSucc_self, predAbove_succ_of_le _ _ h]
    rcases lt_or_eq_of_le h with (h | rfl)
    · rw [predAbove_of_castSucc_lt _ _ h, succ_pred]
    · rw [predAbove_castSucc_self, σ_comp_σ (by rfl)]
  · rcases hp.lt_or_lt with (hp | hp)
    · rw [predAbove_of_castSucc_lt _ _ hp, succ_pred,
        predAbove_succ_of_le _ _ (le_of_lt hp)]
    · rw [predAbove_of_le_castSucc _ _ (le_of_lt hp),
        predAbove_succ_of_lt _ _ hp, succ_castPred_eq_castPred_succ]

open Fin in
@[reassoc]
lemma σ_predAbove_zero_comp_σ_predAbove_zero {n : ℕ} {i j : Fin (n + 2)} (h : i ≤ j) :
    σ (predAbove 0 j.succ) ≫ σ (predAbove 0 i) =
      σ (predAbove 0 i.castSucc) ≫ σ (predAbove 0 j) := by
  rw [← castSucc_zero, castSucc_predAbove_castSucc,
    σ_predAbove_comp_σ_predAbove h]
  cases' i using cases with i
  · exact Or.inl (by rfl)
  · exact Or.inr (ne_zero_of_lt (castSucc_lt_iff_succ_le.mpr h)).symm

lemma SimplexCategory.factor_δ_δ_eq {n : ℕ} (j : Fin (n+2)) :
    factor_δ (δ j) j = 𝟙 _ := by
  dsimp only [factor_δ]
  cases' j using Fin.cases with j
  · rw [δ_comp_σ_self' (by rfl)]
  · rw [Fin.predAbove_zero_succ, δ_comp_σ_succ]

namespace standardSimplex

def factor_δ {n : ℕ} {m : SimplexCategoryᵒᵖ} (α : Δ[n + 1].obj m)
    (j : Fin (n + 2)) : Δ[n].obj m :=
  standardSimplex.map (σ (Fin.predAbove 0 j)) |>.app m α

lemma factor_δ_spec {n : ℕ} {m : SimplexCategoryᵒᵖ} (α : Δ[n + 1].obj m)
    (j : Fin (n + 2)) (hj : ∀ k, asOrderHom α k ≠ j) :
    (standardSimplex.map (δ j)).app m (factor_δ α j) = α := by
  change { down := SimplexCategory.factor_δ (m := m.unop.len) _ j ≫ δ j } = α
  rw [SimplexCategory.factor_δ_spec _ j hj]
  rfl

lemma factor_δ_δ_eq {n : ℕ} {m : SimplexCategoryᵒᵖ}
    (α : Δ[n].obj m) (j : Fin (n + 2)) :
    factor_δ ((standardSimplex.map (δ j)).app m α) j = α := by
  dsimp only [factor_δ]
  rw [← FunctorToTypes.comp, ← Functor.map_comp]
  change (standardSimplex.map (SimplexCategory.factor_δ _ _)).app _ _ = _
  rw [SimplexCategory.factor_δ_δ_eq, CategoryTheory.Functor.map_id]
  rfl

end standardSimplex

abbrev factor_δ₂ {n : ℕ} {m : SimplexCategoryᵒᵖ} (α : Δ[n + 2].obj m)
    (i : Fin (n + 2)) (j : Fin (n + 3)) : Δ[n].obj m :=
  standardSimplex.factor_δ (standardSimplex.factor_δ α j) i

open Fin in
lemma δ_factor_δ₂_le {n : ℕ} {m : SimplexCategoryᵒᵖ} (α : Δ[n + 2].obj m)
    {i j : Fin (n + 2)} (h : i ≤ j) (hi : ∀ x, (asOrderHom α) x ≠ i.castSucc)
    (hj : ∀ x, (asOrderHom α) x ≠ j.succ) :
    (standardSimplex.map (δ i)).app m (factor_δ₂ α i j.succ) =
      standardSimplex.factor_δ α j.succ := by
  simp only [standardSimplex.factor_δ, predAbove_zero_succ]
  apply standardSimplex.factor_δ_spec
  intro k; specialize hi k; specialize hj k
  simp only [σ, asOrderHom, yoneda_obj_obj, standardSimplex, uliftFunctor,
    Functor.comp_obj, mkHom, Functor.comp_map,
    SimplicialObject.whiskering_obj_map_app, uliftFunctor_map, yoneda_map_app,
    comp_toOrderHom, len_mk, Hom.toOrderHom_mk, OrderHom.comp_coe,
    OrderHom.coe_mk, Function.comp_apply, ne_eq]
  rcases lt_or_eq_of_le h with (h | rfl)
  · exact hi ∘ (predAbove_eq_lt_iff h _).mp
  · rw [predAbove_eq_iff, not_or]
    exact And.intro hi hj

open Fin in
lemma δ_factor_δ₂_ge {n : ℕ} {m : SimplexCategoryᵒᵖ} (α : Δ[n + 2].obj m)
    {i j : Fin (n + 2)} (h : i ≤ j) (hi : ∀ x, (asOrderHom α) x ≠ i.castSucc)
    (hj : ∀ x, (asOrderHom α) x ≠ j.succ) :
    (standardSimplex.map (δ j)).app m (factor_δ₂ α i j.succ) =
      standardSimplex.factor_δ α i.castSucc := by
  simp only [standardSimplex.factor_δ, standardSimplex, uliftFunctor,
    Functor.comp_obj, SimplicialObject.whiskering_obj_obj_obj, yoneda_obj_obj,
    uliftFunctor_obj, Functor.comp_map, SimplicialObject.whiskering_obj_map_app,
    uliftFunctor_map, yoneda_map_app, Category.assoc, ULift.up_inj]
  rw [σ_predAbove_zero_comp_σ_predAbove_zero_assoc h]
  change factor_δ (m := m.unop.len) (_ ≫ σ _) _ ≫ δ _ = _
  apply factor_δ_spec
  intro k; specialize hi k; specialize hj k
  dsimp [σ]
  rcases lt_or_eq_of_le h with (h | rfl)
  · rw [predAbove_eq_gt_iff]
    · exact hj
    · exact lt_of_le_of_lt (castSucc_le_castSucc_iff.mp (predAbove_le _ _)) h
  · cases' i using cases with i
    · rw [castSucc_zero] at hi ⊢
      change ¬predAbove _ (asOrderHom α k) = _
      rw [predAbove_right_zero, predAbove_eq_iff, not_or]
      exact And.intro hi hj
    · rw [← succ_castSucc, predAbove_zero_succ,
        predAbove_eq_gt_iff (castSucc_lt_succ i)]
      exact hj

def diagram (n : ℕ) : MultispanIndex SSet where
  L := { (i, j) : Fin (n + 2) × Fin (n + 3) | i.castSucc < j }
  R := Fin (n + 3)
  fstFrom p := p.1.1.castSucc
  sndFrom p := p.1.2
  left _ := Δ[n]
  right _ := Δ[n + 1]
  fst p := standardSimplex.map <| δ <| p.1.2.pred <| Fin.ne_zero_of_lt p.2
  snd p := standardSimplex.map <| δ p.1.1

lemma π_factor_δ_lt {n : ℕ} (X : Multicofork (diagram n)) {m : SimplexCategoryᵒᵖ}
    (α : Δ[n + 2].obj m) {i j : Fin (n + 3)} (h : i < j)
    (hi : ∀ x, asOrderHom α x ≠ i) (hj : ∀ x, asOrderHom α x ≠ j) :
    (X.π i).app m (standardSimplex.factor_δ α i) =
      (X.π j).app m (standardSimplex.factor_δ α j) := by
  have hlast := Fin.ne_last_of_lt h
  have h0 := Fin.ne_zero_of_lt h
  have hle := Fin.castPred_le_pred_iff hlast h0 |>.mpr h
  let ij : { (i, j) : Fin (n + 2) × Fin (n + 3) | i.castSucc < j } :=
    ⟨(i.castPred hlast, j), h⟩
  rw [← Fin.castSucc_castPred i hlast] at hi ⊢
  rw [← Fin.succ_pred j h0] at hj ⊢
  rw [← δ_factor_δ₂_le α hle hi hj, ← δ_factor_δ₂_ge α hle hi hj,
    ← FunctorToTypes.comp, ← FunctorToTypes.comp, Fin.succ_pred]
  change ((diagram n).fst ij ≫ X.π _).app m _ =
    ((diagram n).snd ij ≫ X.π _).app m _
  rw [X.condition]

lemma π_factor_δ {n : ℕ} (X : Multicofork (diagram n))
    {m : SimplexCategoryᵒᵖ} (α : Δ[n + 2].obj m)
    (i : Fin (n + 3)) (hi : ∀ x, asOrderHom α x ≠ i)
    (j : Fin (n + 3)) (hj : ∀ x, asOrderHom α x ≠ j) :
    (X.π i).app m (standardSimplex.factor_δ α i) =
      (X.π j).app m (standardSimplex.factor_δ α j) := by
  rcases lt_trichotomy i j with (h | rfl | h)
  · exact π_factor_δ_lt X α h hi hj
  · rfl
  · exact π_factor_δ_lt X α h hj hi |>.symm

abbrev cocone (n : ℕ) : Multicofork (diagram n) := by
  refine Multicofork.ofπ (diagram n) ∂Δ[n + 2] ?_ ?_
  · intro k
    refine {
      app := fun m α ↦ ⟨standardSimplex.map (δ k) |>.app m α, ?_⟩
      naturality := fun a b f ↦ rfl }
    apply δ_not_surjective k ∘ Function.Surjective.of_comp
  · intro ⟨⟨i, j⟩, h⟩
    ext m α
    apply Subtype.ext
    rw [NatTrans.comp_app, NatTrans.comp_app]
    dsimp only [diagram, Set.coe_setOf, Set.mem_setOf_eq, types_comp_apply]
    rw [← FunctorToTypes.comp, ← Functor.map_comp, ← δ_comp_δ' h]
    rfl

open standardSimplex boundary in
noncomputable def isColimit (n : ℕ) : IsColimit (cocone n) := by
  refine Multicofork.IsColimit.mk (cocone n) ?_ ?_ ?_
  · intro X
    refine {
      app := fun m α ↦ X.π (skips α) |>.app m <| factor_δ α.1 (skips α),
      naturality := ?_ }
    intro a b f
    ext α
    dsimp only [Multicofork.ofπ_pt, types_comp_apply] at α ⊢
    rw [π_factor_δ X _ _ _ (skips α)]
    · rw [← types_comp_apply _ (X.pt.map f), ← NatTrans.naturality]
      rfl
    · intro k; apply skips_spec α
    · exact skips_spec <| ∂Δ[n + 2].map f α
  · intro X k
    ext m α
    dsimp only [diagram] at k α
    change (X.π _).app _ (factor_δ ((standardSimplex.map _).app _ _) _) = _
    rw [π_factor_δ X _ _ _ k]
    · rw [standardSimplex.factor_δ_δ_eq]
    · intro j; exact Fin.succAbove_ne k _
    · exact skips_spec <| cocone n |>.π k |>.app m α
  · intro X f h
    ext m α
    simp only [Multicofork.ofπ_pt, ← h (skips α)]
    apply congr_arg
    apply Subtype.ext
    exact standardSimplex.factor_δ_spec _ _ (skips_spec α) |>.symm

end SSet
