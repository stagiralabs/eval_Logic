import VerifiedAgora.tagger
/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Control.EquivFunctor
import Mathlib.Data.Option.Basic
import Mathlib.Data.Subtype
import Mathlib.Logic.Equiv.Defs

/-!
# Equivalences for `Option α`


We define
* `Equiv.optionCongr`: the `Option α ≃ Option β` constructed from `e : α ≃ β` by sending `none` to
  `none`, and applying `e` elsewhere.
* `Equiv.removeNone`: the `α ≃ β` constructed from `Option α ≃ Option β` by removing `none` from
  both sides.
-/

universe u

namespace Equiv

open Option

variable {α β γ : Type*}

section OptionCongr

/-- A universe-polymorphic version of `EquivFunctor.mapEquiv Option e`. -/
@[simps apply]
def optionCongr (e : α ≃ β) : Option α ≃ Option β where
  toFun := Option.map e
  invFun := Option.map e.symm
  left_inv x := (Option.map_map _ _ _).trans <| e.symm_comp_self.symm ▸ congr_fun Option.map_id x
  right_inv x := (Option.map_map _ _ _).trans <| e.self_comp_symm.symm ▸ congr_fun Option.map_id x

@[target] theorem optionCongr_refl : optionCongr (Equiv.refl α) = Equiv.refl _ := by sorry

@[simp]
theorem optionCongr_symm (e : α ≃ β) : (optionCongr e).symm = optionCongr e.symm :=
  rfl

@[simp]
theorem optionCongr_trans (e₁ : α ≃ β) (e₂ : β ≃ γ) :
    (optionCongr e₁).trans (optionCongr e₂) = optionCongr (e₁.trans e₂) :=
  ext <| Option.map_map _ _

/-- When `α` and `β` are in the same universe, this is the same as the result of
`EquivFunctor.mapEquiv`. -/
@[target] theorem optionCongr_eq_equivFunctor_mapEquiv {α β : Type u} (e : α ≃ β) :
    optionCongr e = EquivFunctor.mapEquiv Option e := by sorry

end OptionCongr

section RemoveNone

variable (e : Option α ≃ Option β)

/-- If we have a value on one side of an `Equiv` of `Option`
    we also have a value on the other side of the equivalence
-/
def removeNone_aux (x : α) : β :=
  if h : (e (some x)).isSome then Option.get _ h
  else
    Option.get _ <|
      show (e none).isSome by
        rw [← Option.ne_none_iff_isSome]
        intro hn
        rw [Option.not_isSome_iff_eq_none, ← hn] at h
        exact Option.some_ne_none _ (e.injective h)

theorem removeNone_aux_some {x : α} (h : ∃ x', e (some x) = some x') :
    some (removeNone_aux e x) = e (some x) := by
  simp [removeNone_aux, Option.isSome_iff_exists.mpr h]

@[target] theorem removeNone_aux_none {x : α} (h : e (some x) = none) :
    some (removeNone_aux e x) = e none := by sorry

theorem removeNone_aux_inv (x : α) : removeNone_aux e.symm (removeNone_aux e x) = x :=
  Option.some_injective _
    (by
      cases h1 : e.symm (some (removeNone_aux e x)) <;> cases h2 : e (some x)
      · rw [removeNone_aux_none _ h1]
        exact (e.eq_symm_apply.mpr h2).symm

      · rw [removeNone_aux_some _ ⟨_, h2⟩] at h1
        simp at h1

      · rw [removeNone_aux_none _ h2] at h1
        simp at h1

      · rw [removeNone_aux_some _ ⟨_, h1⟩]
        rw [removeNone_aux_some _ ⟨_, h2⟩]
        simp)

/-- Given an equivalence between two `Option` types, eliminate `none` from that equivalence by
mapping `e.symm none` to `e none`. -/
def removeNone : α ≃ β where
  toFun := removeNone_aux e
  invFun := removeNone_aux e.symm
  left_inv := removeNone_aux_inv e
  right_inv := removeNone_aux_inv e.symm

@[simp]
theorem removeNone_symm : (removeNone e).symm = removeNone e.symm :=
  rfl

@[target] theorem removeNone_some {x : α} (h : ∃ x', e (some x) = some x') :
    some (removeNone e x) = e (some x) := by sorry

theorem removeNone_none {x : α} (h : e (some x) = none) : some (removeNone e x) = e none :=
  removeNone_aux_none e h

@[target] theorem option_symm_apply_none_iff : e.symm none = none ↔ e none = none := by sorry

@[target] theorem some_removeNone_iff {x : α} : some (removeNone e x) = e none ↔ e.symm none = some x := by sorry

@[target] theorem removeNone_optionCongr (e : α ≃ β) : removeNone e.optionCongr = e := by sorry

end RemoveNone

@[target] theorem optionCongr_injective : Function.Injective (optionCongr : α ≃ β → Option α ≃ Option β) := by sorry

def optionSubtype [DecidableEq β] (x : β) :
    { e : Option α ≃ β // e none = x } ≃ (α ≃ { y : β // y ≠ x }) where
  toFun e :=
    { toFun := fun a =>
        ⟨(e : Option α ≃ β) a, ((EquivLike.injective _).ne_iff' e.property).2 (some_ne_none _)⟩,
      invFun := fun b =>
        get _
          (ne_none_iff_isSome.1
            (((EquivLike.injective _).ne_iff'
              ((apply_eq_iff_eq_symm_apply _).1 e.property).symm).2 b.property)),
      left_inv := fun a => by
        rw [← some_inj, some_get]
        exact symm_apply_apply (e : Option α ≃ β) a,
      right_inv := fun b => by
        ext
        simp }
  invFun e :=
    ⟨{  toFun := fun a => casesOn' a x (Subtype.val ∘ e),
        invFun := fun b => if h : b = x then none else e.symm ⟨b, h⟩,
        left_inv := fun a => by
          cases a with
          | none => simp
          | some a =>
            simp only [casesOn'_some, Function.comp_apply, Subtype.coe_eta,
              symm_apply_apply, dite_eq_ite]
            exact if_neg (e a).property,
        right_inv := fun b => by
          by_cases h : b = x <;> simp [h] },
      rfl⟩
  left_inv e := by
    ext a
    cases a
    · simpa using e.property.symm
    · simp
  right_inv e := by
    ext a
    rfl

@[target] theorem optionSubtype_apply_apply
    [DecidableEq β] (x : β)
    (e : { e : Option α ≃ β // e none = x })
    (a : α)
    (h) : optionSubtype x e a = ⟨(e : Option α ≃ β) a, h⟩ := by sorry

@[target] theorem coe_optionSubtype_apply_apply
    [DecidableEq β] (x : β)
    (e : { e : Option α ≃ β // e none = x })
    (a : α) : ↑(optionSubtype x e a) = (e : Option α ≃ β) a := by sorry

@[target] theorem optionSubtype_apply_symm_apply
    [DecidableEq β] (x : β)
    (e : { e : Option α ≃ β // e none = x })
    (b : { y : β // y ≠ x }) : ↑((optionSubtype x e).symm b) = (e : Option α ≃ β).symm b := by sorry

@[simp]
theorem optionSubtype_symm_apply_apply_coe [DecidableEq β] (x : β) (e : α ≃ { y : β // y ≠ x })
    (a : α) : ((optionSubtype x).symm e : Option α ≃ β) a = e a :=
  rfl

@[simp]
theorem optionSubtype_symm_apply_apply_some
    [DecidableEq β]
    (x : β)
    (e : α ≃ { y : β // y ≠ x })
    (a : α) : ((optionSubtype x).symm e : Option α ≃ β) (some a) = e a :=
  rfl

@[target] theorem optionSubtype_symm_apply_apply_none
    [DecidableEq β]
    (x : β)
    (e : α ≃ { y : β // y ≠ x }) : ((optionSubtype x).symm e : Option α ≃ β) none = x := by sorry

@[target] theorem optionSubtype_symm_apply_symm_apply [DecidableEq β] (x : β) (e : α ≃ { y : β // y ≠ x })
    (b : { y : β // y ≠ x }) : ((optionSubtype x).symm e : Option α ≃ β).symm b = e.symm b := by sorry

@[simps!]
def optionSubtypeNe (a : α) : Option {b // b ≠ a} ≃ α := optionSubtype a |>.symm (.refl _) |>.1

@[target] lemma optionSubtypeNe_symm_self (a : α) : (optionSubtypeNe a).symm a = none := by sorry

@[target] lemma optionSubtypeNe_symm_of_ne (hba : b ≠ a) : (optionSubtypeNe a).symm b = some ⟨b, hba⟩ := by sorry

@[target] lemma optionSubtypeNe_none (a : α) : optionSubtypeNe a none = a := by sorry

@[target] lemma optionSubtypeNe_some (a : α) (b) : optionSubtypeNe a (some b) = b := by sorry

end Equiv
