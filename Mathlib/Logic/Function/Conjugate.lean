import VerifiedAgora.tagger
/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Logic.Function.Basic

/-!
# Semiconjugate and commuting maps

We define the following predicates:

* `Function.Semiconj`: `f : α → β` semiconjugates `ga : α → α` to `gb : β → β` if `f ∘ ga = gb ∘ f`;
* `Function.Semiconj₂`: `f : α → β` semiconjugates a binary operation `ga : α → α → α`
  to `gb : β → β → β` if `f (ga x y) = gb (f x) (f y)`;
* `Function.Commute`: `f : α → α` commutes with `g : α → α` if `f ∘ g = g ∘ f`,
  or equivalently `Semiconj f g g`.
-/

namespace Function

variable {α : Type*} {β : Type*} {γ : Type*}

/--
We say that `f : α → β` semiconjugates `ga : α → α` to `gb : β → β` if `f ∘ ga = gb ∘ f`.
We use `∀ x, f (ga x) = gb (f x)` as the definition, so given `h : Function.Semiconj f ga gb` and
`a : α`, we have `h a : f (ga a) = gb (f a)` and `h.comp_eq : f ∘ ga = gb ∘ f`.
-/
def Semiconj (f : α → β) (ga : α → α) (gb : β → β) : Prop :=
  ∀ x, f (ga x) = gb (f x)

namespace Semiconj

variable {f fab : α → β} {fbc : β → γ} {ga ga' : α → α} {gb gb' : β → β} {gc : γ → γ}

/-- Definition of `Function.Semiconj` in terms of functional equality. -/
lemma _root_.Function.semiconj_iff_comp_eq : Semiconj f ga gb ↔ f ∘ ga = gb ∘ f := funext_iff.symm

protected alias ⟨comp_eq, _⟩ := semiconj_iff_comp_eq

protected theorem eq (h : Semiconj f ga gb) (x : α) : f (ga x) = gb (f x) :=
  h x

/-- If `f` semiconjugates `ga` to `gb` and `ga'` to `gb'`,
then it semiconjugates `ga ∘ ga'` to `gb ∘ gb'`. -/
theorem comp_right (h : Semiconj f ga gb) (h' : Semiconj f ga' gb') :
    Semiconj f (ga ∘ ga') (gb ∘ gb') := fun x ↦ by
  simp only [comp_apply, h.eq, h'.eq]

/-- If `fab : α → β` semiconjugates `ga` to `gb` and `fbc : β → γ` semiconjugates `gb` to `gc`,
then `fbc ∘ fab` semiconjugates `ga` to `gc`.

See also `Function.Semiconj.comp_left` for a version with reversed arguments. -/
protected theorem trans (hab : Semiconj fab ga gb) (hbc : Semiconj fbc gb gc) :
    Semiconj (fbc ∘ fab) ga gc := fun x ↦ by
  simp only [comp_apply, hab.eq, hbc.eq]

/-- If `fbc : β → γ` semiconjugates `gb` to `gc` and `fab : α → β` semiconjugates `ga` to `gb`,
then `fbc ∘ fab` semiconjugates `ga` to `gc`.

See also `Function.Semiconj.trans` for a version with reversed arguments.

**Backward compatibility note:** before 2024-01-13,
this lemma used to have the same order of arguments that `Function.Semiconj.trans` has now. -/
theorem comp_left (hbc : Semiconj fbc gb gc) (hab : Semiconj fab ga gb) :
    Semiconj (fbc ∘ fab) ga gc :=
  hab.trans hbc

/-- Any function semiconjugates the identity function to the identity function. -/
theorem id_right : Semiconj f id id := fun _ ↦ rfl

/-- The identity function semiconjugates any function to itself. -/
theorem id_left : Semiconj id ga ga := fun _ ↦ rfl

/-- If `f : α → β` semiconjugates `ga : α → α` to `gb : β → β`,
`ga'` is a right inverse of `ga`, and `gb'` is a left inverse of `gb`,
then `f` semiconjugates `ga'` to `gb'` as well. -/
theorem inverses_right (h : Semiconj f ga gb) (ha : RightInverse ga' ga) (hb : LeftInverse gb' gb) :
    Semiconj f ga' gb' := fun x ↦ by
  rw [← hb (f (ga' x)), ← h.eq, ha x]

/-- If `f` semiconjugates `ga` to `gb` and `f'` is both a left and a right inverse of `f`,
then `f'` semiconjugates `gb` to `ga`. -/
lemma inverse_left {f' : β → α} (h : Semiconj f ga gb)
    (hf₁ : LeftInverse f' f) (hf₂ : RightInverse f' f) : Semiconj f' gb ga := fun x ↦ by
  rw [← hf₁.injective.eq_iff, h, hf₂, hf₂]

/-- If `f : α → β` semiconjugates `ga : α → α` to `gb : β → β`,
then `Option.map f` semiconjugates `Option.map ga` to `Option.map gb`. -/
theorem option_map {f : α → β} {ga : α → α} {gb : β → β} (h : Semiconj f ga gb) :
    Semiconj (Option.map f) (Option.map ga) (Option.map gb)
  | none => rfl
  | some _ => congr_arg some <| h _

end Semiconj

/--
Two maps `f g : α → α` commute if `f (g x) = g (f x)` for all `x : α`.
Given `h : Function.commute f g` and `a : α`, we have `h a : f (g a) = g (f a)` and
`h.comp_eq : f ∘ g = g ∘ f`.
-/
protected def Commute (f g : α → α) : Prop :=
  Semiconj f g g

open Function (Commute)

/-- Reinterpret `Function.Semiconj f g g` as `Function.Commute f g`. These two predicates are
definitionally equal but have different dot-notation lemmas. -/
theorem Semiconj.commute {f g : α → α} (h : Semiconj f g g) : Commute f g := h

namespace Commute

variable {f f' g g' : α → α}

/-- Reinterpret `Function.Commute f g` as `Function.Semiconj f g g`. These two predicates are
definitionally equal but have different dot-notation lemmas. -/
theorem semiconj (h : Commute f g) : Semiconj f g g := h

protected lemma ProvablyEquivalent.refl [System.Minimal 𝓢] (φ : F) : φ ≡ φ := by sorry


protected lemma ProvablyEquivalent.symm [System.Minimal 𝓢] {φ ψ : F} : φ ≡ ψ → ψ ≡ φ := by sorry


/-- If `f` commutes with `g` and `g'`, then it commutes with `g ∘ g'`. -/
theorem comp_right (h : Commute f g) (h' : Commute f g') : Commute f (g ∘ g') :=
  Semiconj.comp_right h h'

/-- If `f` and `f'` commute with `g`, then `f ∘ f'` commutes with `g` as well. -/
nonrec theorem comp_left (h : Commute f g) (h' : Commute f' g) : Commute (f ∘ f') g :=
  h.comp_left h'

/-- Any self-map commutes with the identity map. -/
theorem id_right : Commute f id := Semiconj.id_right

/-- The identity map commutes with any self-map. -/
theorem id_left : Commute id f :=
  Semiconj.id_left

/-- If `f` commutes with `g`, then `Option.map f` commutes with `Option.map g`. -/
nonrec theorem option_map {f g : α → α} (h : Commute f g) : Commute (Option.map f) (Option.map g) :=
  h.option_map

end Commute

/--
A map `f` semiconjugates a binary operation `ga` to a binary operation `gb` if
for all `x`, `y` we have `f (ga x y) = gb (f x) (f y)`. E.g., a `MonoidHom`
semiconjugates `(*)` to `(*)`.
-/
def Semiconj₂ (f : α → β) (ga : α → α → α) (gb : β → β → β) : Prop :=
  ∀ x y, f (ga x y) = gb (f x) (f y)

namespace Semiconj₂

variable {f : α → β} {ga : α → α → α} {gb : β → β → β}

protected theorem eq (h : Semiconj₂ f ga gb) (x y : α) : f (ga x y) = gb (f x) (f y) :=
  h x y

protected theorem comp_eq (h : Semiconj₂ f ga gb) : bicompr f ga = bicompl gb f f :=
  funext fun x ↦ funext <| h x

theorem id_left (op : α → α → α) : Semiconj₂ id op op := fun _ _ ↦ rfl

def comp (Ψ : L₂ →ᵥ L₃) (Φ : L₁ →ᵥ L₂) : L₁ →ᵥ L₃ where
  func := by sorry


theorem isAssociative_right [Std.Associative ga] (h : Semiconj₂ f ga gb) (h_surj : Surjective f) :
    Std.Associative gb :=
  ⟨h_surj.forall₃.2 fun x₁ x₂ x₃ ↦ by simp only [← h.eq, Std.Associative.assoc (op := ga)]⟩

theorem isAssociative_left [Std.Associative gb] (h : Semiconj₂ f ga gb) (h_inj : Injective f) :
    Std.Associative ga :=
  ⟨fun x₁ x₂ x₃ ↦ h_inj <| by simp only [h.eq, Std.Associative.assoc (op := gb)]⟩

theorem isIdempotent_right [Std.IdempotentOp ga] (h : Semiconj₂ f ga gb) (h_surj : Surjective f) :
    Std.IdempotentOp gb :=
  ⟨h_surj.forall.2 fun x ↦ by simp only [← h.eq, Std.IdempotentOp.idempotent (op := ga)]⟩

theorem isIdempotent_left [Std.IdempotentOp gb] (h : Semiconj₂ f ga gb) (h_inj : Injective f) :
    Std.IdempotentOp ga :=
  ⟨fun x ↦ h_inj <| by rw [h.eq, Std.IdempotentOp.idempotent (op := gb)]⟩

end Semiconj₂

end Function
