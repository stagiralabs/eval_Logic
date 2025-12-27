import VerifiedAgora.tagger
/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Logic.Relator
import Mathlib.Tactic.Use
import Mathlib.Tactic.MkIffOfInductiveProp
import Mathlib.Tactic.SimpRw
import Mathlib.Logic.Basic
import Mathlib.Order.Defs.Unbundled

/-!
# Relation closures

This file defines the reflexive, transitive, reflexive transitive and equivalence closures
of relations and proves some basic results on them.

Note that this is about unbundled relations, that is terms of types of the form `α → β → Prop`. For
the bundled version, see `Rel`.

## Definitions

* `Relation.ReflGen`: Reflexive closure. `ReflGen r` relates everything `r` related, plus for all
  `a` it relates `a` with itself. So `ReflGen r a b ↔ r a b ∨ a = b`.
* `Relation.TransGen`: Transitive closure. `TransGen r` relates everything `r` related
  transitively. So `TransGen r a b ↔ ∃ x₀ ... xₙ, r a x₀ ∧ r x₀ x₁ ∧ ... ∧ r xₙ b`.
* `Relation.ReflTransGen`: Reflexive transitive closure. `ReflTransGen r` relates everything
  `r` related transitively, plus for all `a` it relates `a` with itself. So
  `ReflTransGen r a b ↔ (∃ x₀ ... xₙ, r a x₀ ∧ r x₀ x₁ ∧ ... ∧ r xₙ b) ∨ a = b`. It is the same as
  the reflexive closure of the transitive closure, or the transitive closure of the reflexive
  closure. In terms of rewriting systems, this means that `a` can be rewritten to `b` in a number of
  rewrites.
* `Relation.EqvGen`: Equivalence closure. `EqvGen r` relates everything `ReflTransGen r` relates,
  plus for all related pairs it relates them in the opposite order.
* `Relation.Comp`:  Relation composition. We provide notation `∘r`. For `r : α → β → Prop` and
  `s : β → γ → Prop`, `r ∘r s`relates `a : α` and `c : γ` iff there exists `b : β` that's related to
  both.
* `Relation.Map`: Image of a relation under a pair of maps. For `r : α → β → Prop`, `f : α → γ`,
  `g : β → δ`, `Map r f g` is the relation `γ → δ → Prop` relating `f a` and `g b` for all `a`, `b`
  related by `r`.
* `Relation.Join`: Join of a relation. For `r : α → α → Prop`, `Join r a b ↔ ∃ c, r a c ∧ r b c`. In
  terms of rewriting systems, this means that `a` and `b` can be rewritten to the same term.
-/


open Function

variable {α β γ δ ε ζ : Type*}

section NeImp

variable {r : α → α → Prop}

theorem IsRefl.reflexive [IsRefl α r] : Reflexive r := fun x ↦ IsRefl.refl x

/-- To show a reflexive relation `r : α → α → Prop` holds over `x y : α`,
it suffices to show it holds when `x ≠ y`. -/
theorem Reflexive.rel_of_ne_imp (h : Reflexive r) {x y : α} (hr : x ≠ y → r x y) : r x y := by
  by_cases hxy : x = y
  · exact hxy ▸ h x
  · exact hr hxy


/-- If a reflexive relation `r : α → α → Prop` holds over `x y : α`,
then it holds whether or not `x ≠ y`. -/
theorem Reflexive.ne_imp_iff (h : Reflexive r) {x y : α} : x ≠ y → r x y ↔ r x y :=
  ⟨h.rel_of_ne_imp, fun hr _ ↦ hr⟩

/-- If a reflexive relation `r : α → α → Prop` holds over `x y : α`,
then it holds whether or not `x ≠ y`. Unlike `Reflexive.ne_imp_iff`, this uses `[IsRefl α r]`. -/
theorem reflexive_ne_imp_iff [IsRefl α r] {x y : α} : x ≠ y → r x y ↔ r x y :=
  IsRefl.reflexive.ne_imp_iff

protected theorem Symmetric.iff (H : Symmetric r) (x y : α) : r x y ↔ r y x :=
  ⟨fun h ↦ H h, fun h ↦ H h⟩

theorem Symmetric.flip_eq (h : Symmetric r) : flip r = r :=
  funext₂ fun _ _ ↦ propext <| h.iff _ _

theorem Symmetric.swap_eq : Symmetric r → swap r = r :=
  Symmetric.flip_eq

theorem flip_eq_iff : flip r = r ↔ Symmetric r :=
  ⟨fun h _ _ ↦ (congr_fun₂ h _ _).mp, Symmetric.flip_eq⟩

theorem swap_eq_iff : swap r = r ↔ Symmetric r :=
  flip_eq_iff

end NeImp

section Comap

variable {r : β → β → Prop}

theorem Reflexive.comap (h : Reflexive r) (f : α → β) : Reflexive (r on f) := fun a ↦ h (f a)

theorem Symmetric.comap (h : Symmetric r) (f : α → β) : Symmetric (r on f) := fun _ _ hab ↦ h hab

theorem Transitive.comap (h : Transitive r) (f : α → β) : Transitive (r on f) :=
  fun _ _ _ hab hbc ↦ h hab hbc

theorem Equivalence.comap (h : Equivalence r) (f : α → β) : Equivalence (r on f) :=
  ⟨fun a ↦ h.refl (f a), h.symm, h.trans⟩

end Comap

namespace Relation

section Comp

variable {r : α → β → Prop} {p : β → γ → Prop} {q : γ → δ → Prop}

/-- The composition of two relations, yielding a new relation.  The result
relates a term of `α` and a term of `γ` if there is an intermediate
term of `β` related to both.
-/
def Comp (r : α → β → Prop) (p : β → γ → Prop) (a : α) (c : γ) : Prop :=
  ∃ b, r a b ∧ p b c

@[inherit_doc]
local infixr:80 " ∘r " => Relation.Comp

@[simp]
theorem comp_eq_fun (f : γ → β) : r ∘r (· = f ·) = (r · <| f ·) := by
  ext x y
  simp [Comp]

@[simp]
theorem comp_eq : r ∘r (· = ·) = r := comp_eq_fun ..

@[simp]
theorem fun_eq_comp (f : γ → α) : (f · = ·) ∘r r = (r <| f ·) := by
  ext x y
  simp [Comp]

@[simp]
theorem eq_comp : (· = ·) ∘r r = r := fun_eq_comp ..

@[simp]
theorem iff_comp {r : Prop → α → Prop} : (· ↔ ·) ∘r r = r := by
  have : (· ↔ ·) = (· = ·) := by funext a b; exact iff_eq_eq
  rw [this, eq_comp]

@[simp]
theorem comp_iff {r : α → Prop → Prop} : r ∘r (· ↔ ·) = r := by
  have : (· ↔ ·) = (· = ·) := by funext a b; exact iff_eq_eq
  rw [this, comp_eq]

theorem comp_assoc : (r ∘r p) ∘r q = r ∘r p ∘r q := by
  funext a d
  apply propext
  constructor
  · exact fun ⟨c, ⟨b, hab, hbc⟩, hcd⟩ ↦ ⟨b, hab, c, hbc, hcd⟩
  · exact fun ⟨b, hab, c, hbc, hcd⟩ ↦ ⟨c, ⟨b, hab, hbc⟩, hcd⟩

theorem flip_comp : flip (r ∘r p) = flip p ∘r flip r := by
  funext c a
  apply propext
  constructor
  · exact fun ⟨b, hab, hbc⟩ ↦ ⟨b, hbc, hab⟩
  · exact fun ⟨b, hbc, hab⟩ ↦ ⟨b, hab, hbc⟩

end Comp

section Fibration

variable (rα : α → α → Prop) (rβ : β → β → Prop) (f : α → β)

/-- A function `f : α → β` is a fibration between the relation `rα` and `rβ` if for all
  `a : α` and `b : β`, whenever `b : β` and `f a` are related by `rβ`, `b` is the image
  of some `a' : α` under `f`, and `a'` and `a` are related by `rα`. -/
def Fibration :=
  ∀ ⦃a b⦄, rβ b (f a) → ∃ a', rα a' a ∧ f a' = b

variable {rα rβ}

/-- If `f : α → β` is a fibration between relations `rα` and `rβ`, and `a : α` is
  accessible under `rα`, then `f a` is accessible under `rβ`. -/
theorem _root_.Acc.of_fibration (fib : Fibration rα rβ f) {a} (ha : Acc rα a) : Acc rβ (f a) := by
  induction ha with | intro a _ ih => ?_
  refine Acc.intro (f a) fun b hr ↦ ?_
  obtain ⟨a', hr', rfl⟩ := fib hr
  exact ih a' hr'

theorem _root_.Acc.of_downward_closed (dc : ∀ {a b}, rβ b (f a) → ∃ c, f c = b) (a : α)
    (ha : Acc (InvImage rβ f) a) : Acc rβ (f a) :=
  ha.of_fibration f fun a _ h ↦
    let ⟨a', he⟩ := dc h
    -- Porting note: Lean 3 did not need the motive
    ⟨a', he.substr (p := fun x ↦ rβ x (f a)) h, he⟩

end Fibration

section Map
variable {r : α → β → Prop} {f : α → γ} {g : β → δ} {c : γ} {d : δ}

/-- The map of a relation `r` through a pair of functions pushes the
relation to the codomains of the functions.  The resulting relation is
defined by having pairs of terms related if they have preimages
related by `r`.
-/
protected def Map (r : α → β → Prop) (f : α → γ) (g : β → δ) : γ → δ → Prop := fun c d ↦
  ∃ a b, r a b ∧ f a = c ∧ g b = d

lemma map_apply : Relation.Map r f g c d ↔ ∃ a b, r a b ∧ f a = c ∧ g b = d := Iff.rfl

@[simp] lemma map_map (r : α → β → Prop) (f₁ : α → γ) (g₁ : β → δ) (f₂ : γ → ε) (g₂ : δ → ζ) :
    Relation.Map (Relation.Map r f₁ g₁) f₂ g₂ = Relation.Map r (f₂ ∘ f₁) (g₂ ∘ g₁) := by
  ext a b
  simp_rw [Relation.Map, Function.comp_apply, ← exists_and_right, @exists_comm γ, @exists_comm δ]
  refine exists₂_congr fun a b ↦ ⟨?_, fun h ↦ ⟨_, _, ⟨⟨h.1, rfl, rfl⟩, h.2⟩⟩⟩
  rintro ⟨_, _, ⟨hab, rfl, rfl⟩, h⟩
  exact ⟨hab, h⟩

@[simp]
lemma map_apply_apply (hf : Injective f) (hg : Injective g) (r : α → β → Prop) (a : α) (b : β) :
    Relation.Map r f g (f a) (g b) ↔ r a b := by simp [Relation.Map, hf.eq_iff, hg.eq_iff]

@[simp] lemma map_id_id (r : α → β → Prop) : Relation.Map r id id = r := by ext; simp [Relation.Map]

instance [Decidable (∃ a b, r a b ∧ f a = c ∧ g b = d)] : Decidable (Relation.Map r f g c d) :=
  ‹Decidable _›

end Map

variable {r : α → α → Prop} {a b c : α}

/-- `ReflTransGen r`: reflexive transitive closure of `r` -/
@[mk_iff ReflTransGen.cases_tail_iff]
inductive ReflTransGen (r : α → α → Prop) (a : α) : α → Prop
  | refl : ReflTransGen r a a
  | tail {b c} : ReflTransGen r a b → r b c → ReflTransGen r a c

attribute [refl] ReflTransGen.refl

/-- `ReflGen r`: reflexive closure of `r` -/
@[mk_iff]
inductive ReflGen (r : α → α → Prop) (a : α) : α → Prop
  | refl : ReflGen r a a
  | single {b} : r a b → ReflGen r a b

variable (r) in
/-- `EqvGen r`: equivalence closure of `r`. -/
@[mk_iff]
inductive EqvGen : α → α → Prop
  | rel x y : r x y → EqvGen x y
  | refl x : EqvGen x x
  | symm x y : EqvGen x y → EqvGen y x
  | trans x y z : EqvGen x y → EqvGen y z → EqvGen x z

attribute [mk_iff] TransGen
attribute [refl] ReflGen.refl

namespace ReflGen

theorem to_reflTransGen : ∀ {a b}, ReflGen r a b → ReflTransGen r a b
  | a, _, refl => by rfl
  | _, _, single h => ReflTransGen.tail ReflTransGen.refl h

theorem mono {p : α → α → Prop} (hp : ∀ a b, r a b → p a b) : ∀ {a b}, ReflGen r a b → ReflGen p a b
  | a, _, ReflGen.refl => by rfl
  | a, b, single h => single (hp a b h)

instance : IsRefl α (ReflGen r) :=
  ⟨@refl α r⟩

end ReflGen

namespace ReflTransGen

protected lemma ProvablyEquivalent.trans [System.Minimal 𝓢] {φ ψ χ : F} : φ ≡ ψ → ψ ≡ χ → φ ≡ χ := by sorry


theorem single (hab : r a b) : ReflTransGen r a b :=
  refl.tail hab

theorem head (hab : r a b) (hbc : ReflTransGen r b c) : ReflTransGen r a c := by
  induction hbc with
  | refl => exact refl.tail hab
  | tail _ hcd hac => exact hac.tail hcd

@[target] lemma symmetric : Symmetric ClassicalFrame := by sorry


theorem cases_tail : ReflTransGen r a b → b = a ∨ ∃ c, ReflTransGen r a c ∧ r c b :=
  (cases_tail_iff r a b).1

@[elab_as_elim]
theorem head_induction_on {P : ∀ a : α, ReflTransGen r a b → Prop} {a : α} (h : ReflTransGen r a b)
    (refl : P b refl)
    (head : ∀ {a c} (h' : r a c) (h : ReflTransGen r c b), P c h → P a (h.head h')) : P a h := by
  induction h with
  | refl => exact refl
  | @tail b c _ hbc ih =>
  apply ih
  · exact head hbc _ refl
  · exact fun h1 h2 ↦ head h1 (h2.tail hbc)

@[elab_as_elim]
theorem trans_induction_on {P : ∀ {a b : α}, ReflTransGen r a b → Prop} {a b : α}
    (h : ReflTransGen r a b) (ih₁ : ∀ a, @P a a refl) (ih₂ : ∀ {a b} (h : r a b), P (single h))
    (ih₃ : ∀ {a b c} (h₁ : ReflTransGen r a b) (h₂ : ReflTransGen r b c), P h₁ → P h₂ →
     P (h₁.trans h₂)) : P h := by
  induction h with
  | refl => exact ih₁ a
  | tail hab hbc ih => exact ih₃ hab (single hbc) ih (ih₂ hbc)

theorem cases_head (h : ReflTransGen r a b) : a = b ∨ ∃ c, r a c ∧ ReflTransGen r c b := by
  induction h using Relation.ReflTransGen.head_induction_on
  · left
    rfl
  · right
    exact ⟨_, by assumption, by assumption⟩

theorem cases_head_iff : ReflTransGen r a b ↔ a = b ∨ ∃ c, r a c ∧ ReflTransGen r c b := by
  use cases_head
  rintro (rfl | ⟨c, hac, hcb⟩)
  · rfl
  · exact head hac hcb

theorem total_of_right_unique (U : Relator.RightUnique r) (ab : ReflTransGen r a b)
    (ac : ReflTransGen r a c) : ReflTransGen r b c ∨ ReflTransGen r c b := by
  induction ab with
  | refl => exact Or.inl ac
  | tail _ bd IH =>
    rcases IH with (IH | IH)
    · rcases cases_head IH with (rfl | ⟨e, be, ec⟩)
      · exact Or.inr (single bd)
      · cases U bd be
        exact Or.inl ec
    · exact Or.inr (IH.tail bd)

end ReflTransGen

namespace TransGen

theorem to_reflTransGen {a b} (h : TransGen r a b) : ReflTransGen r a b := by
  induction h with
  | single h => exact ReflTransGen.single h
  | tail _ bc ab => exact ReflTransGen.tail ab bc

theorem trans_left (hab : TransGen r a b) (hbc : ReflTransGen r b c) : TransGen r a c := by
  induction hbc with
  | refl => assumption
  | tail _ hcd hac => exact hac.tail hcd

instance : Trans (TransGen r) (ReflTransGen r) (TransGen r) :=
  ⟨trans_left⟩

attribute [trans] trans

instance : Trans (TransGen r) (TransGen r) (TransGen r) :=
  ⟨trans⟩

theorem head' (hab : r a b) (hbc : ReflTransGen r b c) : TransGen r a c :=
  trans_left (single hab) hbc

theorem tail' (hab : ReflTransGen r a b) (hbc : r b c) : TransGen r a c := by
  induction hab generalizing c with
  | refl => exact single hbc
  | tail _ hdb IH => exact tail (IH hdb) hbc

theorem head (hab : r a b) (hbc : TransGen r b c) : TransGen r a c :=
  head' hab hbc.to_reflTransGen

@[elab_as_elim]
theorem head_induction_on {P : ∀ a : α, TransGen r a b → Prop} {a : α} (h : TransGen r a b)
    (base : ∀ {a} (h : r a b), P a (single h))
    (ih : ∀ {a c} (h' : r a c) (h : TransGen r c b), P c h → P a (h.head h')) : P a h := by
  induction h with
  | single h => exact base h
  | @tail b c _ hbc h_ih =>
  apply h_ih
  · exact fun h ↦ ih h (single hbc) (base hbc)
  · exact fun hab hbc ↦ ih hab _

@[elab_as_elim]
theorem trans_induction_on {P : ∀ {a b : α}, TransGen r a b → Prop} {a b : α} (h : TransGen r a b)
    (base : ∀ {a b} (h : r a b), P (single h))
    (ih : ∀ {a b c} (h₁ : TransGen r a b) (h₂ : TransGen r b c), P h₁ → P h₂ → P (h₁.trans h₂)) :
    P h := by
  induction h with
  | single h => exact base h
  | tail hab hbc h_ih => exact ih hab (single hbc) h_ih (base hbc)

theorem trans_right (hab : ReflTransGen r a b) (hbc : TransGen r b c) : TransGen r a c := by
  induction hbc with
  | single hbc => exact tail' hab hbc
  | tail _ hcd hac => exact hac.tail hcd

instance : Trans (ReflTransGen r) (TransGen r) (TransGen r) :=
  ⟨trans_right⟩

theorem tail'_iff : TransGen r a c ↔ ∃ b, ReflTransGen r a b ∧ r b c := by
  refine ⟨fun h ↦ ?_, fun ⟨b, hab, hbc⟩ ↦ tail' hab hbc⟩
  cases h with
  | single hac => exact ⟨_, by rfl, hac⟩
  | tail hab hbc => exact ⟨_, hab.to_reflTransGen, hbc⟩

theorem head'_iff : TransGen r a c ↔ ∃ b, r a b ∧ ReflTransGen r b c := by
  refine ⟨fun h ↦ ?_, fun ⟨b, hab, hbc⟩ ↦ head' hab hbc⟩
  induction h with
  | single hac => exact ⟨_, hac, by rfl⟩
  | tail _ hbc IH =>
  rcases IH with ⟨d, had, hdb⟩
  exact ⟨_, had, hdb.tail hbc⟩

end TransGen


section reflGen

lemma reflGen_eq_self (hr : Reflexive r) : ReflGen r = r := by
  ext x y
  simpa only [reflGen_iff, or_iff_right_iff_imp] using fun h ↦ h ▸ hr y

lemma reflexive_reflGen : Reflexive (ReflGen r) := fun _ ↦ .refl

lemma reflGen_minimal {r' : α → α → Prop} (hr' : Reflexive r') (h : ∀ x y, r x y → r' x y) {x y : α}
    (hxy : ReflGen r x y) : r' x y := by
  simpa [reflGen_eq_self hr'] using ReflGen.mono h hxy

end reflGen

section TransGen

theorem transGen_eq_self (trans : Transitive r) : TransGen r = r :=
  funext fun a ↦ funext fun b ↦ propext <|
    ⟨fun h ↦ by
      induction h with
      | single hc => exact hc
      | tail _ hcd hac => exact trans hac hcd, TransGen.single⟩

theorem transitive_transGen : Transitive (TransGen r) := fun _ _ _ ↦ TransGen.trans

instance : IsTrans α (TransGen r) :=
  ⟨@TransGen.trans α r⟩

theorem transGen_idem : TransGen (TransGen r) = TransGen r :=
  transGen_eq_self transitive_transGen

theorem TransGen.lift {p : β → β → Prop} {a b : α} (f : α → β) (h : ∀ a b, r a b → p (f a) (f b))
    (hab : TransGen r a b) : TransGen p (f a) (f b) := by
  induction hab with
  | single hac => exact TransGen.single (h a _ hac)
  | tail _ hcd hac => exact TransGen.tail hac (h _ _ hcd)

theorem TransGen.lift' {p : β → β → Prop} {a b : α} (f : α → β)
    (h : ∀ a b, r a b → TransGen p (f a) (f b)) (hab : TransGen r a b) :
    TransGen p (f a) (f b) := by
simpa [transGen_idem] using hab.lift f h

theorem TransGen.closed {p : α → α → Prop} :
    (∀ a b, r a b → TransGen p a b) → TransGen r a b → TransGen p a b :=
  TransGen.lift' id

lemma TransGen.closed' {P : α → Prop} (dc : ∀ {a b}, r a b → P b → P a)
    {a b : α} (h : TransGen r a b) : P b → P a :=
  h.head_induction_on dc fun hr _ hi ↦ dc hr ∘ hi

theorem TransGen.mono {p : α → α → Prop} :
    (∀ a b, r a b → p a b) → TransGen r a b → TransGen p a b :=
  TransGen.lift id

lemma transGen_minimal {r' : α → α → Prop} (hr' : Transitive r') (h : ∀ x y, r x y → r' x y)
    {x y : α} (hxy : TransGen r x y) : r' x y := by
  simpa [transGen_eq_self hr'] using TransGen.mono h hxy

theorem TransGen.swap (h : TransGen r b a) : TransGen (swap r) a b := by
  induction h with
  | single h => exact TransGen.single h
  | tail _ hbc ih => exact ih.head hbc

theorem transGen_swap : TransGen (swap r) a b ↔ TransGen r b a :=
  ⟨TransGen.swap, TransGen.swap⟩

end TransGen

section ReflTransGen

open ReflTransGen

theorem reflTransGen_iff_eq (h : ∀ b, ¬r a b) : ReflTransGen r a b ↔ b = a := by
  rw [cases_head_iff]; simp [h, eq_comm]

theorem reflTransGen_iff_eq_or_transGen : ReflTransGen r a b ↔ b = a ∨ TransGen r a b := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · cases h with
    | refl => exact Or.inl rfl
    | tail hac hcb => exact Or.inr (TransGen.tail' hac hcb)
  · rcases h with (rfl | h)
    · rfl
    · exact h.to_reflTransGen

theorem ReflTransGen.lift {p : β → β → Prop} {a b : α} (f : α → β)
    (h : ∀ a b, r a b → p (f a) (f b)) (hab : ReflTransGen r a b) : ReflTransGen p (f a) (f b) :=
  ReflTransGen.trans_induction_on hab (fun _ ↦ refl) (ReflTransGen.single ∘ h _ _) fun _ _ ↦ trans

theorem ReflTransGen.mono {p : α → α → Prop} : (∀ a b, r a b → p a b) →
    ReflTransGen r a b → ReflTransGen p a b :=
  ReflTransGen.lift id

theorem reflTransGen_eq_self (refl : Reflexive r) (trans : Transitive r) : ReflTransGen r = r :=
  funext fun a ↦ funext fun b ↦ propext <|
    ⟨fun h ↦ by
      induction h with
      | refl => apply refl
      | tail _ h₂ IH => exact trans IH h₂, single⟩

lemma reflTransGen_minimal {r' : α → α → Prop} (hr₁ : Reflexive r') (hr₂ : Transitive r')
    (h : ∀ x y, r x y → r' x y) {x y : α} (hxy : ReflTransGen r x y) : r' x y := by
  simpa [reflTransGen_eq_self hr₁ hr₂] using ReflTransGen.mono h hxy

theorem reflexive_reflTransGen : Reflexive (ReflTransGen r) := fun _ ↦ refl

theorem transitive_reflTransGen : Transitive (ReflTransGen r) := fun _ _ _ ↦ trans

instance : IsRefl α (ReflTransGen r) :=
  ⟨@ReflTransGen.refl α r⟩

instance : IsTrans α (ReflTransGen r) :=
  ⟨@ReflTransGen.trans α r⟩

theorem reflTransGen_idem : ReflTransGen (ReflTransGen r) = ReflTransGen r :=
  reflTransGen_eq_self reflexive_reflTransGen transitive_reflTransGen

theorem ReflTransGen.lift' {p : β → β → Prop} {a b : α} (f : α → β)
    (h : ∀ a b, r a b → ReflTransGen p (f a) (f b))
    (hab : ReflTransGen r a b) : ReflTransGen p (f a) (f b) := by
  simpa [reflTransGen_idem] using hab.lift f h

theorem reflTransGen_closed {p : α → α → Prop} :
    (∀ a b, r a b → ReflTransGen p a b) → ReflTransGen r a b → ReflTransGen p a b :=
  ReflTransGen.lift' id

theorem ReflTransGen.swap (h : ReflTransGen r b a) : ReflTransGen (swap r) a b := by
  induction h with
  | refl => rfl
  | tail _ hbc ih => exact ih.head hbc

theorem reflTransGen_swap : ReflTransGen (swap r) a b ↔ ReflTransGen r b a :=
  ⟨ReflTransGen.swap, ReflTransGen.swap⟩

@[simp] lemma reflGen_transGen : ReflGen (TransGen r) = ReflTransGen r := by
  ext x y
  simp_rw [reflTransGen_iff_eq_or_transGen, reflGen_iff]

@[simp] lemma transGen_reflGen : TransGen (ReflGen r) = ReflTransGen r := by
  ext x y
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa [reflTransGen_idem]
      using TransGen.to_reflTransGen <| TransGen.mono (fun _ _ ↦ ReflGen.to_reflTransGen) h
  · obtain (rfl | h) := reflTransGen_iff_eq_or_transGen.mp h
    · exact .single .refl
    · exact TransGen.mono (fun _ _ ↦ .single) h

@[simp] lemma reflTransGen_reflGen : ReflTransGen (ReflGen r) = ReflTransGen r := by
  simp only [← transGen_reflGen, reflGen_eq_self reflexive_reflGen]

@[simp] lemma reflTransGen_transGen : ReflTransGen (TransGen r) = ReflTransGen r := by
  simp only [← reflGen_transGen, transGen_idem]

lemma reflTransGen_eq_transGen (hr : Reflexive r) :
    ReflTransGen r = TransGen r := by
  rw [← transGen_reflGen, reflGen_eq_self hr]

lemma reflTransGen_eq_reflGen (hr : Transitive r) :
    ReflTransGen r = ReflGen r := by
  rw [← reflGen_transGen, transGen_eq_self hr]

end ReflTransGen

namespace EqvGen

variable (r)

theorem is_equivalence : Equivalence (@EqvGen α r) :=
  Equivalence.mk EqvGen.refl (EqvGen.symm _ _) (EqvGen.trans _ _ _)

/-- `EqvGen.setoid r` is the setoid generated by a relation `r`.

The motivation for this definition is that `Quot r` behaves like `Quotient (EqvGen.setoid r)`,
see for example `Quot.eqvGen_exact` and `Quot.eqvGen_sound`. -/
def ProvablyEquivalent.setoid [System.Minimal 𝓢] : Setoid F where
  r := by sorry


theorem mono {r p : α → α → Prop} (hrp : ∀ a b, r a b → p a b) (h : EqvGen r a b) :
    EqvGen p a b := by
  induction h with
  | rel a b h => exact EqvGen.rel _ _ (hrp _ _ h)
  | refl => exact EqvGen.refl _
  | symm a b _ ih => exact EqvGen.symm _ _ ih
  | trans a b c _ _ hab hbc => exact EqvGen.trans _ _ _ hab hbc

@[deprecated (since := "2024-09-01")] alias _root_.EqvGen.is_equivalence := is_equivalence
@[deprecated (since := "2024-09-01")] alias _root_.EqvGen.Setoid := setoid
@[deprecated (since := "2024-09-01")] alias _root_.EqvGen.mono := mono

end EqvGen

/-- The join of a relation on a single type is a new relation for which
pairs of terms are related if there is a third term they are both
related to.  For example, if `r` is a relation representing rewrites
in a term rewriting system, then *confluence* is the property that if
`a` rewrites to both `b` and `c`, then `join r` relates `b` and `c`
(see `Relation.church_rosser`).
-/
def Join (r : α → α → Prop) : α → α → Prop := fun a b ↦ ∃ c, r a c ∧ r b c

section Join

open ReflTransGen ReflGen

/-- A sufficient condition for the Church-Rosser property. -/
theorem church_rosser (h : ∀ a b c, r a b → r a c → ∃ d, ReflGen r b d ∧ ReflTransGen r c d)
    (hab : ReflTransGen r a b) (hac : ReflTransGen r a c) : Join (ReflTransGen r) b c := by
  induction hab with
  | refl => exact ⟨c, hac, refl⟩
  | @tail d e _ hde ih =>
    rcases ih with ⟨b, hdb, hcb⟩
    have : ∃ a, ReflTransGen r e a ∧ ReflGen r b a := by
      clear hcb
      induction hdb with
      | refl => exact ⟨e, refl, ReflGen.single hde⟩
      | @tail f b _ hfb ih =>
        rcases ih with ⟨a, hea, hfa⟩
        cases hfa with
        | refl => exact ⟨b, hea.tail hfb, ReflGen.refl⟩
        | single hfa =>
          rcases h _ _ _ hfb hfa with ⟨c, hbc, hac⟩
          exact ⟨c, hea.trans hac, hbc⟩
    rcases this with ⟨a, hea, hba⟩
    cases hba with
    | refl => exact ⟨b, hea, hcb⟩
    | single hba => exact ⟨a, hea, hcb.tail hba⟩


theorem join_of_single (h : Reflexive r) (hab : r a b) : Join r a b :=
  ⟨b, hab, h b⟩

theorem symmetric_join : Symmetric (Join r) := fun _ _ ⟨c, hac, hcb⟩ ↦ ⟨c, hcb, hac⟩

theorem reflexive_join (h : Reflexive r) : Reflexive (Join r) := fun a ↦ ⟨a, h a, h a⟩

theorem transitive_join (ht : Transitive r) (h : ∀ a b c, r a b → r a c → Join r b c) :
    Transitive (Join r) :=
  fun _ b _ ⟨x, hax, hbx⟩ ⟨y, hby, hcy⟩ ↦
  let ⟨z, hxz, hyz⟩ := h b x y hbx hby
  ⟨z, ht hax hxz, ht hcy hyz⟩

theorem equivalence_join (hr : Reflexive r) (ht : Transitive r)
    (h : ∀ a b c, r a b → r a c → Join r b c) : Equivalence (Join r) :=
  ⟨reflexive_join hr, @symmetric_join _ _, @transitive_join _ _ ht h⟩

theorem equivalence_join_reflTransGen
    (h : ∀ a b c, r a b → r a c → ∃ d, ReflGen r b d ∧ ReflTransGen r c d) :
    Equivalence (Join (ReflTransGen r)) :=
  equivalence_join reflexive_reflTransGen transitive_reflTransGen fun _ _ _ ↦ church_rosser h

theorem join_of_equivalence {r' : α → α → Prop} (hr : Equivalence r) (h : ∀ a b, r' a b → r a b) :
    Join r' a b → r a b
  | ⟨_, hac, hbc⟩ => hr.trans (h _ _ hac) (hr.symm <| h _ _ hbc)

theorem reflTransGen_of_transitive_reflexive {r' : α → α → Prop} (hr : Reflexive r)
    (ht : Transitive r) (h : ∀ a b, r' a b → r a b) (h' : ReflTransGen r' a b) : r a b := by
  induction h' with
  | refl => exact hr _
  | tail _ hbc ih => exact ht ih (h _ _ hbc)

theorem reflTransGen_of_equivalence {r' : α → α → Prop} (hr : Equivalence r) :
    (∀ a b, r' a b → r a b) → ReflTransGen r' a b → r a b :=
  reflTransGen_of_transitive_reflexive hr.1 (fun _ _ _ ↦ hr.trans)

end Join

end Relation

section EqvGen

open Relation

variable {r : α → α → Prop} {a b : α}

theorem Quot.eqvGen_exact (H : Quot.mk r a = Quot.mk r b) : EqvGen r a b :=
  @Quotient.exact _ (EqvGen.setoid r) a b (congrArg
    (Quot.lift (Quotient.mk (EqvGen.setoid r)) (fun x y h ↦ Quot.sound (EqvGen.rel x y h))) H)

theorem Quot.eqvGen_sound (H : EqvGen r a b) : Quot.mk r a = Quot.mk r b :=
  EqvGen.rec
    (fun _ _ h ↦ Quot.sound h)
    (fun _ ↦ rfl)
    (fun _ _ _ IH ↦ Eq.symm IH)
    (fun _ _ _ _ _ IH₁ IH₂ ↦ Eq.trans IH₁ IH₂)
    H

theorem Equivalence.eqvGen_iff (h : Equivalence r) : EqvGen r a b ↔ r a b :=
  Iff.intro
    (by
      intro h
      induction h with
      | rel => assumption
      | refl => exact h.1 _
      | symm => apply h.symm; assumption
      | trans _ _ _ _ _ hab hbc => exact h.trans hab hbc)
    (EqvGen.rel a b)

theorem Equivalence.eqvGen_eq (h : Equivalence r) : EqvGen r = r :=
  funext fun _ ↦ funext fun _ ↦ propext <| h.eqvGen_iff

@[deprecated (since := "2024-08-29")] alias Quot.exact := Quot.eqvGen_exact
@[deprecated (since := "2024-08-29")] alias Quot.EqvGen_sound := Quot.eqvGen_sound

end EqvGen
