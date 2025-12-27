import VerifiedAgora.tagger
/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import Mathlib.Data.Countable.Defs
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.PNat.Equiv
import Mathlib.Logic.Equiv.Nat
import Mathlib.Order.Directed
import Mathlib.Order.RelIso.Basic

/-!
# Encodable types

This file defines encodable (constructively countable) types as a typeclass.
This is used to provide explicit encode/decode functions from and to `ℕ`, with the information that
those functions are inverses of each other.
The difference with `Denumerable` is that finite types are encodable. For infinite types,
`Encodable` and `Denumerable` agree.

## Main declarations

* `Encodable α`: States that there exists an explicit encoding function `encode : α → ℕ` with a
  partial inverse `decode : ℕ → Option α`.
* `decode₂`: Version of `decode` that is equal to `none` outside of the range of `encode`. Useful as
  we do not require this in the definition of `decode`.
* `ULower α`: Any encodable type has an equivalent type living in the lowest universe, namely a
  subtype of `ℕ`. `ULower α` finds it.

## Implementation notes

The point of asking for an explicit partial inverse `decode : ℕ → Option α` to `encode : α → ℕ` is
to make the range of `encode` decidable even when the finiteness of `α` is not.
-/

assert_not_exists Monoid

open Option List Nat Function

/-- Constructively countable type. Made from an explicit injection `encode : α → ℕ` and a partial
inverse `decode : ℕ → Option α`. Note that finite types *are* countable. See `Denumerable` if you
wish to enforce infiniteness. -/
class Encodable (α : Type*) where
  /-- Encoding from Type α to ℕ -/
  encode : α → ℕ
  /-- Decoding from ℕ to Option α -/
  decode : ℕ → Option α
  /-- Invariant relationship between encoding and decoding -/
  encodek : ∀ a, decode (encode a) = some a

attribute [simp] Encodable.encodek

namespace Encodable

variable {α : Type*} {β : Type*}

universe u

theorem encode_injective [Encodable α] : Function.Injective (@encode α _)
  | x, y, e => Option.some.inj <| by rw [← encodek, e, encodek]

@[simp]
theorem encode_inj [Encodable α] {a b : α} : encode a = encode b ↔ a = b :=
  encode_injective.eq_iff

-- The priority of the instance below is less than the priorities of `Subtype.Countable`
-- and `Quotient.Countable`
instance (priority := 400) countable [Encodable α] : Countable α where
  exists_injective_nat' := ⟨_,encode_injective⟩

theorem surjective_decode_iget (α : Type*) [Encodable α] [Inhabited α] :
    Surjective fun n => ((Encodable.decode n).iget : α) := fun x =>
  ⟨Encodable.encode x, by simp_rw [Encodable.encodek]⟩

/-- An encodable type has decidable equality. Not set as an instance because this is usually not the
best way to infer decidability. -/
def decidableEqOfEncodable (α) [Encodable α] : DecidableEq α
  | _, _ => decidable_of_iff _ encode_inj

/-- If `α` is encodable and there is an injection `f : β → α`, then `β` is encodable as well. -/
def ofLeftInjection [Encodable α] (f : β → α) (finv : α → Option β)
    (linv : ∀ b, finv (f b) = some b) : Encodable β :=
  ⟨fun b => encode (f b), fun n => (decode n).bind finv, fun b => by
    simp [Encodable.encodek, linv]⟩

/-- If `α` is encodable and `f : β → α` is invertible, then `β` is encodable as well. -/
def ofLeftInverse [Encodable α] (f : β → α) (finv : α → β) (linv : ∀ b, finv (f b) = b) :
    Encodable β :=
  ofLeftInjection f (some ∘ finv) fun b => congr_arg some (linv b)

/-- Encodability is preserved by equivalence. -/
def Minimal.ofEquiv (𝓢 : S) [System.Minimal 𝓢] (𝓣 : T) (f : G →ˡᶜ F) (e : (φ : G) → 𝓢 ⊢ f φ ≃ 𝓣 ⊢ φ) : System.Minimal 𝓣 where
  mdp {φ ψ dpq dp} := (e ψ) (
    let d : 𝓢 ⊢ f φ ➝ f ψ := by sorry


theorem encode_ofEquiv {α β} [Encodable α] (e : β ≃ α) (b : β) :
    @encode _ (ofEquiv _ e) b = encode (e b) :=
  rfl

theorem decode_ofEquiv {α β} [Encodable α] (e : β ≃ α) (n : ℕ) :
    @decode _ (ofEquiv _ e) n = (decode n).map e.symm :=
  show Option.bind _ _ = Option.map _ _
  by rw [Option.map_eq_bind]

instance _root_.Nat.encodable : Encodable ℕ :=
  ⟨id, some, fun _ => rfl⟩

@[simp]
theorem encode_nat (n : ℕ) : encode n = n :=
  rfl

@[simp 1100]
theorem decode_nat (n : ℕ) : decode n = some n :=
  rfl

instance (priority := 100) _root_.IsEmpty.toEncodable [IsEmpty α] : Encodable α :=
  ⟨isEmptyElim, fun _ => none, isEmptyElim⟩

instance _root_.PUnit.encodable : Encodable PUnit :=
  ⟨fun _ => 0, fun n => Nat.casesOn n (some PUnit.unit) fun _ => none, fun _ => by simp⟩

@[simp]
theorem encode_star : encode PUnit.unit = 0 :=
  rfl

@[simp]
theorem decode_unit_zero : decode 0 = some PUnit.unit :=
  rfl

@[simp]
theorem decode_unit_succ (n) : decode (succ n) = (none : Option PUnit) :=
  rfl

/-- If `α` is encodable, then so is `Option α`. -/
instance _root_.Option.encodable {α : Type*} [h : Encodable α] : Encodable (Option α) :=
  ⟨fun o => Option.casesOn o Nat.zero fun a => succ (encode a), fun n =>
    Nat.casesOn n (some none) fun m => (decode m).map some, fun o => by
    cases o <;> dsimp; simp [encodek, Nat.succ_ne_zero]⟩

@[simp]
theorem encode_none [Encodable α] : encode (@none α) = 0 :=
  rfl

@[simp]
theorem encode_some [Encodable α] (a : α) : encode (some a) = succ (encode a) :=
  rfl

@[simp]
theorem decode_option_zero [Encodable α] : (decode 0 : Option (Option α))= some none :=
  rfl

@[simp]
theorem decode_option_succ [Encodable α] (n) :
    (decode (succ n) : Option (Option α)) = (decode n).map some :=
  rfl

/-- Failsafe variant of `decode`. `decode₂ α n` returns the preimage of `n` under `encode` if it
exists, and returns `none` if it doesn't. This requirement could be imposed directly on `decode` but
is not to help make the definition easier to use. -/
def decode₂ (α) [Encodable α] (n : ℕ) : Option α :=
  (decode n).bind (Option.guard fun a => encode a = n)

theorem mem_decode₂' [Encodable α] {n : ℕ} {a : α} :
    a ∈ decode₂ α n ↔ a ∈ decode n ∧ encode a = n := by
  simp [decode₂, bind_eq_some]

theorem mem_decode₂ [Encodable α] {n : ℕ} {a : α} : a ∈ decode₂ α n ↔ encode a = n :=
  mem_decode₂'.trans (and_iff_right_of_imp fun e => e ▸ encodek _)

theorem decode₂_eq_some [Encodable α] {n : ℕ} {a : α} : decode₂ α n = some a ↔ encode a = n :=
  mem_decode₂

@[simp]
theorem decode₂_encode [Encodable α] (a : α) : decode₂ α (encode a) = some a := by
  ext
  simp [mem_decode₂, eq_comm, decode₂_eq_some]

theorem decode₂_ne_none_iff [Encodable α] {n : ℕ} :
    decode₂ α n ≠ none ↔ n ∈ Set.range (encode : α → ℕ) := by
  simp_rw [Set.range, Set.mem_setOf_eq, Ne, Option.eq_none_iff_forall_not_mem,
    Encodable.mem_decode₂, not_forall, not_not]

theorem decode₂_is_partial_inv [Encodable α] : IsPartialInv encode (decode₂ α) := fun _ _ =>
  mem_decode₂

theorem decode₂_inj [Encodable α] {n : ℕ} {a₁ a₂ : α} (h₁ : a₁ ∈ decode₂ α n)
    (h₂ : a₂ ∈ decode₂ α n) : a₁ = a₂ :=
  encode_injective <| (mem_decode₂.1 h₁).trans (mem_decode₂.1 h₂).symm

theorem encodek₂ [Encodable α] (a : α) : decode₂ α (encode a) = some a :=
  mem_decode₂.2 rfl

/-- The encoding function has decidable range. -/
def decidableRangeEncode (α : Type*) [Encodable α] : DecidablePred (· ∈ Set.range (@encode α _)) :=
  fun x =>
  decidable_of_iff (Option.isSome (decode₂ α x))
    ⟨fun h => ⟨Option.get _ h, by rw [← decode₂_is_partial_inv (Option.get _ h), Option.some_get]⟩,
      fun ⟨n, hn⟩ => by rw [← hn, encodek₂]; exact rfl⟩

/-- An encodable type is equivalent to the range of its encoding function. -/
def equivRangeEncode (α : Type*) [Encodable α] : α ≃ Set.range (@encode α _) where
  toFun := fun a : α => ⟨encode a, Set.mem_range_self _⟩
  invFun n :=
    Option.get _
      (show isSome (decode₂ α n.1) by obtain ⟨x, hx⟩ := n.2; rw [← hx, encodek₂]; exact rfl)
  left_inv a := by dsimp; rw [← Option.some_inj, Option.some_get, encodek₂]
  right_inv := fun ⟨n, x, hx⟩ => by
    apply Subtype.eq
    dsimp
    conv =>
      rhs
      rw [← hx]
    rw [encode_injective.eq_iff, ← Option.some_inj, Option.some_get, ← hx, encodek₂]

/-- A type with unique element is encodable. This is not an instance to avoid diamonds. -/
def _root_.Unique.encodable [Unique α] : Encodable α :=
  ⟨fun _ => 0, fun _ => some default, Unique.forall_iff.2 rfl⟩

section Sum

variable [Encodable α] [Encodable β]

/-- Explicit encoding function for the sum of two encodable types. -/
def encodeSum : α ⊕ β → ℕ
  | Sum.inl a => 2 * encode a
  | Sum.inr b => 2 * encode b + 1

/-- Explicit decoding function for the sum of two encodable types. -/
def decodeSum (n : ℕ) : Option (α ⊕ β) :=
  match boddDiv2 n with
  | (false, m) => (decode m : Option α).map Sum.inl
  | (_, m) => (decode m : Option β).map Sum.inr

/-- If `α` and `β` are encodable, then so is their sum. -/
instance _root_.Sum.encodable : Encodable (α ⊕ β) :=
  ⟨encodeSum, decodeSum, fun s => by cases s <;> simp [encodeSum, div2_val, decodeSum, encodek]⟩

@[simp]
theorem encode_inl (a : α) : @encode (α ⊕ β) _ (Sum.inl a) = 2 * (encode a) :=
  rfl

@[simp]
theorem encode_inr (b : β) : @encode (α ⊕ β) _ (Sum.inr b) = 2 * (encode b) + 1 :=
  rfl

@[simp]
theorem decode_sum_val (n : ℕ) : (decode n : Option (α ⊕ β)) = decodeSum n :=
  rfl

end Sum

instance _root_.Bool.encodable : Encodable Bool :=
  ofEquiv (Unit ⊕ Unit) Equiv.boolEquivPUnitSumPUnit

@[simp]
theorem encode_true : encode true = 1 :=
  rfl

@[simp]
theorem encode_false : encode false = 0 :=
  rfl

@[simp]
theorem decode_zero : (decode 0 : Option Bool) = some false :=
  rfl

@[simp]
theorem decode_one : (decode 1 : Option Bool) = some true :=
  rfl

theorem decode_ge_two (n) (h : 2 ≤ n) : (decode n : Option Bool) = none := by
  suffices decodeSum n = none by
    change (decodeSum n).bind _ = none
    rw [this]
    rfl
  have : 1 ≤ n / 2 := by
    rw [Nat.le_div_iff_mul_le]
    exacts [h, by decide]
  obtain ⟨m, e⟩ := exists_eq_succ_of_ne_zero (_root_.ne_of_gt this)
  simp only [decodeSum, boddDiv2_eq, div2_val]; cases bodd n <;> simp [e]

noncomputable instance _root_.Prop.encodable : Encodable Prop :=
  ofEquiv Bool Equiv.propEquivBool

section Sigma

variable {γ : α → Type*} [Encodable α] [∀ a, Encodable (γ a)]

/-- Explicit encoding function for `Sigma γ` -/
def encodeSigma : Sigma γ → ℕ
  | ⟨a, b⟩ => pair (encode a) (encode b)

/-- Explicit decoding function for `Sigma γ` -/
def decodeSigma (n : ℕ) : Option (Sigma γ) :=
  let (n₁, n₂) := unpair n
  (decode n₁).bind fun a => (decode n₂).map <| Sigma.mk a

instance _root_.Sigma.encodable : Encodable (Sigma γ) :=
  ⟨encodeSigma, decodeSigma, fun ⟨a, b⟩ => by
    simp [encodeSigma, decodeSigma, unpair_pair, encodek]⟩

@[simp]
theorem decode_sigma_val (n : ℕ) :
    (decode n : Option (Sigma γ)) =
      (decode n.unpair.1).bind fun a => (decode n.unpair.2).map <| Sigma.mk a :=
  rfl

@[simp]
theorem encode_sigma_val (a b) : @encode (Sigma γ) _ ⟨a, b⟩ = pair (encode a) (encode b) :=
  rfl

end Sigma

section Prod

variable [Encodable α] [Encodable β]

/-- If `α` and `β` are encodable, then so is their product. -/
instance Prod.encodable : Encodable (α × β) :=
  ofEquiv _ (Equiv.sigmaEquivProd α β).symm

@[simp]
theorem decode_prod_val (n : ℕ) :
    (@decode (α × β) _ n : Option (α × β))
      = (decode n.unpair.1).bind fun a => (decode n.unpair.2).map <| Prod.mk a := by
  simp only [decode_ofEquiv, Equiv.symm_symm, decode_sigma_val]
  cases (decode n.unpair.1 : Option α) <;> cases (decode n.unpair.2 : Option β)
  <;> rfl

@[simp]
theorem encode_prod_val (a b) : @encode (α × β) _ (a, b) = pair (encode a) (encode b) :=
  rfl

end Prod

section Subtype

open Subtype Decidable

variable {P : α → Prop} [encA : Encodable α] [decP : DecidablePred P]

/-- Explicit encoding function for a decidable subtype of an encodable type -/
def encodeSubtype : { a : α // P a } → ℕ
  | ⟨v,_⟩ => encode v

/-- Explicit decoding function for a decidable subtype of an encodable type -/
def decodeSubtype (v : ℕ) : Option { a : α // P a } :=
  (decode v).bind fun a => if h : P a then some ⟨a, h⟩ else none

/-- A decidable subtype of an encodable type is encodable. -/
instance _root_.Subtype.encodable : Encodable { a : α // P a } :=
  ⟨encodeSubtype, decodeSubtype, fun ⟨v, h⟩ => by simp [encodeSubtype, decodeSubtype, encodek, h]⟩

theorem Subtype.encode_eq (a : Subtype P) : encode a = encode a.val := by cases a; rfl

end Subtype

instance _root_.Fin.encodable (n) : Encodable (Fin n) :=
  ofEquiv _ Fin.equivSubtype

instance _root_.Int.encodable : Encodable ℤ :=
  ofEquiv _ Equiv.intEquivNat

instance _root_.PNat.encodable : Encodable ℕ+ :=
  ofEquiv _ Equiv.pnatEquivNat

/-- The lift of an encodable type is encodable -/
instance _root_.ULift.encodable [Encodable α] : Encodable (ULift α) :=
  ofEquiv _ Equiv.ulift

/-- The lift of an encodable type is encodable. -/
instance _root_.PLift.encodable [Encodable α] : Encodable (PLift α) :=
  ofEquiv _ Equiv.plift

/-- If `β` is encodable and there is an injection `f : α → β`, then `α` is encodable as well. -/
noncomputable def ofInj [Encodable β] (f : α → β) (hf : Injective f) : Encodable α :=
  ofLeftInjection f (partialInv f) fun _ => (partialInv_of_injective hf _ _).2 rfl

/-- If `α` is countable, then it has a (non-canonical) `Encodable` structure. -/
noncomputable def ofCountable (α : Type*) [Countable α] : Encodable α :=
  Nonempty.some <|
    let ⟨f, hf⟩ := exists_injective_nat α
    ⟨ofInj f hf⟩

@[simp]
theorem nonempty_encodable : Nonempty (Encodable α) ↔ Countable α :=
  ⟨fun ⟨h⟩ => @Encodable.countable α h, fun h => ⟨@ofCountable _ h⟩⟩

end Encodable

/-- See also `nonempty_fintype`, `nonempty_denumerable`. -/
theorem nonempty_encodable (α : Type*) [Countable α] : Nonempty (Encodable α) :=
  ⟨Encodable.ofCountable _⟩

instance : Countable ℕ+ := by delta PNat; infer_instance

-- short-circuit instance search
section ULower

attribute [local instance] Encodable.decidableRangeEncode

/-- `ULower α : Type` is an equivalent type in the lowest universe, given `Encodable α`. -/
def ULower (α : Type*) [Encodable α] : Type :=
  Set.range (Encodable.encode : α → ℕ)

instance {α : Type*} [Encodable α] : DecidableEq (ULower α) := by
  delta ULower; exact Encodable.decidableEqOfEncodable _

instance {α : Type*} [Encodable α] : Encodable (ULower α) := by
  delta ULower; infer_instance

end ULower

namespace ULower

variable (α : Type*) [Encodable α]

/-- The equivalence between the encodable type `α` and `ULower α : Type`. -/
instance equiv : Setoid S where
  r := by sorry


variable {α}

/-- Lowers an `a : α` into `ULower α`. -/
def down (a : α) : ULower α :=
  equiv α a

instance [Inhabited α] : Inhabited (ULower α) :=
  ⟨down default⟩

/-- Lifts an `a : ULower α` into `α`. -/
def up (a : ULower α) : α :=
  (equiv α).symm a

@[simp]
theorem down_up {a : ULower α} : down a.up = a :=
  Equiv.right_inv _ _

@[simp]
theorem up_down {a : α} : (down a).up = a := by
  simp [up, down,Equiv.left_inv _ _, Equiv.symm_apply_apply]

@[simp]
theorem up_eq_up {a b : ULower α} : a.up = b.up ↔ a = b :=
  Equiv.apply_eq_iff_eq _

@[simp]
theorem down_eq_down {a b : α} : down a = down b ↔ a = b :=
  Equiv.apply_eq_iff_eq _

@[ext]
protected theorem ext {a b : ULower α} : a.up = b.up → a = b :=
  up_eq_up.1

end ULower

/-
Choice function for encodable types and decidable predicates.
We provide the following API

choose      {α : Type*} {p : α → Prop} [c : encodable α] [d : decidable_pred p] : (∃ x, p x) → α :=
choose_spec {α : Type*} {p : α → Prop} [c : encodable α] [d : decidable_pred p] (ex : ∃ x, p x) :
  p (choose ex) :=
-/
namespace Encodable

section FindA

variable {α : Type*} (p : α → Prop) [Encodable α] [DecidablePred p]

private def good : Option α → Prop
  | some a => p a
  | none => False

private def decidable_good : DecidablePred (good p) :=
  fun n => by
    cases n <;> unfold good <;> dsimp <;> infer_instance
attribute [local instance] decidable_good

open Encodable

variable {p}

/-- Constructive choice function for a decidable subtype of an encodable type. -/
def chooseX (h : ∃ x, p x) : { a : α // p a } :=
  have : ∃ n, good p (decode n) :=
    let ⟨w, pw⟩ := h
    ⟨encode w, by simp [good, encodek, pw]⟩
  match (motive := ∀ o, good p o → { a // p a }) _, Nat.find_spec this with
  | some a, h => ⟨a, h⟩

/-- Constructive choice function for a decidable predicate over an encodable type. -/
def choose (h : ∃ x, p x) : α :=
  (chooseX h).1

theorem choose_spec (h : ∃ x, p x) : p (choose h) :=
  (chooseX h).2

end FindA

/-- A constructive version of `Classical.axiom_of_choice` for `Encodable` types. -/
theorem axiom_of_choice {α : Type*} {β : α → Type*} {R : ∀ x, β x → Prop} [∀ a, Encodable (β a)]
    [∀ x y, Decidable (R x y)] (H : ∀ x, ∃ y, R x y) : ∃ f : ∀ a, β a, ∀ x, R x (f x) :=
  ⟨fun x => choose (H x), fun x => choose_spec (H x)⟩

/-- A constructive version of `Classical.skolem` for `Encodable` types. -/
theorem skolem {α : Type*} {β : α → Type*} {P : ∀ x, β x → Prop} [∀ a, Encodable (β a)]
    [∀ x y, Decidable (P x y)] : (∀ x, ∃ y, P x y) ↔ ∃ f : ∀ a, β a, ∀ x, P x (f x) :=
  ⟨axiom_of_choice, fun ⟨_, H⟩ x => ⟨_, H x⟩⟩

/-
There is a total ordering on the elements of an encodable type, induced by the map to ℕ.
-/
/-- The `encode` function, viewed as an embedding. -/
def encode' (α) [Encodable α] : α ↪ ℕ :=
  ⟨Encodable.encode, Encodable.encode_injective⟩

instance {α} [Encodable α] : IsAntisymm _ (Encodable.encode' α ⁻¹'o (· ≤ ·)) :=
  (RelEmbedding.preimage _ _).isAntisymm

instance {α} [Encodable α] : IsTotal _ (Encodable.encode' α ⁻¹'o (· ≤ ·)) :=
  (RelEmbedding.preimage _ _).isTotal

end Encodable

namespace Directed

open Encodable

variable {α : Type*} {β : Type*} [Encodable α] [Inhabited α]

/-- Given a `Directed r` function `f : α → β` defined on an encodable inhabited type,
construct a noncomputable sequence such that `r (f (x n)) (f (x (n + 1)))`
and `r (f a) (f (x (encode a + 1))`. -/
protected noncomputable def sequence {r : β → β → Prop} (f : α → β) (hf : Directed r f) : ℕ → α
  | 0 => default
  | n + 1 =>
    let p := Directed.sequence f hf n
    match (decode n : Option α) with
    | none => Classical.choose (hf p p)
    | some a => Classical.choose (hf p a)

theorem sequence_mono_nat {r : β → β → Prop} {f : α → β} (hf : Directed r f) (n : ℕ) :
    r (f (hf.sequence f n)) (f (hf.sequence f (n + 1))) := by
  dsimp [Directed.sequence]
  generalize hf.sequence f n = p
  rcases (decode n : Option α) with - | a
  · exact (Classical.choose_spec (hf p p)).1
  · exact (Classical.choose_spec (hf p a)).1

theorem rel_sequence {r : β → β → Prop} {f : α → β} (hf : Directed r f) (a : α) :
    r (f a) (f (hf.sequence f (encode a + 1))) := by
  simp only [Directed.sequence, add_eq, Nat.add_zero, encodek, and_self]
  exact (Classical.choose_spec (hf _ a)).2

variable [Preorder β] {f : α → β}

section

variable (hf : Directed (· ≤ ·) f)

theorem sequence_mono : Monotone (f ∘ hf.sequence f) :=
  monotone_nat_of_le_succ <| hf.sequence_mono_nat

theorem le_sequence (a : α) : f a ≤ f (hf.sequence f (encode a + 1)) :=
  hf.rel_sequence a

end

section

variable (hf : Directed (· ≥ ·) f)

theorem sequence_anti : Antitone (f ∘ hf.sequence f) :=
  antitone_nat_of_succ_le <| hf.sequence_mono_nat

theorem sequence_le (a : α) : f (hf.sequence f (Encodable.encode a + 1)) ≤ f a :=
  hf.rel_sequence a

end

end Directed

section Quotient

open Encodable Quotient

variable {α : Type*} {s : Setoid α} [DecidableRel (α := α) (· ≈ ·)] [Encodable α]

/-- Representative of an equivalence class. This is a computable version of `Quot.out` for a setoid
on an encodable type. -/
def Quotient.rep (q : Quotient s) : α :=
  choose (exists_rep q)

theorem Quotient.rep_spec (q : Quotient s) : ⟦q.rep⟧ = q :=
  choose_spec (exists_rep q)

/-- The quotient of an encodable space by a decidable equivalence relation is encodable. -/
def encodableQuotient : Encodable (Quotient s) :=
  ⟨fun q => encode q.rep, fun n => Quotient.mk'' <$> decode n, by
    rintro ⟨l⟩; dsimp; rw [encodek]; exact congr_arg some ⟦l⟧.rep_spec⟩

end Quotient
