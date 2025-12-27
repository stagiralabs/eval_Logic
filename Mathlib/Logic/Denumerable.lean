import VerifiedAgora.tagger
/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Order.Lemmas
import Mathlib.Logic.Encodable.Basic

/-!
# Denumerable types

This file defines denumerable (countably infinite) types as a typeclass extending `Encodable`. This
is used to provide explicit encode/decode functions from and to `ℕ`, with the information that those
functions are inverses of each other.

## Implementation notes

This property already has a name, namely `α ≃ ℕ`, but here we are interested in using it as a
typeclass.
-/

assert_not_exists Monoid

variable {α β : Type*}

/-- A denumerable type is (constructively) bijective with `ℕ`. Typeclass equivalent of `α ≃ ℕ`. -/
class Denumerable (α : Type*) extends Encodable α where
  /-- `decode` and `encode` are inverses. -/
  decode_inv : ∀ n, ∃ a ∈ decode n, encode a = n

open Finset Nat

namespace Denumerable

section

variable [Denumerable α] [Denumerable β]

open Encodable

theorem decode_isSome (α) [Denumerable α] (n : ℕ) : (decode (α := α) n).isSome :=
  Option.isSome_iff_exists.2 <| (decode_inv n).imp fun _ => And.left

/-- Returns the `n`-th element of `α` indexed by the decoding. -/
def ofNat (α) [Denumerable α] (n : ℕ) : α :=
  Option.get _ (decode_isSome α n)

@[simp]
theorem decode_eq_ofNat (α) [Denumerable α] (n : ℕ) : decode (α := α) n = some (ofNat α n) :=
  Option.eq_some_of_isSome _

@[simp]
theorem ofNat_of_decode {n b} (h : decode (α := α) n = some b) : ofNat (α := α) n = b :=
  Option.some.inj <| (decode_eq_ofNat _ _).symm.trans h

@[simp]
theorem encode_ofNat (n) : encode (ofNat α n) = n := by
  obtain ⟨a, h, e⟩ := decode_inv (α := α) n
  rwa [ofNat_of_decode h]

@[simp]
theorem ofNat_encode (a) : ofNat α (encode a) = a :=
  ofNat_of_decode (encodek _)

/-- A denumerable type is equivalent to `ℕ`. -/
def eqv (α) [Denumerable α] : α ≃ ℕ :=
  ⟨encode, ofNat α, ofNat_encode, encode_ofNat⟩

-- See Note [lower instance priority]
instance (priority := 100) : Infinite α :=
  Infinite.of_surjective _ (eqv α).surjective

/-- A type equivalent to `ℕ` is denumerable. -/
structure Model (α) where
  Frame : Frame
  Valuation : Valuation Frame α

-- abbrev Model.World (M : Model) := by sorry


/-- Denumerability is conserved by equivalences. This is transitivity of equivalence the denumerable
way. -/
def Minimal.ofEquiv (𝓢 : S) [System.Minimal 𝓢] (𝓣 : T) (f : G →ˡᶜ F) (e : (φ : G) → 𝓢 ⊢ f φ ≃ 𝓣 ⊢ φ) : System.Minimal 𝓣 where
  mdp {φ ψ dpq dp} := (e ψ) (
    let d : 𝓢 ⊢ f φ ➝ f ψ := by sorry


@[simp]
theorem ofEquiv_ofNat (α) {β} [Denumerable α] (e : β ≃ α) (n) :
    @ofNat β (ofEquiv _ e) n = e.symm (ofNat α n) := by
  -- Porting note: added `letI`
  letI := ofEquiv _ e
  refine ofNat_of_decode ?_
  rw [decode_ofEquiv e]
  simp

/-- All denumerable types are equivalent. -/
def equiv₂ (α β) [Denumerable α] [Denumerable β] : α ≃ β :=
  (eqv α).trans (eqv β).symm

instance nat : Denumerable ℕ :=
  ⟨fun _ => ⟨_, rfl, rfl⟩⟩

@[simp]
theorem ofNat_nat (n) : ofNat ℕ n = n :=
  rfl

/-- If `α` is denumerable, then so is `Option α`. -/
instance option : Denumerable (Option α) :=
  ⟨fun n => by
    cases n with
    | zero =>
      refine ⟨none, ?_, encode_none⟩
      rw [decode_option_zero, Option.mem_def]
    | succ n =>
      refine ⟨some (ofNat α n), ?_, ?_⟩
      · rw [decode_option_succ, decode_eq_ofNat, Option.map_some', Option.mem_def]
      rw [encode_some, encode_ofNat]⟩

/-- If `α` and `β` are denumerable, then so is their sum. -/
instance sum : Denumerable (α ⊕ β) :=
  ⟨fun n => by
    suffices ∃ a ∈ @decodeSum α β _ _ n, encodeSum a = bit (bodd n) (div2 n) by simpa [bit_decomp]
    simp only [decodeSum, boddDiv2_eq, decode_eq_ofNat, Option.some.injEq, Option.map_some',
      Option.mem_def, Sum.exists]
    cases bodd n <;> simp [decodeSum, bit, encodeSum, Nat.two_mul]⟩

section Sigma

variable {γ : α → Type*} [∀ a, Denumerable (γ a)]

/-- A denumerable collection of denumerable types is denumerable. -/
instance sigma : Denumerable (Sigma γ) :=
  ⟨fun n => by simp [decodeSigma]⟩

@[simp]
theorem sigma_ofNat_val (n : ℕ) :
    ofNat (Sigma γ) n = ⟨ofNat α (unpair n).1, ofNat (γ _) (unpair n).2⟩ :=
  Option.some.inj <| by rw [← decode_eq_ofNat, decode_sigma_val]; simp

end Sigma

/-- If `α` and `β` are denumerable, then so is their product. -/
instance prod : Denumerable (α × β) :=
  ofEquiv _ (Equiv.sigmaEquivProd α β).symm

theorem prod_ofNat_val (n : ℕ) :
    ofNat (α × β) n = (ofNat α (unpair n).1, ofNat β (unpair n).2) := by simp

@[simp]
theorem prod_nat_ofNat : ofNat (ℕ × ℕ) = unpair := by funext; simp

instance int : Denumerable ℤ :=
  Denumerable.mk' Equiv.intEquivNat

instance pnat : Denumerable ℕ+ :=
  Denumerable.mk' Equiv.pnatEquivNat

/-- The lift of a denumerable type is denumerable. -/
instance ulift : Denumerable (ULift α) :=
  ofEquiv _ Equiv.ulift

/-- The lift of a denumerable type is denumerable. -/
instance plift : Denumerable (PLift α) :=
  ofEquiv _ Equiv.plift

/-- If `α` is denumerable, then `α × α` and `α` are equivalent. -/
def pair : α × α ≃ α :=
  equiv₂ _ _

end

end Denumerable

namespace Nat.Subtype

open Function Encodable

/-! ### Subsets of `ℕ` -/

variable {s : Set ℕ} [Infinite s]

section Classical

theorem exists_succ (x : s) : ∃ n, (x : ℕ) + n + 1 ∈ s := by
  by_contra h
  have (a : ℕ) (ha : a ∈ s) : a < x + 1 :=
    lt_of_not_ge fun hax => h ⟨a - (x + 1), by rwa [Nat.add_right_comm, Nat.add_sub_cancel' hax]⟩
  classical
  exact Fintype.false
    ⟨(((Multiset.range (succ x)).filter (· ∈ s)).pmap
      (fun (y : ℕ) (hy : y ∈ s) => Subtype.mk y hy) (by simp [-Multiset.range_succ])).toFinset,
      by simpa [Subtype.ext_iff_val, Multiset.mem_filter, -Multiset.range_succ] ⟩

end Classical

variable [DecidablePred (· ∈ s)]

/-- Returns the next natural in a set, according to the usual ordering of `ℕ`. -/
def succ (x : s) : s :=
  have h : ∃ m, (x : ℕ) + m + 1 ∈ s := exists_succ x
  ⟨↑x + Nat.find h + 1, Nat.find_spec h⟩

theorem succ_le_of_lt {x y : s} (h : y < x) : succ y ≤ x :=
  have hx : ∃ m, (y : ℕ) + m + 1 ∈ s := exists_succ _
  let ⟨k, hk⟩ := Nat.exists_eq_add_of_lt h
  have : Nat.find hx ≤ k := Nat.find_min' _ (hk ▸ x.2)
  show (y : ℕ) + Nat.find hx + 1 ≤ x by omega

theorem le_succ_of_forall_lt_le {x y : s} (h : ∀ z < x, z ≤ y) : x ≤ succ y :=
  have hx : ∃ m, (y : ℕ) + m + 1 ∈ s := exists_succ _
  show (x : ℕ) ≤ (y : ℕ) + Nat.find hx + 1 from
    le_of_not_gt fun hxy =>
      (h ⟨_, Nat.find_spec hx⟩ hxy).not_lt <|
        (by omega : (y : ℕ) < (y : ℕ) + Nat.find hx + 1)

theorem lt_succ_self (x : s) : x < succ x :=
  calc
    -- Porting note: replaced `x + _`, added type annotations
    (x : ℕ) ≤ (x + Nat.find (exists_succ x) : ℕ) := le_add_right ..
    _ < (succ x : ℕ) := Nat.lt_succ_self (x + _)

theorem lt_succ_iff_le {x y : s} : x < succ y ↔ x ≤ y :=
  ⟨fun h => le_of_not_gt fun h' => not_le_of_gt h (succ_le_of_lt h'), fun h =>
    lt_of_le_of_lt h (lt_succ_self _)⟩

/-- Returns the `n`-th element of a set, according to the usual ordering of `ℕ`. -/
def ofNat (s : Set ℕ) [DecidablePred (· ∈ s)] [Infinite s] : ℕ → s
  | 0 => ⊥
  | n + 1 => succ (ofNat s n)

theorem ofNat_surjective : Surjective (ofNat s)
  | ⟨x, hx⟩ => by
    set t : List s :=
      ((List.range x).filter fun y => y ∈ s).pmap
        (fun (y : ℕ) (hy : y ∈ s) => ⟨y, hy⟩)
        (by intros a ha; simpa using (List.mem_filter.mp ha).2) with ht
    have hmt : ∀ {y : s}, y ∈ t ↔ y < ⟨x, hx⟩ := by
      simp [List.mem_filter, Subtype.ext_iff_val, ht]
    cases hmax : List.maximum t with
    | bot =>
      refine ⟨0, le_antisymm bot_le (le_of_not_gt fun h => List.not_mem_nil (⊥ : s) ?_)⟩
      rwa [← List.maximum_eq_bot.1 hmax, hmt]
    | coe m =>
      have wf : ↑m < x := by simpa using hmt.mp (List.maximum_mem hmax)
      rcases ofNat_surjective m with ⟨a, rfl⟩
      refine ⟨a + 1, le_antisymm (succ_le_of_lt wf) ?_⟩
      exact le_succ_of_forall_lt_le fun z hz => List.le_maximum_of_mem (hmt.2 hz) hmax
  termination_by n => n.val

@[simp]
theorem ofNat_range : Set.range (ofNat s) = Set.univ :=
  ofNat_surjective.range_eq

@[simp]
theorem coe_comp_ofNat_range : Set.range ((↑) ∘ ofNat s : ℕ → ℕ) = s := by
  rw [Set.range_comp Subtype.val, ofNat_range, Set.image_univ, Subtype.range_coe]

private def toFunAux (x : s) : ℕ :=
  (List.range x).countP (· ∈ s)

private theorem toFunAux_eq {s : Set ℕ} [DecidablePred (· ∈ s)] (x : s) :
    toFunAux x = #{y ∈ Finset.range x | y ∈ s} := by
  rw [toFunAux, List.countP_eq_length_filter]
  rfl

open Finset

private theorem right_inverse_aux : ∀ n, toFunAux (ofNat s n) = n
  | 0 => by
    rw [toFunAux_eq, card_eq_zero, eq_empty_iff_forall_not_mem]
    rintro n hn
    rw [mem_filter, ofNat, mem_range] at hn
    exact bot_le.not_lt (show (⟨n, hn.2⟩ : s) < ⊥ from hn.1)
  | n + 1 => by
    have ih : toFunAux (ofNat s n) = n := right_inverse_aux n
    have h₁ : (ofNat s n : ℕ) ∉ {x ∈ range (ofNat s n) | x ∈ s} := by simp
    have h₂ : {x ∈ range (succ (ofNat s n)) | x ∈ s} =
        insert ↑(ofNat s n) {x ∈ range (ofNat s n) | x ∈ s} := by
      simp only [Finset.ext_iff, mem_insert, mem_range, mem_filter]
      exact fun m =>
        ⟨fun h => by
          simp only [h.2, and_true]
          exact Or.symm (lt_or_eq_of_le ((@lt_succ_iff_le _ _ _ ⟨m, h.2⟩ _).1 h.1)),
         fun h =>
          h.elim (fun h => h.symm ▸ ⟨lt_succ_self _, (ofNat s n).prop⟩) fun h =>
            ⟨h.1.trans (lt_succ_self _), h.2⟩⟩
    simp only [toFunAux_eq, ofNat, range_succ] at ih ⊢
    conv =>
      rhs
      rw [← ih, ← card_insert_of_not_mem h₁, ← h₂]

/-- Any infinite set of naturals is denumerable. -/
def denumerable (s : Set ℕ) [DecidablePred (· ∈ s)] [Infinite s] : Denumerable s :=
  Denumerable.ofEquiv ℕ
    { toFun := toFunAux
      invFun := ofNat s
      left_inv := leftInverse_of_surjective_of_rightInverse ofNat_surjective right_inverse_aux
      right_inv := right_inverse_aux }

end Nat.Subtype

namespace Denumerable

open Encodable

/-- An infinite encodable type is denumerable. -/
def ofEncodableOfInfinite (α : Type*) [Encodable α] [Infinite α] : Denumerable α := by
  letI := @decidableRangeEncode α _
  letI : Infinite (Set.range (@encode α _)) :=
    Infinite.of_injective _ (Equiv.ofInjective _ encode_injective).injective
  letI := Nat.Subtype.denumerable (Set.range (@encode α _))
  exact Denumerable.ofEquiv (Set.range (@encode α _)) (equivRangeEncode α)

end Denumerable

/-- See also `nonempty_encodable`, `nonempty_fintype`. -/
theorem nonempty_denumerable (α : Type*) [Countable α] [Infinite α] : Nonempty (Denumerable α) :=
  (nonempty_encodable α).map fun h => @Denumerable.ofEncodableOfInfinite _ h _

theorem nonempty_denumerable_iff {α : Type*} :
    Nonempty (Denumerable α) ↔ Countable α ∧ Infinite α :=
  ⟨fun ⟨_⟩ ↦ ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ ↦ nonempty_denumerable _⟩

instance nonempty_equiv_of_countable [Countable α] [Infinite α] [Countable β] [Infinite β] :
    Nonempty (α ≃ β) := by
  cases nonempty_denumerable α
  cases nonempty_denumerable β
  exact ⟨(Denumerable.eqv _).trans (Denumerable.eqv _).symm⟩
