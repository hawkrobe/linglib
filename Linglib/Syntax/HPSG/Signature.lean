import Mathlib.Order.Basic
import Mathlib.Order.Max

/-!
# RSRL signatures
@cite{richter-2000}, @cite{richter-2024}, @cite{pollard-sag-1994}

An RSRL **signature** (Def. 47): a sort hierarchy `[PartialOrder Srt]` (`a ≤ b` = "`a` at least
as specific as `b`") with appropriateness declarations and relation symbols. The
model-theoretic foundation of HPSG (Pollard & Sag 1994 onward); `Interpretation.lean` gives the
models, `Description.lean` the description language.
-/

namespace HPSG.RSRL

universe u

/-- Build a `PartialOrder` from a decidable boolean order whose laws hold (typically `by decide`
on a finite type). Reducible so `≤` unfolds to `leB · · = true` in instance search. -/
@[reducible] def partialOrderOfBool {α : Type u} (leB : α → α → Bool)
    (le_refl : ∀ a, leB a a = true)
    (le_trans : ∀ a b c, leB a b = true → leB b c = true → leB a c = true)
    (le_antisymm : ∀ a b, leB a b = true → leB b a = true → a = b) : PartialOrder α where
  le a b := leB a b = true
  le_refl := le_refl
  le_trans := le_trans
  le_antisymm := le_antisymm

/-- An RSRL signature (@cite{richter-2000}, Def. 47) over a sort hierarchy `Srt`. -/
structure Signature (Srt : Type u) [PartialOrder Srt] where
  /-- Attributes (feature names). -/
  Attr : Type u
  /-- Relation symbols (unused until a principle needs relations). -/
  Rel : Type u
  /-- Relation arities. -/
  arity : Rel → Nat
  /-- Appropriateness: `approp σ α = some τ` means `α` is appropriate to `σ` with value sort `τ`. -/
  approp : Srt → Attr → Option Srt
  /-- Feature inheritance: a more specific sort inherits appropriateness with an at-least-as-
  specific value. -/
  approp_inherits : ∀ {σ₁ σ₂ : Srt} {α : Attr} {τ₁ : Srt},
    σ₂ ≤ σ₁ → approp σ₁ α = some τ₁ → ∃ τ₂, approp σ₂ α = some τ₂ ∧ τ₂ ≤ τ₁

/-- A **species** is a maximally specific sort — minimal in the specificity order. -/
abbrev IsSpecies {Srt : Type u} [PartialOrder Srt] (σ : Srt) : Prop := IsMin σ

/-- An **atomic** sort: a species with no appropriate attributes. (Distinct from `IsAtom`.) -/
def Signature.IsAtomicSort {Srt : Type u} [PartialOrder Srt] (Sig : Signature Srt) (σ : Srt) :
    Prop := IsMin σ ∧ ∀ α, Sig.approp σ α = none

/-- A `:`-rooted attribute **path** (Def. 52, variable-free fragment): `[]` is the described
entity, `α :: p` follows `α` then the rest. -/
abbrev Path {Srt : Type u} [PartialOrder Srt] (Sig : Signature Srt) := List Sig.Attr

/-- An RSRL **term** (Def. 52): rooted at the described entity (`colon`) or a variable (`var n`),
extended by attributes (`feat t α`). Variables support relations and quantification. -/
inductive Term {Srt : Type u} [PartialOrder Srt] (Sig : Signature Srt) where
  /-- The described entity (RSRL `:`). -/
  | colon : Term Sig
  /-- A variable. -/
  | var : Nat → Term Sig
  /-- Follow attribute `α` from `t` (RSRL `tα`). -/
  | feat : Term Sig → Sig.Attr → Term Sig

/-- The `:`-rooted term following a path: `Term.path [α, β] = (colon.feat α).feat β`. -/
def Term.path {Srt : Type u} [PartialOrder Srt] {Sig : Signature Srt} (p : Path Sig) : Term Sig :=
  p.foldl Term.feat Term.colon

end HPSG.RSRL
