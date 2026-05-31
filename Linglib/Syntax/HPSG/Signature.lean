import Mathlib.Order.Basic
import Mathlib.Order.Max

/-!
# RSRL signatures
@cite{richter-2000}, @cite{richter-2024}, @cite{pollard-sag-1994}

A native Lean rendering of an RSRL **signature** — the sort hierarchy and appropriateness
declarations that fix the space of possible feature structures of an HPSG grammar
(@cite{richter-2000}, Def. 47; @cite{richter-2024}, Ch. 3 §2).

HPSG since @cite{pollard-sag-1994} is **model-theoretic**: a grammar is a signature plus a
set of descriptions (its principles), and its meaning is the class of total, sort-resolved
objects satisfying every principle. This file provides the signature; `Interpretation.lean`
the models, `Description.lean` the description language, `Model.lean` a worked instantiation.

## Main declarations

* `HPSG.RSRL.Signature` — over a sort hierarchy `Srt` (a mathlib `PartialOrder`; `a ≤ b` reads
  "`a` is at least as specific as `b`", so species are the *minimal* sorts) it carries the
  attributes, relation symbols with arities, and the appropriateness function with feature
  inheritance.
* `HPSG.RSRL.IsSpecies` — a maximally specific sort, i.e. `IsMin` in the specificity order.
* `HPSG.RSRL.Signature.IsAtomicSort` — a species with no appropriate attributes.
* `HPSG.RSRL.Path` — a `:`-rooted attribute path (the variable-free fragment of RSRL terms,
  Def. 52).

## Implementation notes

* The sort hierarchy is a genuine `[PartialOrder Srt]` (RSRL's `⊑`); `IsSpecies := IsMin`.
* The chain/relation/quantifier apparatus of full RSRL is not yet modelled (RSRL is strictly
  richer than first-order logic — @cite{richter-2024}, Ch. 3); `Rel`/`arity` are carried for
  signature completeness but unused until a principle needs relations.
-/

namespace HPSG.RSRL

universe u

/-- An RSRL signature (@cite{richter-2000}, Def. 47) over a sort hierarchy `Srt`: the sorts
form a `PartialOrder` (subsumption `⊑`, here `≤`), and the signature adds attributes, relation
symbols with arities, and an appropriateness function obeying feature inheritance. -/
structure Signature (Srt : Type u) [PartialOrder Srt] where
  /-- The attributes `𝒜` (feature names). -/
  Attr : Type u
  /-- The relation symbols `ℛ` (carried but unused until a principle needs relations). -/
  Rel : Type u
  /-- Relation arities `𝒜ℛ`. -/
  arity : Rel → Nat
  /-- Appropriateness `ℱ`: `approp σ α = some τ` means `α` is appropriate to `σ` with value
  sort `τ`; `none` means `α` is not appropriate to `σ`. -/
  approp : Srt → Attr → Option Srt
  /-- Feature inheritance (@cite{richter-2000}, Def. 47): if `α` is appropriate to `σ₁` and
  `σ₂` is at least as specific as `σ₁`, then `α` is appropriate to `σ₂` with an
  at-least-as-specific value. -/
  approp_inherits : ∀ {σ₁ σ₂ : Srt} {α : Attr} {τ₁ : Srt},
    σ₂ ≤ σ₁ → approp σ₁ α = some τ₁ → ∃ τ₂, approp σ₂ α = some τ₂ ∧ τ₂ ≤ τ₁

/-- A **species** is a maximally specific sort (@cite{richter-2000}, Def. 47): a minimal
element of the specificity order `≤`. -/
abbrev IsSpecies {Srt : Type u} [PartialOrder Srt] (σ : Srt) : Prop := IsMin σ

namespace Signature

variable {Srt : Type u} [PartialOrder Srt] (Sig : Signature Srt)

/-- An **atomic** sort: a species with no appropriate attributes. (Named `IsAtomicSort` to
avoid colliding with mathlib's order-theoretic `IsAtom`.) -/
def IsAtomicSort (σ : Srt) : Prop := IsMin σ ∧ ∀ α, Sig.approp σ α = none

end Signature

/-- A `:`-rooted attribute **path** (the variable-free fragment of RSRL terms,
@cite{richter-2000}, Def. 52): `[]` denotes the described entity itself, and `α :: p` follows
attribute `α` and then the rest of the path. -/
abbrev Path {Srt : Type u} [PartialOrder Srt] (Sig : Signature Srt) := List Sig.Attr

/-- An RSRL **term** (@cite{richter-2000}, Def. 52): rooted at either the described entity
(`colon`, the reserved `:`) or a variable (`var n`), then extended by attributes (`feat t α`).
Variables are needed for relational formulae and component quantification (Def. 54). -/
inductive Term {Srt : Type u} [PartialOrder Srt] (Sig : Signature Srt) where
  /-- The described entity itself (RSRL `:`). -/
  | colon : Term Sig
  /-- A variable (de Bruijn-free; `n : ℕ` names it). -/
  | var : Nat → Term Sig
  /-- Follow attribute `α` from the term `t` (RSRL `tα`). -/
  | feat : Term Sig → Sig.Attr → Term Sig

/-- The `:`-rooted term following a path of attributes — bridges the PR1 `Path` notation
(`[α, β]`) into the term language: `Term.path [α, β] = (colon.feat α).feat β`. -/
def Term.path {Srt : Type u} [PartialOrder Srt] {Sig : Signature Srt}
    (p : Path Sig) : Term Sig :=
  p.foldl Term.feat Term.colon

end HPSG.RSRL
