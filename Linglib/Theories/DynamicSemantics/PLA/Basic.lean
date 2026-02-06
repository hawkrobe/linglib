/-
# Predicate Logic with Anaphora (PLA)

Dekker's foundational system for dynamic semantics (Dekker 2012, Ch. 2).

## Innovation

PLA distinguishes variables (x_i) from pronouns (p_i):
- Variables are bound by quantifiers (∃x_i)
- Pronouns are anaphoric expressions resolved from discourse context

This distinction prevents variable clash and enables clean compositional semantics.

## Core Definitions (Dekker §2)

| Concept | Notation | Description |
|---------|----------|-------------|
| Domain | n(φ) | Variables existentially bound in φ |
| Range | r(φ) | Pronouns occurring in φ |
| Resolution | φ^ρ | Replace pronouns with variables |

## Implementation Notes

Uses `Finset.biUnion` instead of `List.foldl` for cleaner proofs.

## References

- Dekker, P. (2012). Dynamic Semantics. Springer.
- Dekker, P. (2008). A Guide to Dynamic Semantics.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Finset.Union
import Mathlib.Data.List.Basic
import Mathlib.Data.Fintype.Basic

namespace Theories.DynamicSemantics.PLA

open Classical


/-- Variable index: identifies a variable x_i -/
abbrev VarIdx := Nat

/-- Pronoun index: identifies a pronoun p_i -/
abbrev PronIdx := Nat


/-- Term: either a variable or a pronoun -/
inductive Term where
  | var : VarIdx → Term
  | pron : PronIdx → Term
  deriving DecidableEq, Repr, Hashable

namespace Term

/-- Pronouns in a term (singleton or empty) -/
def pronouns : Term → Finset PronIdx
  | .var _ => ∅
  | .pron i => {i}

/-- Variables in a term -/
def vars : Term → Finset VarIdx
  | .var i => {i}
  | .pron _ => ∅

/-- Is this a pronoun? -/
def isPron : Term → Bool
  | .var _ => false
  | .pron _ => true

theorem pronouns_var (i : VarIdx) : (Term.var i).pronouns = ∅ := rfl
theorem pronouns_pron (i : PronIdx) : (Term.pron i).pronouns = {i} := rfl

end Term


/-- Pronouns in a list of terms via `Finset.biUnion`. -/
def termsPronouns (ts : List Term) : Finset PronIdx :=
  ts.toFinset.biUnion Term.pronouns

theorem mem_termsPronouns (ts : List Term) (i : PronIdx) :
    i ∈ termsPronouns ts ↔ ∃ t ∈ ts, i ∈ t.pronouns := by
  simp only [termsPronouns, Finset.mem_biUnion, List.mem_toFinset]

theorem termsPronouns_nil : termsPronouns [] = ∅ := by
  simp [termsPronouns]


/-- PLA Formula -/
inductive Formula where
  | atom : String → List Term → Formula
  | neg : Formula → Formula
  | conj : Formula → Formula → Formula
  | exists_ : VarIdx → Formula → Formula
  deriving Repr

namespace Formula

-- Logical notation
infixr:35 " ⋀ " => conj
prefix:40 "∼" => neg

def disj (φ ψ : Formula) : Formula := neg (conj (neg φ) (neg ψ))
infixr:30 " ⋁ " => disj

def impl (φ ψ : Formula) : Formula := neg (conj φ (neg ψ))
infixr:25 " ⟶ " => impl

def forall_ (i : VarIdx) (φ : Formula) : Formula := neg (exists_ i (neg φ))


/-- Domain: existentially bound variables -/
def domain : Formula → Finset VarIdx
  | .atom _ _ => ∅
  | .neg φ => φ.domain
  | .conj φ ψ => φ.domain ∪ ψ.domain
  | .exists_ i φ => insert i φ.domain

/-- Range: pronouns in formula (using biUnion for atoms) -/
def range : Formula → Finset PronIdx
  | .atom _ ts => termsPronouns ts
  | .neg φ => φ.range
  | .conj φ ψ => φ.range ∪ ψ.range
  | .exists_ _ φ => φ.range

/-- Free variables in formula -/
def freeVars : Formula → Finset VarIdx
  | .atom _ ts => ts.toFinset.biUnion Term.vars
  | .neg φ => φ.freeVars
  | .conj φ ψ => φ.freeVars ∪ ψ.freeVars
  | .exists_ i φ => φ.freeVars.erase i


theorem range_atom (name : String) (ts : List Term) :
    (atom name ts).range = termsPronouns ts := rfl

theorem range_neg (φ : Formula) : (neg φ).range = φ.range := rfl

theorem range_conj (φ ψ : Formula) : (conj φ ψ).range = φ.range ∪ ψ.range := rfl

theorem range_exists (i : VarIdx) (φ : Formula) : (exists_ i φ).range = φ.range := rfl

/-- If a pronoun appears in a term in the formula's argument list, it's in the range -/
theorem pron_in_atom_range (name : String) (ts : List Term) (t : Term) (i : PronIdx)
    (ht : t ∈ ts) (hi : i ∈ t.pronouns) :
    i ∈ (atom name ts).range := by
  simp only [range, mem_termsPronouns]
  exact ⟨t, ht, hi⟩

/-- Range is monotonic over conjunction -/
theorem range_conj_left (φ ψ : Formula) : φ.range ⊆ (φ ⋀ ψ).range :=
  Finset.subset_union_left

theorem range_conj_right (φ ψ : Formula) : ψ.range ⊆ (φ ⋀ ψ).range :=
  Finset.subset_union_right

end Formula


/-- Resolution: maps pronouns to variables -/
abbrev Resolution := PronIdx → VarIdx

/-- Apply resolution to a term -/
def Term.resolve (ρ : Resolution) : Term → Term
  | .var i => .var i
  | .pron i => .var (ρ i)

/-- Apply resolution to a formula -/
def Formula.resolve (ρ : Resolution) : Formula → Formula
  | .atom name ts => .atom name (ts.map (Term.resolve ρ))
  | .neg φ => .neg (φ.resolve ρ)
  | .conj φ ψ => .conj (φ.resolve ρ) (ψ.resolve ρ)
  | .exists_ i φ => .exists_ i (φ.resolve ρ)

/-- Resolution removes all pronouns from a term -/
theorem Term.resolve_no_pronouns (t : Term) (ρ : Resolution) :
    (t.resolve ρ).pronouns = ∅ := by
  cases t <;> rfl

/-- Resolution removes all pronouns from a formula -/
theorem Formula.resolve_no_pronouns (φ : Formula) (ρ : Resolution) :
    (φ.resolve ρ).range = ∅ := by
  induction φ with
  | atom name ts =>
    simp only [Formula.resolve, Formula.range, termsPronouns]
    ext i
    simp only [Finset.mem_biUnion, List.mem_toFinset]
    constructor
    · intro ⟨t, ht, hi⟩
      obtain ⟨t', _, rfl⟩ := List.mem_map.mp ht
      rw [Term.resolve_no_pronouns] at hi
      simp at hi
    · simp
  | neg φ ih => exact ih
  | conj φ ψ ih1 ih2 => simp [Formula.resolve, Formula.range, ih1, ih2]
  | exists_ i φ ih => exact ih

end Theories.DynamicSemantics.PLA
