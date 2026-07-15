import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Finset.Union
import Mathlib.Data.List.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Predicate Logic with Anaphora: syntax

Syntax for Predicate Logic with Anaphora (PLA), the dynamic system originating
in [dekker-1994] and consolidated in [dekker-2012]. PLA distinguishes variables
`x_i`, bound by quantifiers, from pronouns `p_i`, anaphoric expressions resolved
from discourse context; the distinction prevents variable clash and keeps
composition clean.

## Main definitions

- `PLA.Term`, `PLA.Formula`: terms (variables or pronouns) and formulas
- `PLA.Formula.domain`: the variables existentially bound in a formula, `n(φ)`
- `PLA.Formula.range`: the pronouns occurring in a formula, `r(φ)`
- `PLA.Resolution`, `PLA.Formula.resolve`: replacing pronouns with variables, `φ^ρ`

## Main results

- `PLA.Formula.resolve_preserves_domain`: resolution preserves the domain
- `PLA.Formula.resolve_no_pronouns`: resolution eliminates all pronouns
-/

namespace PLA


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

end Term


/-- Pronouns in a list of terms via `Finset.biUnion`. -/
def termsPronouns (ts : List Term) : Finset PronIdx :=
  ts.toFinset.biUnion Term.pronouns

theorem mem_termsPronouns (ts : List Term) (i : PronIdx) :
    i ∈ termsPronouns ts ↔ ∃ t ∈ ts, i ∈ t.pronouns := by
  simp only [termsPronouns, Finset.mem_biUnion, List.mem_toFinset]


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
scoped infixr:25 " ⟶ " => impl

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

/--
Observation 2 ([dekker-2012] §2.1): Resolution preserves domain.

n(φ^ρ) = n(φ): resolving pronouns doesn't affect which variables are bound.
-/
theorem Formula.resolve_preserves_domain (φ : Formula) (ρ : Resolution) :
    (φ.resolve ρ).domain = φ.domain := by
  induction φ with
  | atom _ _ => rfl
  | neg φ ih => simp only [resolve, domain, ih]
  | conj φ ψ ih1 ih2 => simp only [resolve, domain, ih1, ih2]
  | exists_ i φ ih => simp only [resolve, domain, ih]

/-- Resolution removes all pronouns from a term -/
theorem Term.resolve_no_pronouns (t : Term) (ρ : Resolution) :
    (t.resolve ρ).pronouns = ∅ := by
  cases t <;> rfl

/--
Observation 3 ([dekker-2012] §2.1): Resolution eliminates all pronouns.

r(φ^ρ) = ∅: after resolution, the formula contains no pronouns.
-/
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

end PLA
