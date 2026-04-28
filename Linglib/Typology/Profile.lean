import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Order.SymmDiff

/-!
# Typological micro-parameter profiles

A `Profile ι` records which members of an enum `ι` of micro-parameter
names are "active" (positive setting) for a single language or dialect.
Reuses `Set ι` definitionally so that mathlib's set lattice (`∪`, `∩`,
`\`, `symmDiff`) and set-literal syntax (`{.A, .B, .C}`) become the
natural surface notation for fragment files.

## Examples

* V2 micro-parameters indexed by @cite{westergaard-2009}'s `ForceHead`
  (`Theories/Syntax/Minimalism/Formal/ExtendedProjection/Basic.lean`).
* Future: NPI licensing environments per language; WALS feature
  presence; Greenbergian universal antecedents.

## Why an `abbrev` over `Set ι`, not a fresh `structure`

A typological profile is a set of active parameters — nothing more.
Wrapping it in a struct would force consumers to re-implement set
lattice operations (`∪`, `∆`, etc.) on the wrapper, or to constantly
project. The `abbrev` carries the intent (this is a typological
profile, not an arbitrary set) without losing mathlib's API surface.

## Why `activeCount` over `Set.ncard`

`Set.ncard` is the mathlib-canonical cardinality for an arbitrary
`Set α`, but for our use case (small `[Fintype ι]` enums where
`decide` should close `p.activeCount < q.activeCount`-shaped theorems)
we want the structurally-reducible `(Finset.univ.filter ...).card`
form. `Set.ncard` routes through `Set.Finite.toFinset` and is
non-computable in this kernel sense.
-/

universe u

namespace Typology

/-- A typological micro-parameter profile over the parameter-name enum
    `ι`: the set of names whose value is "active" (`+`) for a single
    language or dialect. -/
abbrev Profile (ι : Type u) : Type u := Set ι

namespace Profile

variable {ι : Type u}

/-- Number of active micro-parameters in a profile. Structurally
    reducible to `(Finset.univ.filter (· ∈ p)).card` so that `decide`
    closes consumer theorems comparing counts. -/
def activeCount [Fintype ι] (p : Profile ι) [DecidablePred (· ∈ p)] : ℕ :=
  (Finset.univ.filter (· ∈ p)).card

/-- Two profiles disagree exactly at parameter `i`: their values differ
    at `i` and agree everywhere else. The Westergaard cross-Germanic
    "differ only on Decl°" / "differ only on Excl°" theorems instance
    this. -/
def DiffersExactlyOn (p q : Profile ι) (i : ι) : Prop :=
  i ∈ symmDiff p q ∧ ∀ j, j ≠ i → (j ∈ p ↔ j ∈ q)

end Profile

end Typology
