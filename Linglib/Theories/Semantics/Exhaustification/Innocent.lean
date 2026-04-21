import Linglib.Theories.Semantics.Exhaustification.Excluder

/-!
# Innocent Exclusion (Fox 2007)
@cite{fox-2007} @cite{spector-2016}

Fox's innocent-exclusion algorithm as an `Excluder` (`Excluder.lean`):
the chosen alternatives are those whose complement is in **every**
maximal compatible exclusion of the prejacent.

A `Finset`-throughout formulation that obeys mathlib discipline: one
definition, decidability falls out of `Finset.powerset` + `Finset.filter`,
no parallel `Bool`/`List` API.

Worlds are an arbitrary `[Fintype W] [DecidableEq W]`. A proposition is
the `Finset W` of worlds where it holds. An alternative collection is a
`Finset (Finset W)`. Exhaustification returns a `Finset W`.

## Key definitions

- `excludables ALT φ` — bound on every `IsCompatible` witness
- `IsCompatible ALT φ E` — Spector Definition 3.2 (Finset version)
- `IsMCSet ALT φ E` — maximal compatible set within `excludables`
- `IE ALT φ` — propositions in every MC-set
- `innocentlyExcludable ALT φ` — alternatives whose complement is in `IE`
- `Exhaustification.innocent : Excluder W` — the `Excluder` package

Consumers call `innocent.exh ALT φ` for the exhaustified meaning.

## Relation to the Set / Spector reference API

The Set-side formalization in `Operators/Basic.lean` is the reference
implementation for paper-level theorems (Spector's Props 6/7, Cor 8,
Thm 9, Thm 10). `SetFinsetBridge.lean` proves the two agree on
`IsCompatible`, `IsMCSet`, `IE`, and `IsInnocentlyExcludable`, so
Spector-side results transport here. New code that needs decidability
or `Excluder` uniformity (sibling Tolerant/Relevance excluders) should
use the API in this file.
-/

namespace Exhaustification.Innocent

variable {W : Type*} [Fintype W] [DecidableEq W]
variable (ALT : Finset (Finset W)) (φ : Finset W)

/-- Bound on every `IsCompatible` set: the prejacent plus complements
    of every alternative. Every member of any compatible set is either
    `φ` or `aᶜ` for some `a ∈ ALT`, so the powerset of this set is the
    natural search space. -/
def excludables : Finset (Finset W) :=
  insert φ (ALT.image (fun a => Finset.univ \ a))

/-- Spector Def 3.2 (Finset version): `E` is `(ALT, φ)`-compatible if
    it lies in `excludables`, contains `φ`, and is jointly satisfiable
    (intersection nonempty). -/
def IsCompatible (E : Finset (Finset W)) : Prop :=
  E ⊆ excludables ALT φ ∧ φ ∈ E ∧ (E.inf id).Nonempty

instance decidableIsCompatible (E : Finset (Finset W)) :
    Decidable (IsCompatible ALT φ E) := by
  unfold IsCompatible; exact inferInstance

/-- Spector Def 3.3: maximal compatible set. Maximality is checked
    against extensions within `excludables` (which is enough, since
    every compatible set is a subset of `excludables`). -/
def IsMCSet (E : Finset (Finset W)) : Prop :=
  IsCompatible ALT φ E ∧
    ∀ E' ∈ (excludables ALT φ).powerset,
      IsCompatible ALT φ E' → E ⊆ E' → E' ⊆ E

instance decidableIsMCSet (E : Finset (Finset W)) :
    Decidable (IsMCSet ALT φ E) := by
  unfold IsMCSet; exact inferInstance

/-- Spector Def 3.4: `IE = {ψ : ψ is in every MC-set}`. Bounded by
    `excludables`, since membership in MC-sets restricts to that set. -/
def IE : Finset (Finset W) :=
  (excludables ALT φ).filter fun ψ =>
    ∀ E ∈ (excludables ALT φ).powerset, IsMCSet ALT φ E → ψ ∈ E

/-- The innocently-excludable alternatives: `a ∈ ALT` such that `aᶜ ∈ IE`.
    For each such `a`, exhaustification negates `a` (asserts `aᶜ`). -/
def innocentlyExcludable : Finset (Finset W) :=
  ALT.filter (fun a => (Finset.univ \ a) ∈ IE ALT φ)

theorem innocentlyExcludable_subset (ALT : Finset (Finset W)) (φ : Finset W) :
    innocentlyExcludable ALT φ ⊆ ALT := Finset.filter_subset _ _

/-- The prejacent is in every compatible set, hence in `IE`. -/
theorem phi_mem_IE : φ ∈ IE ALT φ := by
  unfold IE
  refine Finset.mem_filter.mpr ⟨?_, ?_⟩
  · exact Finset.mem_insert_self φ _
  · intro E _ hMC
    exact hMC.1.2.1

end Exhaustification.Innocent

namespace Exhaustification

/-- The Fox 2007 innocent-exclusion excluder. The `Excluder` package
    around `Innocent.innocentlyExcludable`; `innocent.exh ALT φ` is the
    exhaustified meaning. -/
def innocent {W : Type*} [Fintype W] [DecidableEq W] : Excluder W where
  excluded := Innocent.innocentlyExcludable
  excluded_subset := Innocent.innocentlyExcludable_subset

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- **Vacuity**: when no alternative is innocently excludable,
    `innocent.exh` returns the prejacent unchanged. -/
theorem innocent_exh_eq_phi_of_innocentlyExcludable_empty
    {ALT : Finset (Finset W)} {φ : Finset W}
    (h : Innocent.innocentlyExcludable ALT φ = ∅) :
    innocent.exh ALT φ = φ := by
  show φ \ ((Innocent.innocentlyExcludable ALT φ).biUnion id) = φ
  rw [h]
  simp

end Exhaustification
