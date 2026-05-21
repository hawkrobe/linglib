import Linglib.Core.Logic.Team.Closure

/-!
# Closure profiles for team-set predicates

@cite{anttila-2025} @cite{anttila-haggblom-yang-2024}

A team-set's *closure profile* is the conjunction of which closure
properties it satisfies, drawn from the three coordinates:

| Property            | Predicate         |
|---------------------|-------------------|
| Downward closure    | `IsLowerSet T`    |
| Sup-closure         | `SupClosed T`     |
| Empty-team property | `∅ ∈ T`           |

Flatness — Anttila Proposition 2.2.2, formalised as `IsFlat` in
`Closure.lean` — is the **full profile**: all three coordinates hold.
Different team-semantic logics inhabit different cells of this lattice
according to which atoms / connectives their syntax admits:

| Logic family             | DC | UC | ∅∈ | Profile             |
|--------------------------|----|----|----|---------------------|
| BSML (NE-free)           | ✓  | ✓  | ✓  | `IsFlat`            |
| BSML (with NE)           | —  | ✓  | ✓  | `IsUpwardProfile`   |
| BSMLEmpty                | —  | ✓  | ✓  | `IsUpwardProfile`   |
| MIL (modal inclusion)    | —  | ✓  | ✓  | `IsUpwardProfile`   |
| MDL (modal dependence)   | ✓  | —  | ✓  | `IsDownwardProfile` |
| Inquisitive (future)     | ✓  | ✓  | —  | (no name yet)       |
| MTL (future)             | —  | —  | —  | (full Boolean)      |

This file introduces names for the two profiles currently inhabited
by ≥ 2 linglib logics — `IsUpwardProfile` (BSML/BSMLEmpty/MIL) and
`IsDownwardProfile` (MDL) — and provides the bridge theorems
relating them to `IsFlat`. Per-logic instances (e.g.,
`MIL.support_isUpwardProfile`) live in each logic's own file as
bundling theorems over the existing closure-property proofs.

## Main declarations

* `IsUpwardProfile T` — `T` is sup-closed and contains the empty team
  (closure profile when downward closure fails).
* `IsDownwardProfile T` — `T` is downward-closed and contains the
  empty team (closure profile when sup-closure fails).
* `IsFlat.isUpwardProfile`, `IsFlat.isDownwardProfile` — flatness
  implies either weakening.
* `IsUpwardProfile.isFlat_of_isLowerSet`,
  `IsDownwardProfile.isFlat_of_supClosed` — adding the missing
  coordinate recovers flatness.
* `isFlat_iff_isUpwardProfile_and_isLowerSet`,
  `isFlat_iff_isDownwardProfile_and_supClosed` — the iff forms.

## Implementation notes

The profile predicates are `abbrev` — they unfold to their conjunctions
on demand, so callers see no abstraction layer between profile-level
reasoning and direct closure-property arguments. Mathlib precedent for
named conjunctions is `Set.Subsingleton ∧ Set.Nonempty` etc.; here the
two-conjunct case is small enough that the `abbrev` is mostly a
documentation move plus a name to write theorem signatures against.

## Todo

* `IsInquisitiveProfile T := IsLowerSet T ∧ SupClosed T` — drops the
  empty-team property. Add when InqB/InqML lands in
  `Core/Logic/Modal/`.
* Generic theorems about the lattice (e.g., monotonicity:
  `IsFlat → IsUpwardProfile` and `→ IsDownwardProfile`) suggest a
  Galois connection or similar abstraction. Defer until a downstream
  consumer makes the right shape evident.
-/

namespace Core.Logic.Team

variable {α : Type*} [DecidableEq α]

/-! ### Upward profile (sup-closure + empty) -/

/-- A team-set has the **upward profile** iff it is sup-closed and
    contains the empty team. This is the closure profile satisfied by
    BSML (with NE), BSMLEmpty, and MIL — three syntactically distinct
    mechanisms reaching the same closure cell. -/
abbrev IsUpwardProfile (T : Set (Finset α)) : Prop :=
  SupClosed T ∧ ∅ ∈ T

/-! ### Downward profile (downward closure + empty) -/

/-- A team-set has the **downward profile** iff it is downward-closed
    under inclusion and contains the empty team. This is the closure
    profile satisfied by MDL (modal dependence logic), where the
    dependence atom preserves downward closure but breaks sup-closure. -/
abbrev IsDownwardProfile (T : Set (Finset α)) : Prop :=
  IsLowerSet T ∧ ∅ ∈ T

/-! ### Bridges to flatness -/

/-- Flat team-sets have the upward profile (drop downward closure). -/
theorem IsFlat.isUpwardProfile {T : Set (Finset α)} (h : IsFlat T) :
    IsUpwardProfile T :=
  ⟨h.supClosed, h.empty_mem⟩

/-- Flat team-sets have the downward profile (drop sup-closure). -/
theorem IsFlat.isDownwardProfile {T : Set (Finset α)} (h : IsFlat T) :
    IsDownwardProfile T :=
  ⟨h.isLowerSet, h.empty_mem⟩

/-- Upward-profile + downward closure = flat. -/
theorem IsUpwardProfile.isFlat_of_isLowerSet {T : Set (Finset α)}
    (h : IsUpwardProfile T) (hlow : IsLowerSet T) : IsFlat T :=
  isFlat_of_isLowerSet_supClosed_empty hlow h.1 h.2

/-- Downward-profile + sup-closure = flat. -/
theorem IsDownwardProfile.isFlat_of_supClosed {T : Set (Finset α)}
    (h : IsDownwardProfile T) (hsup : SupClosed T) : IsFlat T :=
  isFlat_of_isLowerSet_supClosed_empty h.1 hsup h.2

/-! ### Iff characterisations -/

theorem isFlat_iff_isUpwardProfile_and_isLowerSet {T : Set (Finset α)} :
    IsFlat T ↔ IsUpwardProfile T ∧ IsLowerSet T := by
  refine ⟨fun h => ⟨h.isUpwardProfile, h.isLowerSet⟩, ?_⟩
  rintro ⟨h, hlow⟩
  exact h.isFlat_of_isLowerSet hlow

theorem isFlat_iff_isDownwardProfile_and_supClosed {T : Set (Finset α)} :
    IsFlat T ↔ IsDownwardProfile T ∧ SupClosed T := by
  refine ⟨fun h => ⟨h.isDownwardProfile, h.supClosed⟩, ?_⟩
  rintro ⟨h, hsup⟩
  exact h.isFlat_of_supClosed hsup

end Core.Logic.Team
