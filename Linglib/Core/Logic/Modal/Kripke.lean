import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Kripke models for modal logic

@cite{vaananen-2008}

A **Kripke model** for modal logic over a finite world-type `W` and an
atom-type `Atom`: an accessibility relation `R : W → Finset W` together
with a Boolean valuation `V : Atom → W → Bool`. This is the standard
Kripke structure used as the carrier for classical modal logic and
its team-semantic extensions (BSML, MDL, modal inclusion logic, etc.).

The `Finset` form of accessibility (rather than `Set` or a binary
relation) reflects the decidable / finite-witness use case shared by
the modal team-semantic logics — all current consumers (BSML, QBSML,
the AAY-2024 extensions BSMLOr/BSMLEmpty, modal dependence logic in
`Core/Logic/Modal/Dependence.lean`) consume this finite form.

## Main declarations

* `KripkeModel W Atom` — the carrier structure: accessibility (`access`)
  + valuation (`val`).

## Consumers

* `Core/Logic/Modal/BSML/Defs.lean` — `BSMLModel` is an `abbrev` of
  this type.
* `Core/Logic/Modal/QBSML/Defs.lean` — `QBSMLModel` parameterises
  this carrier with an assignment type.
* `Core/Logic/Modal/Dependence.lean` — modal dependence logic (MDL).
* `Studies/AloniAnttilaYang2024.lean` — BSMLOr,
  BSMLEmpty (via `BSMLModel` alias).

## Todo

* Lift bisimulation infrastructure currently at
  `Core/Logic/Modal/BSML/Bisimulation.lean` to a sibling
  `Core/Logic/Modal/Bisimulation.lean` once a non-BSML consumer
  (MDL bisim invariance, modal inclusion logic) lands.
-/

namespace Core.Logic.Modal

/-- A **Kripke model** over world-type `W` and atom-type `Atom`:
    an accessibility relation `access : W → Finset W` (mapping each
    world to its set of successors) together with a Boolean valuation
    `val : Atom → W → Bool` (mapping each atom to its truth value at
    each world).

    The universe of worlds is given by `[Fintype W]` — use `Finset.univ`
    for the full set. Decidable equality on `W` is required so that
    accessibility images are well-behaved as `Finset`s. -/
structure KripkeModel (W : Type*) (Atom : Type*) [DecidableEq W] [Fintype W] where
  /-- Accessibility: `access w` is the set of worlds accessible from `w`. -/
  access : W → Finset W
  /-- Valuation: `val p w` is the truth value of atom `p` at world `w`. -/
  val : Atom → W → Bool

end Core.Logic.Modal
