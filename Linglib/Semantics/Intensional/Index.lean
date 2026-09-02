import Mathlib.Tactic.TypeStar

/-!
# Indices of evaluation

An `Intensional.Index` is a (world, time) pair used as a context of
evaluation for intensional, dynamic, modal, and tense semantics — the
Lewis/Kaplan "index of evaluation", with world and temporal coordinates
only. It is *not* the Kratzer parthood-structured situation (a preordered type, as in
`Conditionals.Counterfactual` lumping) and *not* the Pearl/Halpern partial valuation
(`Causation.Situation`).
-/

namespace Intensional

/-- A world–time index: a (world, time) pair used as a context of
    evaluation in intensional, dynamic, modal, and tense semantics.

    This is the Lewis/Kaplan "index" — a coordinate tuple as point of
    evaluation, abstracting from the parthood structure of Kratzer situations. -/
structure Index (W T : Type*) where
  /-- The world coordinate -/
  world : W
  /-- The temporal coordinate -/
  time : T
  deriving Repr

end Intensional
