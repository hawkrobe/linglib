import Linglib.Syntax.Minimalist.ExtendedProjection.Basic

/-!
# Rational attitude readings

[fusco-sgrizzi-2026] analyse verbs like Italian *convincere* as
carrying a single *rational attitude* semantics whose belief or
intention construal is fixed by complement size: a phase-sized (CP)
complement is existentially closed into a proposition and evaluated
against doxastic content, while a smaller complement leaves the event
variable open and is evaluated against inertial continuation
([dowty-1979]). `Reading` is the two-way construal and
`readingFromSize` derives it from `ComplementSize`.

The paper's single-denotation analysis of *convincere* and its
reading diagnostics live in `Studies/FuscoSgrizzi2026.lean`; the
causal-self-reference semantics for intention reports
([grano-2024]) in `Studies/Grano2024.lean`; the Italian *di*/*a*
complementizer data in `Fragments/Italian/Predicates.lean`.
-/

namespace RationalAttitude

open Minimalist (ComplementSize fValue)

/-- The two construals of a rational attitude verb: propositional
    belief, evaluated against doxastic content, or sub-propositional
    intention, evaluated against inertial continuation. -/
inductive Reading where
  | belief
  | intention
  deriving DecidableEq, Repr

/-- The construal determined by complement size: a phase-sized (CP)
    complement is existentially closed into a proposition and read as
    belief; a smaller complement leaves the event variable open and is
    read as intention. -/
def readingFromSize (cs : ComplementSize) : Reading :=
  if cs.isPhaseSized then .belief else .intention

/-- Complement size determines the construal, with the CP phase
    boundary as the threshold. -/
theorem readingFromSize_eq_belief_iff (cs : ComplementSize) :
    readingFromSize cs = .belief ↔ fValue .C ≤ cs.fLevel := by
  unfold readingFromSize
  cases h : cs.isPhaseSized <;>
    simp_all [ComplementSize.isPhaseSized]

end RationalAttitude
