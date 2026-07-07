import Linglib.Syntax.Particle.Basic
import Linglib.Fragments.German.ClauseTypes

/-!
# German Particles

The German particle inventory as `Particle` values: the modal particles
(*Modalpartikeln*, [gutzmann-2015] Table 6.1) and the question-marking
particles ([theiler-2021], [seeliger-repp-2018]), one entry per lexeme.
Analytical classifications live with their analyses: L_TU typing in
`Gutzmann2015`, highlighting and bias in `Theiler2021`, the PRQ/NRQ
profile in `SeeligerRepp2018`. Response uses of *ja*/*doch* live in
`PolarityMarking.lean`.

Table 6.1's undifferentiated interrogative column is recorded on both
interrogative cells.
-/

namespace German.Particles

open Features (ClauseForm)
open German.ClauseTypes (GermanClauseType)

/-- *ja* — common-ground reminder particle ("as you may already know").
Declaratives only: its use condition references the truth of its
propositional argument, conflicting with interrogative uncertainty and
imperative non-epistemicity (`Gutzmann2015`). Distinct from answer
particle *ja* (`PolarityMarking.lean`). -/
def ja : Particle where
  form := "ja"
  position := some .clauseMedial
  distribution := some
    { declarative := some .optional
      polarInterrogative := some .excluded
      constituentInterrogative := some .excluded
      imperative := some .excluded }
  embedding := some
    { matrix := some .optional
      subordinated := some .excluded }

/-- *denn* — interrogative-only particle, one lexeme under two analyses:
[gutzmann-2015]'s question-prompting UCI (the interrogative counterpart
of *ja*; typing in `Gutzmann2015`) and [theiler-2021]'s
highlighting-sensitive flavoring particle (bias profile in
`Theiler2021`). Licensed in polar and constituent questions, excluded
from declaratives and imperatives. -/
def denn : Particle where
  form := "denn"
  position := some .clauseMedial
  distribution := some
    { declarative := some .excluded
      polarInterrogative := some .optional
      constituentInterrogative := some .optional
      imperative := some .excluded }
  embedding := some
    { matrix := some .optional
      subordinated := some .excluded }

/-- *wohl* — epistemic hedging particle: declaratives and interrogatives
(which involve EPIS), never imperatives (which lack it); see
`wohl_iff_epis` and the selectional analysis in `Gutzmann2015`. -/
def wohl : Particle where
  form := "wohl"
  position := some .clauseMedial
  distribution := some
    { declarative := some .optional
      polarInterrogative := some .optional
      constituentInterrogative := some .optional
      imperative := some .excluded }
  embedding := some
    { matrix := some .optional
      subordinated := some .excluded }

/-- *halt* — resignation/acceptance particle ("that's just the way it
is"). Declaratives only. -/
def halt : Particle where
  form := "halt"
  position := some .clauseMedial
  distribution := some
    { declarative := some .optional
      polarInterrogative := some .excluded
      constituentInterrogative := some .excluded
      imperative := some .excluded }
  embedding := some
    { matrix := some .optional
      subordinated := some .excluded }

/-- *doch* — contradiction/insistence particle. Uniquely among common
MPs, licensed in both declaratives and imperatives. Distinct from the
polarity-reversal response *doch* (`PolarityMarking.lean`; the ambiguity
is formalized in `SeeligerRepp2018.doch_dual_role`). -/
def doch : Particle where
  form := "doch"
  position := some .clauseMedial
  distribution := some
    { declarative := some .optional
      polarInterrogative := some .excluded
      constituentInterrogative := some .excluded
      imperative := some .optional }
  embedding := some
    { matrix := some .optional
      subordinated := some .excluded }

/-- *doch wohl* — non-compositional marker of rejecting questions
([seeliger-repp-2018]): declarative-syntax polar questions (recorded
under `polarInterrogative` following the source schema's
question-function reading), not assertions and not wh-questions. The
PRQ/NRQ bias profile lives in `SeeligerRepp2018`. -/
def dochWohl : Particle where
  form := "doch wohl"
  position := some .clauseMedial
  distribution := some
    { declarative := some .excluded
      polarInterrogative := some .optional
      constituentInterrogative := some .excluded }

/-- The modal-particle inventory ([gutzmann-2015] Table 6.1). -/
def modalParticles : List Particle := [ja, denn, wohl, halt, doch]

/-- The question-marking particles ([theiler-2021],
[seeliger-repp-2018]). *denn* is in both inventories. -/
def questionParticles : List Particle := [denn, dochWohl]

/-- Licensing across the [gutzmann-2015] German clause types, read off
the clause-type facet (dass-VL clauses exclude modal particles). -/
def licensedInClause (p : Particle) : ∀ {f : ClauseForm}, GermanClauseType f → Bool
  | _, .dassVL          => false
  | _, .v2Declarative   => decide (p.LicensedIn .declarative)
  | _, .v2Interrogative => decide (p.LicensedIn .polarInterrogative)
  | _, .vlInterrogative => decide (p.LicensedIn .constituentInterrogative)
  | _, .imperative      => decide (p.LicensedIn .imperative)

/-- Every MP is excluded from dass-VL clauses. -/
theorem all_excluded_from_dassVL :
    ∀ mp ∈ modalParticles, licensedInClause mp .dassVL = false :=
  fun _ _ => rfl

/-- *ja* and *denn* are in complementary distribution: no clause type
licenses both. -/
theorem ja_denn_complementary {f : ClauseForm} (ct : GermanClauseType f) :
    ¬(licensedInClause ja ct = true ∧ licensedInClause denn ct = true) := by
  cases ct <;> decide

end German.Particles
