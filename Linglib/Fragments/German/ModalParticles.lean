import Linglib.Syntax.Particle.Basic
import Linglib.Fragments.German.ClauseTypes

/-!
# German Modal Particles

Lexical entries for German modal particles (*Modalpartikeln*) as
`Particle` values: [gutzmann-2015]'s Table 6.1 mood distribution as
clause-type facets, root restriction as an embedding facet. The L_TU
typing (UCI vs UC-modifier, restriction kinds) is Gutzmann's
classification and lives in `Gutzmann2015`.

## Mood Distribution ([gutzmann-2015], Table 6.1)

| Particle | Declarative | Interrogative | Imperative |
|----------|-------------|---------------|------------|
| ja       | ✓           | ✗             | ✗          |
| denn     | ✗           | ✓             | ✗          |
| wohl     | ✓           | ✓             | ✗          |
| halt     | ✓           | ✗             | ✗          |
| doch     | ✓           | ✗             | ✓          |

Table 6.1's undifferentiated interrogative column is recorded on both
interrogative cells.
-/

namespace German.ModalParticles

open Features (ClauseForm)
open German.ClauseTypes (GermanClauseType)

/-- *ja* — common-ground reminder particle ("as you may already know").
Declaratives only: its use condition references the truth of its
propositional argument, conflicting with interrogative uncertainty and
imperative non-epistemicity (`Gutzmann2015`). -/
def ja : Particle where
  form := "ja"
  position := .clauseMedial
  distribution := some
    { declarative := some .optional
      polarInterrogative := some .excluded
      constituentInterrogative := some .excluded
      imperative := some .excluded }
  embedding := some
    { matrix := some .optional
      subordinated := some .excluded }

/-- *denn* — question-prompting particle, the interrogative counterpart
of *ja*. See `German.QuestionParticles.denn` for the [theiler-2021]
flavoring-particle entry of the same item. -/
def denn : Particle where
  form := "denn"
  position := .clauseMedial
  distribution := some
    { declarative := some .excluded
      polarInterrogative := some .optional
      constituentInterrogative := some .optional
      imperative := some .excluded }
  embedding := some
    { matrix := some .optional
      subordinated := some .excluded }

/-- *wohl* — epistemic hedging particle: declaratives and
interrogatives (which involve EPIS), never imperatives (which lack it);
see `wohl_iff_epis` and the selectional analysis in `Gutzmann2015`. -/
def wohl : Particle where
  form := "wohl"
  position := .clauseMedial
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
  position := .clauseMedial
  distribution := some
    { declarative := some .optional
      polarInterrogative := some .excluded
      constituentInterrogative := some .excluded
      imperative := some .excluded }
  embedding := some
    { matrix := some .optional
      subordinated := some .excluded }

/-- *doch* — contradiction/insistence particle. Uniquely among common
MPs, licensed in both declaratives and imperatives. -/
def doch : Particle where
  form := "doch"
  position := .clauseMedial
  distribution := some
    { declarative := some .optional
      polarInterrogative := some .excluded
      constituentInterrogative := some .excluded
      imperative := some .optional }
  embedding := some
    { matrix := some .optional
      subordinated := some .excluded }

def allModalParticles : List Particle := [ja, denn, wohl, halt, doch]

/-- Licensing across the [gutzmann-2015] German clause types, read off
the clause-type facet (dass-VL clauses exclude modal particles). -/
def licensedInClause (p : Particle) : ∀ {f : ClauseForm}, GermanClauseType f → Bool
  | _, .dassVL          => false
  | _, .v2Declarative   => decide (p.LicensedIn .declarative)
  | _, .v2Interrogative => decide (p.LicensedIn .polarInterrogative)
  | _, .vlInterrogative => decide (p.LicensedIn .constituentInterrogative)
  | _, .imperative      => decide (p.LicensedIn .imperative)

/-- *wohl*'s licensing across German clause types is exactly the
presence of EPIS in the clause type's mood structure — the formal
content of the selectional restriction analysis. -/
theorem wohl_iff_epis {f : ClauseForm} (ct : GermanClauseType f) :
    licensedInClause wohl ct = ct.moodStructure.hasEpistemic := by
  cases ct <;> rfl

/-- Every MP is excluded from dass-VL clauses. -/
theorem all_excluded_from_dassVL :
    ∀ mp ∈ allModalParticles, licensedInClause mp .dassVL = false :=
  fun _ _ => rfl

/-- *ja* and *denn* are in complementary distribution: no clause type
licenses both. -/
theorem ja_denn_complementary {f : ClauseForm} (ct : GermanClauseType f) :
    ¬(licensedInClause ja ct = true ∧ licensedInClause denn ct = true) := by
  cases ct <;> decide

end German.ModalParticles
