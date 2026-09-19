import Linglib.Syntax.Category.Verb.Basic

/-!
# Spanish Mood-Choice Verb Entries [grano-2024]

Minimal verb entries for Spanish attitude and causative predicates
relevant to cross-linguistic mood choice ([grano-2024], Table 1).

Spanish robustly rejects indicative under 'want', 'hope', 'intend',
and 'make' — all four take subjunctive or nonfinite complements.

## Key examples (from [grano-2024])

- (1a) Victoria quiere que Marcela **venga**/\*viene al picnic. (SBJV/\*IND)
- (9) Espero que mi hermano **viniera**/\*vino ayer. (SBJV/\*IND)
- (25) Tengo la intención de que Juan **vaya**/\*va/\*irá al parque hoy. (SBJV)
- (40) Hice que Juan **fuera**/\*fue al parque. (SBJV/\*IND)
-/

namespace Spanish.MoodChoice

open ArgumentStructure

/-- *querer* 'want' — robustly subjunctive-selecting.
    [grano-2024], (1a): SBJV required, IND rejected. -/
def querer : Verb where
  form := "querer"
  frames := [ArgumentFrame.finiteClause, ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.finiteClause, control := some .subjectControl }]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))

/-- *esperar* 'hope' — subjunctive in Spanish (unlike Portuguese/French).
    [grano-2024], (9): SBJV required, IND rejected. -/
def esperar : Verb where
  form := "esperar"
  frames := [ArgumentFrame.finiteClause, ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.finiteClause, control := some .subjectControl }]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))

/-- *tener la intención (de)* 'intend' — robustly rejects indicative.
    [grano-2024], (25): SBJV required in non-control complements.
    Periphrastic form (nominal predicate). -/
def tener_la_intencion : Verb where
  form := "tener la intención"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))

/-- *hacer* 'make' — causative, robustly subjunctive-selecting.
    [grano-2024], (40): SBJV required, IND rejected.
    Infinitival complements with object control. -/
def hacer : Verb where
  form := "hacer"
  frames := [ArgumentFrame.infinitival, ArgumentFrame.finiteClause]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .objectControl }]
  causative := some .make

/-- *convencer* 'convince' — hybrid predicate (§6.2, (102)–(103)).
    SBJV complement → intention: "Wendy convenció a Paula de que le pidiera
      un aumento al jefe" (SBJV)
    IND complement → belief: "Alice convenció a Emily de que estaba
      diciendo la verdad" (IND) -/
def convencer : Verb where
  form := "convencer"
  frames := [ArgumentFrame.infinitival, ArgumentFrame.finiteClause]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .objectControl }]
  opaqueContext := true

-- ════════════════════════════════════════════════════════════════
-- Bridge Theorems
-- ════════════════════════════════════════════════════════════════

theorem hacer_is_causative :
    hacer.causative.isSome = true := rfl

end Spanish.MoodChoice
