import Linglib.Syntax.Category.Verb.Basic

/-!
# Portuguese Mood-Choice Verb Entries [grano-2024]

Minimal verb entries for Portuguese attitude and causative predicates
relevant to cross-linguistic mood choice ([grano-2024], Table 1).

Portuguese 'want' robustly takes SBJV; 'hope' allows both IND and SBJV;
'intend' takes SBJV. Causatives reject indicative.

## Key examples (from [grano-2024])

- (3a) João quer que a Maria **esteja**/\*está feliz. (SBJV/\*IND)
- (11) João espera que a Maria **esteja**/está feliz. (SBJV/IND)
- (26) Pretendo que o João **vá**/\*vai/\*irá ao parque. (SBJV/\*IND)
- (41) Eu fiz com que João **fosse**/\*foi ao parque. (SBJV/\*IND)
-/

namespace Portuguese.MoodChoice

open ArgumentStructure

/-- *querer* 'want' — robustly subjunctive-selecting.
    [grano-2024], (3a): SBJV required. -/
def querer : Verb where
  form := "querer"
  frames := [ArgumentFrame.finiteClause, ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.finiteClause, control := some .subjectControl }]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))

/-- *esperar* 'hope' — cross-linguistically variable (IND/SBJV).
    [grano-2024], (11): both IND and SBJV accepted. -/
def esperar : Verb where
  form := "esperar"
  frames := [ArgumentFrame.finiteClause, ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.finiteClause, control := some .subjectControl }]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))

/-- *pretender* 'intend' — robustly rejects indicative.
    [grano-2024], (26): SBJV required, IND rejected. -/
def pretender : Verb where
  form := "pretender"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))

/-- *fazer* 'make' — causative, rejects indicative.
    [grano-2024], (41): SBJV required via *com que*, IND rejected. -/
def fazer : Verb where
  form := "fazer"
  frames := [ArgumentFrame.infinitival, ArgumentFrame.finiteClause]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .objectControl }]
  causative := some .make

-- ════════════════════════════════════════════════════════════════
-- Bridge Theorems
-- ════════════════════════════════════════════════════════════════

theorem fazer_is_causative :
    fazer.causative.isSome = true := rfl

end Portuguese.MoodChoice
