import Linglib.Semantics.Verb.Basic

/-!
# Greek Mood-Choice Verb Entries [grano-2024]

Minimal verb entries for Modern Greek attitude and causative predicates
relevant to cross-linguistic mood choice ([grano-2024], Table 1).

In Greek, mood is reflected in complementizer choice (*na* = SBJV vs
*oti* = IND) rather than verb inflection. Greek lacks nonfinite
complementation. 'want' and 'intend' take *na* (SBJV); 'hope' allows
both *na* and *oti* (IND/SBJV). Causatives take *na* (SBJV).

## Key examples (from [grano-2024])

- (5) Thelo **na**/\*oti kerdisi o Janis. ('want': SBJV/\*IND)
- (13) Elpizo **na**/oti kerdise o Janis. ('hope': SBJV/IND)
- (22) I Ariadne protithete **na**/\*oti fiji noris. ('intend': SBJV/\*IND)
- (45a) Evala ton Jani **na** pai sto parko. ('make': SBJV)
-/

namespace Greek.StandardModern.MoodChoice

open Semantics.Lexical

/-- *thélo* (θέλω) 'want' — robustly subjunctive-selecting via *na*.
    [grano-2024], (5): *na* (SBJV) required, *oti* (IND) rejected.
    Cited from [giannakidou-mari-2021]. -/
def thelo : Verb where
  form := "thélo"
  frames := [Frame.finiteClause]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))
  levinClass := some .want

/-- *elpízo* (ελπίζω) 'hope' — accepts both *na* (SBJV) and *oti* (IND).
    [grano-2024], (13): both complementizers accepted.
    Cited from [giannakidou-mari-2021]. -/
def elpizo : Verb where
  form := "elpízo"
  frames := [Frame.finiteClause]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))

/-- *protíthete* (προτίθεται) 'intend' — robustly rejects indicative.
    [grano-2024], (22): *na* (SBJV) required, *oti* (IND) rejected.
    Cited from [giannakidou-mari-2021]. -/
def protithete : Verb where
  form := "protíthete"
  frames := [Frame.finiteClause]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))
  levinClass := some .want

/-- *vázo* (βάζω) 'put/make' — causative, subjunctive-selecting via *na*.
    [grano-2024], (45): *na* (SBJV) required, *oti* (IND) rejected.
    Past tense form *évala* used in the paper's examples. -/
def vazo : Verb where
  form := "vázo"
  frames := [Frame.finiteClause]
  readings := [{ frame := Frame.finiteClause, control := some .objectControl }]
  causative := some .make

-- ════════════════════════════════════════════════════════════════
-- Bridge Theorems
-- ════════════════════════════════════════════════════════════════

theorem thelo_is_want_class :
    thelo.levinClass = some .want := rfl

theorem elpizo_not_want_class :
    elpizo.levinClass ≠ some .want := by decide

theorem protithete_is_want_class :
    protithete.levinClass = some .want := rfl

theorem vazo_is_causative :
    vazo.causative.isSome = true := rfl

/-- Greek mood is via complementizer (*na* vs *oti*), not verb morphology.
    All four predicates take finite clause complements (no infinitivals). -/
theorem greek_all_finite :
    thelo.complementType = .finiteClause ∧
    elpizo.complementType = .finiteClause ∧
    protithete.complementType = .finiteClause ∧
    vazo.complementType = .finiteClause := ⟨rfl, rfl, rfl, rfl⟩

end Greek.StandardModern.MoodChoice
