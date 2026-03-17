import Linglib.Theories.Semantics.Lexical.Verb.VerbEntry

/-!
# Greek Mood-Choice Verb Entries @cite{grano-2024}

Minimal verb entries for Modern Greek attitude and causative predicates
relevant to cross-linguistic mood choice (@cite{grano-2024}, Table 1).

In Greek, mood is reflected in complementizer choice (*na* = SBJV vs
*oti* = IND) rather than verb inflection. Greek lacks nonfinite
complementation. 'want' and 'intend' take *na* (SBJV); 'hope' allows
both *na* and *oti* (IND/SBJV). Causatives take *na* (SBJV).

## Key examples (from @cite{grano-2024})

- (5) Thelo **na**/\*oti kerdisi o Janis. ('want': SBJV/\*IND)
- (13) Elpizo **na**/oti kerdise o Janis. ('hope': SBJV/IND)
- (22) I Ariadne protithete **na**/\*oti fiji noris. ('intend': SBJV/\*IND)
- (45a) Evala ton Jani **na** pai sto parko. ('make': SBJV)
-/

namespace Fragments.Greek.MoodChoice

open Core.Verbs

/-- *thélo* (θέλω) 'want' — robustly subjunctive-selecting via *na*.
    @cite{grano-2024}, (5): *na* (SBJV) required, *oti* (IND) rejected.
    Cited from @cite{giannakidou-mari-2021}. -/
def thelo : VerbCore where
  form := "thélo"
  complementType := .finiteClause
  passivizable := false
  opaqueContext := true
  attitudeBuilder := some (.preferential (.degreeComparison .positive))
  levinClass := some .want

/-- *elpízo* (ελπίζω) 'hope' — accepts both *na* (SBJV) and *oti* (IND).
    @cite{grano-2024}, (13): both complementizers accepted.
    Cited from @cite{giannakidou-mari-2021}. -/
def elpizo : VerbCore where
  form := "elpízo"
  complementType := .finiteClause
  passivizable := false
  opaqueContext := true
  attitudeBuilder := some (.preferential (.degreeComparison .positive))

/-- *protíthete* (προτίθεται) 'intend' — robustly rejects indicative.
    @cite{grano-2024}, (22): *na* (SBJV) required, *oti* (IND) rejected.
    Cited from @cite{giannakidou-mari-2021}. -/
def protithete : VerbCore where
  form := "protíthete"
  complementType := .finiteClause
  passivizable := false
  opaqueContext := true
  attitudeBuilder := some (.preferential (.degreeComparison .positive))
  levinClass := some .want

/-- *vázo* (βάζω) 'put/make' — causative, subjunctive-selecting via *na*.
    @cite{grano-2024}, (45): *na* (SBJV) required, *oti* (IND) rejected.
    Past tense form *évala* used in the paper's examples. -/
def vazo : VerbCore where
  form := "vázo"
  complementType := .finiteClause
  controlType := .objectControl
  causativeBuilder := some .make

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
    vazo.causativeBuilder.isSome = true := rfl

/-- Greek mood is via complementizer (*na* vs *oti*), not verb morphology.
    All four predicates take finite clause complements (no infinitivals). -/
theorem greek_all_finite :
    thelo.complementType = .finiteClause ∧
    elpizo.complementType = .finiteClause ∧
    protithete.complementType = .finiteClause ∧
    vazo.complementType = .finiteClause := ⟨rfl, rfl, rfl, rfl⟩

end Fragments.Greek.MoodChoice
