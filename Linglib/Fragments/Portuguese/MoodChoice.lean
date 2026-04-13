import Linglib.Theories.Semantics.Lexical.Verb.VerbEntry

/-!
# Portuguese Mood-Choice Verb Entries @cite{grano-2024}

Minimal verb entries for Portuguese attitude and causative predicates
relevant to cross-linguistic mood choice (@cite{grano-2024}, Table 1).

Portuguese 'want' robustly takes SBJV; 'hope' allows both IND and SBJV;
'intend' takes SBJV. Causatives reject indicative.

## Key examples (from @cite{grano-2024})

- (3a) João quer que a Maria **esteja**/\*está feliz. (SBJV/\*IND)
- (11) João espera que a Maria **esteja**/está feliz. (SBJV/IND)
- (26) Pretendo que o João **vá**/\*vai/\*irá ao parque. (SBJV/\*IND)
- (41) Eu fiz com que João **fosse**/\*foi ao parque. (SBJV/\*IND)
-/

namespace Fragments.Portuguese.MoodChoice

open Core.Verbs

/-- *querer* 'want' — robustly subjunctive-selecting.
    @cite{grano-2024}, (3a): SBJV required. -/
def querer : VerbCore where
  form := "querer"
  complementType := .finiteClause
  controlType := .subjectControl
  altComplementType := some .infinitival
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))
  levinClass := some .want

/-- *esperar* 'hope' — cross-linguistically variable (IND/SBJV).
    @cite{grano-2024}, (11): both IND and SBJV accepted. -/
def esperar : VerbCore where
  form := "esperar"
  complementType := .finiteClause
  controlType := .subjectControl
  altComplementType := some .infinitival
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))

/-- *pretender* 'intend' — robustly rejects indicative.
    @cite{grano-2024}, (26): SBJV required, IND rejected. -/
def pretender : VerbCore where
  form := "pretender"
  complementType := .infinitival
  controlType := .subjectControl
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))
  levinClass := some .want

/-- *fazer* 'make' — causative, rejects indicative.
    @cite{grano-2024}, (41): SBJV required via *com que*, IND rejected. -/
def fazer : VerbCore where
  form := "fazer"
  complementType := .infinitival
  controlType := .objectControl
  altComplementType := some .finiteClause
  causative := some .make

-- ════════════════════════════════════════════════════════════════
-- Bridge Theorems
-- ════════════════════════════════════════════════════════════════

theorem querer_is_want_class :
    querer.levinClass = some .want := rfl

theorem esperar_not_want_class :
    esperar.levinClass ≠ some .want := by decide

theorem pretender_is_want_class :
    pretender.levinClass = some .want := rfl

theorem fazer_is_causative :
    fazer.causative.isSome = true := rfl

end Fragments.Portuguese.MoodChoice
