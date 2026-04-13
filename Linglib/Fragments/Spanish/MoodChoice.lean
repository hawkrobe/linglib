import Linglib.Theories.Semantics.Lexical.Verb.VerbEntry

/-!
# Spanish Mood-Choice Verb Entries @cite{grano-2024}

Minimal verb entries for Spanish attitude and causative predicates
relevant to cross-linguistic mood choice (@cite{grano-2024}, Table 1).

Spanish robustly rejects indicative under 'want', 'hope', 'intend',
and 'make' — all four take subjunctive or nonfinite complements.

## Key examples (from @cite{grano-2024})

- (1a) Victoria quiere que Marcela **venga**/\*viene al picnic. (SBJV/\*IND)
- (9) Espero que mi hermano **viniera**/\*vino ayer. (SBJV/\*IND)
- (25) Tengo la intención de que Juan **vaya**/\*va/\*irá al parque hoy. (SBJV)
- (40) Hice que Juan **fuera**/\*fue al parque. (SBJV/\*IND)
-/

namespace Fragments.Spanish.MoodChoice

open Core.Verbs

/-- *querer* 'want' — robustly subjunctive-selecting.
    @cite{grano-2024}, (1a): SBJV required, IND rejected. -/
def querer : VerbCore where
  form := "querer"
  complementType := .finiteClause
  controlType := .subjectControl
  altComplementType := some .infinitival
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))
  levinClass := some .want

/-- *esperar* 'hope' — subjunctive in Spanish (unlike Portuguese/French).
    @cite{grano-2024}, (9): SBJV required, IND rejected. -/
def esperar : VerbCore where
  form := "esperar"
  complementType := .finiteClause
  controlType := .subjectControl
  altComplementType := some .infinitival
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))

/-- *tener la intención (de)* 'intend' — robustly rejects indicative.
    @cite{grano-2024}, (25): SBJV required in non-control complements.
    Periphrastic form (nominal predicate). -/
def tener_la_intencion : VerbCore where
  form := "tener la intención"
  complementType := .infinitival
  controlType := .subjectControl
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))
  levinClass := some .want

/-- *hacer* 'make' — causative, robustly subjunctive-selecting.
    @cite{grano-2024}, (40): SBJV required, IND rejected.
    Infinitival complements with object control. -/
def hacer : VerbCore where
  form := "hacer"
  complementType := .infinitival
  controlType := .objectControl
  altComplementType := some .finiteClause
  causative := some .make

/-- *convencer* 'convince' — hybrid predicate (§6.2, (102)–(103)).
    SBJV complement → intention: "Wendy convenció a Paula de que le pidiera
      un aumento al jefe" (SBJV)
    IND complement → belief: "Alice convenció a Emily de que estaba
      diciendo la verdad" (IND) -/
def convencer : VerbCore where
  form := "convencer"
  complementType := .infinitival
  controlType := .objectControl
  altComplementType := some .finiteClause
  opaqueContext := true

-- ════════════════════════════════════════════════════════════════
-- Bridge Theorems
-- ════════════════════════════════════════════════════════════════

theorem querer_is_want_class :
    querer.levinClass = some .want := rfl

theorem esperar_not_want_class :
    esperar.levinClass ≠ some .want := by decide

theorem tener_la_intencion_is_want_class :
    tener_la_intencion.levinClass = some .want := rfl

theorem hacer_is_causative :
    hacer.causative.isSome = true := rfl

/-- Spanish mood asymmetry: querer and tener la intención share want-class;
    esperar does not. Unlike Portuguese/French/Italian, Spanish 'hope' ALSO
    robustly rejects IND (Table 1), so the asymmetry is structural, not
    empirically visible in mood choice. -/
theorem spanish_mood_asymmetry :
    querer.levinClass = some .want ∧
    tener_la_intencion.levinClass = some .want ∧
    esperar.levinClass ≠ some .want := by
  exact ⟨rfl, rfl, by decide⟩

end Fragments.Spanish.MoodChoice
