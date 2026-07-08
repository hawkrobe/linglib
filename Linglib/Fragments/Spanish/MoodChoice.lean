import Linglib.Semantics.Verb.Basic

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
  frames := [Frame.finiteClause, Frame.infinitival]
  readings := [{ frame := Frame.finiteClause, control := some .subjectControl }]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))
  levinClass := some .want

/-- *esperar* 'hope' — subjunctive in Spanish (unlike Portuguese/French).
    [grano-2024], (9): SBJV required, IND rejected. -/
def esperar : Verb where
  form := "esperar"
  frames := [Frame.finiteClause, Frame.infinitival]
  readings := [{ frame := Frame.finiteClause, control := some .subjectControl }]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))

/-- *tener la intención (de)* 'intend' — robustly rejects indicative.
    [grano-2024], (25): SBJV required in non-control complements.
    Periphrastic form (nominal predicate). -/
def tener_la_intencion : Verb where
  form := "tener la intención"
  frames := [Frame.infinitival]
  readings := [{ frame := Frame.infinitival, control := some .subjectControl }]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))
  levinClass := some .want

/-- *hacer* 'make' — causative, robustly subjunctive-selecting.
    [grano-2024], (40): SBJV required, IND rejected.
    Infinitival complements with object control. -/
def hacer : Verb where
  form := "hacer"
  frames := [Frame.infinitival, Frame.finiteClause]
  readings := [{ frame := Frame.infinitival, control := some .objectControl }]
  causative := some .make

/-- *convencer* 'convince' — hybrid predicate (§6.2, (102)–(103)).
    SBJV complement → intention: "Wendy convenció a Paula de que le pidiera
      un aumento al jefe" (SBJV)
    IND complement → belief: "Alice convenció a Emily de que estaba
      diciendo la verdad" (IND) -/
def convencer : Verb where
  form := "convencer"
  frames := [Frame.infinitival, Frame.finiteClause]
  readings := [{ frame := Frame.infinitival, control := some .objectControl }]
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

end Spanish.MoodChoice
