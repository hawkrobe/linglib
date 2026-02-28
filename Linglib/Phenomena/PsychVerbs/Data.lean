import Linglib.Core.Empirical

/-!
# Psych Verb Data (B&R 1988, Kim 2024)

@cite{belletti-rizzi-1988} @cite{kim-2024}

Theory-neutral empirical data on psych verbs from Belletti & Rizzi (1988)
and Kim (2024).

## Belletti & Rizzi (1988) classification

| Class | Subject | Object | Example |
|-------|---------|--------|---------|
| I | experiencer | theme | "Mary enjoys jazz" / It. *temere* |
| II | stimulus/cause | experiencer | "Jazz interests Mary" / It. *preoccupare* |
| III | (dative experiencer) | | It. "A Gianni piace la musica" |

## B&R syntactic diagnostics (§§1–2)

The Class I/II split is diagnosed by five syntactic tests:
1. **Anaphoric cliticization** (§1.1): Class II allows partitive *ne* from subject;
   Class I does not
2. **Arbitrary pro** (§1.2): Class I allows arb pro subject; Class II does not
3. **Causative fare** (§1.3): Class I embeds under *fare* infinitive; Class II does not
   (but see caveat: *preoccupare*-class verbs embed under *fare* due to independent
   unaccusative representation, B&R ex. 37)
4. **Backward binding** (§2.1): Class II allows object-to-subject binding; Class I does not
5. **Passive type** (§1.5): Class II passive is adjectival; Class I is verbal

## Kim (2024) diagnostics

Kim extends B&R with two further diagnostics on the *within*-Class II split:
5. **Intensionality** (Ch. 4): Stative Class II verbs create intensional
   subject positions; eventive Class II verbs do not
6. **T/SM restriction** (Ch. 5): Cause and Subject Matter cannot cooccur
-/

namespace Phenomena.PsychVerbs.Data

/-- Belletti & Rizzi (1988) classification of psych verbs. -/
inductive PsychVerbClass where
  | classI    -- Experiencer-subject: enjoy, like, fear / It. temere
  | classII   -- Object-experiencer: frighten, concern / It. preoccupare
  | classIII  -- Dative experiencer (Romance): It. piacere
  deriving DecidableEq, Repr, BEq

/-- Aspectual reading of a Class II psych verb (Kim 2024). -/
inductive ClassIIReading where
  | eventive  -- External cause: "the noise frightened John"
  | stative   -- Internal cause: "the problem concerns John"
  deriving DecidableEq, Repr, BEq

-- ════════════════════════════════════════════════════
-- § B&R (1988) Syntactic Diagnostics
-- ════════════════════════════════════════════════════

/-- B&R syntactic diagnostic for discriminating psych verb classes (§§1–2). -/
inductive BRDiagnostic where
  | anaphoricCliticization -- §1.1: partitive ne extraction from subject
  | arbitraryPro           -- §1.2: arb pro interpretation of subject
  | causativeFare          -- §1.3: embedding under fare/make infinitive
  | backwardBinding        -- §2.1: anaphor in subject bound by object
  | adjectivalPassive      -- §1.5: passive is adjectival (not verbal)
  deriving DecidableEq, Repr, BEq

/-- Result of a B&R diagnostic applied to each class.
    `classI`/`classII` record whether the class *passes* the test. -/
structure BRDiagnosticResult where
  diagnostic : BRDiagnostic
  classI : Bool
  classII : Bool
  deriving Repr, BEq

/-- B&R (1988) diagnostic data.

    | Diagnostic | Class I (*temere*) | Class II (*preoccupare*) |
    |---|---|---|
    | Anaphoric clitic *ne* (§1.1) | ✗ | ✓ (11a) |
    | Arbitrary *pro* (§1.2) | ✓ (24a) | ✗ (24b) |
    | Causative *fare* (§1.3) | ✓ (35) | ✗ (36) |
    | Backward binding (§2.1) | ✗ | ✓ (57a) |
    | Adjectival passive (§1.5) | ✗ | ✓ (47) | -/
def brDiagnosticData : List BRDiagnosticResult := [
  ⟨.anaphoricCliticization, false, true⟩,  -- Class II allows ne; Class I doesn't (11a)
  ⟨.arbitraryPro,           true,  false⟩,  -- Class I allows arb pro; Class II doesn't (24a/b)
  ⟨.causativeFare,          true,  false⟩,  -- Class I embeds under fare; Class II doesn't (35/36)
  ⟨.backwardBinding,        false, true⟩,   -- Class II allows backward binding (57a)
  ⟨.adjectivalPassive,      false, true⟩    -- Class II passive is adjectival (47)
]

/-- Every B&R diagnostic discriminates Class I from Class II:
    the two classes never give the same result on any test. -/
theorem br_diagnostics_discriminate :
    brDiagnosticData.all (fun d => d.classI != d.classII) = true := by native_decide

/-- Class I passes arb-pro and causative-fare but fails the other three. -/
theorem classI_pattern :
    brDiagnosticData.all (fun d =>
      match d.diagnostic with
      | .anaphoricCliticization => d.classI == false
      | .arbitraryPro => d.classI == true
      | .causativeFare => d.classI == true
      | .backwardBinding => d.classI == false
      | .adjectivalPassive => d.classI == false
    ) = true := by native_decide

/-- Class II shows the mirror pattern: passes ne-cliticization, backward
    binding, and adjectival passive; fails arb-pro and causative-fare. -/
theorem classII_pattern :
    brDiagnosticData.all (fun d =>
      match d.diagnostic with
      | .anaphoricCliticization => d.classII == true
      | .arbitraryPro => d.classII == false
      | .causativeFare => d.classII == false
      | .backwardBinding => d.classII == true
      | .adjectivalPassive => d.classII == true
    ) = true := by native_decide

-- ════════════════════════════════════════════════════
-- § Theta-Role Reversal
-- ════════════════════════════════════════════════════

/-- The Class I/II distinction is characterized by theta-role reversal:
    Class I maps experiencer to subject, Class II maps experiencer to object.

    | Position | Class I | Class II |
    |----------|---------|----------|
    | Subject  | experiencer | stimulus |
    | Object   | stimulus/theme | experiencer | -/
inductive SubjectRole where
  | experiencer  -- Class I: subject = experiencer
  | stimulus     -- Class II: subject = stimulus/cause
  deriving DecidableEq, Repr, BEq

/-- Map from B&R class to expected subject role. -/
def PsychVerbClass.expectedSubjectRole : PsychVerbClass → Option SubjectRole
  | .classI => some .experiencer
  | .classII => some .stimulus
  | .classIII => none  -- dative experiencer, not captured by nom/acc pattern

/-- Intensionality datum: does substitution of co-referential terms fail
    in subject position?

    - Stative "concern": "Cicero concerns Mary" ≠ "Tully concerns Mary"
      (can differ in truth value — substitution fails)
    - Eventive "frighten": "Cicero frightened Mary" = "Tully frightened Mary"
      (same truth value — substitution succeeds) -/
structure IntensionalityDatum where
  verb : String
  reading : ClassIIReading
  substitutionFails : Bool
  deriving Repr, BEq

/-- Empirical intensionality data from Kim (2024, Ch. 4). -/
def intensionalityData : List IntensionalityDatum := [
  ⟨"concern", .stative, true⟩,
  ⟨"interest", .stative, true⟩,
  ⟨"frighten", .eventive, false⟩,
  ⟨"amuse", .eventive, false⟩
]

/-- The T/SM restriction: Cause and Subject Matter cannot cooccur.

    *"The noise about the deadline concerned John"
    — both "the noise" (Cause) and "about the deadline" (SM) present → ill-formed.

    This follows from the Onset Condition: both map to the onset position
    of the causal chain, but only one slot is available. -/
structure TSMRestriction where
  causePresent : Bool
  smPresent : Bool
  wellFormed : Bool
  deriving Repr, BEq

/-- Cause and SM cannot cooccur (Kim 2024, Ch. 5). -/
def tsmData : List TSMRestriction := [
  ⟨true, false, true⟩,    -- Cause only: ✓ "The noise concerned John"
  ⟨false, true, true⟩,    -- SM only: ✓ "John was concerned about the deadline"
  ⟨true, true, false⟩,    -- Both: ✗ *"The noise about the deadline concerned John"
  ⟨false, false, true⟩    -- Neither: ✓ "John was concerned"
]

/-- Stative Class II verbs create intensional subject positions. -/
theorem stative_substitution_fails :
    (intensionalityData.filter (·.reading == .stative)).all
      (·.substitutionFails) = true := by native_decide

/-- Eventive Class II verbs have extensional subject positions. -/
theorem eventive_substitution_succeeds :
    (intensionalityData.filter (·.reading == .eventive)).all
      (!·.substitutionFails) = true := by native_decide

/-- Cause + SM cooccurrence is always ill-formed. -/
theorem cause_sm_cooccurrence_illformed :
    (tsmData.filter (fun d => d.causePresent && d.smPresent)).all
      (!·.wellFormed) = true := by native_decide

end Phenomena.PsychVerbs.Data
