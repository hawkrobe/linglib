import Linglib.Core.Semantics.CommonGround
import Linglib.Core.Lexical.Word

/-!
# Romero & Han (2004): Negative Yes/No Questions and Epistemic Bias
@cite{romero-han-2004} @cite{ladd-1981}

## Core Contribution

Preposed negation in yes/no questions forces an epistemic implicature via
the VERUM operator (FOR-SURE-CG). Ladd's PI/NI ambiguity is scope ambiguity:

- PI: [Q [not [VERUM [p]]]] → speaker believes p, double-checking
- NI: [Q [VERUM [not [p]]]] → speaker believes ¬p, double-checking

The VERUM operator is the conversational-epistemic mechanism:

  FOR-SURE-CG_x(p) = ∀w' ∈ Epi_x(w)[∀w'' ∈ Conv_x(w')[p ∈ CG_w'']]

"For all worlds compatible with x's knowledge, for all worlds compatible
with x's conversational goals, p is in the Common Ground." Short form:
"It is for sure that we should add p to the CG."

## Results

1. VERUM creates unbalanced partitions: {FOR-SURE-CG(p), ¬FOR-SURE-CG(p)}
   rather than {p, ¬p}.
2. Ladd's PI/NI ambiguity is scope ambiguity over VERUM and negation.
3. Epistemic implicature follows from intent/pronunciation:
   - Asserting ¬FOR-SURE-CG(p) (PI) implicates belief in p
   - Asserting FOR-SURE-CG(¬p) (NI) implicates belief in ¬p

## Related Work

- `Phenomena/Questions/Studies/Holmberg2016.lean` — complementary analysis.
  R&H explains the *structural source of bias* (preposed negation forces
  an epistemic expectation via VERUM); Holmberg explains *cross-linguistic
  answer variation* (the [±Pol] feature, negation height). Both agree
  that negative questions denote an unbalanced partition; R&H derives
  this from VERUM scope, Holmberg from negation-height + [±Pol].
- van Rooy & Šafářová (2003) decision-theoretic complement: vR&Š
  explain *which* polar question to use; R&H explain *why* certain
  forms have bias. (Apparatus deleted in Bool/List → Prop/Set
  migration; reinstate in Prop/Set form when needed.)
- `Theories/Syntax/Minimalism/Polarity.lean` — the [±Pol] feature.
-/

namespace RomeroHan2004

-- ════════════════════════════════════════════════════════════════
-- § 1. VERUM apparatus (formal mechanism)
-- ════════════════════════════════════════════════════════════════

namespace Verum

-- Part 1.1: Epistemic and Conversational States

/-- A world type with Common Ground -/
structure CGWorld (W : Type*) where
  /-- The possible world -/
  world : W
  /-- The Common Ground at this world (set of propositions) -/
  cg : List (W → Bool)

/-- Epistemic accessibility: worlds compatible with agent's knowledge -/
abbrev EpistemicAccessibility (W : Type*) := W → W → Bool

/-- Conversational accessibility: worlds compatible with agent's conversational goals -/
abbrev ConversationalAccessibility (W : Type*) := W → W → Bool

/-- Full modal frame for VERUM semantics -/
structure VerumFrame (W : Type*) where
  /-- Set of worlds -/
  worlds : List W
  /-- Epistemic accessibility (Epi_x) -/
  epiAccessible : EpistemicAccessibility W
  /-- Conversational accessibility (Conv_x) -/
  convAccessible : ConversationalAccessibility W
  /-- Common Ground function: for each world, what's in the CG -/
  commonGround : W → List (W → Bool)

-- Part 1.2: The VERUM Operator

/-- FOR-SURE-CG: The VERUM operator.

∀w' ∈ Epi_x(w)[∀w'' ∈ Conv_x(w')[p ∈ CG_w'']]

For all epistemic alternatives w', for all conversational alternatives w'',
p is in the Common Ground at w''.

This captures: "It is for sure that we should add p to the CG."
-/
def forSureCG {W : Type*} (frame : VerumFrame W)
    (w : W) (p : W → Bool) : Bool :=
  frame.worlds.all λ w' =>
    if frame.epiAccessible w w' then
      frame.worlds.all λ w'' =>
        if frame.convAccessible w' w'' then
          (frame.commonGround w'').any λ q =>
            frame.worlds.all λ v => p v == q v  -- p ∈ CG means p equals some CG proposition
        else true
    else true

/-- Simplified VERUM for finite models -/
def verum {W : Type*} [DecidableEq W]
    (cgMembership : W → (W → Bool) → Bool)  -- Is p in CG at w?
    (epiWorlds : W → List W)                 -- Epi_x(w)
    (convWorlds : W → List W)                -- Conv_x(w')
    (w : W) (p : W → Bool) : Bool :=
  (epiWorlds w).all λ w' =>
    (convWorlds w').all λ w'' =>
      cgMembership w'' p

-- Part 1.3: Unbalanced Partitions

/-- A polar question partition -/
structure QuestionPartition (W : Type*) where
  /-- The two cells of the partition -/
  cell1 : W → Bool
  cell2 : W → Bool
  /-- Which cell is "pronounced" (the surface form asks about) -/
  pronounced : W → Bool

/-- Standard balanced polar question: {p, ¬p} -/
def balancedQuestion {W : Type*} (p : W → Bool) : QuestionPartition W := {
  cell1 := p
  cell2 := λ w => !p w
  pronounced := p
}

/-- Unbalanced VERUM question: {FOR-SURE-CG(p), ¬FOR-SURE-CG(p)}

When VERUM is present, the partition is about epistemic commitment
to CG membership, not about p's truth directly.
-/
def verumQuestion {W : Type*} [DecidableEq W]
    (cgMembership : W → (W → Bool) → Bool)
    (epiWorlds : W → List W)
    (convWorlds : W → List W)
    (p : W → Bool)
    (pronounceNeg : Bool)  -- true for PI, false for NI
    : QuestionPartition W := {
  cell1 := λ w => verum cgMembership epiWorlds convWorlds w p
  cell2 := λ w => !verum cgMembership epiWorlds convWorlds w p
  pronounced := if pronounceNeg
    then λ w => !verum cgMembership epiWorlds convWorlds w p  -- PI: ¬FOR-SURE-CG(p)
    else λ w => verum cgMembership epiWorlds convWorlds w p   -- NI: FOR-SURE-CG(p)
}

-- Part 1.4: Ladd's Ambiguity (PI vs NI)

/-- Reading type for negative polar questions -/
inductive NegQuestionReading where
  | PI : NegQuestionReading  -- Positive-implicature (double-check p)
  | NI : NegQuestionReading  -- Negative-implicature (double-check ¬p)
  deriving Repr, DecidableEq

/-- LF structure for negative polar questions -/
inductive NegQuestionLF (W : Type*) where
  /-- PI: [Q [not [VERUM [p]]]] -/
  | piLF : (W → Bool) → NegQuestionLF W
  /-- NI: [Q [VERUM [not [p]]]] -/
  | niLF : (W → Bool) → NegQuestionLF W

/-- Extract the embedded proposition -/
def NegQuestionLF.proposition {W : Type*} : NegQuestionLF W → (W → Bool)
  | .piLF p => p
  | .niLF p => p

/-- Get the reading type -/
def NegQuestionLF.reading {W : Type*} : NegQuestionLF W → NegQuestionReading
  | .piLF _ => .PI
  | .niLF _ => .NI

/-- Interpret a negative question LF as a partition

- PI: {¬FOR-SURE-CG(p), FOR-SURE-CG(p)}
- NI: {FOR-SURE-CG(¬p), ¬FOR-SURE-CG(¬p)}
-/
def interpretNegQuestion {W : Type*} [DecidableEq W]
    (cgMembership : W → (W → Bool) → Bool)
    (epiWorlds : W → List W)
    (convWorlds : W → List W)
    (lf : NegQuestionLF W) : QuestionPartition W :=
  match lf with
  | .piLF p =>
    -- PI: asking about ¬FOR-SURE-CG(p)
    verumQuestion cgMembership epiWorlds convWorlds p true
  | .niLF p =>
    -- NI: VERUM scopes over negation, asking about FOR-SURE-CG(¬p)
    let notP : W → Bool := λ w => !p w
    verumQuestion cgMembership epiWorlds convWorlds notP false

-- Part 1.5: Epistemic Implicature

/-- Speaker's prior epistemic state -/
structure SpeakerEpistemicState (W : Type*) where
  /-- Worlds compatible with speaker's beliefs -/
  beliefWorlds : List W
  /-- Does speaker believe p? -/
  believes : (W → Bool) → Bool

/-- Implicature from pronounced cell

The pronounced cell of a VERUM question implicates the speaker's
prior belief:
- PI pronounces ¬FOR-SURE-CG(p) → implicates belief in p
- NI pronounces FOR-SURE-CG(¬p) → implicates belief in ¬p
-/
def epistemicImplicature {W : Type*}
    (reading : NegQuestionReading)
    (_p : W → Bool) : String :=
  match reading with
  | .PI => "Speaker believes p (expected 'yes')"
  | .NI => "Speaker believes ¬p (expected 'no')"

/-- Derive the implicature direction -/
def implicaturePolarity (reading : NegQuestionReading) : String :=
  match reading with
  | .PI => "positive"
  | .NI => "negative"

-- Part 1.6: Polarity Item Licensing

/-- Polarity item type -/
inductive PolarityItem where
  | PPI : String → PolarityItem  -- too, some, already
  | NPI : String → PolarityItem  -- either, any, yet
  deriving Repr, DecidableEq

/-- Check if polarity item is licensed under a reading

- PPIs licensed under PI reading (in scope of ¬FOR-SURE-CG)
- NPIs licensed under NI reading (in scope of VERUM over negation)
-/
def isLicensed (item : PolarityItem) (reading : NegQuestionReading) : Bool :=
  match item, reading with
  | .PPI _, .PI => true   -- PPIs licensed under PI
  | .NPI _, .NI => true   -- NPIs licensed under NI
  | .PPI _, .NI => false  -- PPIs not licensed under NI
  | .NPI _, .PI => false  -- NPIs not licensed under PI

/-- Common polarity items -/
def too : PolarityItem := .PPI "too"
def some_ : PolarityItem := .PPI "some"
def already : PolarityItem := .PPI "already"
def either : PolarityItem := .NPI "either"
def any : PolarityItem := .NPI "any"
def yet : PolarityItem := .NPI "yet"

/-- Ladd's generalization: PPIs → PI, NPIs → NI -/
theorem ppi_implies_pi (item : PolarityItem) (reading : NegQuestionReading) :
    isLicensed item reading = true →
    match item with
    | .PPI _ => reading = .PI
    | .NPI _ => reading = .NI := by
  intro h
  cases item <;> cases reading <;> simp [isLicensed] at h ⊢

-- Part 1.7: VERUM Sources

/-- Sources that contribute VERUM to the LF -/
inductive VerumSource where
  /-- Preposed negation: "Doesn't John..." -/
  | preposedNegation : VerumSource
  /-- The adverb "really": "Does John really..." -/
  | reallyAdverb : VerumSource
  /-- Focus on auxiliary: "DOES John..." -/
  | auxiliaryFocus : VerumSource
  /-- Focus on negation: "Does John NOT..." -/
  | negationFocus : VerumSource
  deriving Repr, DecidableEq

/-- Does this source necessarily trigger VERUM? -/
def necessarilyTriggersVerum : VerumSource → Bool
  | .preposedNegation => true   -- always triggers VERUM
  | .reallyAdverb => true       -- always triggers VERUM
  | .auxiliaryFocus => true     -- always triggers VERUM
  | .negationFocus => true      -- always triggers VERUM

/-- Romero & Han's Generalization 1 -/
theorem preposed_negation_forces_verum :
    necessarilyTriggersVerum .preposedNegation = true := rfl

end Verum

-- ════════════════════════════════════════════════════════════════
-- § 2. Negative question data
-- ════════════════════════════════════════════════════════════════

open Verum

/-- A negative question datum records epistemic bias. -/
structure NegativeQuestionDatum where
  /-- The sentence -/
  sentence : String
  /-- Negation position -/
  negationPosition : String  -- "preposed", "non_preposed", "none"
  /-- Epistemic bias (positive, negative, or none) -/
  epistemicBias : Option String
  /-- Notes -/
  notes : String := ""
  deriving Repr

/-- Preposed negation forces positive bias. -/
def preposedNegation : NegativeQuestionDatum :=
  { sentence := "Doesn't John drink?"
  , negationPosition := "preposed"
  , epistemicBias := some "positive"
  , notes := "Preposed negation forces positive bias. Speaker expected 'yes'."
  }

/-- Non-preposed negation allows neutral reading. -/
def nonPreposedNegation : NegativeQuestionDatum :=
  { sentence := "Does John not drink?"
  , negationPosition := "non_preposed"
  , epistemicBias := none
  , notes := "Non-preposed negation: neutral information-seeking question possible."
  }

/-- Adverb "really" triggers positive bias. -/
def reallyBias : NegativeQuestionDatum :=
  { sentence := "Does John really drink?"
  , negationPosition := "none"
  , epistemicBias := some "positive"
  , notes := "'Really' signals speaker checking expected positive answer."
  }

/-- Preposed negation necessarily triggers VERUM (bridge to Verum apparatus). -/
theorem preposed_triggers_verum :
    necessarilyTriggersVerum .preposedNegation = true := rfl

/-- "Really" also triggers VERUM. -/
theorem really_triggers_verum :
    necessarilyTriggersVerum .reallyAdverb = true := rfl

-- ════════════════════════════════════════════════════════════════
-- § 3. Ladd's PI/NI ambiguity
-- ════════════════════════════════════════════════════════════════

/-! @cite{ladd-1981}: the same negative question form is ambiguous between
    positive-implicature (PI) and negative-implicature (NI) readings,
    disambiguated by polarity items. -/

/-- A Ladd ambiguity datum: same form, opposite implicatures. -/
structure LaddAmbiguityDatum where
  /-- The question template -/
  question : String
  /-- Positive-implicature variant (with PPIs like "too") -/
  piVariant : String
  /-- Negative-implicature variant (with NPIs like "either") -/
  niVariant : String
  /-- PI interpretation -/
  piReading : String
  /-- NI interpretation -/
  niReading : String
  deriving Repr

/-- Classic Ladd example: too vs either. -/
def laddJaneComing : LaddAmbiguityDatum :=
  { question := "Isn't Jane coming ___?"
  , piVariant := "Isn't Jane coming too?"
  , niVariant := "Isn't Jane coming either?"
  , piReading := "I thought Jane was coming. [double-check p]"
  , niReading := "I thought Jane wasn't coming. [double-check ¬p]"
  }

/-- Some vs any. -/
def laddSomeAny : LaddAmbiguityDatum :=
  { question := "Wasn't there ___ pizza left?"
  , piVariant := "Wasn't there some pizza left?"
  , niVariant := "Wasn't there any pizza left?"
  , piReading := "I thought there was pizza. [surprised if none]"
  , niReading := "I thought there wasn't pizza. [surprised if some]"
  }

/-- Already vs yet. -/
def laddAlreadyYet : LaddAmbiguityDatum :=
  { question := "Hasn't John ___ left?"
  , piVariant := "Hasn't John already left?"
  , niVariant := "Hasn't John left yet?"
  , piReading := "I expected John to have left. [double-check p]"
  , niReading := "I expected John not to have left. [double-check ¬p]"
  }

/-- PPIs diagnose PI readings; NPIs diagnose NI readings.
    Bridge to the polarity-item licensing apparatus. -/
theorem ppi_diagnoses_pi : isLicensed too .PI = true := rfl
theorem npi_diagnoses_ni : isLicensed either .NI = true := rfl
theorem ppi_blocks_ni : isLicensed too .NI = false := rfl
theorem npi_blocks_pi : isLicensed either .PI = false := rfl

-- ════════════════════════════════════════════════════════════════
-- § 4. Cross-linguistic bias marking
-- ════════════════════════════════════════════════════════════════

/-- Cross-linguistic negative question data. -/
structure CrossLinguisticDatum where
  /-- Language -/
  language : String
  /-- Sentence -/
  sentence : String
  /-- Gloss -/
  gloss : String
  /-- Translation -/
  translation : String
  /-- How the language marks bias -/
  biasStrategy : String
  deriving Repr

/-- German: clitic position determines PI vs NI. -/
def germanNegQ : CrossLinguisticDatum :=
  { language := "German"
  , sentence := "Hat Hans nicht schon angerufen?"
  , gloss := "Has Hans not already called?"
  , translation := "Hasn't Hans already called?"
  , biasStrategy := "clitic_position"
  }

/-- Spanish: tampoco/también for NI/PI. -/
def spanishNegQ : CrossLinguisticDatum :=
  { language := "Spanish"
  , sentence := "¿No viene María también/tampoco?"
  , gloss := "Not comes María too/either?"
  , translation := "Isn't María coming too/either?"
  , biasStrategy := "polarity_item"
  }

/-- Korean: morphological marking. -/
def koreanNegQ : CrossLinguisticDatum :=
  { language := "Korean"
  , sentence := "Chelswu-ka an o-ni?"
  , gloss := "Chelswu-NOM not come-Q?"
  , translation := "Isn't Chelswu coming?"
  , biasStrategy := "morphological"
  }

/-- Bulgarian: separate negation and question particles. -/
def bulgarianNegQ : CrossLinguisticDatum :=
  { language := "Bulgarian"
  , sentence := "Ne dojde li Ivan?"
  , gloss := "Not came Q Ivan?"
  , translation := "Didn't Ivan come?"
  , biasStrategy := "particle_order"
  }

/-- Modern Greek: dhen vs mi negation. -/
def greekNegQ : CrossLinguisticDatum :=
  { language := "Modern Greek"
  , sentence := "Dhen irthe o Yannis?"
  , gloss := "Not came the Yannis?"
  , translation := "Didn't Yannis come?"
  , biasStrategy := "negation_choice"
  }

-- ════════════════════════════════════════════════════════════════
-- § 5. Generalizations
-- ════════════════════════════════════════════════════════════════

/-- Generalization 1: preposed negation forces positive epistemic implicature. -/
def generalization1 : String :=
  "Preposed negation yes/no questions necessarily carry a positive epistemic " ++
  "implicature. Non-preposed negation yes/no questions do not necessarily carry " ++
  "an epistemic implicature."

/-- Generalization 2: Ladd's p/¬p ambiguity. -/
def generalization2 : String :=
  "Preposed negation yes/no questions are potentially ambiguous between two readings: " ++
  "PI-reading (double-check p, licenses PPIs) and NI-reading (double-check ¬p, licenses NPIs)."

-- ════════════════════════════════════════════════════════════════
-- § 6. Examples
-- ════════════════════════════════════════════════════════════════

/-- Example: "Doesn't John drink?" (PI reading)

LF: [Q [not [VERUM [John drinks]]]]
Partition: {¬FOR-SURE-CG(drinks(j)), FOR-SURE-CG(drinks(j))}
Pronounced: ¬FOR-SURE-CG(drinks(j))
Implicature: Speaker believes John drinks
-/
def examplePI : NegQuestionLF Unit := .piLF (λ () => true)

/-- Example: "Doesn't John drink?" (NI reading, with "either")

LF: [Q [VERUM [not [John drinks]]]]
Partition: {FOR-SURE-CG(¬drinks(j)), ¬FOR-SURE-CG(¬drinks(j))}
Pronounced: FOR-SURE-CG(¬drinks(j))
Implicature: Speaker believes John doesn't drink
-/
def exampleNI : NegQuestionLF Unit := .niLF (λ () => true)

end RomeroHan2004
