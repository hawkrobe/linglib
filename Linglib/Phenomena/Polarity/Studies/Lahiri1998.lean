import Linglib.Theories.Semantics.Focus.Particles
import Linglib.Theories.Semantics.Entailment.Basic
import Linglib.Theories.Semantics.Entailment.Polarity
import Linglib.Phenomena.Polarity.NPIs
import Linglib.Fragments.Hindi.PolarityItems

/-!
# Lahiri (1998): Focus and Negative Polarity in Hindi
@cite{lahiri-1998} @cite{kadmon-landman-1993} @cite{krifka-1995} @cite{lee-horn-1994}

Hindi NPIs (*koii bhii* 'anyone', *ek bhii* 'even one', *kuch bhii* 'anything',
*zaraa bhii* 'even a little') are morphologically composed of a weak indefinite
plus the focus particle *bhii* ('even'). @cite{lahiri-1998} shows that their
distribution — both as NPIs and as free-choice items — follows from the
compositional semantics of these parts.

## The implicature clash mechanism

1. *bhii* = 'even': contributes a scalar presupposition that the assertion
   is the LEAST LIKELY among focus-induced alternatives
2. Weak indefinites as bottom of scale: *ek* ('one') denotes the weakest
   cardinality predicate — true of everything that exists
3. In UE contexts: every alternative entails the assertion (because 'one'
   is weakest), so the assertion is the MOST likely. EVEN requires the
   opposite. Contradiction → unacceptable.
4. In DE contexts: entailment reverses, so the assertion is genuinely the
   LEAST likely. EVEN is satisfied → acceptable.

## The ek bhii / koii bhii distinction

*ek bhii* introduces cardinality alternatives {one, two, three, ...}.
*koii bhii* introduces contextually salient property alternatives.
This explains why *koii bhii* has free-choice readings in generic contexts
(the alternatives are contextual, not entailment-ordered) while *ek bhii*
does not.
-/

namespace Phenomena.Polarity.Studies.Lahiri1998

open Semantics.FocusParticles (TraditionalEven LikelihoodOrder)
open Semantics.Entailment (World allWorlds entails pnot)
open Phenomena.Polarity.NPIs (NPIDatum)
open Core.Lexical.PolarityItem

-- ============================================================================
-- §1. Morphological Decomposition
-- ============================================================================

/-- The two readings of the Hindi particle *bhii*, disambiguated by focus.
    In non-focused contexts *bhii* means 'also'; in focus-affected contexts
    (including all NPI uses) it means 'even'. -/
inductive BhiiReading where
  | even  -- scalar 'even': least-likely presupposition
  | also  -- additive 'also': someone else has the property
  deriving DecidableEq, Repr

/-- Morphological decomposition of a Hindi NPI.
    All items in the paradigm share the structure: base indefinite + *bhii*. -/
structure NPIDecomposition where
  base : String
  baseGloss : String
  npiForm : String
  npiGloss : String
  deriving Repr

def ekBhii : NPIDecomposition :=
  { base := "ek", baseGloss := "one"
  , npiForm := "ek bhii", npiGloss := "even one, any" }

def koiiBhiiD : NPIDecomposition :=
  { base := "koii", baseGloss := "someone"
  , npiForm := "koii bhii", npiGloss := "anyone" }

def kuchBhii : NPIDecomposition :=
  { base := "kuch", baseGloss := "something (mass)"
  , npiForm := "kuch bhii", npiGloss := "anything" }

def zaraaBhii : NPIDecomposition :=
  { base := "zaraa", baseGloss := "a little"
  , npiForm := "zaraa bhii", npiGloss := "even a little" }

def kabhiiBhii : NPIDecomposition :=
  { base := "kabhii", baseGloss := "sometime"
  , npiForm := "kabhii bhii", npiGloss := "ever, anytime" }

def kahiiNBhii : NPIDecomposition :=
  { base := "kahiiN", baseGloss := "somewhere"
  , npiForm := "kahiiN bhii", npiGloss := "anywhere" }

def hindiNPIs : List NPIDecomposition :=
  [ekBhii, koiiBhiiD, kuchBhii, zaraaBhii, kabhiiBhii, kahiiNBhii]

/-- All Hindi NPIs share the particle *bhii* — the morphological uniformity
    that motivates the compositional analysis. -/
theorem all_share_bhii :
    hindiNPIs.all (λ d => d.npiForm.endsWith "bhii") = true := by native_decide

-- ============================================================================
-- §2. Alternative Types
-- ============================================================================

/-- *ek* and *zaraa* introduce cardinality/measure alternatives;
    *koii* and *kuch* introduce contextual property alternatives. -/
def alternativeTypeOf : NPIDecomposition → AlternativeType
  | { base := "ek", .. }    => .cardinality
  | { base := "zaraa", .. } => .cardinality
  | _                        => .contextualProperty

-- ============================================================================
-- §3. Concrete Model: The Cardinality Scale
-- ============================================================================

/-! We model the cardinality scale using the existing 4-world semantics
    from `Semantics.Entailment.Basic`.

    World assignment:
    - w0: ≥3 entities satisfy the VP
    - w1: exactly 2 satisfy the VP
    - w2: exactly 1 satisfies the VP
    - w3: 0 satisfy the VP

    The propositions `∃x[n(x) ∧ VP(x)]` then have clear truth values,
    and their entailment relations model the cardinality scale. -/

/-- At least one entity satisfies the VP. True at w0, w1, w2. -/
def atLeastOne : BProp World := λ w => w != .w3

/-- At least two entities satisfy the VP. True at w0, w1. -/
def atLeastTwo : BProp World := λ w => w == .w0 || w == .w1

/-- At least three entities satisfy the VP. True at w0 only. -/
def atLeastThree : BProp World := λ w => w == .w0

-- ============================================================================
-- §4. Weakness of `one`
-- ============================================================================

/-! The central semantic property: `one` is the weakest cardinality predicate.
    For any cardinality predicate P: ∃x[P(x) ∧ VP(x)] → ∃x[one(x) ∧ VP(x)].

    In the 4-world model, this means every `atLeastN` proposition entails
    `atLeastOne`, but not vice versa. -/

theorem two_entails_one : entails atLeastTwo atLeastOne = true := by native_decide
theorem three_entails_one : entails atLeastThree atLeastOne = true := by native_decide
theorem three_entails_two : entails atLeastThree atLeastTwo = true := by native_decide

/-- The entailment is strict: `atLeastOne` does not entail stronger predicates. -/
theorem one_not_entails_two : entails atLeastOne atLeastTwo = false := by native_decide
theorem one_not_entails_three : entails atLeastOne atLeastThree = false := by native_decide

-- ============================================================================
-- §5. The Implicature Clash
-- ============================================================================

/-! The paper's core result.

    **UE (positive context)**: "*koii bhii aayaa" ('*Anyone came')
    - Assertion: `atLeastOne` (= ∃x[one(x) ∧ came(x)])
    - Alternatives: `atLeastTwo`, `atLeastThree`
    - Each alternative entails the assertion (`two_entails_one`, `three_entails_one`)
    - By likelihood monotonicity: likelihood(alt) ≤ likelihood(assertion)
    - EVEN requires: likelihood(assertion) < likelihood(alt)
    - Contradiction: can't have `assertion < alt ≤ assertion`

    **DE (under negation)**: "koii bhii nahiiN aayaa" ('No one came')
    - Assertion: `pnot atLeastOne` (= ¬∃x[one(x) ∧ came(x)])
    - Alternatives: `pnot atLeastTwo`, `pnot atLeastThree`
    - The assertion entails each alternative (negation reverses)
    - By likelihood monotonicity: likelihood(assertion) ≤ likelihood(alt)
    - EVEN requires: likelihood(assertion) < likelihood(alt)
    - Compatible: `assertion ≤ alt` is consistent with `assertion < alt` -/

section ImplicatureClash

/-- UE pattern: all alternatives entail the assertion.
    This makes the assertion the MOST likely — fatal for EVEN. -/
theorem ue_alt_entails_assertion :
    entails atLeastTwo atLeastOne = true ∧
    entails atLeastThree atLeastOne = true :=
  ⟨by native_decide, by native_decide⟩

/-- DE pattern: the assertion entails all alternatives.
    Negation reverses the entailment direction.
    This makes the assertion the LEAST likely — satisfying EVEN. -/
theorem de_assertion_entails_alt :
    entails (pnot atLeastOne) (pnot atLeastTwo) = true ∧
    entails (pnot atLeastOne) (pnot atLeastThree) = true :=
  ⟨by native_decide, by native_decide⟩

/-- The asymmetry: in UE the assertion does NOT entail alternatives. -/
theorem ue_not_reverse :
    entails atLeastOne atLeastTwo = false ∧
    entails atLeastOne atLeastThree = false :=
  ⟨by native_decide, by native_decide⟩

/-- The asymmetry: in DE the alternatives do NOT entail the assertion. -/
theorem de_not_reverse :
    entails (pnot atLeastTwo) (pnot atLeastOne) = false ∧
    entails (pnot atLeastThree) (pnot atLeastOne) = false :=
  ⟨by native_decide, by native_decide⟩

end ImplicatureClash

-- ============================================================================
-- §6. Abstract Implicature Clash
-- ============================================================================

/-- A likelihood ordering is MONOTONE w.r.t. entailment when stronger
    propositions (true in fewer worlds) are less likely.

    If `p` entails `q`, then `p` is at least as strong, so
    `lessLikely p q` (p is less likely than or equal to q).

    This is the bridge between `Theories/Semantics/Entailment/` and
    `Theories/Semantics/Focus/Particles.lean` — the connection that
    @cite{lahiri-1998} relies on throughout. -/
def LikelihoodMonotone {W : Type} (lessLikely : BProp W → BProp W → Prop) : Prop :=
  ∀ (p q : BProp W), (∀ w, p w = true → q w = true) → lessLikely p q

/-- An EVEN presupposition is CONTRADICTED when the assertion is entailed
    by all alternatives. Under `LikelihoodMonotone`, each alternative is
    then at most as likely as the assertion, but EVEN requires the assertion
    to be strictly less likely than each alternative. -/
theorem even_clash_abstract
    {W : Type}
    (lt : BProp W → BProp W → Prop)
    (le : BProp W → BProp W → Prop)
    (hMono : ∀ (p q : BProp W), (∀ w, p w = true → q w = true) → le p q)
    (hCompat : ∀ (a b : BProp W), lt a b → le b a → False)
    (assertion : BProp W)
    (alt : BProp W)
    (hEntails : ∀ w, alt w = true → assertion w = true)
    (hEven : lt assertion alt) :
    False :=
  hCompat assertion alt hEven (hMono alt assertion hEntails)

-- ============================================================================
-- §7. Hindi NPI Data
-- ============================================================================

/-! Licensing judgments from @cite{lahiri-1998} §4. Each datum demonstrates
    the compositional prediction: bhii + indefinite is licensed in DE
    contexts and blocked in UE contexts.

    Uses `NPIDatum` from `Phenomena.Polarity.NPIs`. -/

-- Use the Phenomena-level licensing context type
open Phenomena.Polarity.NPIs (LicensingContext)

-- Clausemate negation (§4.1)

def koiiBhii_neg : NPIDatum :=
  { sentence := "koii bhii nahiiN aayaa"
  , npiItem := "koii bhii", grammatical := true
  , context := some .sententialNegation
  , notes := "(6b) 'No one came.' Negation is DE → no clash" }

def koiiBhii_pos : NPIDatum :=
  { sentence := "*koii bhii aayaa"
  , npiItem := "koii bhii", grammatical := false
  , context := none
  , notes := "(6a) '*Anyone came.' Positive is UE → clash" }

def ekBhii_neg : NPIDatum :=
  { sentence := "ek bhii aadmii nahiiN aayaa"
  , npiItem := "ek bhii", grammatical := true
  , context := some .sententialNegation
  , notes := "(7b) 'No man came.' DE → no clash" }

def ekBhii_pos : NPIDatum :=
  { sentence := "*ek bhii aadmii aayaa"
  , npiItem := "ek bhii", grammatical := false
  , context := none
  , notes := "(7a) '*Any man came.' UE → clash" }

def kuchBhii_neg : NPIDatum :=
  { sentence := "maiN-ne kuch bhii nahiiN khaayaa"
  , npiItem := "kuch bhii", grammatical := true
  , context := some .sententialNegation
  , notes := "(8b) 'I didn't eat anything.' DE → no clash" }

def kuchBhii_pos : NPIDatum :=
  { sentence := "*maiN-ne kuch bhii khaayaa"
  , npiItem := "kuch bhii", grammatical := false
  , context := none
  , notes := "(8a) '*I ate anything.' UE → clash" }

def zaraaBhii_neg : NPIDatum :=
  { sentence := "maiN-ne zaraa bhii khaanaa nahiiN khaayaa"
  , npiItem := "zaraa bhii", grammatical := true
  , context := some .sententialNegation
  , notes := "(9b) 'I didn't eat any food.' DE → no clash" }

def zaraaBhii_pos : NPIDatum :=
  { sentence := "*maiN-ne zaraa bhii khaanaa khaayaa"
  , npiItem := "zaraa bhii", grammatical := false
  , context := none
  , notes := "(9a) '*I ate any food.' UE → clash" }

-- Conditionals (§4.2)

def npi_cond_protasis : NPIDatum :=
  { sentence := "agar raam kisii-ko bhii dekhegaa to tumheN bataayegaa"
  , npiItem := "kisii-ko bhii", grammatical := true
  , context := some .conditional
  , notes := "(10a) 'If Ram sees anyone, he will inform you.' Protasis is DE" }

def npi_cond_apodosis : NPIDatum :=
  { sentence := "*agar raam aayegaa, to kuch bhii karegaa"
  , npiItem := "kuch bhii", grammatical := false
  , context := none
  , notes := "(10c) '*If Ram comes, he will do anything.' Apodosis is UE" }

-- Universal restrictor (§4.3)

def npi_univ_restrictor : NPIDatum :=
  { sentence := "aisaa har chaatr jisne ek bhii kitaab paRhii, paas ho gayaa"
  , npiItem := "ek bhii", grammatical := true
  , context := some .universalRestrictor
  , notes := "(11a) 'Every student who read any book passed.' Restrictor of ∀ is DE" }

def npi_exist_restrictor : NPIDatum :=
  { sentence := "*aisaa koii chaatr jisne ek bhii kitaab paRhii, paas ho gayaa"
  , npiItem := "ek bhii", grammatical := false
  , context := none
  , notes := "(12a) '*Some student who read any book passed.' Restrictor of ∃ is UE" }

-- Before-clauses (§4.6)

def npi_before : NPIDatum :=
  { sentence := "kisiike bhii aane-se pahle raam ghar calaa gayaa"
  , npiItem := "kisiike bhii", grammatical := true
  , context := some .beforeClause
  , notes := "(32a) 'Ram went home before anyone came.' Before is DE" }

-- Questions (§4.7)

def npi_question : NPIDatum :=
  { sentence := "tumheN koii bhii kitaab pasand aayii kyaa?"
  , npiItem := "koii bhii", grammatical := true
  , context := some .question
  , notes := "(34a) 'Did you like any book?' Rhetorical → negative bias" }

-- Subject position (§6) — Hindi differs from English

def npi_subject_hindi : NPIDatum :=
  { sentence := "koi bhii aadmii nahiiN aayaa"
  , npiItem := "koi bhii", grammatical := true
  , context := some .sententialNegation
  , notes := "(41a) 'No one came.' Hindi: subject NPI + clausemate negation OK" }

-- ============================================================================
-- §8. All Data
-- ============================================================================

def allHindiNPIData : List NPIDatum :=
  [ koiiBhii_neg, koiiBhii_pos
  , ekBhii_neg, ekBhii_pos
  , kuchBhii_neg, kuchBhii_pos
  , zaraaBhii_neg, zaraaBhii_pos
  , npi_cond_protasis, npi_cond_apodosis
  , npi_univ_restrictor, npi_exist_restrictor
  , npi_before, npi_question, npi_subject_hindi ]

/-- Every grammatical datum has a licensing context; every ungrammatical one does not. -/
theorem licensing_context_iff_grammatical :
    allHindiNPIData.Forall (λ d =>
      (d.grammatical → d.context.isSome) ∧
      (¬d.grammatical → d.context.isNone)) := by decide

/-- All licensing contexts in the grammatical data are DE environments
    (or questions, which license via negative bias rather than pure DE). -/
def isDEOrQuestion : Phenomena.Polarity.NPIs.LicensingContext → Bool
  | .sententialNegation  => true
  | .conditional         => true
  | .universalRestrictor => true
  | .beforeClause        => true
  | .question            => true
  | _                    => false

theorem grammatical_contexts_are_de :
    (allHindiNPIData.filter (·.grammatical)).all (λ d =>
      match d.context with
      | some ctx => isDEOrQuestion ctx
      | none => false) = true := by native_decide

-- ============================================================================
-- §9. Subject NPI Licensing: Hindi vs English
-- ============================================================================

/-! @cite{lahiri-1998} §6: Hindi allows subject NPIs under clausemate
    negation, unlike English.

    Hindi: "koi bhii aadmii nahiiN aayaa" ('No one came') ✓
    English: "*Anyone didn't come" ✗

    The paper's explanation: in Hindi, negation can take wide scope over
    the subject indefinite (NegP > IP), placing the NPI in the semantic
    scope of negation at LF. In English, the subject is outside NegP's
    c-command domain at S-structure, and reconstruction is restricted.

    This difference is *independent* of the implicature clash mechanism —
    both languages have the same EVEN + weak predicate semantics, but
    differ in whether the syntactic configuration allows the NPI to be
    in the semantic scope of negation. -/

structure SubjectNPIContrast where
  hindiSentence : String
  hindiGrammatical : Bool
  englishSentence : String
  englishGrammatical : Bool
  notes : String
  deriving Repr

def subjectNPI : SubjectNPIContrast :=
  { hindiSentence := "koi bhii aadmii nahiiN aayaa"
  , hindiGrammatical := true
  , englishSentence := "*Anyone didn't come"
  , englishGrammatical := false
  , notes := "Hindi NegP c-commands subject at LF; English NegP does not" }

theorem hindi_allows_subject_npi : subjectNPI.hindiGrammatical = true := rfl
theorem english_blocks_subject_npi : subjectNPI.englishGrammatical = false := rfl

-- ============================================================================
-- §10. Connection to Existing Fragment Entries
-- ============================================================================

/-! The fragment entry `Fragments.Hindi.PolarityItems.koiiBhii` stores
    licensing contexts as a list. @cite{lahiri-1998}'s contribution is
    showing that these contexts are not arbitrary — they are exactly the
    DE environments (for NPI readings) and generic/modal environments
    (for FC readings) where the EVEN implicature is satisfiable.

    The study file derives this; the fragment file stores it.
    A future refactoring should make the fragment derive from the theory. -/

open Fragments.Hindi.PolarityItems (koiiBhii koiiNahiin)
-- PolarityType now available from Core.Lexical.PolarityItem opened above

theorem koiiBhii_is_fci : koiiBhii.polarityType = .fci := rfl
theorem koiiNahiin_is_npi : koiiNahiin.polarityType = .npiWeak := rfl

/-- The decomposition in this study matches the fragment entry. -/
theorem decomposition_matches_fragment :
    koiiBhiiD.npiForm = "koii bhii" ∧ koiiBhii.form = "koii bhii" :=
  ⟨rfl, rfl⟩

end Phenomena.Polarity.Studies.Lahiri1998
