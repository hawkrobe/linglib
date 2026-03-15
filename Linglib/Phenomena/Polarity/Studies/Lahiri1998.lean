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

1. *bhii* in focused contexts contributes a scalar implicature (following
   @cite{karttunen-peters-1979}) that the assertion is the LEAST LIKELY
   among focus-induced alternatives
2. Weak indefinites as bottom of scale: *ek* ('one') denotes the weakest
   cardinality predicate — true of everything that exists
3. In UE contexts: every alternative entails the assertion (because 'one'
   is weakest), so the assertion is the MOST likely. The scalar implicature
   requires the opposite. Contradiction → unacceptable.
4. In DE contexts: entailment reverses, so the assertion is genuinely the
   LEAST likely. The scalar implicature is satisfiable → acceptable.

## The ek bhii / koii bhii distinction (§8)

*ek bhii* introduces cardinality alternatives {one, two, three, ...}.
*koii bhii* introduces contextually salient property alternatives.
This explains why *koii bhii* has free-choice readings in generic contexts
(the alternatives are contextual, not entailment-ordered) while *ek bhii*
does not.
-/

namespace Phenomena.Polarity.Studies.Lahiri1998

open Semantics.FocusParticles (TraditionalEven LikelihoodOrder LikelihoodMonotone)
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
  | even  -- scalar 'even': least-likely implicature
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
  , npiForm := "ek bhii", npiGloss := "any, even one" }

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
    *koii* and *kuch* introduce contextual property alternatives.

    This distinction is stored in the lexicon (§8): the kind of alternatives
    a lexical item allows is part of its lexical entry. -/
def alternativeTypeOf (d : NPIDecomposition) : AlternativeType :=
  if d.base == "ek" || d.base == "zaraa" then .cardinality
  else .contextualProperty

#guard alternativeTypeOf ekBhii == .cardinality
#guard alternativeTypeOf zaraaBhii == .cardinality
#guard alternativeTypeOf koiiBhiiD == .contextualProperty
#guard alternativeTypeOf kuchBhii == .contextualProperty

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
    `atLeastOne`, but not vice versa. This is eq. (70) in the paper:
    ∀x(P(x) → one(x)). -/

theorem two_entails_one : entails atLeastTwo atLeastOne = true := by native_decide
theorem three_entails_one : entails atLeastThree atLeastOne = true := by native_decide
theorem three_entails_two : entails atLeastThree atLeastTwo = true := by native_decide

/-- The entailment is strict: `atLeastOne` does not entail stronger predicates. -/
theorem one_not_entails_two : entails atLeastOne atLeastTwo = false := by native_decide
theorem one_not_entails_three : entails atLeastOne atLeastThree = false := by native_decide

-- ============================================================================
-- §5. The Implicature Clash (§7.4)
-- ============================================================================

/-! The paper's core result (§7.4, eqs. 66–79).

    **UE (positive context)**: "*koii bhii aayaa" ('*Anyone came')
    - Assertion: `atLeastOne` (= ∃x[one(x) ∧ came(x)])
    - Alternatives: `atLeastTwo`, `atLeastThree`
    - Each alternative entails the assertion (`two_entails_one`, `three_entails_one`)
    - By likelihood monotonicity (eq. 71): likelihood(alt) ≤ likelihood(assertion)
    - EVEN requires (eq. 69): likelihood(assertion) < likelihood(alt)
    - Contradiction: can't have both

    **DE (under negation)**: "koii bhii nahiiN aayaa" ('No one came')
    - Assertion: `pnot atLeastOne` (= ¬∃x[one(x) ∧ came(x)])
    - Alternatives: `pnot atLeastTwo`, `pnot atLeastThree`
    - The assertion entails each alternative (negation reverses, eq. 78)
    - By likelihood monotonicity (eq. 79): likelihood(assertion) ≤ likelihood(alt)
    - EVEN requires (eq. 77): likelihood(assertion) < likelihood(alt)
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
-- §6. End-to-End: TraditionalEven Instances
-- ============================================================================

/-! We build `TraditionalEven` instances for *ek bhii* in UE and DE contexts,
    connecting the cardinality model to the `Particles.lean` API.

    In UE: `atLeastOne` is the prejacent, `[atLeastTwo, atLeastThree]` are
    alternatives. The presupposition requires `atLeastOne` to be less likely
    than each alternative — but since each alternative entails `atLeastOne`,
    the opposite holds under any monotone likelihood ordering.

    In DE: `pnot atLeastOne` is the prejacent. The assertion entails each
    negated alternative, so the prejacent IS the least likely. -/

/-- EVEN instance for *ek bhii aayaa ('*Even one came') in UE context. -/
def ekBhiiEvenUE : TraditionalEven (World := World) :=
  { prejacent := atLeastOne
  , alternatives := [atLeastTwo, atLeastThree]
  , likelihood := λ _ _ => True }  -- placeholder; clash proved independently

/-- EVEN instance for *ek bhii nahiiN aayaa* ('Not even one came') in DE. -/
def ekBhiiEvenDE : TraditionalEven (World := World) :=
  { prejacent := pnot atLeastOne
  , alternatives := [pnot atLeastTwo, pnot atLeastThree]
  , likelihood := λ _ _ => True }  -- placeholder; satisfaction proved independently

/-- In UE, the EVEN presupposition for *ek bhii* is contradicted:
    every alternative entails the assertion, so under any monotone likelihood
    ordering the assertion cannot be strictly less likely than its alternatives.

    This is the abstract version of the paper's argument (§7.4, eqs. 68–71). -/
theorem ekBhii_even_clash_UE
    (lt : BProp World → BProp World → Prop)
    (le : BProp World → BProp World → Prop)
    (hMono : LikelihoodMonotone le)
    (hCompat : ∀ (a b : BProp World), lt a b → le b a → False)
    (alt : BProp World)
    (hAlt : alt = atLeastTwo ∨ alt = atLeastThree)
    (hEven : lt atLeastOne alt) :
    False := by
  cases hAlt with
  | inl h =>
    exact hCompat atLeastOne alt hEven
      (hMono alt atLeastOne (by subst h; intro w; cases w <;> native_decide))
  | inr h =>
    exact hCompat atLeastOne alt hEven
      (hMono alt atLeastOne (by subst h; intro w; cases w <;> native_decide))

/-- In DE, the EVEN presupposition for *ek bhii nahiiN* is satisfiable:
    the negated assertion entails each negated alternative, so the assertion
    IS the least likely under a monotone ordering.

    This is the paper's argument (§7.4, eqs. 76–79). -/
theorem ekBhii_even_ok_DE :
    entails (pnot atLeastOne) (pnot atLeastTwo) = true ∧
    entails (pnot atLeastOne) (pnot atLeastThree) = true :=
  ⟨by native_decide, by native_decide⟩

-- ============================================================================
-- §7. Abstract Implicature Clash
-- ============================================================================

/-- An EVEN scalar implicature is CONTRADICTED when the assertion is entailed
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
-- §8. Hindi NPI Data (§4)
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

-- Object position (§4.1, eqs. 6c-d)

def koiiBhii_obj_neg : NPIDatum :=
  { sentence := "maiN-ne kisii-ko bhii nahiiN dekhaa"
  , npiItem := "kisii-ko bhii", grammatical := true
  , context := some .sententialNegation
  , notes := "(6d) 'I didn't see anyone.' Object NPI under negation" }

def koiiBhii_obj_pos : NPIDatum :=
  { sentence := "*maiN-ne kisii-ko bhii dekhaa"
  , npiItem := "kisii-ko bhii", grammatical := false
  , context := none
  , notes := "(6c) '*I saw anyone.' Object NPI in UE → clash" }

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
  , notes := "(10c) '*If Ram comes, he will do anything.' Apodosis is UE (NPI reading)" }

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

-- Adversative predicates (§4.5)

def npi_adversative_surprise_ek : NPIDatum :=
  { sentence := "mujhe is baat par aaScarya huaa ki ek bhii aadmii tumhaare ghar gayaa"
  , npiItem := "ek bhii", grammatical := true
  , context := some .adversative
  , notes := "(29a) 'I am surprised that even one person went to your house.'" }

def npi_adversative_surprise_koii : NPIDatum :=
  { sentence := "mujhe is baat par aaScarya huaa ki koii bhii tumhaare ghar gayaa"
  , npiItem := "koii bhii", grammatical := true
  , context := some .adversative
  , notes := "(29b) 'I am surprised that anyone went to your house.'" }

def npi_prohibition_obj : NPIDatum :=
  { sentence := "maiN-ne rameS-ko kisii-se bhii baat-ciit karne-se manaa kiyaa"
  , npiItem := "kisii-se bhii", grammatical := true
  , context := some .denyVerb
  , notes := "(29c) 'I prohibited Rames from talking to anyone.' Object NPI under prohibition" }

def npi_prohibition_subj : NPIDatum :=
  { sentence := "*maiN-ne kisii-ko bhii rameS-se baat-ciit karne-se manaa kiyaa/rokaa"
  , npiItem := "kisii-ko bhii", grammatical := false
  , context := none
  , notes := "(29d) '*I prohibited anyone from talking to Rames.' Subject NPI outside DE scope" }

def npi_glad_bad : NPIDatum :=
  { sentence := "*maiN is baat par khuS huuN ki koii bhii mere ghar aayaa"
  , npiItem := "koii bhii", grammatical := false
  , context := none
  , notes := "(31a) '*I am glad that anyone came to my place.' Non-adversative factive blocks NPI" }

def npi_glad_settle : NPIDatum :=
  { sentence := "tum is baat se khuS raho ki koii bhii tumhaare ghar aayaa"
  , npiItem := "koii bhii", grammatical := true
  , context := some .adversative
  , notes := "(31b) 'Be glad that ANYONE came.' K&L 'settle for less' → adversative reading" }

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
-- §9. Free Choice in Generic and Modal Contexts (§5)
-- ============================================================================

/-! @cite{lahiri-1998} §5: Hindi NPIs also behave as free-choice items in
    generic and modal contexts. The environments are:

    1. Generic sentences (§5.1): *koii bhii aadmii is mez-ko uThaa letaa hai*
       'Any man lifts this table'
    2. Modals of possibility (§5.2): *ek bhii aadmii is mez-ko uThaa saktaa hai*
       'Even one person can lift this table'
    3. **NOT** modals of necessity (§5.2): **kisii-ko bhii ghar jaanaa caahiye*
       '*Anyone must go home'

    The unified account: in generic contexts, indefinites are bound by
    the GEN operator. The restriction of GEN is a strengthening environment
    (§7.6, eqs. 95–98), so the EVEN implicature is satisfiable. Modals
    of possibility pattern with generics; necessity modals do not. -/

structure FCDatum where
  sentence : String
  npiItem : String
  contextType : String
  grammatical : Bool
  notes : String := ""
  deriving Repr

-- Generics (§5.1)

def fc_generic_koii : FCDatum :=
  { sentence := "koii bhii aadmii is mez-ko uThaa letaa hai"
  , npiItem := "koii bhii", contextType := "generic"
  , grammatical := true
  , notes := "(35a) 'Any man lifts this table.' Generic → FC reading" }

def fc_generic_owl : FCDatum :=
  { sentence := "koii bhii ulluu cuuhoN-kaa Sikaar karta hai"
  , npiItem := "koii bhii", contextType := "generic"
  , grammatical := true
  , notes := "(35b) 'Any owl hunts mice.' Generic → FC reading" }

def fc_generic_ek : FCDatum :=
  { sentence := "ek bhii cingaarii ghar-ko jalaa detii hai"
  , npiItem := "ek bhii", contextType := "generic"
  , grammatical := true
  , notes := "(35d) 'Even one spark burns the house.' Generic + cardinality" }

def fc_generic_zaraa : FCDatum :=
  { sentence := "zaraa bhii zahar khaane-ko bigaaR detii hai"
  , npiItem := "zaraa bhii", contextType := "generic"
  , grammatical := true
  , notes := "(35e) 'Even a little poison spoils the food.' Generic + measure" }

-- Modals of possibility (§5.2)

def fc_possibility_ek : FCDatum :=
  { sentence := "ek bhii aadmii is mez-ko uThaa saktaa hai"
  , npiItem := "ek bhii", contextType := "modal_possibility"
  , grammatical := true
  , notes := "(36a) 'Even one person can lift this table.' Possibility modal" }

def fc_possibility_koii : FCDatum :=
  { sentence := "koii bhii aadmii is mez-ko uThaa saktaa hai"
  , npiItem := "koii bhii", contextType := "modal_possibility"
  , grammatical := true
  , notes := "(36b) 'Anyone can lift this table.' Possibility modal" }

def fc_possibility_kabhii : FCDatum :=
  { sentence := "tum kabhii bhii ghar jaa sakte ho"
  , npiItem := "kabhii bhii", contextType := "modal_possibility"
  , grammatical := true
  , notes := "(36c) 'You may go home anytime.' Possibility modal" }

-- Modals of necessity BLOCK NPIs (§5.2)

def fc_necessity_kisii : FCDatum :=
  { sentence := "*kisii-ko bhii ghar jaanaa caahiye"
  , npiItem := "kisii-ko bhii", contextType := "modal_necessity"
  , grammatical := false
  , notes := "(36d) '*Anyone must go home.' Necessity blocks FC reading" }

def fc_necessity_ek : FCDatum :=
  { sentence := "*ek bhii aadmii-ko ghar jaanaa caahiye"
  , npiItem := "ek bhii", contextType := "modal_necessity"
  , grammatical := false
  , notes := "(36e) '*Even one person must go home.' Necessity blocks" }

-- Imperatives (§5.4, §10)

def fc_imperative_kuch : FCDatum :=
  { sentence := "kuchh bhii khaa lo"
  , npiItem := "kuchh bhii", contextType := "imperative"
  , grammatical := true
  , notes := "(39a) 'Eat anything.' Permission imperative → FC" }

def fc_imperative_koii : FCDatum :=
  { sentence := "koii bhii seb uThaa lo"
  , npiItem := "koii bhii", contextType := "imperative"
  , grammatical := true
  , notes := "(39b) 'Pick any apple.' Permission imperative → FC" }

-- ek bhii / zaraa bhii ODD in imperatives (§5.4, ex. 40)

def fc_imperative_zaraa_odd : FCDatum :=
  { sentence := "*?zaraa bhii khaa lo"
  , npiItem := "zaraa bhii", contextType := "imperative"
  , grammatical := false
  , notes := "(40a) '*?Eat even a little.' Numeral/measure NPIs degraded in imperatives" }

def fc_imperative_ek_odd : FCDatum :=
  { sentence := "*?ek bhii seb uThaa to"
  , npiItem := "ek bhii", contextType := "imperative"
  , grammatical := false
  , notes := "(40b) '*?Pick even one apple.' Numeral NPIs degraded in imperatives" }

def allFCData : List FCDatum :=
  [ fc_generic_koii, fc_generic_owl, fc_generic_ek, fc_generic_zaraa
  , fc_possibility_ek, fc_possibility_koii, fc_possibility_kabhii
  , fc_necessity_kisii, fc_necessity_ek
  , fc_imperative_kuch, fc_imperative_koii
  , fc_imperative_zaraa_odd, fc_imperative_ek_odd ]

/-- Generics and possibility modals license FC readings. -/
theorem generic_and_possibility_license :
    (allFCData.filter (λ d =>
      d.contextType == "generic" || d.contextType == "modal_possibility")).all
      (·.grammatical) = true := by native_decide

/-- Necessity modals block FC readings. -/
theorem necessity_blocks :
    (allFCData.filter (λ d => d.contextType == "modal_necessity")).all
      (! ·.grammatical) = true := by native_decide

-- ============================================================================
-- §10. The ek bhii / koii bhii Contrast (§8)
-- ============================================================================

/-! @cite{lahiri-1998} §8: The first approximation (§7) treats *koii bhii*
    and *ek bhii* as semantically equivalent, but they differ:

    (99a) *ek bhii aadmii is mez-ko uThaa saktaa hai*
          'Even one person can lift this table.'
          Implicature: more people lifting is MORE likely.
    (99b) *koii bhii aadmii is mez-ko uThaa saktaa hai*
          'Anyone can lift this table.'
          No cardinality implicature; FC reading.

    (100a) *koii bhii tiin log is mez-ko uThaa sakte haiN*
           'Any three people can lift this table.' ✓
    (100b) **ek bhii tiin log is mez-ko uThaa sakte haiN*
           '*Even one three people can lift this table.' ✗

    The explanation: *ek* introduces CARDINALITY alternatives (other
    numerals), while *koii* introduces CONTEXTUAL PROPERTY alternatives
    (pragmatically salient properties like 'not sick', 'strong', etc.).
    Only contextual alternatives give rise to FC readings. -/

structure EkKoiiContrastDatum where
  ekSentence : String
  koiiSentence : String
  contextType : String
  ekGrammatical : Bool
  koiiGrammatical : Bool
  notes : String := ""
  deriving Repr

/-- In generic contexts with numerals, *koii bhii* is fine but *ek bhii*
    is blocked (100a vs 100b). -/
def numeral_contrast : EkKoiiContrastDatum :=
  { ekSentence := "*ek bhii tiin log is mez-ko uThaa sakte haiN"
  , koiiSentence := "koii bhii tiin log is mez-ko uThaa sakte haiN"
  , contextType := "generic_with_numeral"
  , ekGrammatical := false
  , koiiGrammatical := true
  , notes := "(100) *ek bhii* blocked with numerals; *koii bhii* OK" }

/-- In generic contexts, both are fine but carry different implicatures (99). -/
def generic_contrast : EkKoiiContrastDatum :=
  { ekSentence := "ek bhii aadmii is mez-ko uThaa saktaa hai"
  , koiiSentence := "koii bhii aadmii is mez-ko uThaa saktaa hai"
  , contextType := "generic_simple"
  , ekGrammatical := true
  , koiiGrammatical := true
  , notes := "(99) Both OK, but ek bhii has cardinality implicature; koii bhii has FC reading" }

theorem numeral_contrast_asymmetry :
    numeral_contrast.ekGrammatical = false ∧
    numeral_contrast.koiiGrammatical = true := ⟨rfl, rfl⟩

/-- The alternative type distinction predicts the contrast: cardinality
    alternatives clash with explicit numerals (one ≠ three), while
    contextual property alternatives are compatible. -/
theorem alternative_type_predicts_contrast :
    alternativeTypeOf ekBhii = .cardinality ∧
    alternativeTypeOf koiiBhiiD = .contextualProperty := ⟨rfl, rfl⟩

-- ============================================================================
-- §11. All NPI Data
-- ============================================================================

def allHindiNPIData : List NPIDatum :=
  [ koiiBhii_neg, koiiBhii_pos
  , ekBhii_neg, ekBhii_pos
  , kuchBhii_neg, kuchBhii_pos
  , zaraaBhii_neg, zaraaBhii_pos
  , koiiBhii_obj_neg, koiiBhii_obj_pos
  , npi_cond_protasis, npi_cond_apodosis
  , npi_univ_restrictor, npi_exist_restrictor
  , npi_adversative_surprise_ek, npi_adversative_surprise_koii
  , npi_prohibition_obj, npi_prohibition_subj
  , npi_glad_bad, npi_glad_settle
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
  | .adversative         => true  -- Strawson-DE (@cite{von-fintel-1999})
  | .denyVerb            => true  -- semantically negative
  | _                    => false

theorem grammatical_contexts_are_de :
    (allHindiNPIData.filter (·.grammatical)).all (λ d =>
      match d.context with
      | some ctx => isDEOrQuestion ctx
      | none => false) = true := by native_decide

-- ============================================================================
-- §12. Subject NPI Licensing: Hindi vs English (§6)
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
-- §13. Connection to Existing Fragment Entries
-- ============================================================================

/-! The fragment entry `Fragments.Hindi.PolarityItems.koiiBhii` stores
    licensing contexts as a list. @cite{lahiri-1998}'s contribution is
    showing that these contexts are not arbitrary — they are exactly the
    DE environments (for NPI readings) and generic/modal environments
    (for FC readings) where the EVEN implicature is satisfiable.

    The study file derives this; the fragment file stores it.
    A future refactoring should make the fragment derive from the theory. -/

open Fragments.Hindi.PolarityItems (koiiBhii koiiNahiin)

theorem koiiBhii_is_fci : koiiBhii.polarityType = .fci := rfl
theorem koiiNahiin_is_npi : koiiNahiin.polarityType = .npiWeak := rfl

/-- The decomposition in this study matches the fragment entry. -/
theorem decomposition_matches_fragment :
    koiiBhiiD.npiForm = "koii bhii" ∧ koiiBhii.form = "koii bhii" :=
  ⟨rfl, rfl⟩

/-- The morphology classification in the fragment entry matches the
    decomposition analysis: *koii bhii* is indefinite + even. -/
theorem fragment_morphology_matches :
    koiiBhii.morphology = .indefPlusEven ∧
    koiiNahiin.morphology = .indefPlusNeg := ⟨rfl, rfl⟩

/-- The alternative type in the fragment matches the study's prediction:
    *koii bhii* introduces contextual property alternatives. -/
theorem fragment_alternativeType_matches :
    koiiBhii.alternativeType = .contextualProperty ∧
    alternativeTypeOf koiiBhiiD = .contextualProperty := ⟨rfl, rfl⟩

end Phenomena.Polarity.Studies.Lahiri1998
