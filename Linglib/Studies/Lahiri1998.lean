import Linglib.Semantics.Focus.Particles
import Linglib.Semantics.Entailment.Basic
import Linglib.Semantics.Polarity.Licensing
import Linglib.Fragments.Hindi.PolarityItems

/-!
# Lahiri 1998 — Focus and negative polarity in Hindi

Hindi NPIs (*koii bhii* 'anyone', *ek bhii* 'even one', *kuch bhii*
'anything', *zaraa bhii* 'even a little') are morphologically an
indefinite plus the focus particle *bhii* 'even' (paper p. 58).
[lahiri-1998] derives their distribution — as NPIs and as free-choice
items — compositionally: *bhii* contributes the scalar implicature
([karttunen-peters-1979]) that the assertion is least likely among the
focus alternatives, and the weak indefinite sits at the bottom of the
entailment scale. In UE contexts every alternative entails the
assertion, making it the *most* likely — the implicature is
contradicted (§7.4). In DE contexts entailment reverses and the
implicature is satisfiable. Free-choice readings arise where the
implicature is satisfiable in generic and possibility-modal contexts
(§5, §7.6); *ek bhii*'s cardinality alternatives vs *koii bhii*'s
contextual-property alternatives explain their contrasts (§8).
-/

namespace Lahiri1998

open Focus.Particles (evenPresup LikelihoodMonotone)
open Entailment (World entails pnot)
open Semantics.Polarity

/-! ### Morphological decomposition (paper p. 58)

Every item in the paradigm is a weak indefinite plus *bhii*; the kind
of alternatives an item activates (cardinality vs contextually salient
properties, §8) is a lexical property. -/

/-- A row of the paper's decomposition table: base indefinite, the
*bhii*-compound, and the alternative type the item activates. -/
structure NPIDecomposition where
  base : String
  baseGloss : String
  npiForm : String
  npiGloss : String
  alternativeType : AlternativeType
  deriving Repr

/-- The paper's decomposition table (p. 58): *ek*/*zaraa* activate
cardinality (measure) alternatives, the others contextual properties. -/
def hindiNPIs : List NPIDecomposition :=
  [ ⟨"ek", "one", "ek bhii", "any, even one", .cardinality⟩
  , ⟨"koii", "someone", "koii bhii", "anyone", .contextualProperty⟩
  , ⟨"kuch", "something (mass)", "kuch bhii", "anything", .contextualProperty⟩
  , ⟨"zaraa", "a little", "zaraa bhii", "even a little", .cardinality⟩
  , ⟨"kabhii", "sometime", "kabhii bhii", "ever, anytime", .contextualProperty⟩
  , ⟨"kahiiN", "somewhere", "kahiiN bhii", "anywhere", .contextualProperty⟩ ]

/-- Morphological uniformity: every NPI form is its base plus *bhii*. -/
theorem npiForm_eq_base_bhii :
    ∀ d ∈ hindiNPIs, d.npiForm = d.base ++ " bhii" := by decide

/-! ### The cardinality model

The scale `∃x[n(x) ∧ VP(x)]` over the 4-world semantics of
`Entailment.Basic`: w0 = at least three entities satisfy the VP,
w1 = exactly two, w2 = exactly one, w3 = none. -/

/-- At least one entity satisfies the VP (Bool form). -/
def atLeastOneB : (World → Bool) := λ w => w != .w3

/-- At least two entities satisfy the VP (Bool form). -/
def atLeastTwoB : (World → Bool) := λ w => w == .w0 || w == .w1

/-- At least three entities satisfy the VP (Bool form). -/
def atLeastThreeB : (World → Bool) := λ w => w == .w0

/-- At least one entity satisfies the VP. True at w0, w1, w2. -/
def atLeastOne : Set World := {w | atLeastOneB w = true}

/-- At least two entities satisfy the VP. True at w0, w1. -/
def atLeastTwo : Set World := {w | atLeastTwoB w = true}

/-- At least three entities satisfy the VP. True at w0 only. -/
def atLeastThree : Set World := {w | atLeastThreeB w = true}

/-! ### Weakness of `one` (§7.4, eq. 70)

`one` is the weakest cardinality predicate: every `atLeastN`
proposition entails `atLeastOne`, and not conversely. -/

theorem two_entails_one : entails atLeastTwo atLeastOne := by
  intro w hw
  simp [atLeastOne, atLeastOneB, atLeastTwo, atLeastTwoB] at *
  rcases hw with h | h <;> simp [h]
theorem three_entails_one : entails atLeastThree atLeastOne := by
  intro w hw
  simp [atLeastOne, atLeastOneB, atLeastThree, atLeastThreeB] at *
  simp [hw]
theorem three_entails_two : entails atLeastThree atLeastTwo := by
  intro w hw
  simp [atLeastThree, atLeastThreeB, atLeastTwo, atLeastTwoB] at *
  left; exact hw

/-- The entailment is strict: `atLeastOne` does not entail stronger predicates. -/
theorem one_not_entails_two : ¬ entails atLeastOne atLeastTwo := by
  intro h
  have hw : (.w2 : World) ∈ atLeastOne := by simp [atLeastOne, atLeastOneB]
  have := h hw
  simp [atLeastTwo, atLeastTwoB] at this
theorem one_not_entails_three : ¬ entails atLeastOne atLeastThree := by
  intro h
  have hw : (.w2 : World) ∈ atLeastOne := by simp [atLeastOne, atLeastOneB]
  have := h hw
  simp [atLeastThree, atLeastThreeB] at this

/-! ### The implicature clash (§7.4, eqs. 66–79)

In UE, each alternative entails the assertion, so a monotone
likelihood ordering makes the assertion most likely — but EVEN demands
it be least likely. Under negation the entailments reverse and EVEN is
satisfiable. -/

section ImplicatureClash

/-- UE pattern: all alternatives entail the assertion — fatal for EVEN. -/
theorem ue_alt_entails_assertion :
    entails atLeastTwo atLeastOne ∧
    entails atLeastThree atLeastOne :=
  ⟨two_entails_one, three_entails_one⟩

/-- DE pattern: the assertion entails all alternatives — EVEN is
satisfiable. -/
theorem de_assertion_entails_alt :
    entails (pnot atLeastOne) (pnot atLeastTwo) ∧
    entails (pnot atLeastOne) (pnot atLeastThree) := by
  refine ⟨?_, ?_⟩
  · intro w hw hw'
    exact hw (two_entails_one hw')
  · intro w hw hw'
    exact hw (three_entails_one hw')

/-- In UE the assertion does NOT entail the alternatives. -/
theorem ue_not_reverse :
    ¬ entails atLeastOne atLeastTwo ∧
    ¬ entails atLeastOne atLeastThree :=
  ⟨one_not_entails_two, one_not_entails_three⟩

/-- In DE the alternatives do NOT entail the assertion. -/
theorem de_not_reverse :
    ¬ entails (pnot atLeastTwo) (pnot atLeastOne) ∧
    ¬ entails (pnot atLeastThree) (pnot atLeastOne) := by
  refine ⟨?_, ?_⟩
  · intro h
    have h1 : (.w2 : World) ∈ pnot atLeastTwo := by
      simp [pnot, atLeastTwo, atLeastTwoB, Set.mem_compl_iff]
    have h2 := h h1
    simp [pnot, atLeastOne, atLeastOneB] at h2
  · intro h
    have h1 : (.w1 : World) ∈ pnot atLeastThree := by
      simp [pnot, atLeastThree, atLeastThreeB, Set.mem_compl_iff]
    have h2 := h h1
    simp [pnot, atLeastOne, atLeastOneB] at h2

end ImplicatureClash

/-! ### The clash through the EVEN presupposition -/

/-- An EVEN scalar implicature is contradicted whenever the assertion
is entailed by an alternative: the alternative is then at most as
likely, but EVEN requires the assertion to be strictly less likely. -/
theorem even_clash_abstract {W : Type*}
    (lt le : Set W → Set W → Prop)
    (hMono : LikelihoodMonotone le)
    (hCompat : ∀ a b, lt a b → le b a → False)
    {assertion alt : Set W}
    (hEntails : alt ⊆ assertion)
    (hEven : lt assertion alt) :
    False :=
  hCompat assertion alt hEven (hMono hEntails)

/-- In UE, the EVEN presupposition for *ek bhii* is contradicted
(§7.4, eqs. 68–71). -/
theorem ekBhii_even_clash_UE
    (lt le : Set World → Set World → Prop)
    (hMono : LikelihoodMonotone le)
    (hCompat : ∀ a b, lt a b → le b a → False)
    (hEven : evenPresup lt atLeastOne [atLeastTwo, atLeastThree]) :
    False :=
  even_clash_abstract lt le hMono hCompat two_entails_one
    (hEven atLeastTwo (by simp))

/-- In DE, the EVEN presupposition for *ek bhii nahiiN* is satisfiable:
the negated assertion entails each negated alternative (§7.4,
eqs. 76–79). -/
theorem ekBhii_even_ok_DE :
    entails (pnot atLeastOne) (pnot atLeastTwo) ∧
    entails (pnot atLeastOne) (pnot atLeastThree) :=
  de_assertion_entails_alt

/-! ### NPI data (§4)

Licensing judgments from [lahiri-1998] §4: *bhii* + indefinite is
licensed in DE contexts and blocked in UE contexts. The adversative
rescue in (31b) is [kadmon-landman-1993]'s "settle for less". -/

/-- A judged Hindi NPI sentence, with the licensing context (if any). -/
structure HindiNPIDatum where
  /-- The sentence -/
  sentence : String
  /-- The NPI item -/
  npiItem : String
  /-- Grammaticality judgment (true = OK, false = bad) -/
  grammatical : Bool
  /-- Type of licensing context (if grammatical) -/
  context : Option LicensingContext
  /-- Paper reference and translation -/
  notes : String
  deriving Repr

-- Clausemate negation (§4.1)

def koiiBhii_neg : HindiNPIDatum :=
  { sentence := "koii bhii nahiiN aayaa"
  , npiItem := "koii bhii", grammatical := true
  , context := some .negation
  , notes := "(6b) 'No one came.' Negation is DE → no clash" }

def koiiBhii_pos : HindiNPIDatum :=
  { sentence := "*koii bhii aayaa"
  , npiItem := "koii bhii", grammatical := false
  , context := none
  , notes := "(6a) '*Anyone came.' Positive is UE → clash" }

def ekBhii_neg : HindiNPIDatum :=
  { sentence := "ek bhii aadmii nahiiN aayaa"
  , npiItem := "ek bhii", grammatical := true
  , context := some .negation
  , notes := "(7b) 'No man came.' DE → no clash" }

def ekBhii_pos : HindiNPIDatum :=
  { sentence := "*ek bhii aadmii aayaa"
  , npiItem := "ek bhii", grammatical := false
  , context := none
  , notes := "(7a) '*Any man came.' UE → clash" }

def kuchBhii_neg : HindiNPIDatum :=
  { sentence := "maiN-ne kuch bhii nahiiN khaayaa"
  , npiItem := "kuch bhii", grammatical := true
  , context := some .negation
  , notes := "(8b) 'I didn't eat anything.' DE → no clash" }

def kuchBhii_pos : HindiNPIDatum :=
  { sentence := "*maiN-ne kuch bhii khaayaa"
  , npiItem := "kuch bhii", grammatical := false
  , context := none
  , notes := "(8a) '*I ate anything.' UE → clash" }

def zaraaBhii_neg : HindiNPIDatum :=
  { sentence := "maiN-ne zaraa bhii khaanaa nahiiN khaayaa"
  , npiItem := "zaraa bhii", grammatical := true
  , context := some .negation
  , notes := "(9b) 'I didn't eat any food.' DE → no clash" }

def zaraaBhii_pos : HindiNPIDatum :=
  { sentence := "*maiN-ne zaraa bhii khaanaa khaayaa"
  , npiItem := "zaraa bhii", grammatical := false
  , context := none
  , notes := "(9a) '*I ate any food.' UE → clash" }

-- Object position (§4.1)

def koiiBhii_obj_neg : HindiNPIDatum :=
  { sentence := "maiN-ne kisii-ko bhii nahiiN dekhaa"
  , npiItem := "kisii-ko bhii", grammatical := true
  , context := some .negation
  , notes := "(6d) 'I didn't see anyone.' Object NPI under negation" }

def koiiBhii_obj_pos : HindiNPIDatum :=
  { sentence := "*maiN-ne kisii-ko bhii dekhaa"
  , npiItem := "kisii-ko bhii", grammatical := false
  , context := none
  , notes := "(6c) '*I saw anyone.' Object NPI in UE → clash" }

-- Conditionals (§4.2)

def npi_cond_protasis : HindiNPIDatum :=
  { sentence := "agar raam kisii-ko bhii dekhegaa to tumheN bataayegaa"
  , npiItem := "kisii-ko bhii", grammatical := true
  , context := some .conditionalAntecedent
  , notes := "(10a) 'If Ram sees anyone, he will inform you.' Protasis is DE" }

def npi_cond_apodosis : HindiNPIDatum :=
  { sentence := "*agar raam aayegaa, to kuch bhii karegaa"
  , npiItem := "kuch bhii", grammatical := false
  , context := none
  , notes := "(10c) '*If Ram comes, he will do anything.' Apodosis is UE (NPI reading)" }

-- Universal restrictor (§4.3)

def npi_univ_restrictor : HindiNPIDatum :=
  { sentence := "aisaa har chaatr jisne ek bhii kitaab paRhii, paas ho gayaa"
  , npiItem := "ek bhii", grammatical := true
  , context := some .universalRestrictor
  , notes := "(11a) 'Every student who read any book passed.' Restrictor of ∀ is DE" }

def npi_exist_restrictor : HindiNPIDatum :=
  { sentence := "*aisaa koii chaatr jisne ek bhii kitaab paRhii, paas ho gayaa"
  , npiItem := "ek bhii", grammatical := false
  , context := none
  , notes := "(12a) '*Some student who read any book passed.' Restrictor of ∃ is UE" }

-- Adversative predicates (§4.5)

def npi_adversative_surprise_ek : HindiNPIDatum :=
  { sentence := "mujhe is baat par aaScarya huaa ki ek bhii aadmii tumhaare ghar gayaa"
  , npiItem := "ek bhii", grammatical := true
  , context := some .adversative
  , notes := "(29a) 'I am surprised that even one person went to your house.'" }

def npi_adversative_surprise_koii : HindiNPIDatum :=
  { sentence := "mujhe is baat par aaScarya huaa ki koii bhii tumhaare ghar gayaa"
  , npiItem := "koii bhii", grammatical := true
  , context := some .adversative
  , notes := "(29b) 'I am surprised that anyone went to your house.'" }

def npi_prohibition_obj : HindiNPIDatum :=
  { sentence := "maiN-ne rameS-ko kisii-se bhii baat-ciit karne-se manaa kiyaa"
  , npiItem := "kisii-se bhii", grammatical := true
  , context := some .denyVerb
  , notes := "(29c) 'I prohibited Rames from talking to anyone.' Object NPI under prohibition" }

def npi_prohibition_subj : HindiNPIDatum :=
  { sentence := "*maiN-ne kisii-ko bhii rameS-se baat-ciit karne-se manaa kiyaa/rokaa"
  , npiItem := "kisii-ko bhii", grammatical := false
  , context := none
  , notes := "(29d) '*I prohibited anyone from talking to Rames.' Subject NPI outside DE scope" }

def npi_glad_bad : HindiNPIDatum :=
  { sentence := "*maiN is baat par khuS huuN ki koii bhii mere ghar aayaa"
  , npiItem := "koii bhii", grammatical := false
  , context := none
  , notes := "(31a) '*I am glad that anyone came to my place.' Non-adversative factive blocks NPI" }

def npi_glad_settle : HindiNPIDatum :=
  { sentence := "tum is baat se khuS raho ki koii bhii tumhaare ghar aayaa"
  , npiItem := "koii bhii", grammatical := true
  , context := some .adversative
  , notes := "(31b) 'Be glad that ANYONE came.' 'Settle for less' → adversative reading" }

-- Before-clauses (§4.6)

def npi_before : HindiNPIDatum :=
  { sentence := "kisiike bhii aane-se pahle raam ghar calaa gayaa"
  , npiItem := "kisiike bhii", grammatical := true
  , context := some .beforeClause
  , notes := "(32a) 'Ram went home before anyone came.' Before is DE" }

-- Questions (§4.7)

def npi_question : HindiNPIDatum :=
  { sentence := "tumheN koii bhii kitaab pasand aayii kyaa?"
  , npiItem := "koii bhii", grammatical := true
  , context := some .question
  , notes := "(34a) 'Did you like any book?' Rhetorical → negative bias" }

-- Subject position (§6): Hindi, unlike English, licenses subject NPIs
-- under clausemate negation — negation scopes over the subject at LF.

def npi_subject_hindi : HindiNPIDatum :=
  { sentence := "koi bhii aadmii nahiiN aayaa"
  , npiItem := "koi bhii", grammatical := true
  , context := some .negation
  , notes := "(41a) 'No one came.' Hindi: subject NPI + clausemate negation OK" }

def allHindiNPIData : List HindiNPIDatum :=
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

/-- A DE-or-question licenser, derived from `contextProperties`: the
context's Strawson row supplies Zwarts strength, or it licenses by
entropy (questions license via negative bias rather than pure DE). -/
abbrev isDEOrQuestion (c : LicensingContext) : Prop :=
  ((Semantics.Polarity.Licensing.contextProperties c).strawsonSignature.toDEStrength).isSome ∨
    (Semantics.Polarity.Licensing.contextProperties c).mechanism = .byEntropy

/-- The datum's context is some DE-or-question licenser. -/
def hasDELicenser (d : HindiNPIDatum) : Prop :=
  match d.context with
  | none => False
  | some c => isDEOrQuestion c

instance : DecidablePred hasDELicenser := fun d => by
  unfold hasDELicenser
  cases d.context <;> infer_instance

/-- Every grammatical datum's licensing context is DE (or a question):
the distribution follows the implicature-clash prediction. -/
theorem grammatical_contexts_are_de :
    (allHindiNPIData.filter (·.grammatical)).Forall hasDELicenser := by decide

/-! ### Free choice in generic and modal contexts (§5)

Hindi NPIs are free-choice items in generic sentences and under
possibility modals, but not under necessity modals; the GEN
restriction is a strengthening environment, so the EVEN implicature is
satisfiable there (§7.6, eqs. 95–98). -/

/-- A judged free-choice datum: the environment tested and the
judgment. -/
structure FCDatum where
  sentence : String
  npiItem : String
  contextType : LicensingContext
  grammatical : Bool
  notes : String := ""
  deriving Repr

-- Generics (§5.1)

def fc_generic_koii : FCDatum :=
  { sentence := "koii bhii aadmii is mez-ko uThaa letaa hai"
  , npiItem := "koii bhii", contextType := .generic
  , grammatical := true
  , notes := "(35a) 'Any man lifts this table.' Generic → FC reading" }

def fc_generic_owl : FCDatum :=
  { sentence := "koii bhii ulluu cuuhoN-kaa Sikaar karta hai"
  , npiItem := "koii bhii", contextType := .generic
  , grammatical := true
  , notes := "(35b) 'Any owl hunts mice.' Generic → FC reading" }

def fc_generic_ek : FCDatum :=
  { sentence := "ek bhii cingaarii ghar-ko jalaa detii hai"
  , npiItem := "ek bhii", contextType := .generic
  , grammatical := true
  , notes := "(35d) 'Even one spark burns the house.' Generic + cardinality" }

def fc_generic_zaraa : FCDatum :=
  { sentence := "zaraa bhii zahar khaane-ko bigaaR detii hai"
  , npiItem := "zaraa bhii", contextType := .generic
  , grammatical := true
  , notes := "(35e) 'Even a little poison spoils the food.' Generic + measure" }

-- Modals of possibility (§5.2)

def fc_possibility_ek : FCDatum :=
  { sentence := "ek bhii aadmii is mez-ko uThaa saktaa hai"
  , npiItem := "ek bhii", contextType := .modalPossibility
  , grammatical := true
  , notes := "(36a) 'Even one person can lift this table.' Possibility modal" }

def fc_possibility_koii : FCDatum :=
  { sentence := "koii bhii aadmii is mez-ko uThaa saktaa hai"
  , npiItem := "koii bhii", contextType := .modalPossibility
  , grammatical := true
  , notes := "(36b) 'Anyone can lift this table.' Possibility modal" }

def fc_possibility_kabhii : FCDatum :=
  { sentence := "tum kabhii bhii ghar jaa sakte ho"
  , npiItem := "kabhii bhii", contextType := .modalPossibility
  , grammatical := true
  , notes := "(36c) 'You may go home anytime.' Possibility modal" }

-- Modals of necessity block FC readings (§5.2)

def fc_necessity_kisii : FCDatum :=
  { sentence := "*kisii-ko bhii ghar jaanaa caahiye"
  , npiItem := "kisii-ko bhii", contextType := .modalNecessity
  , grammatical := false
  , notes := "(36d) '*Anyone must go home.' Necessity blocks FC reading" }

def fc_necessity_ek : FCDatum :=
  { sentence := "*ek bhii aadmii-ko ghar jaanaa caahiye"
  , npiItem := "ek bhii", contextType := .modalNecessity
  , grammatical := false
  , notes := "(36e) '*Even one person must go home.' Necessity blocks" }

-- Imperatives (§5.4): fine with contextual-property items, degraded
-- with cardinality/measure items ((39) vs (40))

def fc_imperative_kuch : FCDatum :=
  { sentence := "kuchh bhii khaa lo"
  , npiItem := "kuchh bhii", contextType := .imperative
  , grammatical := true
  , notes := "(39a) 'Eat anything.' Permission imperative → FC" }

def fc_imperative_koii : FCDatum :=
  { sentence := "koii bhii seb uThaa lo"
  , npiItem := "koii bhii", contextType := .imperative
  , grammatical := true
  , notes := "(39b) 'Pick any apple.' Permission imperative → FC" }

def fc_imperative_zaraa_odd : FCDatum :=
  { sentence := "*?zaraa bhii khaa lo"
  , npiItem := "zaraa bhii", contextType := .imperative
  , grammatical := false
  , notes := "(40a) '*?Eat even a little.' Measure NPIs degraded in imperatives" }

def fc_imperative_ek_odd : FCDatum :=
  { sentence := "*?ek bhii seb uThaa to"
  , npiItem := "ek bhii", contextType := .imperative
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
    ∀ d ∈ allFCData,
      (d.contextType = .generic ∨ d.contextType = .modalPossibility) →
        d.grammatical = true := by decide

/-- Necessity modals block FC readings. -/
theorem necessity_blocks :
    ∀ d ∈ allFCData, d.contextType = .modalNecessity →
      d.grammatical = false := by decide

/-! ### The ek bhii / koii bhii contrast (§8)

The first approximation treats *koii bhii* and *ek bhii* as
equivalent, but *ek* activates cardinality alternatives (other
numerals) while *koii* activates contextually salient properties —
only the latter yield free-choice readings, and cardinality
alternatives clash with explicit numerals ((99)–(100)). -/

/-- A minimal *ek bhii* / *koii bhii* pair in the same frame. -/
structure EkKoiiContrastDatum where
  ekSentence : String
  koiiSentence : String
  ekGrammatical : Bool
  koiiGrammatical : Bool
  notes : String := ""
  deriving Repr

/-- With an explicit numeral, *koii bhii* is fine and *ek bhii* is
blocked ((100a) vs (100b)): cardinality alternatives clash with the
numeral. -/
def numeral_contrast : EkKoiiContrastDatum :=
  { ekSentence := "*ek bhii tiin log is mez-ko uThaa sakte haiN"
  , koiiSentence := "koii bhii tiin log is mez-ko uThaa sakte haiN"
  , ekGrammatical := false
  , koiiGrammatical := true
  , notes := "(100) '(*Even one)/(Any) three people can lift this table.'" }

/-- Without a numeral both are fine, with different implicatures ((99)):
*ek bhii* carries the cardinality implicature, *koii bhii* the FC
reading. -/
def generic_contrast : EkKoiiContrastDatum :=
  { ekSentence := "ek bhii aadmii is mez-ko uThaa saktaa hai"
  , koiiSentence := "koii bhii aadmii is mez-ko uThaa saktaa hai"
  , ekGrammatical := true
  , koiiGrammatical := true
  , notes := "(99) Cardinality implicature vs FC reading" }

/-! ### Fragment grounding

The fragment entry `Hindi.PolarityItems.koiiBhii` stores the
distribution this study derives: DE environments for NPI readings,
generic/modal environments for FC readings. -/

open Hindi.PolarityItems (koiiBhii koiiNahiin)

/-- The fragment's *koii bhii* matches the analysis: free-choice,
indefinite + *even* morphology, contextual-property alternatives. -/
theorem koiiBhii_fragment_grounded :
    koiiBhii.freeChoice = true ∧
    koiiBhii.morphology = .indefPlusEven ∧
    koiiBhii.alternativeType = .contextualProperty :=
  ⟨rfl, rfl, rfl⟩

/-- The fragment's *koii nahiiN* is a strength-licensed NPI with
indefinite + negation morphology — the non-*bhii* route. -/
theorem koiiNahiin_fragment_grounded :
    koiiNahiin.licensor = some .weak ∧
    koiiNahiin.morphology = .indefPlusNeg :=
  ⟨rfl, rfl⟩

end Lahiri1998
