import Linglib.Features.Gender.Basic
import Linglib.Data.UD.Basic
import Linglib.Syntax.Category.Pronoun.Basic

/-!
# San Martín Peras Mixtec (SMPM) Fragment
[ostrove-2026]

Language data for San Martín Peras Mixtec (ISO: jmx), an Oto-Manguean
language spoken by about 12,000 people in Oaxaca, Mexico. SMPM is
predicate-initial (VSO) and non-*pro*-drop: all clauses require overt
subjects and all transitive clauses require overt objects.

## Coverage

- Morpho-aspectual system: completive, continuous, irrealis
- Pronoun paradigm ((4), (5), (61), (62)): `PersonalPronoun` entries in two
  series, clitic vs non-clitic, with per-entry C&S `strength`
- Embedded clause typology (three-way: finite, tensed subj., untensed subj.)
- Complement-taking predicate classification by clause type selected
-/

namespace Mixtec.SMPM

-- ════════════════════════════════════════════════════════════════
-- § 1: Morpho-Aspectual System
-- ════════════════════════════════════════════════════════════════

/-- SMPM's three morpho-aspectual categories.

    All clauses must be marked with one of these. SMPM lacks
    morphologically nonfinite predicates — the completive/continuous/
    irrealis distinction is the only TAM system. Aspect is primarily
    tonal: completive by low tone or prefix *nì-*, continuous by high
    tone, irrealis by mid/unmarked tone or stem changes. -/
inductive Aspect where
  /-- Completive (COMP): low tone on first vowel, or prefix *nì-* -/
  | comp
  /-- Continuous (CONT): high tone on first vowel -/
  | cont
  /-- Irrealis (IRR): mid/unmarked tone or stem changes -/
  | irr
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════════════════
-- § 2: Gender
-- ════════════════════════════════════════════════════════════════

/-- Grammatical genders for nonlocal (3rd person) pronouns ((5)).

    SMPM distinguishes six genders in the singular and two in the
    plural. There is no number distinction for most nonlocal pronouns:
    e.g., =rà 'he, they (all-male group)'. -/
inductive Gender where
  | neutral  -- =ñà/=(y)à (default, unspecified)
  | fem      -- =ñá
  | masc     -- =rà
  | liq      -- =rá (liquid gender)
  | wd       -- =tún (wooden gender)
  | aml      -- =rí (animal gender)
  deriving DecidableEq, Repr

/-- Map SMPM gender to the shared surface-level gender type.
    Only fem/masc map directly; the remaining four genders
    (neutral, liquid, wooden, animal) are language-specific
    noun class distinctions without cross-linguistic surface equivalents. -/
def Gender.toGender : Gender → _root_.Gender
  | .fem  => .feminine
  | .masc => .masculine
  | _     => .common  -- neutral/liq/wd/aml: no sex-based distinction

-- ════════════════════════════════════════════════════════════════
-- § 3: Pronoun Paradigm
-- ════════════════════════════════════════════════════════════════

/-! ### Clitic series ((4), (61))

SMPM distinguishes clitic and non-clitic pronouns ([cardinaletti-starke-1999],
cited at [ostrove-2026] (63)): clitics cannot be coordinated (63a), cannot
occur on their own (63b), may have impersonal readings (63c), and cannot bear
focus ((65), with *íntàà* 'only'; speaker comment at (66)). Each entry
declares the C&S class on the shared `Pronoun.strength` field. -/

def cl1sg : PersonalPronoun :=
  { form := "=ì", person := some .first, number := some .singular,
    strength := some .clitic }

def cl1plIncl : PersonalPronoun :=
  { form := "=(y)é", person := some .firstInclusive, number := some .plural,
     strength := some .clitic }

def cl1plExcl : PersonalPronoun :=
  { form := "=ndú", person := some .firstExclusive, number := some .plural,
     strength := some .clitic }

def cl2sg : PersonalPronoun :=
  { form := "=ú", person := some .second, number := some .singular,
    strength := some .clitic }

def cl2pl : PersonalPronoun :=
  { form := "=ndó", person := some .second, number := some .plural,
    strength := some .clitic }

/-- Surface form of the nonlocal (3rd person) clitic for each gender ((5);
    the neutral has a prevocalic allomorph *=(y)à*). -/
def Gender.cliticForm : Gender → String
  | .neutral => "=ñà"
  | .fem     => "=ñá"
  | .masc    => "=rà"
  | .liq     => "=rá"
  | .wd      => "=tún"
  | .aml     => "=rí"

/-- Nonlocal (3rd person) clitic by gender ((5)). `number := none`: most
    nonlocal pronouns make no number distinction (*=rà* 'he, they (all-male
    group)'); the API gender is derived via `Gender.toGender`. -/
def cl3 (g : Gender) : PersonalPronoun :=
  { form := g.cliticForm, person := some .third,
    gender := some g.toGender, strength := some .clitic }

/-- *=nà* — nonlocal plural, neutral ((5)). -/
def cl3plNeutral : PersonalPronoun :=
  { form := "=nà", person := some .third, number := some .plural,
    gender := some .common, strength := some .clitic }

/-- *=ná* — nonlocal plural, feminine ((5)). -/
def cl3plFem : PersonalPronoun :=
  { form := "=ná", person := some .third, number := some .plural,
    gender := some .feminine, strength := some .clitic }

/-! ### Non-clitic series ((4), (62))

Focusable and coordinable ((64)–(66)) — the C&S `.strong` class. (62) has a
gap: 1PL.INCL and the nonlocal persons lack dedicated non-clitic forms;
'strengthening' strategies fill the gap phrasally — clitic + demonstrative
(*yé yo'o* 'we (INCL) here', *=ra kan* 'he there' in (65b)) or the definite
article *mí* (*mí =rà* 'himself', also the reflexive, §7 below; cf.
McCloskey & Hale 1984 on Irish). Being phrasal, they are not lexical
entries here. -/

def str1sg : PersonalPronoun :=
  { form := "yù'u", person := some .first, number := some .singular,
    strength := some .strong }

def str1plExcl : PersonalPronoun :=
  { form := "ndú'ú", person := some .firstExclusive, number := some .plural,
     strength := some .strong }

def str2sg : PersonalPronoun :=
  { form := "yô'o", person := some .second, number := some .singular,
    strength := some .strong }

def str2pl : PersonalPronoun :=
  { form := "ndó'ó", person := some .second, number := some .plural,
    strength := some .strong }

/-! ### Series structure -/

/-- The clitic series ((4), (5), (61)). -/
def cliticSeries : List PersonalPronoun :=
  [cl1sg, cl1plIncl, cl1plExcl, cl2sg, cl2pl,
   cl3 .neutral, cl3 .fem, cl3 .masc, cl3 .liq, cl3 .wd, cl3 .aml,
   cl3plNeutral, cl3plFem]

/-- The non-clitic series ((4), (62)). -/
def strongSeries : List PersonalPronoun :=
  [str1sg, str1plExcl, str2sg, str2pl]

/-- The local-person clitic/non-clitic pairs ((61)–(62)); `none` marks the
    (62) gap (1PL.INCL, filled only by phrasal strengthening). -/
def localPairs : List (PersonalPronoun × Option PersonalPronoun) :=
  [(cl1sg, some str1sg), (cl1plIncl, none), (cl1plExcl, some str1plExcl),
   (cl2sg, some str2sg), (cl2pl, some str2pl)]

/-- Both series are strength-homogeneous — the per-series C&S facts, now
    per-entry data on the shared field. -/
theorem series_homogeneous :
    (∀ p ∈ cliticSeries, p.strength = some .clitic) ∧
    (∀ p ∈ strongSeries, p.strength = some .strong) := by
  constructor <;> decide

/-- Paired variants share their φ-features — the two series differ in
    deficiency class, not in person/number/clusivity content. -/
theorem pairs_share_phi : ∀ pr ∈ localPairs, ∀ s ∈ pr.2,
    pr.1.person = s.person ∧ pr.1.number = s.number := by decide

/-- Within each pair, the clitic is strictly more deficient — derived from
    the shared deficiency order, not stipulated. -/
theorem pairs_deficiency_contrast : ∀ pr ∈ localPairs, ∀ s ∈ pr.2,
    ∀ a ∈ pr.1.strength, ∀ b ∈ s.strength, a < b := by decide

/-- The Cardinaletti–Starke class required of a controlled subject in an
    untensed subjunctive: the clitic (most deficient). Non-clitic forms —
    including strengthened *mí =rà* — are sharply ungrammatical there ((67)). -/
def controlledSubjectStrength : Pronoun.Strength := .clitic

/-- SMPM's ban on non-clitic controlled subjects ((67)) realizes the
    Cardinaletti–Starke prediction: the required class sits strictly below
    every non-clitic entry's declared class in the deficiency order. -/
theorem controlledSubject_is_most_deficient :
    ∀ p ∈ strongSeries, ∀ s ∈ p.strength,
      controlledSubjectStrength < s := by decide

-- ════════════════════════════════════════════════════════════════
-- § 4: Embedded Clause Typology (table 26)
-- ════════════════════════════════════════════════════════════════

/-- SMPM's three embedded clause types, distinguished by three
    binary features (table 26).

    SMPM lacks morphologically nonfinite predicates: all clauses are
    marked with one of the three aspects. The "tensed" vs "untensed"
    subjunctive distinction is diagnosed by independent temporal
    adverbs and noncoreferential subject availability, not by overt
    tense morphology. -/
inductive EmbeddedClauseType where
  /-- Finite embedded clause: unrestricted TAM, free subject
      reference, no restructuring.
      Selected by: ka'án 'think', nakanini 'believe', kà'àn 'say',
      káchi 'said', kusijǐ ini 'be happy', etc. -/
  | finiteEmbedded
  /-- Tensed subjunctive: restricted TAM (irrealis only), free
      subject reference, no restructuring. Allows *ná* for disjoint
      reference.
      Selected by: kòni 'want', sǐso ini 'hate', ntatu 'hope', etc. -/
  | tensedSubjunctive
  /-- Untensed subjunctive: restricted TAM (irrealis only),
      obligatory coreference, mandatory restructuring. Subject must
      be overt clitic pronoun.
      Selected by: ntùkú 'try', nàkú'ún 'remember', kìxà 'start',
      sakwā'a 'learn', etc. -/
  | untensedSubjunctive
  deriving DecidableEq, Repr

/-- Properties distinguishing the three clause types (table 26). -/
structure ClauseProperties where
  /-- Unrestricted TAM morphology (all three aspects available) -/
  unrestrictedTAM : Bool
  /-- Noncoreferential embedded subject allowed -/
  noncoreferentialSubject : Bool
  /-- Shows restructuring effects (quantifier fronting targets matrix) -/
  restructuring : Bool
  deriving DecidableEq, Repr

def clauseProperties : EmbeddedClauseType → ClauseProperties
  | .finiteEmbedded      => ⟨true,  true,  false⟩
  | .tensedSubjunctive   => ⟨false, true,  false⟩
  | .untensedSubjunctive => ⟨false, false, true⟩

-- ════════════════════════════════════════════════════════════════
-- § 5: Complement-Taking Predicates (27a–c)
-- ════════════════════════════════════════════════════════════════

/-- A complement-taking predicate in SMPM. -/
structure CTP where
  form : String
  gloss : String
  selects : EmbeddedClauseType
  deriving Repr, DecidableEq

-- Predicates selecting finite embedded clauses (27a)
def think    : CTP := ⟨"ka'án",       "think",     .finiteEmbedded⟩
def believe  : CTP := ⟨"nakanini",    "believe",   .finiteEmbedded⟩
def wonder   : CTP := ⟨"kuntàà ini",  "wonder",    .finiteEmbedded⟩
def know     : CTP := ⟨"kòni",        "know",      .finiteEmbedded⟩
def say      : CTP := ⟨"kà'àn",       "say",       .finiteEmbedded⟩
def chat     : CTP := ⟨"ntatǔ'un",   "chat",      .finiteEmbedded⟩
def said     : CTP := ⟨"káchi",        "said",      .finiteEmbedded⟩
def beHappy  : CTP := ⟨"kusijǐ ini",  "be happy",  .finiteEmbedded⟩
def beSad    : CTP := ⟨"ntsi'i ini",  "be sad",    .finiteEmbedded⟩
def regret   : CTP := ⟨"ntsiko ini",  "regret",    .finiteEmbedded⟩

-- Predicates selecting tensed subjunctives (27b)
def want     : CTP := ⟨"kòni",        "want",      .tensedSubjunctive⟩
def hate     : CTP := ⟨"sǐso ini",    "hate",      .tensedSubjunctive⟩
def beAfraid : CTP := ⟨"iyì'bí",      "be afraid", .tensedSubjunctive⟩
def beScared : CTP := ⟨"kuntasí",     "be scared", .tensedSubjunctive⟩
def pray     : CTP := ⟨"nakwatu",     "pray",      .tensedSubjunctive⟩
def hope     : CTP := ⟨"ntatu",       "hope",      .tensedSubjunctive⟩
def agree    : CTP := ⟨"xiinka",      "agree",     .tensedSubjunctive⟩
def refuse   : CTP := ⟨"xǐunka",     "refuse",    .tensedSubjunctive⟩
def getIdea  : CTP := ⟨"chikàà ini",  "get the idea", .tensedSubjunctive⟩

-- Predicates selecting untensed subjunctives (27c)
def try_      : CTP := ⟨"ntùkú",       "try",          .untensedSubjunctive⟩
def remember  : CTP := ⟨"nàkú'ún",    "remember",     .untensedSubjunctive⟩
def forget    : CTP := ⟨"nantōso",     "forget",       .untensedSubjunctive⟩
def likeTo    : CTP := ⟨"kutō",        "like to",      .untensedSubjunctive⟩
def start     : CTP := ⟨"kìxà",        "start",        .untensedSubjunctive⟩
def finish    : CTP := ⟨"ntsi'i",      "finish",       .untensedSubjunctive⟩
def stop      : CTP := ⟨"xikwīn",     "stop",         .untensedSubjunctive⟩
def continue_ : CTP := ⟨"kò xikwīn",  "continue",     .untensedSubjunctive⟩
def need      : CTP := ⟨"xiniñu'u",   "need",         .untensedSubjunctive⟩
def knowHow   : CTP := ⟨"kòni xá kasa", "know how to", .untensedSubjunctive⟩
def learnHow  : CTP := ⟨"sakwā'a",    "learn how to", .untensedSubjunctive⟩
def notBother : CTP := ⟨"kò ntaa",    "not bother",   .untensedSubjunctive⟩

-- Per-datum verification: representative predicates select correct clause type
theorem think_finite    : think.selects    = .finiteEmbedded      := rfl
theorem want_tensed     : want.selects     = .tensedSubjunctive   := rfl
theorem try_untensed    : try_.selects     = .untensedSubjunctive := rfl
theorem hope_tensed     : hope.selects     = .tensedSubjunctive   := rfl
theorem remember_untensed : remember.selects = .untensedSubjunctive := rfl
theorem notBother_untensed : notBother.selects = .untensedSubjunctive := rfl
theorem chat_finite     : chat.selects     = .finiteEmbedded      := rfl
theorem beHappy_finite  : beHappy.selects  = .finiteEmbedded      := rfl

-- ════════════════════════════════════════════════════════════════
-- § 6: Typological Profile
-- ════════════════════════════════════════════════════════════════

/-- SMPM is non-*pro*-drop: all clauses require overt subjects (3). -/
def allowsProDrop : Bool := false

/-- SMPM is predicate-initial: VSO for verbal, copula-initial for
    nominal/adjectival predicates (2a–c). -/
def predicateInitial : Bool := true

-- ════════════════════════════════════════════════════════════════
-- § 7: Reflexive and Binding Data
-- ════════════════════════════════════════════════════════════════

/-- SMPM reflexive anaphors are formed with the definite article *mí*
    plus a clitic pronoun (71). Only locally bound — without *mí*, only
    a noncoreferential interpretation is available (72).

    Examples:
    - *Xini Juân mí =rà ini yùtátá.* 'Juan saw himself in the mirror.'
    - *Saá kâ'àn María xa'ǎ mí =ñá.* 'María always talks about herself.' -/
def reflexiveFormation : String := "mí + clitic pronoun"

/-- Quantified nominals can locally bind reflexive anaphors (73).
    - *Tá'iin'iin =nà bálí xìni mí =nà ini yùtátá.*
      'Every child saw themselves in the mirror.' -/
def quantifiersBindReflexives : Bool := true

/-- Exempt anaphors (reflexive forms used outside canonical binding domain)
    CANNOT have quantified antecedents (75, 78).
    - \**Tá'iin'iin tsǐnà tsìi ndò'ò mí =rí.* 'Each dog bit its own tail.'
    - \**Ni'iin =ná bálí ní- xìni táta mí =ná.* 'No girl saw her own father.' -/
def exemptAnaphorAllowsQuantifiedAntecedent : Bool := false

/-- Exempt anaphors occur as possessors (74) but are restricted:
    they cannot have quantified antecedents.
    - *Tsìi tsǐnà ndò'ò {=rí, mí =rí}.* 'The dog bit {its, its own} tail.'
    - *Xìni María táta {=ñá, mí =ñá}.* 'María saw {her, her own} father.' -/
def exemptAnaphorsAsPossessors : Bool := true

/-- *Ná* is a morpheme used in tensed subjunctives to force disjoint
    reference when the embedded subject does not match the matrix subject
    in φ-features (18b–d). It is optional with nonpronominal subjects (18d).
    *Ná* does NOT occur with untensed subjunctives (19). -/
def naDisjointReferenceMarker : Bool := true

/-- Clitic left-dislocation in SMPM is NOT island-sensitive (80–82):
    it is available out of adjunct islands and wh-islands.
    This argues against a movement analysis of left-dislocation. -/
def cliticLeftDislocationIslandSensitive : Bool := false

end Mixtec.SMPM
