/-!
# San Martín Peras Mixtec (SMPM) Fragment
@cite{ostrove-2026} @cite{ostrove-2022}

Language data for San Martín Peras Mixtec (ISO: jmx), an Oto-Manguean
language spoken by about 12,000 people in Oaxaca, Mexico. SMPM is
predicate-initial (VSO) and non-*pro*-drop: all clauses require overt
subjects and all transitive clauses require overt objects.

## Coverage

- Morpho-aspectual system: completive, continuous, irrealis
- Pronoun paradigm: person × number × gender, clitic vs nonclitic
- Embedded clause typology (three-way: finite, tensed subj., untensed subj.)
- Complement-taking predicate classification by clause type selected
-/

namespace Fragments.Mixtec.SMPM

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
  deriving DecidableEq, BEq, Repr

-- ════════════════════════════════════════════════════════════════
-- § 2: Person, Number, Gender
-- ════════════════════════════════════════════════════════════════

inductive Person where | first | second | third
  deriving DecidableEq, BEq, Repr

inductive Number where | sg | pl
  deriving DecidableEq, BEq, Repr

inductive Clusivity where | incl | excl
  deriving DecidableEq, BEq, Repr

/-- Grammatical genders for nonlocal (3rd person) pronouns (table 5).

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
  deriving DecidableEq, BEq, Repr

-- ════════════════════════════════════════════════════════════════
-- § 3: Pronoun Paradigm
-- ════════════════════════════════════════════════════════════════

/-- A pronoun form: clitic and (optional) nonclitic variant.

    SMPM distinguishes clitic and nonclitic pronouns
    (@cite{cardinaletti-starke-1999}). Clitics cannot be coordinated,
    cannot occur on their own, and may have impersonal readings.
    Nonclitic forms can bear focus (e.g., with *íntàà* 'only'). -/
structure PronounForm where
  clitic : String
  nonclitic : Option String  -- `none` if no distinct nonclitic form exists
  deriving Repr, BEq, DecidableEq

/-- Local person clitic pronouns (tables 4, 61). -/
def pron1sg     : PronounForm := ⟨"=ì",    some "yù'u"⟩
def pron2sg     : PronounForm := ⟨"=ú",    some "yô'o"⟩
def pron1plIncl : PronounForm := ⟨"=(y)é", none⟩
def pron1plExcl : PronounForm := ⟨"=ndú",  some "ndú'ú"⟩
def pron2pl     : PronounForm := ⟨"=ndó",  some "ndó'ó"⟩

/-- Nonlocal (3rd person) singular clitic forms (table 5). -/
def pron3sgNeutral : String := "=ñà"
def pron3sgFem     : String := "=ñá"
def pron3sgMasc    : String := "=rà"
def pron3sgLiq     : String := "=rá"
def pron3sgWd      : String := "=tún"
def pron3sgAml     : String := "=rí"

/-- Nonlocal plural clitic forms (table 5). -/
def pron3plNeutral : String := "=nà"
def pron3plFem     : String := "=ná"

/-- Controlled subjects in untensed subjunctives must be CLITIC pronouns.
    Nonclitic forms are ungrammatical in this position (67). -/
def controlledSubjectMustBeClitic : Bool := true

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
inductive ClauseType where
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
  deriving DecidableEq, BEq, Repr

/-- Properties distinguishing the three clause types (table 26). -/
structure ClauseProperties where
  /-- Unrestricted TAM morphology (all three aspects available) -/
  unrestrictedTAM : Bool
  /-- Noncoreferential embedded subject allowed -/
  noncoreferentialSubject : Bool
  /-- Shows restructuring effects (quantifier fronting targets matrix) -/
  restructuring : Bool
  deriving DecidableEq, BEq, Repr

def clauseProperties : ClauseType → ClauseProperties
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
  selects : ClauseType
  deriving Repr, BEq, DecidableEq

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

end Fragments.Mixtec.SMPM
