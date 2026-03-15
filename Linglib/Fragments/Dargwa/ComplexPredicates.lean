import Linglib.Core.Alternation
import Linglib.Core.Lexical.RootFeatures

/-!
# Dargwa (Tanti / Muira) Complex Predicates @cite{sumbatova-2021}
@cite{kalyakin-2026}

Complex verbs in Dargwa consist of a **light verb** (LV, = v) and a
**lexical stem** (NV, = nominal root inside VP). The lexical stems
are highly variable: noun stems, adjectives, numerals, verbs, or
ideophones. Often the lexical element does not occur independently.

This is the structural basis for @cite{kalyakin-2026}'s analysis of
**v-stranding VP ellipsis (vVPE)** in Muira Dargwa: the light verb
(= v) survives while its complement (= VP, containing the nominal
root) is elided. The theoretical analysis (mismatch predictions,
root position mapping, *again* diagnostics) lives in the study file
`Phenomena/Ellipsis/Studies/Kalyakin2026.lean`.

## Light Verbs (§4.5.1 of @cite{sumbatova-2021})

The most common light verbs (ex. 31a):
- *b-arq'*- 'do, make'
- *b-iχ*- 'become'
- *w-ik'*- 'speak'

Other light verbs include *b-at*- 'leave', *b-ič*- 'fall',
*b-ig*- 'sit down', *aq*- 'hang', *aʁ*- 'reach', *b-ač'*- 'come',
etc. (ex. 31b).

## Connection to vVPE (@cite{kalyakin-2026})

Under vVPE, the light verb (v head) survives while the nominal root
(in VP) is elided. This directly explains why:
1. The light verb is overt in the ellipsis site
2. Causative alternations (which differ only in Voice) are tolerated
3. Antipassive roots (v-adjoined) cannot be elided
-/

namespace Fragments.Dargwa.ComplexPredicates

-- ============================================================================
-- § 1: Light Verb Inventory
-- ============================================================================

/-- A Dargwa light verb entry. The `genderSlot` field indicates whether
    the light verb carries a gender agreement prefix (most do). -/
structure LightVerb where
  /-- Citation form (with gender prefix placeholder b-) -/
  form : String
  /-- English gloss -/
  gloss : String
  /-- Does this LV carry a gender prefix? -/
  genderSlot : Bool
  /-- Is this LV used only in complex predicates (not independently)? -/
  boundToComplex : Bool := false
  deriving Repr, BEq

/-- *b-arq'-* 'do, make' — the most frequent LV. -/
def arq : LightVerb :=
  { form := "b-arq'-", gloss := "do, make"
  , genderSlot := true }

/-- *b-iχ-* 'become' — inchoative/change-of-state LV. -/
def ix : LightVerb :=
  { form := "b-iχ-", gloss := "become"
  , genderSlot := true }

/-- *w-ik'-* 'speak' — speech-act LV. -/
def ik : LightVerb :=
  { form := "w-ik'-", gloss := "speak"
  , genderSlot := true }

/-- *b-at-* 'leave'. -/
def at_ : LightVerb :=
  { form := "b-at-", gloss := "leave"
  , genderSlot := true }

/-- *b-ič-* 'fall'. -/
def ic : LightVerb :=
  { form := "b-ič-", gloss := "fall"
  , genderSlot := true }

/-- *b-ig-* 'sit down'. -/
def ig : LightVerb :=
  { form := "b-ig-", gloss := "sit down"
  , genderSlot := true }

/-- *aq-* 'hang'. No gender prefix. -/
def aq : LightVerb :=
  { form := "aq-", gloss := "hang"
  , genderSlot := false }

/-- *aʁ-* 'reach'. No gender prefix. -/
def ar : LightVerb :=
  { form := "aʁ-", gloss := "reach"
  , genderSlot := false }

/-- *b-uq-* — only used within complex verbs. -/
def uq : LightVerb :=
  { form := "b-uq-", gloss := "LV (bound)"
  , genderSlot := true, boundToComplex := true }

/-- *aq-* — only used within complex verbs (distinct from 'hang'). -/
def aq_bound : LightVerb :=
  { form := "aq-", gloss := "LV (bound)"
  , genderSlot := false, boundToComplex := true }

/-- *b-ik-* — only used within complex verbs. -/
def ik_bound : LightVerb :=
  { form := "b-ik-", gloss := "LV (bound)"
  , genderSlot := true, boundToComplex := true }

/-- *art-* — only used within complex verbs. -/
def art : LightVerb :=
  { form := "art-", gloss := "LV (bound)"
  , genderSlot := false, boundToComplex := true }

def allLightVerbs : List LightVerb :=
  [arq, ix, ik, at_, ic, ig, aq, ar, uq, aq_bound, ik_bound, art]

-- ============================================================================
-- § 2: Complex Predicate Structure
-- ============================================================================

/-- A complex predicate: lexical stem + light verb.
    Examples from @cite{sumbatova-2021} (32):
    - taman 'end' (N) + b-arq' 'do' = 'finish'
    - ħaˁdur 'ready' (ADJ) + b-arq' 'do' = 'prepare'
    - č'u 'two' (NUM) + b-ut' 'cut' = 'divide by two' -/
structure ComplexPredicate where
  /-- Lexical stem (nominal root / NV) -/
  lexicalStem : String
  /-- Part of speech of the lexical stem -/
  stemCategory : String
  /-- Light verb (LV = v head) -/
  lightVerb : LightVerb
  /-- Combined meaning -/
  meaning : String
  deriving Repr

def finish_ : ComplexPredicate :=
  { lexicalStem := "taman", stemCategory := "noun"
  , lightVerb := arq, meaning := "finish" }

def prepare : ComplexPredicate :=
  { lexicalStem := "ħaˁdur", stemCategory := "adjective"
  , lightVerb := arq, meaning := "prepare" }

def divideByTwo : ComplexPredicate :=
  { lexicalStem := "č'u", stemCategory := "numeral"
  , lightVerb := LightVerb.mk "b-ut'-" "cut" true false
  , meaning := "divide by two" }

def cough : ComplexPredicate :=
  { lexicalStem := "qeħ", stemCategory := "ideophone"
  , lightVerb := ik, meaning := "cough" }

-- ============================================================================
-- § 4: Causative (@cite{sumbatova-2021} §4.5.7)
-- ============================================================================

/-- Dargwa has a productive causative morpheme *-aq*.
    Causatives from intransitives are transitive (causee = ABS).
    Causatives from transitives make the causee appear in the elative case.

    This is the construction that undergoes alternation under vVPE
    in @cite{kalyakin-2026}: inchoative → causative and vice versa. -/
structure CausativeEntry where
  baseVerb : String
  baseGloss : String
  baseTransitive : Bool
  causativeForm : String
  causeeCase : String  -- "absolutive" or "elative"
  deriving Repr

/-- (65) *neš-li durħaˁ hajc:-aq-ur* 'Mother caused the boy to stand up.'
    Base: intransitive. Causee: absolutive. -/
def causStandUp : CausativeEntry :=
  { baseVerb := "hajc:-", baseGloss := "stand up"
  , baseTransitive := false
  , causativeForm := "hajc:-aq-"
  , causeeCase := "absolutive" }

/-- (66) *t:at:i-li durħaˁ-li-c:e-r qu b-urq:-aq-ub*
    'Father called the boy to dig the garden.'
    Base: transitive. Causee: elative. -/
def causDig : CausativeEntry :=
  { baseVerb := "b-urq:-", baseGloss := "dig"
  , baseTransitive := true
  , causativeForm := "b-urq:-aq-"
  , causeeCase := "elative" }

/-- Intransitive causatives: causee in absolutive. -/
theorem intr_causative_abs_causee :
    causStandUp.baseTransitive = false ∧
    causStandUp.causeeCase = "absolutive" := ⟨rfl, rfl⟩

/-- Transitive causatives: causee in elative. -/
theorem tr_causative_elat_causee :
    causDig.baseTransitive = true ∧
    causDig.causeeCase = "elative" := ⟨rfl, rfl⟩

-- ============================================================================
-- § 5: Valency Alternations (@cite{sumbatova-2021} §4.7.3)
-- ============================================================================

/-- Dargwa antipassive (A-lability): the A-argument takes absolutive case
    and the P-argument is demoted to ergative (a non-core ergative that
    never controls person or gender agreement). Only available in
    imperfective forms. Affective verbs are excluded.

    This maps to @cite{creissels-2025}'s `antipassivization`: A is
    maintained (becomes S), P is denucleativized. -/
def antipassive : Core.Alternation.ValencyAlternation :=
  Core.Alternation.antipassivization

/-- Dargwa P-lability: many transitive verbs can be used intransitively
    without morphological marking (@cite{sumbatova-2021} §4.7.3, ex. 87).
    The patient is dropped; the remaining S corresponds to the initial A.
    This is characteristic of verbs denoting situations that can occur with
    or without an agent (break, open, fill).

    Maps to @cite{creissels-2025}'s `P_ambitransitivity`: uncoded
    decausativization where S = initial P. -/
def pLability : Core.Alternation.AmbitransitivityType :=
  .P_ambitransitivity

/-- Dargwa causative (-aq) applied to intransitive bases maps to
    Creissels' causativization: S is maintained as P, a new A (causer)
    is introduced. -/
def causativeAlternation : Core.Alternation.ValencyAlternation :=
  Core.Alternation.causativization

/-- The antipassive is valency-decreasing (P is denucleativized). -/
theorem antipassive_decreases :
    antipassive.isValencyDecreasing = true := rfl

/-- The causative is valency-increasing (new A is introduced). -/
theorem causative_increases :
    causativeAlternation.isValencyIncreasing = true := rfl

/-- The antipassive and causative are structural inverses: one removes
    a core term, the other adds one. -/
theorem antipassive_causative_inverse :
    antipassive.isValencyDecreasing = true ∧
    causativeAlternation.isValencyIncreasing = true := ⟨rfl, rfl⟩

-- ============================================================================
-- § 6: Light Verb Verification
-- ============================================================================

/-- Most light verbs carry a gender prefix slot. -/
theorem most_lvs_have_gender :
    (allLightVerbs.filter (·.genderSlot)).length ≥
    (allLightVerbs.filter (fun lv => !lv.genderSlot)).length := by
  native_decide

/-- Some light verbs are bound (only used in complex predicates). -/
theorem some_lvs_bound :
    (allLightVerbs.filter (·.boundToComplex)).length ≥ 1 := by
  native_decide

-- ============================================================================
-- § 7: NV Root Position (@cite{kalyakin-2026} §2.2)
-- ============================================================================

/-- A complex predicate annotated with its NV root position, following
    Marantz (2009a;b, 2013) as applied to Dargwa by @cite{kalyakin-2026} §2.2.

    Uses `RootPosition` from `Core.Lexical.RootFeatures`:
    - `.complement`: change-of-state roots — *wana* 'warm', *hark* 'open'
    - `.adjoined`: manner/activity roots — *duc'* 'run', *taˤh* 'jump'

    The vVPE eligibility implications are derived in the study file. -/
structure AnnotatedCPr where
  lexicalStem : String
  stemGloss : String
  rootPosition : RootPosition
  lightVerb : LightVerb
  meaning : String
  deriving Repr

-- § 7a: Paper examples (@cite{kalyakin-2026})

/-- *wana AGR-arq'*- 'to warm smth. up' (exx. 3, 8a, 64, 66).
    NV *wana* 'warm' is a change-of-state root → object-adjoined. -/
def warmUp : AnnotatedCPr :=
  { lexicalStem := "wana", stemGloss := "warm"
  , rootPosition := .complement, lightVerb := arq, meaning := "warm smth. up" }

/-- *gap AGR-arq'*- 'to praise' (exx. 9, 17).
    NV *gap* 'praise' is a change-of-state root → object-adjoined. -/
def praiseCPr : AnnotatedCPr :=
  { lexicalStem := "gap", stemGloss := "praise"
  , rootPosition := .complement, lightVerb := arq, meaning := "praise" }

/-- *hark AGR-arq'*- 'to open' (ex. 52).
    NV *hark* 'open' is a change-of-state root → object-adjoined. -/
def openCPr : AnnotatedCPr :=
  { lexicalStem := "hark", stemGloss := "open"
  , rootPosition := .complement, lightVerb := arq, meaning := "open" }

/-- *parʁat AGR-arq'*- 'to calm' (exx. 36, 37, 69).
    NV *parʁat* 'calm' is a change-of-state root → object-adjoined. -/
def calmCPr : AnnotatedCPr :=
  { lexicalStem := "parʁat", stemGloss := "calm"
  , rootPosition := .complement, lightVerb := arq, meaning := "calm" }

/-- *dawk AGR-irq'*- 'to repair' (exx. 84–86).
    NV *dawk* 'repaired' is a change-of-state root → object-adjoined. -/
def repairCPr : AnnotatedCPr :=
  { lexicalStem := "dawk", stemGloss := "repaired"
  , rootPosition := .complement
  , lightVerb := { form := "w-irq'-", gloss := "make", genderSlot := true }
  , meaning := "repair" }

/-- *duc' Ø-uq-* 'to run' (ex. 58). Activity root → v-adjoined. -/
def runCPr : AnnotatedCPr :=
  { lexicalStem := "duc'", stemGloss := "run"
  , rootPosition := .adjoined
  , lightVerb := { form := "Ø-uq-", gloss := "move", genderSlot := false }
  , meaning := "run" }

/-- *taˤh Ø-uq-* 'to jump' (ex. 57). Activity root → v-adjoined. -/
def jumpCPr : AnnotatedCPr :=
  { lexicalStem := "taˤh", stemGloss := "jump"
  , rootPosition := .adjoined
  , lightVerb := { form := "Ø-uq-", gloss := "move", genderSlot := false }
  , meaning := "jump" }

end Fragments.Dargwa.ComplexPredicates
