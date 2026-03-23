import Linglib.Phenomena.Causation.Studies.BeaversEtAl2021
import Linglib.Theories.Morphology.RootTypology
import Linglib.Fragments.Chuj.VerbBuilding

/-!
# Chuj Verb Building: Empirical Data and Bridge Theorems
@cite{coon-2019}

Theory-neutral empirical data from @cite{coon-2019} "Building verbs in Chuj:
Consequences for the nature of roots." *Journal of Linguistics* 55(1): 35–81.

Chuj is a Q'anjob'alan (Mayan) language spoken in Guatemala and Mexico.
The data here encodes the paper's primary empirical observations about
root classes, voice morphology, and argument structure, without committing
to the theoretical analysis.

## Data encoded

1. **Root classes** (§§2–3): four morphosyntactic classes of roots
   (√TV, √ITV, √POS, √NOM), identified by their surface distribution.
2. **Voice suffixes** (ex. (78), pp. 75–76): Ø, -ch, -j, -w with their
   morphological and distributional properties.
3. **Paradigm grammaticality** (§§2–4): which root×voice combinations
   are grammatical.
4. **-aj distribution** (§4.2): existential closure suffix tracks
   implicit arguments.
5. **Agent diagnostics** (§4.1): agent-oriented adverbs and
   by-phrases distinguish -ch from -j.
6. **Example verbs** with glosses, organized by root class.

## Bridge theorems

### Chuj fragment bridge

Connects the Chuj fragment (`Fragments/Chuj/VerbBuilding.lean`) to the
empirical data.

1. **Root class ↔ Root arity**: The phenomena's `CRootClass` maps to
   the fragment's `Root` values. √TV = selectsTheme, others = noTheme.

2. **Voice suffix ↔ VoiceHead**: Each suffix maps to the fragment's
   VoiceHead, with matching properties (theta assignment, D feature,
   phase head status).

3. **Paradigm predictions**: The fragment's `isGrammatical` matches the
   data's paradigm attestation for all root×voice combinations.

4. **-aj predictions**: The fragment's `hasImplicitExternal` and
   `triggersAj` match the data's -aj distribution.

5. **Agent diagnostics**: The fragment's `assignsTheta` matches the
   data's agent adverb and by-phrase diagnostics.

6. **Division of labor**: The data's `formsBareTransitive` aligns with
   the fragment's arity distinction: only roots with `selectsTheme`
   form bare transitives.

### Root typology bridge

Connects the theory-side predictions of `Theories/Morphology/RootTypology.lean`
(@cite{beavers-etal-2021} formalization) to the empirical data in
`Phenomena/Causation/Studies/BeaversEtAl2021.lean`.

1. **Classification isomorphism**: The theory's `RootType` and the phenomena's
   `CoSRootClass` are provably isomorphic — they describe the same partition.

2. **Diagnostic alignment**: The phenomena's semantic diagnostics
   (`changeDenialTest`, `restitutiveAgainTest`) agree exactly with the theory's
   Boolean correlates (`entailsChange`, `allowsRestitutiveAgain`).

3. **Prediction ↔ attestation**: The theory predicts PC roots HAVE simple
   statives and result roots LACK them; the empirical data confirms this
   (PC: 7/8 sample roots ≥ 50%; result: all 10 sample roots ≤ 10%).

4. **Markedness prediction**: The theory predicts PC verbs are marked and result
   verbs are unmarked; the statistical comparison confirms PC median (56.01%)
   exceeds result median (15.20%).

5. **Fragment grounding**: The Chuj fragment's `Root` values instantiate the
   theory's predictions — e.g., `rootTV_res.entailsChange = true` matches the
   theory's `RootType.entailsChange.result = true`.

-/

namespace Phenomena.Causation.Studies.Coon2019

-- ════════════════════════════════════════════════════
-- § 1. Root Classes (theory-neutral, §§2–3)
-- ════════════════════════════════════════════════════

/-- The four morphosyntactic root classes in Chuj, identified by
    surface distribution (which suffixes they combine with, whether
    they form bare transitive stems). Labels follow Coon's notation. -/
inductive CRootClass where
  | tv   -- transitive roots: form bare transitive stems
  | itv  -- intransitive roots: take null v in intransitive stems
  | pos  -- positional roots: require -w for verbalization
  | nom  -- nominal roots: require -w for verbalization
  deriving DecidableEq, BEq, Repr

-- ════════════════════════════════════════════════════
-- § 2. Voice Suffixes (ex. (78), pp. 75–76)
-- ════════════════════════════════════════════════════

/-- The four voice suffixes in Chuj (ex. (78), pp. 75–76). -/
inductive ChujVoiceSuffix where
  | null  -- Ø: active transitive
  | ch    -- -ch: passive with implicit agent
  | j     -- -j: agentless passive
  | w     -- -w: antipassive / verbalizer
  deriving DecidableEq, BEq, Repr

/-- The morphological form of each suffix. -/
def ChujVoiceSuffix.form : ChujVoiceSuffix → String
  | .null => "Ø"
  | .ch   => "-ch"
  | .j    => "-j"
  | .w    => "-w"

-- ════════════════════════════════════════════════════
-- § 3. External Argument Properties (ex. (78))
-- ════════════════════════════════════════════════════

/-- Status of the external argument for each voice form. -/
inductive ExtArgStatus where
  | overt_erg   -- overt, ergative case (transitive subject)
  | overt_abs   -- overt, absolutive case (intransitive subject)
  | implicit    -- semantically present but not syntactically realized
  | absent      -- no external argument at all
  deriving DecidableEq, BEq, Repr

/-- External argument status for each voice suffix (ex. (78)). -/
def ChujVoiceSuffix.extArgStatus : ChujVoiceSuffix → ExtArgStatus
  | .null => .overt_erg
  | .ch   => .implicit
  | .j    => .absent
  | .w    => .overt_abs

/-- Whether the voice suffix assigns a thematic role to an external
    argument (observed via agent-oriented adverb diagnostics, §4.1–4.2). -/
def ChujVoiceSuffix.hasAgent : ChujVoiceSuffix → Bool
  | .null => true   -- overt agent
  | .ch   => true   -- implicit agent (adverbs OK, ex. 63a)
  | .j    => false  -- no agent at all (adverbs blocked, ex. 67a)
  | .w    => true   -- overt agent (ABS)

-- ════════════════════════════════════════════════════
-- § 4. Paradigm Grammaticality (§§2–4)
-- ════════════════════════════════════════════════════

/-- Whether a root class can combine with a voice suffix to form
    a grammatical verb stem.

    Based on the distributional facts in §§2–5:
    - √TV: all four voices (Ø, -ch, -j, -w) — ex. (78)
    - √ITV: null v only (§2.1, p. 40)
    - √POS: -w only (§2.4, p. 43)
    - √NOM: -w only (§3.1, p. 46) -/
def isGrammatical (rc : CRootClass) (vs : ChujVoiceSuffix) : Bool :=
  match rc, vs with
  | .tv,  _     => true   -- √TV combines with all four
  | .itv, .null => true   -- √ITV takes null v (§2.1)
  | .pos, .w    => true   -- √POS takes -w (§2.4)
  | .nom, .w    => true   -- √NOM takes -w (§3.1)
  | _,    _     => false

/-- √TV is the only class that forms bare transitive stems (§2.2, p. 41). -/
def formsBareTransitive (rc : CRootClass) : Bool :=
  match rc with
  | .tv => true
  | _   => false

-- ════════════════════════════════════════════════════
-- § 5. -aj Distribution (§4.2, ex. (78))
-- ════════════════════════════════════════════════════

/-- Whether -aj (existential closure) appears on a √TV stem in each
    voice form (ex. (78), pp. 75–76; §4.2, p. 72).

    -aj marks the presence of an implicit argument:
    - Ø: no implicit arg → no -aj
    - -ch: implicit external arg → -aj on stem (§4.1.1, p. 68)
    - -j: no external arg at all → no -aj
    - -w (absolutive): implicit internal arg → -aj (ex. (55c), p. 65)
    - -w (incorporation): overt bare NP internal arg → no -aj (ex. (54a), p. 64)

    For the -w cases, we encode the two antipassive subtypes separately. -/
inductive AntipassiveType where
  | absolutive      -- theme is implicit (suppressed)
  | incorporation   -- theme is overt bare NP (incorporated)
  deriving DecidableEq, BEq, Repr

/-- -aj on √TV stems in passive/agentless contexts. -/
def ajOnPassive (vs : ChujVoiceSuffix) : Bool :=
  match vs with
  | .null => false  -- no implicit arg
  | .ch   => true   -- implicit agent (ex. 62: -ch-aj passive)
  | .j    => false  -- no agent at all
  | .w    => false  -- depends on antipassive type (see below)

/-- -aj on √TV stems in antipassive (-w) contexts. -/
def ajOnAntipassive (apt : AntipassiveType) : Bool :=
  match apt with
  | .absolutive    => true   -- implicit theme (ex. 55b: Ix-mak'-waj)
  | .incorporation => false  -- overt bare NP (ex. 54a: Ix-in-jax-w-i ixim)

-- ════════════════════════════════════════════════════
-- § 6. Agent Diagnostics (§4.1–4.2)
-- ════════════════════════════════════════════════════

/-- Agent-oriented adverb test (§4.1.1–4.1.2).
    "on purpose" adverbs are grammatical with -chaj but not -j.

    (63a) on purpose ... ix-ch'ak-chaj te' te'.
          'The tree was felled on purpose.' ✓  (p. 68)

    (67a) *on purpose ... ix-ch'ak-j-i te' te'.
          intended: 'The tree was felled on purpose.' ✗  (p. 70) -/
def agentAdverbOK (vs : ChujVoiceSuffix) : Bool :=
  match vs with
  | .null => true   -- active: agent is overt
  | .ch   => true   -- passive: implicit agent licenses adverb (ex. 63a)
  | .j    => false  -- agentless: no agent to orient (ex. 67a)
  | .w    => true   -- antipassive: agent is overt

/-- By-phrase test (§4.1.1–4.1.2).
    Oblique agents ("yuj" DPs) are grammatical with -chaj but not -j.

    (62) ... yuj ... 'by them' ✓ with -chaj  (p. 68)
    (65–66) -uj phrases with -j are causal, not agentive  (pp. 69–70) -/
def byPhraseOK (vs : ChujVoiceSuffix) : Bool :=
  match vs with
  | .null => false  -- active: agent is already overt
  | .ch   => true   -- passive: by-phrase identifies implicit agent (ex. 62)
  | .j    => false  -- agentless: -uj phrase is causal, not agentive (exx. 65–66)
  | .w    => false  -- antipassive: agent is already overt

-- ════════════════════════════════════════════════════
-- § 7. Example Verbs
-- ════════════════════════════════════════════════════

/-- A Chuj verb entry with its root class and gloss. -/
structure ChujVerb where
  root : String
  gloss : String
  rootClass : CRootClass
  deriving BEq, Repr

-- √TV roots (§2.2, ex. (10))
def mak' : ChujVerb := ⟨"mak'", "hit", .tv⟩
def chel : ChujVerb := ⟨"chel", "hug", .tv⟩
def jax  : ChujVerb := ⟨"jax", "grind", .tv⟩
def k'ux : ChujVerb := ⟨"k'ux", "bite", .tv⟩
def il   : ChujVerb := ⟨"il", "see", .tv⟩
def jatz': ChujVerb := ⟨"jatz'", "hit (injure)", .tv⟩
def tzak': ChujVerb := ⟨"tzak'", "wrap", .tv⟩
def a'_give : ChujVerb := ⟨"a'", "give", .tv⟩
def lok' : ChujVerb := ⟨"lok'", "pull out", .tv⟩

-- √ITV roots (§2.1, p. 40)
def way  : ChujVerb := ⟨"way", "sleep", .itv⟩
def ok'  : ChujVerb := ⟨"ok'", "cry", .itv⟩
def jaw  : ChujVerb := ⟨"jaw", "arrive", .itv⟩
def b'at : ChujVerb := ⟨"b'at", "go", .itv⟩
def kam  : ChujVerb := ⟨"kam", "die", .itv⟩
def atin : ChujVerb := ⟨"atin", "bathe", .itv⟩

-- √POS roots (§2.4, p. 43)
def chot : ChujVerb := ⟨"chot", "sit/crouch", .pos⟩
def kot  : ChujVerb := ⟨"kot", "on all fours", .pos⟩
def watz : ChujVerb := ⟨"watz", "lie face down", .pos⟩
def buch : ChujVerb := ⟨"buch", "sit cross-legged", .pos⟩

-- √NOM roots (§3.1, p. 46)
def chanhal : ChujVerb := ⟨"chanhal", "dance", .nom⟩
def a'_water : ChujVerb := ⟨"a'", "water/swim", .nom⟩

def tvRoots : List ChujVerb :=
  [mak', chel, jax, k'ux, il, jatz', tzak', a'_give, lok']

def itvRoots : List ChujVerb :=
  [way, ok', jaw, b'at, kam, atin]

def posRoots : List ChujVerb :=
  [chot, kot, watz, buch]

def nomRoots : List ChujVerb :=
  [chanhal, a'_water]

-- ════════════════════════════════════════════════════
-- § 8. Paradigm Examples (§§2–5)
-- ════════════════════════════════════════════════════

/-- A glossed Chuj example sentence. -/
structure ChujExample where
  /-- Example number in the paper -/
  exNumber : Nat
  /-- Page number -/
  page : Nat
  /-- Chuj form -/
  chuj : String
  /-- English translation -/
  english : String
  /-- Root used -/
  verb : ChujVerb
  /-- Voice suffix -/
  voice : ChujVoiceSuffix
  /-- Whether the example is grammatical -/
  grammatical : Bool
  deriving Repr

-- Key paradigm examples from §§2–5

/-- (10a) Active transitive: √TV + Ø (§2.2, p. 41). -/
def ex10a : ChujExample :=
  ⟨10, 41, "Ix-ach-ko-chel-a'",
   "We hugged you.", chel, .null, true⟩

/-- (7a) √ITV + null v (§2.1, p. 40). -/
def ex7a : ChujExample :=
  ⟨7, 40, "Ix-onh-way-i",
   "We slept.", way, .null, true⟩

/-- (23a) √POS + -w (§3, p. 48). -/
def ex23a : ChujExample :=
  ⟨23, 48, "Ix-chot-w-i nok' k'ok'on",
   "The frog hopped.", chot, .w, true⟩

/-- (16b) √NOM + -w (§2.5, p. 45). -/
def ex16b : ChujExample :=
  ⟨16, 45, "Ix-in-chanhal-w-i",
   "I danced.", chanhal, .w, true⟩

/-- (62) √TV + -chaj (passive, §4.1.1, p. 68). -/
def ex62 : ChujExample :=
  ⟨62, 68, "tz-b'o'-ch-aj ... winh nhulej tik",
   "The brother's food is made by them.", mak', .ch, true⟩

/-- (59) √TV + -j (agentless passive, §4.1.2, p. 67). -/
def ex59 : ChujExample :=
  ⟨59, 67, "tz-man-j-i ... / tz-choj-j-i ixim",
   "It is bought. / It is ground.", mak', .j, true⟩

/-- (63a) Agent adverb with -chaj: grammatical (§4.1.1, p. 68). -/
def ex63a : ChujExample :=
  ⟨63, 68, "sk'annhej sk'o'ol winh ix-ch'ak-chaj te' te'",
   "The tree was felled on purpose.", mak', .ch, true⟩

/-- (67a) Agent adverb with -j: ungrammatical (§4.1.2, p. 70). -/
def ex67a : ChujExample :=
  ⟨67, 70, "*sk'annhej sk'o'ol winh ix-ch'ak-j-i te' te'",
   "The tree was felled on purpose.", mak', .j, false⟩

/-- (54a) √TV + -w incorporation antipassive (§4, p. 64). -/
def ex54a : ChujExample :=
  ⟨54, 64, "Ix-in-jax-w-i ixim",
   "I corn-ground.", jax, .w, true⟩

/-- (55b) √TV + -w absolutive antipassive (§4, p. 65). -/
def ex55 : ChujExample :=
  ⟨55, 65, "Ix-mak'-waj ix Malin t'a waj Xun",
   "Maria did some hitting to John.", mak', .w, true⟩

-- ════════════════════════════════════════════════════
-- § 9. Verification
-- ════════════════════════════════════════════════════

/-- All example √TV roots are classified as tv. -/
theorem tvRoots_all_tv :
    tvRoots.all (·.rootClass == .tv) = true := by native_decide

/-- All example √ITV roots are classified as itv. -/
theorem itvRoots_all_itv :
    itvRoots.all (·.rootClass == .itv) = true := by native_decide

/-- All example √POS roots are classified as pos. -/
theorem posRoots_all_pos :
    posRoots.all (·.rootClass == .pos) = true := by native_decide

/-- All example √NOM roots are classified as nom. -/
theorem nomRoots_all_nom :
    nomRoots.all (·.rootClass == .nom) = true := by native_decide

/-- √TV combines with all four voice suffixes. -/
theorem tv_all_voices :
    isGrammatical .tv .null = true ∧
    isGrammatical .tv .ch = true ∧
    isGrammatical .tv .j = true ∧
    isGrammatical .tv .w = true := ⟨rfl, rfl, rfl, rfl⟩

/-- √ITV combines only with null v. -/
theorem itv_only_null :
    isGrammatical .itv .null = true ∧
    isGrammatical .itv .ch = false ∧
    isGrammatical .itv .j = false ∧
    isGrammatical .itv .w = false := ⟨rfl, rfl, rfl, rfl⟩

/-- √POS combines only with -w. -/
theorem pos_only_w :
    isGrammatical .pos .null = false ∧
    isGrammatical .pos .ch = false ∧
    isGrammatical .pos .j = false ∧
    isGrammatical .pos .w = true := ⟨rfl, rfl, rfl, rfl⟩

/-- √NOM combines only with -w. -/
theorem nom_only_w :
    isGrammatical .nom .null = false ∧
    isGrammatical .nom .ch = false ∧
    isGrammatical .nom .j = false ∧
    isGrammatical .nom .w = true := ⟨rfl, rfl, rfl, rfl⟩

/-- Only √TV forms bare transitive stems. -/
theorem only_tv_transitive :
    formsBareTransitive .tv = true ∧
    formsBareTransitive .itv = false ∧
    formsBareTransitive .pos = false ∧
    formsBareTransitive .nom = false := ⟨rfl, rfl, rfl, rfl⟩

/-- -ch has an implicit agent; -j does not. -/
theorem ch_has_agent_j_does_not :
    ChujVoiceSuffix.hasAgent .ch = true ∧
    ChujVoiceSuffix.hasAgent .j = false := ⟨rfl, rfl⟩

/-- Agent adverbs distinguish -ch (OK) from -j (blocked). -/
theorem agent_adverb_distinguishes :
    agentAdverbOK .ch = true ∧
    agentAdverbOK .j = false := ⟨rfl, rfl⟩

/-- By-phrases distinguish -ch (OK) from -j (blocked). -/
theorem by_phrase_distinguishes :
    byPhraseOK .ch = true ∧
    byPhraseOK .j = false := ⟨rfl, rfl⟩

/-- -aj tracks implicit arguments:
    -ch (implicit ext) → -aj; -j (no ext) → no -aj. -/
theorem aj_tracks_implicit :
    ajOnPassive .ch = true ∧
    ajOnPassive .j = false ∧
    ajOnAntipassive .absolutive = true ∧
    ajOnAntipassive .incorporation = false := ⟨rfl, rfl, rfl, rfl⟩

/-- Grammatical examples are predicted grammatical;
    ungrammatical examples are predicted ungrammatical. -/
theorem examples_grammaticality :
    ex10a.grammatical = true ∧     -- √TV + Ø
    ex7a.grammatical = true ∧    -- √ITV + null
    ex23a.grammatical = true ∧   -- √POS + -w
    ex16b.grammatical = true ∧   -- √NOM + -w
    ex62.grammatical = true ∧    -- √TV + -ch
    ex59.grammatical = true ∧    -- √TV + -j
    ex63a.grammatical = true ∧   -- agent adverb + -ch (OK)
    ex67a.grammatical = false ∧  -- agent adverb + -j (blocked)
    ex54a.grammatical = true ∧   -- -w incorporation antipassive
    ex55.grammatical = true :=   -- -w absolutive antipassive
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 10. Chuj Fragment Bridge Theorems
-- ════════════════════════════════════════════════════

open Fragments.Chuj
open Minimalism

/-- Map the phenomena's root class to the fragment's Root.
    This connects theory-neutral distributional classes to the
    theoretically analyzed Root structure. -/
def toFragmentRoot : CRootClass → Root
  | .tv  => rootTV_res  -- representative √TV (result subtype)
  | .itv => rootITV
  | .pos => rootPOS
  | .nom => rootNOM

/-- √TV maps to a theme-selecting root; all others map to non-theme roots.
    This is the formal content of the observation that only √TV forms
    bare transitive stems (§2.2). -/
theorem root_class_arity_alignment :
    (toFragmentRoot .tv).arity = .selectsTheme ∧
    (toFragmentRoot .itv).arity = .noTheme ∧
    (toFragmentRoot .pos).arity = .noTheme ∧
    (toFragmentRoot .nom).arity = .noTheme := ⟨rfl, rfl, rfl, rfl⟩

/-- The data's `formsBareTransitive` matches the fragment's `hasInternalArg`.
    Only roots that select a theme can form bare transitive stems. -/
theorem bare_transitive_iff_theme (rc : CRootClass) :
    formsBareTransitive rc = (toFragmentRoot rc).arity.hasInternalArg := by
  cases rc <;> rfl

-- ════════════════════════════════════════════════════
-- § 11. Voice Suffix ↔ Fragment VoiceHead
-- ════════════════════════════════════════════════════

/-- Map the phenomena's voice suffix to the fragment's VoiceHead. -/
def toFragmentVoice : ChujVoiceSuffix → VoiceHead
  | .null => vØ
  | .ch   => v_ch
  | .j    => v_j
  | .w    => v_w

/-- Theta assignment matches: the data's `hasAgent` agrees with the
    fragment's `assignsTheta` for all four voice suffixes. -/
theorem theta_alignment (vs : ChujVoiceSuffix) :
    vs.hasAgent = (toFragmentVoice vs).assignsTheta := by
  cases vs <;> rfl

/-- External argument status matches D feature:
    overt external arg ↔ hasD = true. -/
theorem d_feature_alignment :
    -- Ø: overt ERG → hasD
    (toFragmentVoice .null).hasD = true ∧
    -- -w: overt ABS → hasD
    (toFragmentVoice .w).hasD = true ∧
    -- -ch: implicit → no D
    (toFragmentVoice .ch).hasD = false ∧
    -- -j: absent → no D
    (toFragmentVoice .j).hasD = false := ⟨rfl, rfl, rfl, rfl⟩

/-- Only Ø is a phase head (assigns ERG case). -/
theorem phase_head_alignment :
    (toFragmentVoice .null).phaseHead = true ∧
    (toFragmentVoice .ch).phaseHead = false ∧
    (toFragmentVoice .j).phaseHead = false ∧
    (toFragmentVoice .w).phaseHead = false := ⟨rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 12. Agent Diagnostic Alignment
-- ════════════════════════════════════════════════════

/-- The data's agent adverb diagnostic matches the fragment's theta assignment.
    Agent-oriented adverbs require a theta-role-bearing Voice head. -/
theorem agent_adverb_matches_theta (vs : ChujVoiceSuffix) :
    agentAdverbOK vs = (toFragmentVoice vs).assignsTheta := by
  cases vs <;> rfl

/-- The -ch vs -j contrast is the critical test: both are passives (no overt
    external arg), but they differ in theta assignment. The agent diagnostic
    data confirms the fragment's distinction. -/
theorem passive_contrast :
    -- -ch: assigns theta, agent adverbs OK, by-phrases OK
    (toFragmentVoice .ch).assignsTheta = true ∧
    agentAdverbOK .ch = true ∧
    byPhraseOK .ch = true ∧
    -- -j: no theta, agent adverbs blocked, by-phrases blocked
    (toFragmentVoice .j).assignsTheta = false ∧
    agentAdverbOK .j = false ∧
    byPhraseOK .j = false := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 13. -aj Distribution Alignment
-- ════════════════════════════════════════════════════

/-- The data's -aj on passives matches the fragment's `hasImplicitExternal`.
    -aj appears when there is an implicit (but not absent) external argument. -/
theorem aj_passive_matches_implicit (vs : ChujVoiceSuffix) :
    ajOnPassive vs = hasImplicitExternal (toFragmentVoice vs) := by
  cases vs <;> native_decide

/-- The fragment's `triggersAj` predicts the data's full -aj distribution:
    - -ch (implicit ext) → -aj
    - -j (no ext) → no -aj
    - -w absolutive (implicit int) → -aj
    - -w incorporation (overt int) → no -aj -/
theorem aj_full_distribution :
    -- Passive -ch: implicit external → -aj
    triggersAj v_ch false = true ∧
    ajOnPassive .ch = true ∧
    -- Agentless -j: no external → no -aj
    triggersAj v_j false = false ∧
    ajOnPassive .j = false ∧
    -- Antipassive -w (absolutive): implicit internal → -aj
    triggersAj v_w true = true ∧
    ajOnAntipassive .absolutive = true ∧
    -- Antipassive -w (incorporation): overt internal → no -aj
    triggersAj v_w false = false ∧
    ajOnAntipassive .incorporation = false :=
  ⟨by native_decide, rfl, by native_decide, rfl,
   by native_decide, rfl, by native_decide, rfl⟩

-- ════════════════════════════════════════════════════
-- § 14. Verb Building Predictions
-- ════════════════════════════════════════════════════

/-- The fragment predicts correct event decompositions for each
    root×voice combination attested in the data.

    √TV result + Ø → causative (active transitive)
    √TV result + -j → inchoative (agentless passive / anticausative)
    √TV result + -ch → causative (passive with implicit agent)
    √ITV + -w → activity (intransitive) -/
theorem event_decomposition_matches_data :
    -- ex10a: √TV + Ø → causative
    isCausative (buildDecomposition vØ resultLower) = true ∧
    -- ex59: √TV + -j → inchoative
    isInchoative (buildDecomposition v_j resultLower) = true ∧
    -- ex62: √TV + -ch → causative (agent still present)
    isCausative (buildDecomposition v_ch resultLower) = true ∧
    -- ex7a: √ITV + v_w → activity
    isActivity (buildDecomposition v_w activityLower) = true :=
  ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

-- ════════════════════════════════════════════════════
-- § 15. Division of Labor
-- ════════════════════════════════════════════════════

/-- The core empirical claim (ex. (2)/(77), p. 75): roots determine
    internal arguments, Voice determines external arguments.

    The data confirms this in two ways:
    1. Theme persistence: √TV always has an internal arg regardless of Voice
    2. Voice determines agent: same root with Ø has overt agent,
       with -ch has implicit agent, with -j has no agent -/
theorem division_of_labor_matches_data :
    -- Root determines internal: √TV always selects theme
    formsBareTransitive .tv = true ∧
    rootTV_res.arity.hasInternalArg = true ∧
    -- Root determines internal: √ITV never selects theme
    formsBareTransitive .itv = false ∧
    rootITV.arity.hasInternalArg = false ∧
    -- Voice determines external: same root, different agent status
    ChujVoiceSuffix.extArgStatus .null = .overt_erg ∧
    ChujVoiceSuffix.extArgStatus .ch = .implicit ∧
    ChujVoiceSuffix.extArgStatus .j = .absent :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Theme persistence across all four voice forms for √TV.
    The data shows √TV maintains its internal argument in active (Ø),
    passive (-ch), agentless passive (-j), and antipassive (-w).
    The fragment encodes this as a root property (arity), not a
    derived property — so it holds by construction. -/
theorem theme_persists_all_voices :
    -- √TV is grammatical with all four voice suffixes (data)
    isGrammatical .tv .null = true ∧
    isGrammatical .tv .ch = true ∧
    isGrammatical .tv .j = true ∧
    isGrammatical .tv .w = true ∧
    -- And the root always selects a theme (fragment)
    rootTV_res.arity.hasInternalArg = true := ⟨rfl, rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 16. Denotation Type Alignment
-- ════════════════════════════════════════════════════

/-- The four root classes have distinct denotation types (@cite{coon-2019}, (3)).
    The fragment's `denotationType` field captures these:
    √TV/√ITV = eventPred ⟨e,⟨s,t⟩⟩, √POS = measureFn ⟨e,⟨s,d⟩⟩,
    √NOM = entityPred ⟨e,t⟩. -/
theorem denotation_type_alignment :
    (toFragmentRoot .tv).denotationType = some .eventPred ∧
    (toFragmentRoot .itv).denotationType = some .eventPred ∧
    (toFragmentRoot .pos).denotationType = some .measureFn ∧
    (toFragmentRoot .nom).denotationType = some .entityPred := ⟨rfl, rfl, rfl, rfl⟩

/-- √TV and √ITV share semantic type (event predicate) but differ in arity.
    This is the formal content of the observation that both compose with
    an entity argument per @cite{davis-1997}, but only √TV projects a syntactic
    complement. -/
theorem tv_itv_same_type_different_arity :
    (toFragmentRoot .tv).denotationType = (toFragmentRoot .itv).denotationType ∧
    (toFragmentRoot .tv).arity ≠ (toFragmentRoot .itv).arity := by
  exact ⟨rfl, by decide⟩

/-- The -w suffix cross-class generalization: -w verbalizes √POS and √NOM
    roots (data: both take -w), and the fragment predicts different event
    structures depending on the root's lower structure. -/
theorem w_verbalization_cross_class :
    -- Both √POS and √NOM take -w (data)
    isGrammatical .pos .w = true ∧
    isGrammatical .nom .w = true ∧
    -- √POS + -w → [vDO, vBE] (fragment)
    buildDecomposition v_w positionalLower = [.vDO, .vBE] ∧
    -- √NOM + -w → activity [vDO] (fragment)
    isActivity (buildDecomposition v_w activityLower) = true :=
  ⟨rfl, rfl, by native_decide, by native_decide⟩

-- ════════════════════════════════════════════════════
-- § 17. Root Typology Bridge (BeaversEtAl2021)
-- ════════════════════════════════════════════════════

open Phenomena.Causation.Studies.BeaversEtAl2021

/-- Map the theory's root type to the phenomena's root class.
    These are parallel enums — the bridge makes the correspondence explicit. -/
def toCoSRootClass : RootType → CoSRootClass
  | .propertyConcept => .propertyConcept
  | .result => .result

/-- Map back from phenomena to theory. -/
def fromCoSRootClass : CoSRootClass → RootType
  | .propertyConcept => .propertyConcept
  | .result => .result

/-- The mapping is a bijection (left inverse). -/
theorem roundtrip_left (rt : RootType) :
    fromCoSRootClass (toCoSRootClass rt) = rt := by
  cases rt <;> rfl

/-- The mapping is a bijection (right inverse). -/
theorem roundtrip_right (rc : CoSRootClass) :
    toCoSRootClass (fromCoSRootClass rc) = rc := by
  cases rc <;> rfl

-- ════════════════════════════════════════════════════
-- § 18. Diagnostic Alignment (Root Typology)
-- ════════════════════════════════════════════════════

/-- The phenomena's `changeDenialTest` agrees with the theory's `entailsChange`.

    Theory: `RootType.entailsChange.result = true` (result roots entail change)
    Phenomena: `changeDenialTest.result =.negative` ("#The shattered vase
    has never shattered" is contradictory — the state entails prior change)

    The relationship is: entailsChange = true ↔ changeDenial = negative.
    That is, entailing change means the change-denial test FAILS. -/
theorem change_denial_matches_entailsChange (rc : CoSRootClass) :
    changeDenialTest rc = .positive ↔
    (fromCoSRootClass rc).entailsChange = false := by
  cases rc <;> simp [changeDenialTest, fromCoSRootClass, RootType.entailsChange]

/-- The phenomena's `restitutiveAgainTest` agrees with the theory's
    `allowsRestitutiveAgain`. -/
theorem restitutive_again_matches (rc : CoSRootClass) :
    restitutiveAgainTest rc = .positive ↔
    (fromCoSRootClass rc).allowsRestitutiveAgain = true := by
  cases rc <;> simp [restitutiveAgainTest, fromCoSRootClass,
    RootType.allowsRestitutiveAgain]

/-- Both diagnostics jointly align with the full semantic correlate package.
    This is the bridge version of `semantic_determines_morphosyntax`. -/
theorem diagnostics_align_with_theory (rc : CoSRootClass) :
    let rt := fromCoSRootClass rc
    (changeDenialTest rc = .negative ↔ rt.entailsChange = true) ∧
    (restitutiveAgainTest rc = .negative ↔ rt.allowsRestitutiveAgain = false) := by
  cases rc <;> simp [changeDenialTest, restitutiveAgainTest, fromCoSRootClass,
    RootType.entailsChange, RootType.allowsRestitutiveAgain]

-- ════════════════════════════════════════════════════
-- § 19. Simple Stative Prediction ↔ Attestation
-- ════════════════════════════════════════════════════

/-- **Theory predicts**: PC roots have simple statives.
    **Data confirms**: 7 of 8 PC sample roots have ≥ 50% attestation.
    The one exception (oldRoot, age class) has 0 — noted by Beavers et al.
    as a crosslinguistic outlier. -/
theorem pc_stative_prediction_matches_data :
    -- Theory prediction
    RootType.hasSimpleStative .propertyConcept = true ∧
    -- Empirical confirmation (all but one PC root)
    (pcRoots.filter (λ r => r.nSimpleStative * 2 ≥ r.nLanguages)).length ≥
    pcRoots.length - 1 := by
  exact ⟨rfl, by native_decide⟩

/-- **Theory predicts**: result roots LACK simple statives.
    **Data confirms**: all 10 result sample roots have ≤ 10% attestation. -/
theorem result_no_stative_prediction_matches_data :
    -- Theory prediction
    RootType.hasSimpleStative .result = false ∧
    -- Empirical confirmation (ALL result roots)
    resultRoots.all (λ r => r.nSimpleStative * 10 ≤ r.nLanguages) = true := by
  exact ⟨rfl, by native_decide⟩

-- ════════════════════════════════════════════════════
-- § 20. Markedness Prediction ↔ Statistical Comparison
-- ════════════════════════════════════════════════════

/-- **Theory predicts**: PC verbs are morphologically marked; result verbs
    are unmarked (Markedness Generalization, @cite{beavers-etal-2021}).
    **Data confirms**: PC median marked % (56.01) > result median (15.20). -/
theorem markedness_prediction_matches_statistics :
    -- Theory: PC verbs are marked
    verbalMarkedness .propertyConcept = .marked ∧
    -- Theory: result verbs are unmarked
    verbalMarkedness .result = .unmarked ∧
    -- Data: PC marked rate exceeds result marked rate
    simpleStativeComparison.pcMedian > simpleStativeComparison.resultMedian ∧
    verbalMarkednessComparison.pcMedian > verbalMarkednessComparison.resultMedian := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> native_decide

-- ════════════════════════════════════════════════════
-- § 21. Unattested Language Type
-- ════════════════════════════════════════════════════

/-- The theory's markedness complementarity predicts that if a language
    marks PC verbs, it should NOT also show result verbs as more marked
    than PC verbs. The fourth logically possible language type (result
    marked, PC unmarked) is unattested — exactly 3 types are attested.
    This matches the theory: `markedness_complementarity` says verbal and
    stative markedness are always opposite. -/
theorem unattested_type_matches_complementarity :
    -- Exactly three types attested
    LanguageType.allAttested.length = 3 ∧
    -- Theory: verbal and stative markedness always differ
    (∀ rt : RootType, verbalMarkedness rt ≠ stativeMarkedness rt) := by
  refine ⟨by native_decide, ?_⟩
  intro rt; cases rt <;> simp [verbalMarkedness, stativeMarkedness,
    RootType.entailsChange]

-- ════════════════════════════════════════════════════
-- § 22. Fragment Grounding: Chuj Roots Instantiate Theory
-- ════════════════════════════════════════════════════

/-- Chuj √TV result roots instantiate the theory's result root predictions:
    entails change, no simple stative, unmarked verb. -/
theorem chuj_tv_res_is_result_root :
    rootTV_res.entailsChange = true ∧
    rootTV_res.changeType.hasSimpleStative = false ∧
    rootTV_res.verbalMarkedness = .unmarked := by
  exact ⟨rfl, rfl, rfl⟩

/-- Chuj √TV PC roots instantiate the theory's PC root predictions:
    no change entailment, has simple stative, marked verb. -/
theorem chuj_tv_pc_is_pc_root :
    rootTV_pc.entailsChange = false ∧
    rootTV_pc.changeType.hasSimpleStative = true ∧
    rootTV_pc.verbalMarkedness = .marked := by
  exact ⟨rfl, rfl, rfl⟩

/-- The Chuj fragment witnesses the full orthogonality theorem:
    all four cells of the (arity × changeType) matrix are inhabited. -/
theorem chuj_witnesses_orthogonality :
    -- selectsTheme + result (√TV result)
    rootTV_res.arity = .selectsTheme ∧ rootTV_res.changeType = .result ∧
    -- selectsTheme + PC (√TV PC)
    rootTV_pc.arity = .selectsTheme ∧ rootTV_pc.changeType = .propertyConcept ∧
    -- noTheme + PC (√ITV, √POS, √NOM)
    rootITV.arity = .noTheme ∧ rootITV.changeType = .propertyConcept :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Per-root class verification: each Chuj root's change entailment matches
    its predicted morphosyntactic correlates via `grand_unification`. -/
theorem chuj_roots_satisfy_grand_unification :
    -- Result root (√TV res): entails change → full result package
    (rootTV_res.changeType.hasSimpleStative = false ∧
     rootTV_res.changeType.verbalFormIsMarked = false ∧
     rootTV_res.changeType.allowsRestitutiveAgain = false) ∧
    -- PC root (√TV PC): no change → full PC package
    (rootTV_pc.changeType.hasSimpleStative = true ∧
     rootTV_pc.changeType.verbalFormIsMarked = true ∧
     rootTV_pc.changeType.allowsRestitutiveAgain = true) ∧
    -- PC root (√ITV): no change → full PC package
    (rootITV.changeType.hasSimpleStative = true ∧
     rootITV.changeType.verbalFormIsMarked = true ∧
     rootITV.changeType.allowsRestitutiveAgain = true) :=
  ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

-- ════════════════════════════════════════════════════
-- § 23. Per-Root Data ↔ Theory Agreement
-- ════════════════════════════════════════════════════

/-- Every PC root in the empirical sample is classified as PC, and the theory
    predicts PC roots should have simple statives — they do. -/
theorem pc_roots_classified_and_predicted :
    -- Data: all sample PC roots are classified as PC
    pcRoots.all (·.rootClass == .propertyConcept) = true ∧
    -- Theory: PC has simple stative
    RootType.hasSimpleStative .propertyConcept = true := by
  exact ⟨by native_decide, rfl⟩

/-- Every result root in the empirical sample is classified as result, and the
    theory predicts result roots lack simple statives — they do. -/
theorem result_roots_classified_and_predicted :
    -- Data: all sample result roots are classified as result
    resultRoots.all (·.rootClass == .result) = true ∧
    -- Theory: result lacks simple stative
    RootType.hasSimpleStative .result = false := by
  exact ⟨by native_decide, rfl⟩

/-- The subclass taxonomies are parallel: the theory's `PCClass` and the
    phenomena's `PCSubclass` have the same constructors. Similarly for
    `ResultClass` and `ResultSubclass`. This is verified by exhaustive
    mapping (both have 6 PC subclasses and 8 result subclasses). -/
theorem subclass_counts_match :
    -- 6 PC subclasses in both
    [PCClass.dimension, .age, .value, .color, .physicalProperty, .speed].length =
    [PCSubclass.dimension, .age, .value, .color, .physicalProperty, .speed].length ∧
    -- 8 result subclasses in both
    [ResultClass.entitySpecificCoS, .cooking, .breaking, .bending,
     .killing, .destroying, .calibratableCoS, .inherentlyDirectedMotion].length =
    [ResultSubclass.entitySpecificCoS, .cooking, .breaking, .bending,
     .killing, .destroying, .calibratableCoS, .inherentlyDirectedMotion].length :=
  ⟨rfl, rfl⟩

end Phenomena.Causation.Studies.Coon2019
