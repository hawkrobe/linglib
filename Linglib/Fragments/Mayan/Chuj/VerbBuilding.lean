import Linglib.Semantics.ArgumentStructure.Root.Classification
import Linglib.Syntax.Voice.Basic

/-!
# Chuj Verb Building Fragment [coon-2019]
[davis-1997]

Theory-neutral fragment for Chuj (Q'anjob'alan, Mayan), encoding
root classification, voice morphology, paradigm grammaticality, and
lexical inventory from [coon-2019] "Building verbs in Chuj:
Consequences for the nature of roots."

## Contents

1. **Root classes** (§§1–3): four abstract `Classification` types (√TV, √ITV, √POS, √NOM)
   with distributional `CRootClass` enum and bridge function.
2. **Voice suffixes** (§§4–5): `ChujVoiceSuffix` (Ø, -ch, -j, -w) with
   external argument status, thematic properties, and morphological forms.
3. **Paradigm grammaticality** (§6): which root×voice combinations are
   grammatical, and which roots form bare transitive stems.
4. **-aj distribution** (§7): existential closure suffix distribution
   across voice forms and antipassive subtypes.
5. **Agent diagnostics** (§8): agent-oriented adverb and by-phrase tests
   distinguishing -ch (implicit agent) from -j (no agent).
6. **Voice system profile** (§9): four-way asymmetrical voice system.
7. **Root lexicon** (§10): `ChujRoot` entries from Table (5) and
   additional examples in the paper.
8. **Verification theorems** (§11): paradigm, -aj, agent diagnostic,
   and root classification checks.

## Modeling Notes

**√TV and √ITV share type and valency; transitive-Voice licensing
separates them.** Coon's semantic types (3) group {√TV, √ITV} together as
⟨e,⟨s,t⟩⟩ — both compose with an internal entity argument per
[davis-1997], and √ITV roots are unaccusative (§3.3), so both carry
valency `{.internal}`. What only √TV has is compatibility with the
transitive-forming v ~ Voice⁰ head that merges an agent
(`licensesTransitiveVoice`) — the source of which Coon expressly declines
to formalize. The -aj diagnostic tracks this: only √TV stems show -aj.

-/

namespace Chuj

open Verb Verb.Root

-- ============================================================================
-- § 1: Abstract Root Classes
-- ============================================================================

/-- √TV root (PC): selects theme, no entailed change-of-state.
    Semantic type ⟨e, ⟨s,t⟩⟩ ([coon-2019], (3)).
    Examples: mak' "hit", tek' "kick". -/
def rootTV_pc : Classification :=
  { valency := {.internal}, changeType := .propertyConcept,
    denotationType := some (.e ⇒ .s ⇒ .t), licensesTransitiveVoice := true }

/-- √TV root (result): selects theme, entails change-of-state.
    Semantic type ⟨e, ⟨s,t⟩⟩ ([coon-2019], (3)). The PC/result
    subdivision of √TV is [beavers-etal-2021]'s axis (after
    [dixon-1982]); [coon-2019] does not subdivide √TV. -/
def rootTV_res : Classification :=
  { valency := {.internal}, changeType := .result,
    denotationType := some (.e ⇒ .s ⇒ .t), licensesTransitiveVoice := true }

/-- √ITV root: semantic type ⟨e,⟨s,t⟩⟩, same as √TV per [davis-1997],
    and unaccusative — it combines with an internal argument (§3.3), so
    its valency is `{.internal}` like √TV's. What it lacks is
    compatibility with the transitive-forming v/Voice⁰ head. The class is
    morphologically defined: roots that appear with null v/Voice⁰ in
    intransitive stems (p. 40).
    `changeType := .propertyConcept` is a placeholder: [coon-2019]
    (p. 60) includes change-of-state verbs like *k'ib'* "grow" and
    *cham* "die" in √ITV, so the class is not uniform on this axis.
    Examples: way "sleep", ok' "cry", jaw "arrive", b'at "go". -/
def rootITV : Classification :=
  { valency := {.internal}, changeType := .propertyConcept,
    denotationType := some (.e ⇒ .s ⇒ .t) }

/-- √POS root: positional/stative. Semantic type ⟨e, ⟨s,d⟩⟩ — a
    measure function, not a truth-value predicate ([coon-2019]
    following [henderson-2017]).
    Examples: chot "crouched", kot "on four legs", tel "lying down". -/
def rootPOS : Classification :=
  { valency := ∅, changeType := .propertyConcept,
    denotationType := some (.e ⇒ .s ⇒ .d) }

/-- √NOM root: nominal base. Semantic type ⟨e,t⟩ — entity predicate
    with no event argument ([coon-2019], (3)).
    Examples: pat "house", ixim "corn", chanhal "dance". -/
def rootNOM : Classification :=
  { valency := ∅, changeType := .propertyConcept,
    denotationType := some (.e ⇒ .t) }

-- ============================================================================
-- § 2: Four-Way Root Classification ([coon-2019], (3))
-- ============================================================================

/-- Coon's four root classes in their coordinates: √TV and √ITV share
    type ⟨e,⟨s,t⟩⟩ and internal-argument valency, split by
    transitive-Voice licensing; √POS is the measure-function type
    ⟨e,⟨s,d⟩⟩ and √NOM the entity predicate ⟨e,t⟩. -/
theorem four_way_classification :
    rootTV_res.licensesTransitiveVoice = true ∧
    rootTV_res.denotationType = some (.e ⇒ .s ⇒ .t) ∧
    rootITV.licensesTransitiveVoice = false ∧
    rootITV.denotationType = some (.e ⇒ .s ⇒ .t) ∧
    rootPOS.valency = ∅ ∧
    rootPOS.denotationType = some (.e ⇒ .s ⇒ .d) ∧
    rootNOM.valency = ∅ ∧
    rootNOM.denotationType = some (.e ⇒ .t) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The four root classes are pairwise distinguishable: √TV and √ITV by
    transitive-Voice licensing, the intransitive classes by semantic
    type. -/
theorem root_classes_pairwise_distinct :
    (rootTV_res.licensesTransitiveVoice ≠ rootITV.licensesTransitiveVoice) ∧
    (rootITV.denotationType ≠ rootPOS.denotationType) ∧
    (rootITV.denotationType ≠ rootNOM.denotationType) ∧
    (rootPOS.denotationType ≠ rootNOM.denotationType) := by
  exact ⟨by decide, by decide, by decide, by decide⟩

-- ============================================================================
-- § 3: CRootClass and Bridge
-- ============================================================================

/-- The four morphosyntactic root classes in Chuj, identified by
    surface distribution (which suffixes they combine with, whether
    they form bare transitive stems). Labels follow Coon's notation. -/
inductive CRootClass where
  | tv   -- transitive roots: form bare transitive stems
  | itv  -- intransitive roots: take null v in intransitive stems
  | pos  -- positional roots: require -w for verbalization
  | nom  -- nominal roots: require -w for verbalization
  deriving DecidableEq, Repr

/-- Map an abstract Classification to the distributional CRootClass.
    The bridge is determined by (transitive-Voice licensing × semantic
    type). -/
def rootToClass (r : Classification) : CRootClass :=
  if r.licensesTransitiveVoice then .tv
  else match r.denotationType with
  | some (.fn .e (.fn .s .t)) => .itv
  | some (.fn .e (.fn .s .d)) => .pos
  | _ => .nom

/-- The bridge is correct for each abstract root definition. -/
theorem rootToClass_correct :
    rootToClass rootTV_pc  = .tv  ∧
    rootToClass rootTV_res = .tv  ∧
    rootToClass rootITV    = .itv ∧
    rootToClass rootPOS    = .pos ∧
    rootToClass rootNOM    = .nom := by decide

-- ============================================================================
-- § 4: Voice Suffixes (ex. (78), p. 76)
-- ============================================================================

/-- The four voice suffixes in Chuj (ex. (78), p. 76). -ch and -w are
    [coon-2019]'s decomposed morphemes: the attested stems are *-chaj*
    and *-waj*, analyzed as -ch and -w plus -aj (table (58), p. 66;
    §4.2). -/
inductive ChujVoiceSuffix where
  | null  -- Ø: active transitive
  | ch    -- -ch: passive with implicit agent
  | j     -- -j: agentless passive
  | w     -- -w: antipassive / verbalizer
  deriving DecidableEq, Repr

/-- The morphological form of each suffix. -/
def ChujVoiceSuffix.form : ChujVoiceSuffix → String
  | .null => "Ø"
  | .ch   => "-ch"
  | .j    => "-j"
  | .w    => "-w"

-- ============================================================================
-- § 5: External Argument Properties (ex. (78))
-- ============================================================================

/-- Status of the external argument for each voice form. -/
inductive ExtArgStatus where
  | overt_erg   -- overt, ergative case (transitive subject)
  | overt_abs   -- overt, absolutive case (intransitive subject)
  | implicit    -- semantically present but not syntactically realized
  | absent      -- no external argument at all
  deriving DecidableEq, Repr

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

-- ============================================================================
-- § 6: Paradigm Grammaticality (§§2–4)
-- ============================================================================

/-- Whether a root class can combine with a voice suffix to form
    a grammatical verb stem.

    Based on the distributional facts in §§2–5:
    - √TV: all four voices (Ø, -ch, -j, -w) — ex. (78)
    - √ITV: null v only (§2.1, p. 40)
    - √POS: -w only (§3.1, (20)/(22), p. 47)
    - √NOM: -w only (§3.1, p. 46) -/
def isGrammatical (rc : CRootClass) (vs : ChujVoiceSuffix) : Bool :=
  match rc, vs with
  | .tv,  _     => true   -- √TV combines with all four
  | .itv, .null => true   -- √ITV takes null v (§2.1)
  | .pos, .w    => true   -- √POS takes -w ((20)/(22), p. 47)
  | .nom, .w    => true   -- √NOM takes -w (§3.1)
  | _,    _     => false

/-- √TV is the only class that forms bare transitive stems (§2.2, p. 41). -/
def formsBareTransitive (rc : CRootClass) : Bool :=
  match rc with
  | .tv => true
  | _   => false

-- ============================================================================
-- § 7: -aj Distribution (§4.2, ex. (78))
-- ============================================================================

/-! -aj marks the presence of an implicit argument on a √TV stem
(ex. (78), p. 76; §4.2, p. 72) — [coon-2019] (p. 73) proposes it is
an overt reflex of Existential Closure ([diesing-1992]):
- Ø: no implicit arg → no -aj
- -ch: implicit external arg → -aj on stem (§4.1.1, p. 68)
- -j: no external arg at all → no -aj
- -w (absolutive): implicit internal arg → -aj (ex. (55c), p. 65)
- -w (incorporation): overt bare NP internal arg → no -aj (ex. (54a), p. 64) -/

/-- The two antipassive (-w) subtypes: absolutive (implicit theme,
    ex. (55b–c), p. 65) vs incorporation (overt bare-NP theme,
    ex. (54a), p. 64). -/
inductive AntipassiveType where
  | absolutive      -- theme is implicit (suppressed)
  | incorporation   -- theme is overt bare NP (incorporated)
  deriving DecidableEq, Repr

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

-- ============================================================================
-- § 8: Agent Diagnostics (§4.1–4.2)
-- ============================================================================

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

-- ============================================================================
-- § 9: Voice System Profile
-- ============================================================================

/-! ### Chuj voice system

    Four-way asymmetrical (Ø, -w, -ch, -j). Unlike pivot systems
    (Toba Batak, Tagalog), Chuj voices don't promote arguments to a
    privileged position. Instead, Voice controls whether an external
    argument is overt, implicit, or absent. Each voice form is built
    independently from root + v/Voice⁰: passive is not derived from
    active. -/
namespace VoiceSystem

def voices : List Voice.VoiceEntry :=
  [ ⟨"Active (Ø)", .agent⟩
  , ⟨"Agentive intransitive (-w)", .agent⟩
  , ⟨"Passive (-ch)", .patient⟩
  , ⟨"Agentless passive (-j)", .patient⟩ ]

def symmetry : Voice.VoiceSystemSymmetry := .asymmetrical

end VoiceSystem

theorem chuj_voice_system_asymmetrical :
    VoiceSystem.symmetry = .asymmetrical := rfl

theorem chuj_voice_count :
    Voice.voiceCount VoiceSystem.voices = 4 := rfl

/-- Chuj is NOT a simple active/passive: it has 4 voices, not 2. -/
theorem chuj_not_simple_active_passive :
    ¬ Voice.isActivePassive VoiceSystem.voices := by decide

theorem chuj_no_oblique_pivots :
    ¬ Voice.distinguishesObliques VoiceSystem.voices := by decide

-- ============================================================================
-- § 10: Root Lexicon (Table (5), p. 39)
-- ============================================================================

/-- A Chuj root entry from the paper's lexicon. -/
structure ChujRoot where
  /-- Chuj root form -/
  form : String
  /-- English gloss -/
  gloss : String
  /-- Abstract root class -/
  root : Classification
  deriving Repr, BEq

-- √TV roots (Table (5), p. 39)
def xik   : ChujRoot := ⟨"xik",   "chop", rootTV_pc⟩
def chonh : ChujRoot := ⟨"chonh", "sell", rootTV_pc⟩
def jax   : ChujRoot := ⟨"jax",   "grind", rootTV_pc⟩
def chel  : ChujRoot := ⟨"chel",  "hug", rootTV_pc⟩
def tek'  : ChujRoot := ⟨"tek'",  "kick", rootTV_pc⟩

-- √TV roots from examples (not in Table (5))
def mak'  : ChujRoot := ⟨"mak'",  "hit", rootTV_pc⟩    -- ex. (55b), p. 65
def il    : ChujRoot := ⟨"il",    "see", rootTV_pc⟩     -- ex. (10d), p. 41
def ch'ak : ChujRoot := ⟨"ch'ak", "fell", rootTV_pc⟩   -- ex. (63a), p. 68
def b'o'  : ChujRoot := ⟨"b'o'",  "make", rootTV_pc⟩   -- ex. (62), p. 68
def man   : ChujRoot := ⟨"man",   "buy", rootTV_pc⟩    -- ex. (59a), p. 67

-- √ITV roots (Table (5), p. 39)
def b'at  : ChujRoot := ⟨"b'at",  "go", rootITV⟩
def way   : ChujRoot := ⟨"way",   "sleep", rootITV⟩
def k'ey  : ChujRoot := ⟨"k'ey",  "ascend", rootITV⟩
def jaw   : ChujRoot := ⟨"jaw",   "arrive", rootITV⟩
def ok'   : ChujRoot := ⟨"ok'",   "cry", rootITV⟩

-- √POS roots (Table (5), p. 39)
def chot  : ChujRoot := ⟨"chot",  "crouched", rootPOS⟩
def jenh  : ChujRoot := ⟨"jenh",  "outstretched", rootPOS⟩
def chek' : ChujRoot := ⟨"chek'", "leaning", rootPOS⟩
def lich' : ChujRoot := ⟨"lich'", "extended", rootPOS⟩
def b'ul  : ChujRoot := ⟨"b'ul",  "gathered", rootPOS⟩

-- √POS roots from Table (20), p. 47
def kot   : ChujRoot := ⟨"kot",   "on four legs", rootPOS⟩
def tel   : ChujRoot := ⟨"tel",   "lying down", rootPOS⟩

-- √NOM roots (Table (5), p. 39)
def pat      : ChujRoot := ⟨"pat",      "house", rootNOM⟩
def k'atzitz : ChujRoot := ⟨"k'atzitz", "wood", rootNOM⟩
def ixim     : ChujRoot := ⟨"ixim",     "corn", rootNOM⟩
def winak    : ChujRoot := ⟨"winak",    "man", rootNOM⟩
def chanhal  : ChujRoot := ⟨"chanhal",  "dance", rootNOM⟩

-- √NOM roots from Table (17), p. 46
def at'is    : ChujRoot := ⟨"at'is",    "sneeze", rootNOM⟩
def tz'ib'   : ChujRoot := ⟨"tz'ib'",   "writing", rootNOM⟩

/-- All √TV roots from Table (5). -/
def tvRoots : List ChujRoot :=
  [xik, chonh, jax, chel, tek']

/-- All √ITV roots from Table (5). -/
def itvRoots : List ChujRoot :=
  [b'at, way, k'ey, jaw, ok']

/-- All √POS roots from Table (5). -/
def posRoots : List ChujRoot :=
  [chot, jenh, chek', lich', b'ul]

/-- All √NOM roots from Table (5). -/
def nomRoots : List ChujRoot :=
  [pat, k'atzitz, ixim, winak, chanhal]

-- ============================================================================
-- § 11: Verification
-- ============================================================================

-- Root classification. Both √TV and √ITV select a theme (p. 61);
-- what distinguishes them is transitive-Voice licensing.
theorem tvRoots_licenseTransitiveVoice :
    tvRoots.all (·.root.licensesTransitiveVoice) = true := by decide

theorem itvRoots_noTransitiveVoice :
    itvRoots.all (fun v => !v.root.licensesTransitiveVoice) = true := by decide

theorem posRoots_measureFn :
    posRoots.all (·.root.denotationType == some (.e ⇒ .s ⇒ .d)) = true := by decide

theorem nomRoots_entityPred :
    nomRoots.all (·.root.denotationType == some (.e ⇒ .t)) = true := by decide

-- Root↔CRootClass bridge
theorem tvRoots_bridge :
    tvRoots.all (λ r => rootToClass r.root == .tv) = true := by decide

theorem itvRoots_bridge :
    itvRoots.all (λ r => rootToClass r.root == .itv) = true := by decide

theorem posRoots_bridge :
    posRoots.all (λ r => rootToClass r.root == .pos) = true := by decide

theorem nomRoots_bridge :
    nomRoots.all (λ r => rootToClass r.root == .nom) = true := by decide

-- Paradigm grammaticality
theorem tv_all_voices :
    isGrammatical .tv .null = true ∧
    isGrammatical .tv .ch = true ∧
    isGrammatical .tv .j = true ∧
    isGrammatical .tv .w = true := ⟨rfl, rfl, rfl, rfl⟩

theorem itv_only_null :
    isGrammatical .itv .null = true ∧
    isGrammatical .itv .ch = false ∧
    isGrammatical .itv .j = false ∧
    isGrammatical .itv .w = false := ⟨rfl, rfl, rfl, rfl⟩

theorem pos_only_w :
    isGrammatical .pos .null = false ∧
    isGrammatical .pos .ch = false ∧
    isGrammatical .pos .j = false ∧
    isGrammatical .pos .w = true := ⟨rfl, rfl, rfl, rfl⟩

theorem nom_only_w :
    isGrammatical .nom .null = false ∧
    isGrammatical .nom .ch = false ∧
    isGrammatical .nom .j = false ∧
    isGrammatical .nom .w = true := ⟨rfl, rfl, rfl, rfl⟩

theorem only_tv_transitive :
    formsBareTransitive .tv = true ∧
    formsBareTransitive .itv = false ∧
    formsBareTransitive .pos = false ∧
    formsBareTransitive .nom = false := ⟨rfl, rfl, rfl, rfl⟩

-- Agent diagnostics
theorem ch_has_agent_j_does_not :
    ChujVoiceSuffix.hasAgent .ch = true ∧
    ChujVoiceSuffix.hasAgent .j = false := ⟨rfl, rfl⟩

theorem agent_adverb_distinguishes :
    agentAdverbOK .ch = true ∧
    agentAdverbOK .j = false := ⟨rfl, rfl⟩

theorem by_phrase_distinguishes :
    byPhraseOK .ch = true ∧
    byPhraseOK .j = false := ⟨rfl, rfl⟩

-- -aj distribution
theorem aj_tracks_implicit :
    ajOnPassive .ch = true ∧
    ajOnPassive .j = false ∧
    ajOnAntipassive .absolutive = true ∧
    ajOnAntipassive .incorporation = false := ⟨rfl, rfl, rfl, rfl⟩

end Chuj
