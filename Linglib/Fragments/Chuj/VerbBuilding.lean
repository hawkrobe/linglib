import Linglib.Theories.Morphology.RootTypology
import Linglib.Core.VoiceSystem

/-!
# Chuj Verb Building Fragment @cite{coon-2019}
@cite{davis-1997}

Theory-neutral fragment for Chuj (Q'anjob'alan, Mayan), encoding
root classification, voice morphology, paradigm grammaticality, and
lexical inventory from @cite{coon-2019} "Building verbs in Chuj:
Consequences for the nature of roots."

## Contents

1. **Root classes** (§§1–3): four abstract `Root` types (√TV, √ITV, √POS, √NOM)
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

**RootArity captures complement projection, not semantic type.**
Coon's semantic types (3) group {√TV, √ITV} together as ⟨e, ⟨s,t⟩⟩ — both
compose with an entity argument per @cite{davis-1997}. But syntactically, only
√TV projects a complement DP that persists across voice alternations; √ITV's
entity argument becomes the subject. Our `RootArity.selectsTheme` captures
the syntactic complement projection, giving {√TV} vs {√ITV, √POS, √NOM}.
This matches the -aj diagnostic: -aj marks implicit arguments, and only √TV
stems show -aj (the theme can be implicit), not √ITV.

-/

namespace Fragments.Chuj

-- ============================================================================
-- § 1: Abstract Root Classes
-- ============================================================================

/-- √TV root (PC): selects theme, no entailed change-of-state.
    Semantic type ⟨e, ⟨s,t⟩⟩ (@cite{coon-2019}, (3)).
    Examples: mak' "hit", tek' "kick". -/
def rootTV_pc : Root :=
  { arity := .selectsTheme, changeType := .propertyConcept,
    denotationType := some .eventPred }

/-- √TV root (result): selects theme, entails change-of-state.
    Semantic type ⟨e, ⟨s,t⟩⟩ (@cite{coon-2019}, (3)).
    Examples: jatz' "hit (breaking)", tzak' "wrap". -/
def rootTV_res : Root :=
  { arity := .selectsTheme, changeType := .result,
    denotationType := some .eventPred }

/-- √ITV root: semantic type ⟨e, ⟨s,t⟩⟩ (same as √TV per @cite{davis-1997}),
    but does NOT project a complement — the entity argument becomes the
    subject. The class is morphologically defined: roots that appear
    with null v/Voice⁰ in intransitive stems (p. 40).
    Examples: way "sleep", ok' "cry", jaw "arrive", b'at "go". -/
def rootITV : Root :=
  { arity := .noTheme, changeType := .propertyConcept,
    denotationType := some .eventPred }

/-- √POS root: positional/stative. Semantic type ⟨e, ⟨s,d⟩⟩ — a
    measure function, not a truth-value predicate.
    Examples: chot "sit", kot "on all fours", watz "lie face down". -/
def rootPOS : Root :=
  { arity := .noTheme, changeType := .propertyConcept,
    denotationType := some .measureFn }

/-- √NOM root: nominal base. Semantic type ⟨e,t⟩ — entity predicate
    with no event argument (@cite{coon-2019}, (3)).
    Examples: a' "water", ixim "corn", chanhal "dance". -/
def rootNOM : Root :=
  { arity := .noTheme, changeType := .propertyConcept,
    denotationType := some .entityPred }

-- ============================================================================
-- § 2: Four-Way Root Classification (@cite{coon-2019}, (3))
-- ============================================================================

/-- Coon's four root classes are recovered as (arity × denotationType) pairs.
    √TV = selectsTheme + eventPred, √ITV = noTheme + eventPred,
    √POS = noTheme + measureFn, √NOM = noTheme + entityPred. -/
theorem four_way_classification :
    rootTV_res.arity = .selectsTheme ∧
    rootTV_res.denotationType = some .eventPred ∧
    rootITV.arity = .noTheme ∧
    rootITV.denotationType = some .eventPred ∧
    rootPOS.arity = .noTheme ∧
    rootPOS.denotationType = some .measureFn ∧
    rootNOM.arity = .noTheme ∧
    rootNOM.denotationType = some .entityPred := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The four root classes are pairwise distinguishable: no two share
    both arity and denotationType. -/
theorem root_classes_pairwise_distinct :
    (rootTV_res.arity ≠ rootITV.arity) ∧
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

/-- Map an abstract Root to the distributional CRootClass.
    The bridge is determined by (arity × denotationType). -/
def rootToClass (r : Root) : CRootClass :=
  match r.arity, r.denotationType with
  | .selectsTheme, _               => .tv
  | .noTheme,      some .eventPred  => .itv
  | .noTheme,      some .measureFn  => .pos
  | _,             _                => .nom

/-- The bridge is correct for each abstract root definition. -/
theorem rootToClass_correct :
    rootToClass rootTV_pc  = .tv  ∧
    rootToClass rootTV_res = .tv  ∧
    rootToClass rootITV    = .itv ∧
    rootToClass rootPOS    = .pos ∧
    rootToClass rootNOM    = .nom := by decide

-- ============================================================================
-- § 4: Voice Suffixes (ex. (78), pp. 75–76)
-- ============================================================================

/-- The four voice suffixes in Chuj (ex. (78), pp. 75–76). -/
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

-- ============================================================================
-- § 7: -aj Distribution (§4.2, ex. (78))
-- ============================================================================

/-- Whether -aj (existential closure) appears on a √TV stem in each
    voice form (ex. (78), pp. 75–76; §4.2, p. 72).

    -aj marks the presence of an implicit argument:
    - Ø: no implicit arg → no -aj
    - -ch: implicit external arg → -aj on stem (§4.1.1, p. 68)
    - -j: no external arg at all → no -aj
    - -w (absolutive): implicit internal arg → -aj (ex. (55c), p. 65)
    - -w (incorporation): overt bare NP internal arg → no -aj (ex. (54a), p. 64) -/
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

/-- Chuj voice system: four-way asymmetrical (Ø, -w, -ch, -j).

    Unlike pivot systems (Toba Batak, Tagalog), Chuj voices don't
    promote arguments to a privileged position. Instead, Voice controls
    whether an external argument is overt, implicit, or absent.
    Each voice form is built independently from root + v/Voice⁰: passive
    is not derived from active. -/
def chujVoiceSystem : Interfaces.VoiceSystemProfile :=
  { language := "Chuj"
    voices := [ ⟨"Active (Ø)", .agent⟩
              , ⟨"Agentive intransitive (-w)", .agent⟩
              , ⟨"Passive (-ch)", .patient⟩
              , ⟨"Agentless passive (-j)", .patient⟩ ]
    symmetry := .asymmetrical
    notes := "Non-pivot system; Voice controls EA status (Coon 2019)" }

theorem chuj_voice_system_asymmetrical :
    chujVoiceSystem.symmetry = .asymmetrical := rfl

theorem chuj_voice_count :
    chujVoiceSystem.voiceCount = 4 := rfl

/-- Chuj is NOT a simple active/passive: it has 4 voices, not 2. -/
theorem chuj_not_simple_active_passive :
    chujVoiceSystem.isActivePassive = false := rfl

theorem chuj_no_oblique_pivots :
    chujVoiceSystem.distinguishesObliques = false := rfl

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
  root : Root
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
def lich' : ChujRoot := ⟨"lich'", "leaning", rootPOS⟩
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
  [chot, jenh, lich', b'ul]

/-- All √NOM roots from Table (5). -/
def nomRoots : List ChujRoot :=
  [pat, k'atzitz, ixim, winak, chanhal]

-- ============================================================================
-- § 11: Verification
-- ============================================================================

-- Root classification
theorem tvRoots_selectTheme :
    tvRoots.all (·.root.arity == .selectsTheme) = true := by native_decide

theorem itvRoots_noTheme :
    itvRoots.all (·.root.arity == .noTheme) = true := by native_decide

theorem posRoots_measureFn :
    posRoots.all (·.root.denotationType == some .measureFn) = true := by native_decide

theorem nomRoots_entityPred :
    nomRoots.all (·.root.denotationType == some .entityPred) = true := by native_decide

-- Root↔CRootClass bridge
theorem tvRoots_bridge :
    tvRoots.all (λ r => rootToClass r.root == .tv) = true := by native_decide

theorem itvRoots_bridge :
    itvRoots.all (λ r => rootToClass r.root == .itv) = true := by native_decide

theorem posRoots_bridge :
    posRoots.all (λ r => rootToClass r.root == .pos) = true := by native_decide

theorem nomRoots_bridge :
    nomRoots.all (λ r => rootToClass r.root == .nom) = true := by native_decide

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

end Fragments.Chuj
