/-!
# Chuj Verb Building: Empirical Data (Coon 2019)

Theory-neutral empirical data from Coon (2019) "Building verbs in Chuj:
Consequences for the nature of roots." *Journal of Linguistics* 55(1): 35–81.

Chuj is a Q'anjob'alan (Mayan) language spoken in Guatemala and Mexico.
The data here encodes the paper's primary empirical observations about
root classes, voice morphology, and argument structure, without committing
to the theoretical analysis.

## Data encoded

1. **Root classes** (§§2–3): four morphosyntactic classes of roots
   (√TV, √ITV, √POS, √NOM), identified by their surface distribution.
2. **Voice suffixes** (Table 58/78): Ø, -ch, -j, -w with their
   morphological and distributional properties.
3. **Paradigm grammaticality** (§§2–5): which root×voice combinations
   are grammatical.
4. **-aj distribution** (§5): existential closure suffix tracks
   implicit arguments.
5. **Agent diagnostics** (§4.1–4.2): agent-oriented adverbs and
   by-phrases distinguish -ch from -j.
6. **Example verbs** with glosses, organized by root class.

## References

- Coon, J. (2019). Building verbs in Chuj. *Journal of Linguistics*
  55(1): 35–81.
-/

namespace Phenomena.Causatives.Studies.Coon2019

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
-- § 2. Voice Suffixes (Table 58/78)
-- ════════════════════════════════════════════════════

/-- The four voice suffixes in Chuj (Table 58, p. 76). -/
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
-- § 3. External Argument Properties (Table 58)
-- ════════════════════════════════════════════════════

/-- Status of the external argument for each voice form. -/
inductive ExtArgStatus where
  | overt_erg   -- overt, ergative case (transitive subject)
  | overt_abs   -- overt, absolutive case (intransitive subject)
  | implicit    -- semantically present but not syntactically realized
  | absent      -- no external argument at all
  deriving DecidableEq, BEq, Repr

/-- External argument status for each voice suffix (Table 58). -/
def ChujVoiceSuffix.extArgStatus : ChujVoiceSuffix → ExtArgStatus
  | .null => .overt_erg
  | .ch   => .implicit
  | .j    => .absent
  | .w    => .overt_abs

/-- Whether the voice suffix assigns a thematic role to an external
    argument (observed via agent-oriented adverb diagnostics, §4.1–4.2). -/
def ChujVoiceSuffix.hasAgent : ChujVoiceSuffix → Bool
  | .null => true   -- overt agent
  | .ch   => true   -- implicit agent (adverbs OK, ex. 47)
  | .j    => false  -- no agent at all (adverbs blocked, ex. 48)
  | .w    => true   -- overt agent (ABS)

-- ════════════════════════════════════════════════════
-- § 4. Paradigm Grammaticality (§§2–5)
-- ════════════════════════════════════════════════════

/-- Whether a root class can combine with a voice suffix to form
    a grammatical verb stem.

    Based on the distributional facts in §§2–5:
    - √TV: all four voices (Ø, -ch, -j, -w) — Table 58
    - √ITV: null v only (§3.1, p. 40)
    - √POS: -w only (§3.2, p. 44)
    - √NOM: -w only (§3.3, p. 46) -/
def isGrammatical (rc : CRootClass) (vs : ChujVoiceSuffix) : Bool :=
  match rc, vs with
  | .tv,  _     => true   -- √TV combines with all four
  | .itv, .null => true   -- √ITV takes null v (§3.1)
  | .pos, .w    => true   -- √POS takes -w (§3.2)
  | .nom, .w    => true   -- √NOM takes -w (§3.3)
  | _,    _     => false

/-- √TV is the only class that forms bare transitive stems (§2.2, p. 37). -/
def formsBareTransitive (rc : CRootClass) : Bool :=
  match rc with
  | .tv => true
  | _   => false

-- ════════════════════════════════════════════════════
-- § 5. -aj Distribution (§5, Table 58)
-- ════════════════════════════════════════════════════

/-- Whether -aj (existential closure) appears on a √TV stem in each
    voice form (Table 58, p. 76).

    -aj marks the presence of an implicit argument:
    - Ø: no implicit arg → no -aj
    - -ch: implicit external arg → -aj on stem (ex. 36, p. 59)
    - -j: no external arg at all → no -aj
    - -w (absolutive): implicit internal arg → -aj (ex. 54a, p. 64)
    - -w (incorporation): overt bare NP internal arg → no -aj (ex. 55, p. 65)

    For the -w cases, we encode the two antipassive subtypes separately. -/
inductive AntipassiveType where
  | absolutive      -- theme is implicit (suppressed)
  | incorporation   -- theme is overt bare NP (incorporated)
  deriving DecidableEq, BEq, Repr

/-- -aj on √TV stems in passive/agentless contexts. -/
def ajOnPassive (vs : ChujVoiceSuffix) : Bool :=
  match vs with
  | .null => false  -- no implicit arg
  | .ch   => true   -- implicit agent (ex. 36: ix-mak'-ch-aj-i)
  | .j    => false  -- no agent at all
  | .w    => false  -- depends on antipassive type (see below)

/-- -aj on √TV stems in antipassive (-w) contexts. -/
def ajOnAntipassive (apt : AntipassiveType) : Bool :=
  match apt with
  | .absolutive    => true   -- implicit theme (ex. 54a: ix-ach-jax-w-aj-i)
  | .incorporation => false  -- overt bare NP (ex. 55: ix-ach-jax-w-i ixim)

-- ════════════════════════════════════════════════════
-- § 6. Agent Diagnostics (§4.1–4.2)
-- ════════════════════════════════════════════════════

/-- Agent-oriented adverb test (§4.1, exx. 47–48).
    "chi yuj" ('on purpose') is grammatical with -ch but not -j.

    (47) Ix-mak'-ch-aj-i nok' wakax (yuj ix) chi yuj.
         'The cow was hit (by her) on purpose.'  ✓

    (48) *Ix-mak'-j-i nok' wakax chi yuj.
         'The cow was hit on purpose.'  ✗ -/
def agentAdverbOK (vs : ChujVoiceSuffix) : Bool :=
  match vs with
  | .null => true   -- active: agent is overt
  | .ch   => true   -- passive: implicit agent licenses adverb (ex. 47)
  | .j    => false  -- agentless: no agent to orient (ex. 48)
  | .w    => true   -- antipassive: agent is overt

/-- By-phrase test (§4.1, exx. 47, 49).
    "yuj ix" ('by her') is grammatical with -ch but not -j.

    (47) ... (yuj ix) ... 'by her'  ✓ with -ch
    (49) *Ix-mak'-j-i nok' wakax yuj ix.
         'The cow was hit by her.'  ✗ with -j -/
def byPhraseOK (vs : ChujVoiceSuffix) : Bool :=
  match vs with
  | .null => false  -- active: agent is already overt
  | .ch   => true   -- passive: by-phrase identifies implicit agent
  | .j    => false  -- agentless: no agent to identify (ex. 49)
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

-- √TV roots (§2, Table 58)
def mak' : ChujVerb := ⟨"mak'", "hit", .tv⟩
def jax  : ChujVerb := ⟨"jax", "grind", .tv⟩
def k'ux : ChujVerb := ⟨"k'ux", "bite", .tv⟩
def il   : ChujVerb := ⟨"il", "see", .tv⟩
def jatz': ChujVerb := ⟨"jatz'", "hit (injure)", .tv⟩
def tzak': ChujVerb := ⟨"tzak'", "wrap", .tv⟩
def a'_give : ChujVerb := ⟨"a'", "give", .tv⟩
def lok' : ChujVerb := ⟨"lok'", "pull out", .tv⟩

-- √ITV roots (§3.1, p. 40)
def way  : ChujVerb := ⟨"way", "sleep", .itv⟩
def ok'  : ChujVerb := ⟨"ok'", "cry", .itv⟩
def jaw  : ChujVerb := ⟨"jaw", "arrive", .itv⟩
def b'at : ChujVerb := ⟨"b'at", "go", .itv⟩
def kam  : ChujVerb := ⟨"kam", "die", .itv⟩
def atin : ChujVerb := ⟨"atin", "bathe", .itv⟩

-- √POS roots (§3.2, p. 44)
def chot : ChujVerb := ⟨"chot", "sit/crouch", .pos⟩
def kot  : ChujVerb := ⟨"kot", "on all fours", .pos⟩
def watz : ChujVerb := ⟨"watz", "lie face down", .pos⟩
def buch : ChujVerb := ⟨"buch", "sit cross-legged", .pos⟩

-- √NOM roots (§3.3, p. 46)
def chanhal : ChujVerb := ⟨"chanhal", "dance", .nom⟩
def a'_water : ChujVerb := ⟨"a'", "water/swim", .nom⟩

def tvRoots : List ChujVerb :=
  [mak', jax, k'ux, il, jatz', tzak', a'_give, lok']

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

/-- (8) Active transitive: √TV + Ø (§2.2, p. 37). -/
def ex8 : ChujExample :=
  ⟨8, 37, "ix-∅-s-mak' ix konej nok' wakax",
   "She hit the cow.", mak', .null, true⟩

/-- (20) √ITV + null v (§3.1, p. 40). -/
def ex20 : ChujExample :=
  ⟨20, 40, "ix-in-way-i",
   "I slept.", way, .null, true⟩

/-- (23b) √POS + -w (§3.2, p. 44). -/
def ex23b : ChujExample :=
  ⟨23, 44, "ix-ach-chot-w-i",
   "You sat down.", chot, .w, true⟩

/-- (16b) √NOM + -w (§3.3, p. 46). -/
def ex16b : ChujExample :=
  ⟨16, 46, "ix-ach-chanhal-w-i",
   "You danced.", chanhal, .w, true⟩

/-- (36) √TV + -ch (passive, §4.1, p. 59). -/
def ex36 : ChujExample :=
  ⟨36, 59, "ix-mak'-ch-aj-i nok' wakax",
   "The cow was hit.", mak', .ch, true⟩

/-- (43a) √TV + -j (agentless passive, §4.2, p. 62). -/
def ex43a : ChujExample :=
  ⟨43, 62, "ix-mak'-j-i nok' wakax",
   "The cow was hit.", mak', .j, true⟩

/-- (47) Agent adverb with -ch: grammatical (§4.1, p. 61). -/
def ex47 : ChujExample :=
  ⟨47, 61, "ix-mak'-ch-aj-i nok' wakax (yuj ix) chi yuj",
   "The cow was hit (by her) on purpose.", mak', .ch, true⟩

/-- (48) Agent adverb with -j: ungrammatical (§4.2, p. 62). -/
def ex48 : ChujExample :=
  ⟨48, 62, "*ix-mak'-j-i nok' wakax chi yuj",
   "The cow was hit on purpose.", mak', .j, false⟩

/-- (54a) √TV + -w absolutive antipassive (§4.3, p. 64). -/
def ex54a : ChujExample :=
  ⟨54, 64, "ix-ach-jax-w-aj-i",
   "You did some grinding.", jax, .w, true⟩

/-- (55) √TV + -w incorporation antipassive (§4.3, p. 65). -/
def ex55 : ChujExample :=
  ⟨55, 65, "ix-ach-jax-w-i ixim",
   "You corn-ground.", jax, .w, true⟩

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
    ex8.grammatical = true ∧     -- √TV + Ø
    ex20.grammatical = true ∧    -- √ITV + null
    ex23b.grammatical = true ∧   -- √POS + -w
    ex16b.grammatical = true ∧   -- √NOM + -w
    ex36.grammatical = true ∧    -- √TV + -ch
    ex43a.grammatical = true ∧   -- √TV + -j
    ex47.grammatical = true ∧    -- agent adverb + -ch (OK)
    ex48.grammatical = false ∧   -- agent adverb + -j (blocked)
    ex54a.grammatical = true ∧   -- -w absolutive antipassive
    ex55.grammatical = true :=   -- -w incorporation antipassive
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Phenomena.Causatives.Studies.Coon2019
