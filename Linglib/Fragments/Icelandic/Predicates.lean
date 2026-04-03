import Linglib.Theories.Syntax.Minimalism.Core.Voice
import Linglib.Theories.Syntax.Minimalism.Core.Applicative
import Linglib.Theories.Syntax.Minimalism.Core.VerbalDecomposition

/-!
# Icelandic Verb Fragment: -st Constructions
@cite{wood-2015} @cite{schaefer-2008}

Icelandic -st (historically *sik* → *-sk* → *-st*) is the
morphological reflex of non-agentive Voice. @cite{wood-2015} shows
that -st spells out Voice across at least six descriptive categories:

1. **Anticausative** -st: Voice_{D} + Ø semantics (e.g., *opnast* 'open')
2. **Middle** -st: Voice_{D} + Ø semantics (e.g., *seljast* 'sell')
3. **Reflexive** -st: Voice_{D} + AGENT semantics + binding (*baðast* 'bathe')
4. **Inherent** -st: lexicalized (*nálgast* 'approach')
5. **Subject-experiencer** -st: Voice_{D} + experiencer (*leiðast* 'be.bored')
6. **Reciprocal** -st: Voice_{D} + AGENT + reciprocal binding

The key argument: -st is NOT a single morpheme with a single
meaning. It is a clitic that merges in the specifier of Voice_{D}
(or SpecpP for figure reflexives) across multiple configurations.
The shared PF realization obscures the underlying syntactic diversity.

Note: @cite{wood-2015}'s Voice parameterization uses Voice_{D}
(has D-feature, projects specifier) vs Voice_{} (specifierless).
The ±θ/±D labels used in the `VoiceFlavor.toParams` function follow
@cite{schaefer-2008}'s notation.

## Morphological Spell-Out

`voiceToSuffix` models the observation that all non-agentive Voice
configurations spell out as -st in Icelandic. In @cite{wood-2015}'s
analysis, -st is a clitic in SpecVoiceP, not a suffix on Voice
itself; `voiceToSuffix` is a simplification for the fragment.
-/

namespace Fragments.Icelandic.Predicates

open Minimalism

-- ============================================================================
-- § 1: -st Construction Types
-- ============================================================================

/-- Classification of Icelandic -st constructions (@cite{wood-2015}).
    Each type maps to a distinct Voice configuration. -/
inductive StType where
  | anticausative    -- Voice[−θ, +D]: *opnast*, *brotna-st*
  | middle           -- Voice[−θ, −D]: *seljast*, *lesast*
  | reflexive        -- Voice[+θ, +D] + binding: *baðast*, *klæddist*
  | inherent         -- Lexicalized: *nálgast*, *minnast*
  | subjectExp       -- Voice_EXP: *leiðast*, *langaðist*
  | reciprocal       -- Voice[+θ, +D] + reciprocal: *kyssast*
  deriving DecidableEq, Repr

/-- Map each -st type to its Voice flavor. -/
def StType.voiceFlavor : StType → VoiceFlavor
  | .anticausative => .nonThematic
  | .middle        => .expletive
  | .reflexive     => .reflexive
  | .inherent      => .nonThematic  -- lexicalized, but syntactically non-thematic
  | .subjectExp    => .experiencer
  | .reciprocal    => .reflexive    -- same Voice as reflexive, different binding

-- ============================================================================
-- § 1b: Anticausative Marking (@cite{wood-2015} Ch. 3, §3.3)
-- ============================================================================

/-- How the anticausative is morphologically marked.

    @cite{wood-2015} Ch. 3 derives three key generalizations:
    - **-st** merges in SpecVoice_{D} (Voice with D-feature)
    - **-na** spells out Voice_{} (specifierless Voice)
    - **-st and -na never co-occur** (different Voice types)
    - **-ka** is a spell-out of v (not Voice); -na and -ka never co-occur
      because -na requires v to be null/pruned -/
inductive AnticausativeMarking where
  | st      -- -st: clitic in SpecVoice_{D}
  | na      -- -na: exponent of specifierless Voice_{}
  | unmarked -- no overt marking (zero alternation)
  | ka      -- -ka: exponent of v (adjectival roots)
  deriving DecidableEq, Repr

/-- -st and -na are complementary: they spell out different Voice types. -/
def AnticausativeMarking.voiceType : AnticausativeMarking → String
  | .st       => "Voice_{D}"
  | .na       => "Voice_{}"
  | .unmarked => "Voice_{D} or Voice_{}"
  | .ka       => "v (not Voice)"

-- ============================================================================
-- § 2: Morphological Spell-Out
-- ============================================================================

/-- PF realization of Voice in Icelandic.

    The key insight: -st does NOT correspond to a single Voice flavor.
    It is the elsewhere exponent for Voice — it appears whenever Voice
    is not agentive (active). -/
def voiceToSuffix : VoiceFlavor → Option String
  | .agentive    => none        -- active: no suffix
  | .causer      => none        -- causative: no suffix
  | .antipassive => none        -- not productive in Icelandic
  | _            => some "-st"  -- all other Voice flavors spell out as -st

-- ============================================================================
-- § 3: Icelandic Verb Entries
-- ============================================================================

/-- An Icelandic verb entry in the -st / -na fragment. -/
structure IcelandicStVerb where
  /-- Active/bare form (if one exists) -/
  activeForm : Option String
  /-- The intransitive form (-st, -na, or same as active) -/
  stForm : String
  /-- English gloss -/
  gloss : String
  /-- Which -st construction type -/
  stType : StType
  /-- Root event structure (@cite{cuervo-2003} notation) -/
  rootStructure : List VerbHead
  /-- Can this verb also appear without -st or -na? -/
  hasActiveVariant : Bool
  /-- How the anticausative is morphologically marked -/
  marking : AnticausativeMarking := .st
  /-- Does this verb license possessive datives? -/
  licensesPossessiveDative : Bool := false
  deriving Repr, BEq

-- ============================================================================
-- § 4: Verb Data (@cite{wood-2015})
-- ============================================================================

/-- *opna/opnast* 'open' — anticausative -st (@cite{wood-2015}).
    Active: *Jón opnaði dyrnar* 'John opened the door'
    -st: *Dyrnar opnuðust* 'The door opened' -/
def opnast : IcelandicStVerb :=
  { activeForm := some "opna"
    stForm := "opnast"
    gloss := "open"
    stType := .anticausative
    rootStructure := [.vCAUSE, .vGO, .vBE]
    hasActiveVariant := true
    licensesPossessiveDative := true }

/-- *splundra/splundrast* 'shatter' — anticausative -st (@cite{wood-2015}).
    Active: *Ásta splundraði rúðunni* 'Ásta shattered the window'
    -st: *Rúðan splundraðist* 'The window shattered'
    Central example in @cite{wood-2015} Ch. 3, §3.5. -/
def splundrast : IcelandicStVerb :=
  { activeForm := some "splundra"
    stForm := "splundrast"
    gloss := "shatter"
    stType := .anticausative
    rootStructure := [.vCAUSE, .vGO, .vBE]
    hasActiveVariant := true
    licensesPossessiveDative := true }

/-- *brjóta/brotna* 'break' — anticausative with *-na* (NOT *-st*).
    Included as comparison: -na marks specifierless Voice_{} whereas
    -st merges in SpecVoice_{D} (@cite{wood-2015} Ch. 3, §3.3.2). -/
def brotna : IcelandicStVerb :=
  { activeForm := some "brjóta"
    stForm := "brotna"
    gloss := "break"
    stType := .anticausative
    rootStructure := [.vCAUSE, .vGO, .vBE]
    hasActiveVariant := true
    marking := .na }

/-- *selja/seljast* 'sell' — middle -st (@cite{wood-2015}).
    *Þessi bók seldist vel* 'This book sold well' -/
def seljast : IcelandicStVerb :=
  { activeForm := some "selja"
    stForm := "seljast"
    gloss := "sell"
    stType := .middle
    rootStructure := [.vCAUSE, .vGO, .vBE]
    hasActiveVariant := true }

/-- *lesa/lesast* 'read' — middle -st (@cite{wood-2015}).
    *Þessi bók lesist vel* 'This book reads well' -/
def lesast : IcelandicStVerb :=
  { activeForm := some "lesa"
    stForm := "lesast"
    gloss := "read"
    stType := .middle
    rootStructure := [.vCAUSE, .vGO, .vBE]
    hasActiveVariant := true }

/-- *baða/baðast* 'bathe' — reflexive -st (@cite{wood-2015}).
    *Hún baðaðist* 'She bathed (herself)' -/
def badast : IcelandicStVerb :=
  { activeForm := some "baða"
    stForm := "baðast"
    gloss := "bathe"
    stType := .reflexive
    rootStructure := [.vCAUSE, .vGO, .vBE]
    hasActiveVariant := true }

/-- *klæða/klæðast* 'dress' — reflexive -st (@cite{wood-2015}).
    *Hann klæddist* 'He dressed (himself)' -/
def klaedast : IcelandicStVerb :=
  { activeForm := some "klæða"
    stForm := "klæðast"
    gloss := "dress"
    stType := .reflexive
    rootStructure := [.vCAUSE, .vGO, .vBE]
    hasActiveVariant := true }

/-- *nálgast* 'approach' — inherent -st (@cite{wood-2015}).
    No active variant; -st is lexicalized. -/
def nalgast : IcelandicStVerb :=
  { activeForm := none
    stForm := "nálgast"
    gloss := "approach"
    stType := .inherent
    rootStructure := [.vGO]
    hasActiveVariant := false }

/-- *minnast* 'remember' — inherent -st (@cite{wood-2015}).
    No active variant. -/
def minnast : IcelandicStVerb :=
  { activeForm := none
    stForm := "minnast"
    gloss := "remember"
    stType := .inherent
    rootStructure := [.vBE]
    hasActiveVariant := false }

/-- *leiðast* 'be bored' — subject-experiencer -st (@cite{wood-2015}).
    *Mér leiðist í skólanum* 'I am bored in school' -/
def leidast : IcelandicStVerb :=
  { activeForm := none
    stForm := "leiðast"
    gloss := "be bored"
    stType := .subjectExp
    rootStructure := [.vBE]
    hasActiveVariant := false }

/-- *kyssa/kyssast* 'kiss' — reciprocal -st (@cite{wood-2015}).
    *Þau kyssast* 'They kissed (each other)' -/
def kyssast : IcelandicStVerb :=
  { activeForm := some "kyssa"
    stForm := "kyssast"
    gloss := "kiss"
    stType := .reciprocal
    rootStructure := [.vCAUSE, .vGO, .vBE]
    hasActiveVariant := true }

/-- All -st verb entries (excludes -na verbs like *brotna*). -/
def allStVerbs : List IcelandicStVerb :=
  [opnast, splundrast, seljast, lesast, badast, klaedast,
   nalgast, minnast, leidast, kyssast]

-- ============================================================================
-- § 5: Verification Theorems
-- ============================================================================

/-- Anticausative -st maps to non-thematic Voice. -/
theorem anticausative_st_is_nonthematic :
    StType.voiceFlavor .anticausative = .nonThematic := rfl

/-- Middle -st maps to expletive Voice. -/
theorem middle_st_is_expletive :
    StType.voiceFlavor .middle = .expletive := rfl

/-- Reflexive -st maps to reflexive Voice. -/
theorem reflexive_st_is_reflexive :
    StType.voiceFlavor .reflexive = .reflexive := rfl

/-- Subject-experiencer -st maps to experiencer Voice. -/
theorem subjectexp_st_is_experiencer :
    StType.voiceFlavor .subjectExp = .experiencer := rfl

/-- All alternating verbs have active variants. -/
theorem alternating_have_active :
    (allStVerbs.filter (·.hasActiveVariant)).all
      (fun v => v.activeForm.isSome) = true := by native_decide

/-- Inherent -st verbs lack active variants. -/
theorem inherent_no_active :
    (allStVerbs.filter (fun v => v.stType == .inherent)).all
      (fun v => !v.hasActiveVariant) = true := by native_decide

/-- Subject-experiencer -st verbs lack active variants. -/
theorem subjectexp_no_active :
    (allStVerbs.filter (fun v => v.stType == .subjectExp)).all
      (fun v => !v.hasActiveVariant) = true := by native_decide

/-- All anticausative -st verbs have inchoative root structure. -/
theorem anticausative_is_inchoative :
    (allStVerbs.filter (fun v => v.stType == .anticausative)).all
      (fun v => isInchoative v.rootStructure) = true := by native_decide

/-- -st spells out all non-agentive Voice flavors. -/
theorem st_spells_out_nonagentive :
    voiceToSuffix .nonThematic = some "-st" ∧
    voiceToSuffix .expletive = some "-st" ∧
    voiceToSuffix .reflexive = some "-st" ∧
    voiceToSuffix .experiencer = some "-st" := ⟨rfl, rfl, rfl, rfl⟩

/-- Active Voice gets no suffix. -/
theorem active_no_suffix :
    voiceToSuffix .agentive = none := rfl

-- ============================================================================
-- § 6: -st/-na Complementary Distribution (@cite{wood-2015} Ch. 3)
-- ============================================================================

/-- -st and -na spell out different Voice types (@cite{wood-2015} Ch. 3).
    -st merges in SpecVoice_{D}; -na spells out Voice_{}.
    They can never co-occur on the same verb form. -/
theorem st_na_different_voice_types :
    AnticausativeMarking.voiceType .st ≠
    AnticausativeMarking.voiceType .na := by decide

/-- *brotna* is -na marked, not -st marked. -/
theorem brotna_is_na : brotna.marking = .na := rfl

/-- All verbs in allStVerbs are -st marked (default). -/
theorem all_st_verbs_are_st_marked :
    allStVerbs.all (fun v => v.marking == .st) = true := by native_decide

/-- Different anticausative roots select different Voice types:
    *opna* takes -st (Voice_{D}), *brjóta* takes -na (Voice_{}).
    The marking choice is lexically determined per root. -/
theorem anticausative_marking_varies :
    opnast.marking = .st ∧
    brotna.marking = .na := ⟨rfl, rfl⟩

end Fragments.Icelandic.Predicates
