import Linglib.Theories.Syntax.Minimalist.Voice
import Linglib.Theories.Syntax.Minimalist.Applicative
import Linglib.Theories.Syntax.Minimalist.VerbalDecomposition
import Linglib.Theories.Interfaces.SyntaxSemantics.Minimalist.VoiceTheta
import Linglib.Fragments.Icelandic.Predicates

/-!
# @cite{wood-2015} — Icelandic Morphosyntax and Argument Structure
@cite{wood-2015} @cite{kratzer-1996} @cite{pylkkanen-2008} @cite{schaefer-2008} @cite{cuervo-2003} @cite{alexiadou-schaefer-2015} @cite{wood-marantz-2017}

@cite{wood-2015} establishes that Icelandic *-st* (from historical
reflexive *sik*) is the morphological reflex of non-agentive Voice
across multiple syntactic configurations, not a single "reflexive"
or "anticausative" morpheme.

## Layer position

This file is the canonical Wood-2015 study site. The Icelandic
Fragment (`Fragments.Icelandic.Predicates`) carries only consensus
lexical data — verb forms, glosses, presence/absence of an active
variant. Wood's analytical apparatus lives here:

- the six-way *-st* classification (`StType`),
- the anticausative-marking enum *-st* / *-na* / *-ka* / unmarked
  (`AnticausativeMarking`),
- the mapping from *-st* types to Voice flavors,
- per-verb projection bundles (`StVerbInfo`) carrying stType, marking,
  and root structure for each verb.

The ±D notation is sourced from @cite{alexiadou-schaefer-2015}
(*External Arguments in Transitivity Alternations*, OUP) and refined
in @cite{wood-marantz-2017}. Earlier versions of this fragment
attributed ±θ/±D to @cite{schaefer-2008} alone, which was imprecise.

## Key Claims Formalized

1. **Voice–CAUSE independence** (Ch. 3): The causal relation is shared
   across causative and anticausative alternants; Voice contributes
   only whether an external argument is introduced. Modeled here using
   @cite{cuervo-2003}'s VerbHead decomposition (@cite{wood-2015}
   himself uses a single v head; the multi-head decomposition is a
   linglib modeling convenience that captures the same independence
   structurally — see `Theories/Syntax/Minimalist/Voice.lean` §5).

2. **-st as elsewhere exponent of Voice** (Ch. 3, §3.3–3.5): -st
   spells out non-agentive Voice across anticausative, middle,
   reflexive, experiencer, inherent, and reciprocal configurations.
   The morphological uniformity masks syntactic diversity.

3. **Voice projection locus** (Ch. 3): @cite{wood-2015}'s
   Voice_{D}/Voice_{∅} distinction is captured structurally by
   `VoiceProjectionLocus` (in `Voice.lean`), with
   `AnticausativeMarking.voiceLocus` projecting from each
   morphological exponent (-st, -na, -ka) to its locus.

4. **-st and -na complementarity** (Ch. 3, §3.3): -st and -na spell out
   different Voice projections (Voice_{D} vs Voice_{∅}) and never
   co-occur. -ka is an exponent of v, not Voice.

5. **Applicative interaction** (Ch. 5): @cite{wood-2015} shows -st
   cannot merge in SpecApplP because Appl assigns dative case
   and -st lacks case features. The high/low Appl interaction
   theorems below follow @cite{pylkkanen-2008} and @cite{schaefer-2008},
   not @cite{wood-2015}'s Icelandic-specific analysis (which argues
   Icelandic lacks true high applicatives).
-/

namespace Wood2015

open Minimalist
open Fragments.Icelandic.Predicates
open Minimalist.VoiceTheta

-- ============================================================================
-- § 0: Wood-Apparatus (the analytical layer over the Fragment)
-- ============================================================================

/-- Classification of Icelandic *-st* constructions (@cite{wood-2015}).
    Each type maps to a distinct Voice configuration. -/
inductive StType where
  | anticausative    -- Voice[−θ, +D]: *opnast*, *splundrast*
  | middle           -- Voice[−θ, −D]: *seljast*, *lesast*
  | reflexive        -- Voice[+θ, +D] + binding: *baðast*, *klæðast*
  | inherent         -- Lexicalized: *nálgast*, *minnast*
  | subjectExp       -- Voice_EXP: *leiðast*
  | reciprocal       -- Voice[+θ, +D] + reciprocal: *kyssast*
  deriving DecidableEq, Repr

/-- Map each *-st* type to its Voice flavor. -/
def StType.voiceFlavor : StType → VoiceFlavor
  | .anticausative => .nonThematic
  | .middle        => .expletive
  | .reflexive     => .reflexive
  | .inherent      => .nonThematic   -- lexicalized; syntactically non-thematic
  | .subjectExp    => .experiencer
  | .reciprocal    => .reflexive     -- same Voice as reflexive, different binding

/-- How an anticausative is morphologically marked
    (@cite{wood-2015} Ch. 3, §3.3).

    - *-st* spells out Voice_{D};
    - *-na* spells out specifierless Voice_{∅};
    - *-ka* spells out v (not Voice);
    - *unmarked*: zero alternation, compatible with either Voice_{D}
      or Voice_{∅}, distinguished by independent diagnostics.

    Per @cite{wood-2015} Ch. 3, §3.3, *-st* and *-na* never co-occur
    because they spell out different Voice types; *-na* and *-ka*
    never co-occur because *-na* requires v to be null/pruned. -/
inductive AnticausativeMarking where
  | st
  | na
  | unmarked
  | ka
  deriving DecidableEq, Repr

/-- Each anticausative-marking morpheme picks out a position in
    Voice/v space (@cite{wood-2015} Ch. 3, §3.3). The structural
    distinction is visible to pattern matching, not hidden behind
    string equality on labels like `"Voice_{D}"`. -/
def AnticausativeMarking.voiceLocus :
    AnticausativeMarking → VoiceProjectionLocus
  | .st       => .voiceD
  | .na       => .voiceBare
  | .unmarked => .voiceDOrBare
  | .ka       => .vHead

/-- PF realization of Voice in Icelandic.

    *-st* is the elsewhere exponent for Voice — it appears whenever
    Voice is non-agentive (modulo antipassive, which is unproductive
    in Icelandic). -/
def voiceToSuffix : VoiceFlavor → Option String
  | .agentive    => none           -- active: no suffix
  | .causer      => none           -- causative: no suffix
  | .antipassive => none           -- not productive in Icelandic
  | _            => some "-st"     -- elsewhere

-- ============================================================================
-- § 0b: Per-Verb Wood-Projections (@cite{wood-2015})
-- ============================================================================

/-- Wood-2015 analytical projection of a single Icelandic *-st* verb.
    Bundles the apparatus the slim Fragment doesn't carry: *-st*
    classification, anticausative marking, root-structure decomposition
    (@cite{cuervo-2003}-style notation per `Voice.lean` §5–§6), and the
    possessive-dative diagnostic. -/
structure StVerbInfo where
  /-- The lexical fragment entry. -/
  verb : IcelandicStVerb
  /-- Wood's *-st* classification. -/
  stType : StType
  /-- Anticausative-marking morpheme. Default *-st*. -/
  marking : AnticausativeMarking := .st
  /-- @cite{cuervo-2003}-style event decomposition. -/
  rootStructure : List VerbHead
  /-- Does this verb license possessive datives (Wood Ch. 5 diagnostic)? -/
  licensesPossessiveDative : Bool := false
  deriving Repr, BEq, DecidableEq

/-- *opna* / *opnast* 'open' — anticausative *-st* (@cite{wood-2015} Ch. 3).
    Active: *Jón opnaði dyrnar* 'John opened the door';
    *-st*: *Dyrnar opnuðust* 'The door opened'. -/
def opnast_info : StVerbInfo :=
  { verb := opnast
    stType := .anticausative
    rootStructure := [.vCAUSE, .vGO, .vBE]
    licensesPossessiveDative := true }

/-- *splundra* / *splundrast* 'shatter' — anticausative *-st*
    (@cite{wood-2015} Ch. 3, §3.5). Central example for the
    Voice–CAUSE independence argument. -/
def splundrast_info : StVerbInfo :=
  { verb := splundrast
    stType := .anticausative
    rootStructure := [.vCAUSE, .vGO, .vBE]
    licensesPossessiveDative := true }

/-- *brjóta* / *brotna* 'break' — anticausative with *-na*, NOT *-st*
    (@cite{wood-2015} Ch. 3, §3.3.2). Comparison case: *-na* spells
    out specifierless Voice_{∅} whereas *-st* picks Voice_{D}. -/
def brotna_info : StVerbInfo :=
  { verb := brotna
    stType := .anticausative
    marking := .na
    rootStructure := [.vCAUSE, .vGO, .vBE] }

/-- *selja* / *seljast* 'sell' — middle *-st* (@cite{wood-2015}). -/
def seljast_info : StVerbInfo :=
  { verb := seljast
    stType := .middle
    rootStructure := [.vCAUSE, .vGO, .vBE] }

/-- *lesa* / *lesast* 'read' — middle *-st* (@cite{wood-2015}). -/
def lesast_info : StVerbInfo :=
  { verb := lesast
    stType := .middle
    rootStructure := [.vCAUSE, .vGO, .vBE] }

/-- *baða* / *baðast* 'bathe' — reflexive *-st* (@cite{wood-2015}). -/
def badast_info : StVerbInfo :=
  { verb := badast
    stType := .reflexive
    rootStructure := [.vCAUSE, .vGO, .vBE] }

/-- *klæða* / *klæðast* 'dress' — reflexive *-st* (@cite{wood-2015}). -/
def klaedast_info : StVerbInfo :=
  { verb := klaedast
    stType := .reflexive
    rootStructure := [.vCAUSE, .vGO, .vBE] }

/-- *nálgast* 'approach' — inherent *-st* (@cite{wood-2015}).
    No active variant; *-st* is lexicalized. -/
def nalgast_info : StVerbInfo :=
  { verb := nalgast
    stType := .inherent
    rootStructure := [.vGO] }

/-- *minnast* 'remember' — inherent *-st* (@cite{wood-2015}).
    No active variant. -/
def minnast_info : StVerbInfo :=
  { verb := minnast
    stType := .inherent
    rootStructure := [.vBE] }

/-- *leiðast* 'be bored' — subject-experiencer *-st* (@cite{wood-2015}).
    *Mér leiðist í skólanum* 'I am bored in school'. -/
def leidast_info : StVerbInfo :=
  { verb := leidast
    stType := .subjectExp
    rootStructure := [.vBE] }

/-- *kyssa* / *kyssast* 'kiss' — reciprocal *-st* (@cite{wood-2015}).
    *Þau kyssast* 'They kissed (each other)'. -/
def kyssast_info : StVerbInfo :=
  { verb := kyssast
    stType := .reciprocal
    rootStructure := [.vCAUSE, .vGO, .vBE] }

/-- All *-st* verb projections (excludes *brotna* which is *-na*-marked). -/
def allStInfo : List StVerbInfo :=
  [opnast_info, splundrast_info, seljast_info, lesast_info,
   badast_info, klaedast_info, nalgast_info, minnast_info,
   leidast_info, kyssast_info]

-- ============================================================================
-- § 1: Voice–CAUSE Independence (Ch. 3)
-- ============================================================================

/-- The causal relation is shared across causative and anticausative
    alternants (@cite{wood-2015} Ch. 3). Modeled using
    @cite{cuervo-2003}'s VerbHead decomposition: causative
    [vDO, vCAUSE, vGO, vBE]; anticausative [vCAUSE, vGO, vBE]. -/
theorem cause_shared_across_alternation :
    let causativeDecomp := buildDecomposition voiceAgent opnast_info.rootStructure
    let anticausativeDecomp := buildDecomposition voiceAnticausative opnast_info.rootStructure
    hasCause causativeDecomp = true ∧
    hasCause anticausativeDecomp = true := by
  decide

/-- The causative alternation for *opna* / *opnast*: same root,
    different Voice. -/
theorem opna_alternation :
    isCausative (buildDecomposition voiceAgent opnast_info.rootStructure) = true ∧
    isInchoative (buildDecomposition voiceAnticausative opnast_info.rootStructure) = true := by
  decide

/-- Voice alone determines causativity for change-of-state roots. -/
theorem voice_alone_determines_causativity :
    buildDecomposition voiceAgent [.vCAUSE, .vGO, .vBE] =
      [.vDO, .vCAUSE, .vGO, .vBE] ∧
    buildDecomposition voiceAnticausative [.vCAUSE, .vGO, .vBE] =
      [.vCAUSE, .vGO, .vBE] := ⟨rfl, rfl⟩

-- ============================================================================
-- § 2: -st as Elsewhere Exponent (Ch. 3, §3.3–3.5)
-- ============================================================================

/-- *-st* spells out Voice across all six construction types.
    Despite morphological uniformity, the underlying Voice
    configurations differ in ±θ/±D parameters. -/
theorem st_covers_all_types :
    voiceToSuffix (StType.voiceFlavor .anticausative) = some "-st" ∧
    voiceToSuffix (StType.voiceFlavor .middle) = some "-st" ∧
    voiceToSuffix (StType.voiceFlavor .reflexive) = some "-st" ∧
    voiceToSuffix (StType.voiceFlavor .subjectExp) = some "-st" ∧
    voiceToSuffix (StType.voiceFlavor .inherent) = some "-st" ∧
    voiceToSuffix (StType.voiceFlavor .reciprocal) = some "-st" :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Despite shared morphology, the Voice configurations differ.
    Anticausative and middle Voice do NOT assign θ; reflexive does.
    Stated using the canonical Voice constants from `Voice.lean`. -/
theorem st_hides_theta_diversity :
    voiceAnticausative.assignsTheta = false ∧
    voiceMiddle.assignsTheta = false ∧
    voiceReflexive.assignsTheta = true := ⟨rfl, rfl, rfl⟩

/-- Lookup table for `StType.voiceFlavor` on the four
    typologically-distinct cells. Bundled into a single theorem so
    the table appears as one proof obligation. -/
theorem stType_voiceFlavor_table :
    StType.voiceFlavor .anticausative = .nonThematic ∧
    StType.voiceFlavor .middle = .expletive ∧
    StType.voiceFlavor .reflexive = .reflexive ∧
    StType.voiceFlavor .subjectExp = .experiencer :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- *-st* spells out all non-agentive Voice flavors. -/
theorem st_spells_out_nonagentive :
    voiceToSuffix .nonThematic = some "-st" ∧
    voiceToSuffix .expletive = some "-st" ∧
    voiceToSuffix .reflexive = some "-st" ∧
    voiceToSuffix .experiencer = some "-st" := ⟨rfl, rfl, rfl, rfl⟩

/-- Active Voice gets no suffix. -/
theorem active_no_suffix : voiceToSuffix .agentive = none := rfl

-- ============================================================================
-- § 3: ±θ/±D Parameterization
-- (@cite{alexiadou-schaefer-2015}, @cite{wood-marantz-2017})
-- ============================================================================

/-- The six *-st* types occupy distinct cells in the ±θ/±D space.
    @cite{wood-2015}'s Voice_{D}/Voice_{∅} distinction maps to the ±D
    axis (`selectsSpecifier`); Voice semantics (Ø vs AGENT) maps to
    the ±λx axis. -/
theorem parametric_diversity :
    -- [−θ, +D]: anticausative
    (VoiceFlavor.toParams (StType.voiceFlavor .anticausative)).selectsSpecifier = some true ∧
    (VoiceFlavor.toParams (StType.voiceFlavor .anticausative)).extArgSemantics = some .expletive ∧
    -- [−θ, −D]: middle
    (VoiceFlavor.toParams (StType.voiceFlavor .middle)).selectsSpecifier = some false ∧
    (VoiceFlavor.toParams (StType.voiceFlavor .middle)).extArgSemantics = some .expletive ∧
    -- [+θ, +D]: reflexive
    (VoiceFlavor.toParams (StType.voiceFlavor .reflexive)).selectsSpecifier = some true ∧
    (VoiceFlavor.toParams (StType.voiceFlavor .reflexive)).extArgSemantics = some .thematicArgument ∧
    -- [+θ, +D]: experiencer
    (VoiceFlavor.toParams (StType.voiceFlavor .subjectExp)).selectsSpecifier = some true ∧
    (VoiceFlavor.toParams (StType.voiceFlavor .subjectExp)).extArgSemantics = some .thematicArgument :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 4: High vs Low Applicative Interaction
-- (@cite{pylkkanen-2008}, @cite{schaefer-2008})
-- ============================================================================

/-- High applicatives are blocked when Voice has no event semantics
    (@cite{pylkkanen-2008}, @cite{schaefer-2008}). Note: @cite{wood-2015}
    Ch. 5 argues Icelandic lacks true high applicatives; the asymmetry
    formalized here follows the cross-linguistic typology. -/
theorem ethical_blocked_in_middle :
    applHigh.licensedWith voiceMiddle = false := rfl

/-- Low applicatives survive when Voice has no event semantics
    because they relate to the theme, not the event
    (@cite{pylkkanen-2008}). -/
theorem possessive_survives_middle :
    applLowRecipient.licensedWith voiceMiddle = true := rfl

/-- In anticausatives, possessive datives also survive. -/
theorem possessive_survives_anticausative :
    applLowRecipient.licensedWith voiceAnticausative = true := rfl

/-- High applicatives ARE licensed with agentive Voice. -/
theorem ethical_ok_in_active :
    applHigh.licensedWith voiceAgent = true := rfl

/-- The full asymmetry: high applicatives require Voice with event
    semantics; low applicatives are independent of Voice
    (@cite{pylkkanen-2008}, @cite{schaefer-2008}). -/
theorem dative_voice_asymmetry :
    applHigh.licensedWith voiceMiddle = false ∧
    applHigh.licensedWith voiceAgent = true ∧
    applLowRecipient.licensedWith voiceMiddle = true ∧
    applLowRecipient.licensedWith voiceAgent = true := ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 5: Theta Role Predictions
-- ============================================================================

/-- Reflexive Voice predicts agent θ-role (agent acts on self). -/
theorem reflexive_predicts_agent :
    VoiceFlavor.thetaRole .reflexive = some .agent := rfl

/-- Experiencer Voice predicts experiencer θ-role. -/
theorem experiencer_predicts_experiencer :
    VoiceFlavor.thetaRole .experiencer = some .experiencer := rfl

/-- Anticausative Voice predicts no external θ-role. -/
theorem anticausative_predicts_none :
    VoiceFlavor.thetaRole .nonThematic = none := rfl

/-- Middle Voice predicts no external θ-role. -/
theorem middle_predicts_none :
    VoiceFlavor.thetaRole .expletive = none := rfl

-- ============================================================================
-- § 6: -st Blocked from SpecApplP (@cite{wood-2015} Ch. 5, §5.3.2)
-- ============================================================================

/-- @cite{wood-2015}'s key applicative claim: *-st* cannot merge in
    SpecApplP because Appl assigns dative case and *-st* lacks case
    features. -/
theorem st_blocked_from_specApplP :
    applLowRecipient.specCanBearCase false = false ∧
    applLowRecipient.specCanBearCase true = true := ⟨rfl, rfl⟩

/-- In ditransitive *-st* alternations, Appl datives are retained
    because Appl assigns case independently of Voice
    (@cite{wood-2015} Ch. 5, §5.3.1). -/
theorem appl_dative_retained_with_st :
    applLowRecipient.licensedWith voiceAnticausative = true := rfl

-- ============================================================================
-- § 7: -st/-na Complementary Distribution (Ch. 3)
-- ============================================================================

/-- *-st* and *-na* spell out different Voice projection loci
    (@cite{wood-2015} Ch. 3). *-st* picks out Voice_{D}; *-na* picks
    out Voice_{∅}. They never co-occur. Stated structurally over
    `VoiceProjectionLocus`, so the inequality is genuine pattern
    distinction (not a string-equality coincidence on labels). -/
theorem st_na_different_voice_loci :
    AnticausativeMarking.voiceLocus .st ≠
    AnticausativeMarking.voiceLocus .na := by decide

/-- *-ka* spells out v, distinct from both Voice exponents. -/
theorem ka_distinct_from_voice_exponents :
    AnticausativeMarking.voiceLocus .ka ≠
    AnticausativeMarking.voiceLocus .st ∧
    AnticausativeMarking.voiceLocus .ka ≠
    AnticausativeMarking.voiceLocus .na := by decide

/-- *brotna* is *-na* marked, not *-st* marked. -/
theorem brotna_is_na : brotna_info.marking = .na := rfl

/-- All *-st* verbs in `allStInfo` carry the `.st` marking. -/
theorem all_st_info_are_st_marked :
    allStInfo.all (fun i => i.marking == .st) = true := by decide

/-- Different anticausative roots select different Voice types:
    *opnast* takes *-st* (Voice_{D}), *brotna* takes *-na* (Voice_{∅}).
    The marking choice is lexically determined per root. -/
theorem anticausative_marking_varies :
    opnast_info.marking = .st ∧
    brotna_info.marking = .na := ⟨rfl, rfl⟩

-- ============================================================================
-- § 8: Fragment Consistency (over `StVerbInfo`)
-- ============================================================================

/-- All anticausative *-st* verbs have inchoative root structure
    (no vDO, with vGO + vBE per @cite{cuervo-2003}). -/
theorem anticausative_is_inchoative :
    (allStInfo.filter (fun i => i.stType == .anticausative)).all
      (fun i => isInchoative i.rootStructure) = true := by decide

/-- All anticausative *-st* verbs have change-of-state root structure
    (contains vGO; finer projection than `isInchoative`). -/
theorem anticausative_verbs_are_cos :
    (allStInfo.filter (fun i => i.stType == .anticausative)).all
      (fun i => i.rootStructure.contains .vGO) = true := by decide

/-- Inherent *-st* verbs lack active variants. -/
theorem inherent_no_active :
    (allStInfo.filter (fun i => i.stType == .inherent)).all
      (fun i => !i.verb.hasActiveVariant) = true := by decide

/-- Subject-experiencer *-st* verbs lack active variants. -/
theorem subjectexp_no_active :
    (allStInfo.filter (fun i => i.stType == .subjectExp)).all
      (fun i => !i.verb.hasActiveVariant) = true := by decide

/-- Ten *-st* verb info entries (excludes *brotna*, which is *-na*-marked). -/
theorem info_count : allStInfo.length = 10 := rfl

end Wood2015
