import Linglib.Syntax.Minimalist.Verbal.Voice
import Linglib.Syntax.Minimalist.Verbal.Applicative
import Linglib.Syntax.Minimalist.Verbal.Decomposition
import Linglib.Fragments.Icelandic.Predicates

/-!
# [wood-2015] — Icelandic *-st* as a specifier-merged clitic
[wood-2015] [kratzer-1996] [pylkkanen-2008] [schaefer-2008] [cuervo-2003] [alexiadou-schaefer-2015] [wood-marantz-2017]

[wood-2015]'s central thesis is that Icelandic *-st* (historically the
reflexive *sik* → *-sk* → *-st*) is **not** an exponent of a Voice head. It
is a defective person clitic — a `[−participant]` feature bundle, a featural
subset of the reflexive pronoun — that **merges in a specifier position** and
cliticizes to the verb. Its many "uses" (anticausative, generic middle, figure
reflexive, reflexive, subject-experiencer, reciprocal, inherent) arise from
*where* it merges, not from *-st* spelling out different Voice flavors. The
genuine Voice/v exponents are *-na* (Voice{∅}), *-Ø* (the elsewhere Voice
exponent), and *-ka* (v).

This file models that thesis: the primitive is *-st*'s **merge site**
(`StSite`), and the construction typology and anti-affixal predictions are
derived from it.

## Layer position

The Icelandic Fragment (`Icelandic.Predicates`) carries only consensus lexical
data — verb forms, glosses, presence of an active variant. Wood's analytical
apparatus lives here: the merge-site classification (`StSite`, `StType.site`),
the host-clause Voice flavor each construction shows (`StType.voiceFlavor`),
the anticausative exponent inventory (`AnticausativeMarking`), and per-verb
projection bundles (`StVerbInfo`).

## Key claims formalized

1. **-st is a specifier-occupant, not a head exponent** (Ch. 2). *-st* checks a
   `[D]` feature in a specifier; *-na* / *-Ø* / *-ka* spell out heads.
   `st_not_head_exponent`, `na_ka_distinct_loci`.

2. **Merge site — not Voice flavor — distinguishes the constructions**
   (Ch. 3–6). An agentive Voice already fills SpecVoiceP with its agent, so
   *-st* can occupy SpecVoiceP only under non-agentive Voice; under agentive
   Voice it merges lower, in SpecpP. `agentive_st_merges_low`.

3. **-st co-occurs with agentive Voice** (Ch. 4: figure reflexives), which an
   exponent of *non-agentive* Voice never could — the core evidence against the
   affixal view. `st_not_single_voice_exponent`.

4. **Voice–CAUSE independence** (Ch. 3): the causal head is shared across the
   causative/anticausative alternation; only Voice's vDO differs. Modeled with
   [cuervo-2003]'s decomposition — [wood-2015] uses a single allosemic v;
   the multi-head notation is a linglib modeling convenience (see `Voice.lean`).
   `opna_alternation`.

5. **-na / -ka complementarity** (Ch. 3): *-na* spells out Voice{∅}, *-ka*
   spells out v; they never co-occur. `na_ka_distinct_loci`.

6. **-st blocked from SpecApplP** (Ch. 5): Appl assigns dative and *-st* is
   caseless, so *-st* cannot occupy SpecApplP, though applied datives are
   otherwise retained. `st_blocked_from_specApplP`, `dative_voice_asymmetry`.
-/

namespace Wood2015

open Minimalist
open Icelandic.Predicates

/-! ### The *-st* clitic and its merge site -/

/-- Where the *-st* clitic merges ([wood-2015]). *-st* is a defective
    `[−participant]` person bundle that occupies a specifier and checks its
    head's `[D]` feature; the construction it yields is fixed by which
    specifier that is. -/
inductive StSite where
  /-- SpecVoiceP of Voice{D} — anticausatives and dative-subject experiencers
      ([wood-2015] §3.5, §5.4). -/
  | specVoiceD
  /-- SpecpP of the figure/ground head p{D} — figure reflexives, including
      "covert" ones like *klæðast* ([wood-2015] Ch. 4, §6.6). -/
  | specLittleP
  /-- A lower vP-internal specifier — reciprocals and the reflexive/middle
      residue ([wood-2015] §6.3, §6.5). -/
  | specLow
  deriving DecidableEq, Repr

/-- [wood-2015]'s descriptive classification of *-st* constructions. Each is
    distinguished by *-st*'s merge site (`StType.site`), not by a Voice flavor
    *-st* would spell out. -/
inductive StType where
  | anticausative    -- *opnast* 'open'
  | middle           -- generic middle / modal passive: *seljast* 'sell'
  | figureReflexive  -- *klæðast* 'dress', *setjast* 'sit down'
  | reflexive        -- non-figure reflexive residue
  | inherent         -- lexicalized, no active variant: *nálgast*, *minnast*
  | subjectExp       -- dative-subject psych: *leiðast* 'be bored'
  | reciprocal       -- *kyssast* 'kiss (each other)'
  deriving DecidableEq, Repr

/-- The specifier *-st* occupies in each construction ([wood-2015]).
    Anticausatives and subject-experiencers put *-st* in SpecVoiceP; figure
    reflexives in SpecpP; the rest in a lower specifier. -/
def StType.site : StType → StSite
  | .anticausative   => .specVoiceD
  | .subjectExp      => .specVoiceD
  | .figureReflexive => .specLittleP
  | .reflexive       => .specLittleP
  | .middle          => .specLow
  | .reciprocal      => .specLow
  | .inherent        => .specLow

/-- The Voice flavor of the *host clause* in each *-st* construction — the
    flavor *-st* co-occurs with, **not** one *-st* realizes ([wood-2015]).
    Anticausative and subject-experiencer clauses have non-thematic Voice (for
    the psych verbs the experiencer is an applicative dative, §5.4); figure
    reflexives and reciprocals are agentive (§4); the generic middle is
    expletive (§6.3). -/
def StType.voiceFlavor : StType → VoiceFlavor
  | .anticausative   => .nonThematic
  | .subjectExp      => .nonThematic
  | .inherent        => .nonThematic
  | .middle          => .expletive
  | .figureReflexive => .agentive
  | .reflexive       => .agentive
  | .reciprocal      => .agentive

/-! ### The anticausative exponent inventory (*-na* / *-Ø* / *-ka*) -/

/-- How an anticausative alternation is morphologically marked ([wood-2015]
    §3.3). *-st* is set apart from the others: *-na*, *-Ø* (unmarked), and
    *-ka* are **exponents of heads**, while *-st* realizes no head — it
    occupies a specifier. -/
inductive AnticausativeMarking where
  | st
  | na
  | unmarked
  | ka
  deriving DecidableEq, Repr

/-- The head a marker spells out, if any ([wood-2015] §3.3). *-st* spells out
    no head (`none`): it is a clitic in a specifier, not an exponent. *-na*
    spells out specifierless Voice{∅}; *-Ø* is the elsewhere Voice exponent
    (compatible with either Voice projection); *-ka* spells out v. -/
def AnticausativeMarking.exponentOf : AnticausativeMarking → Option VoiceProjectionLocus
  | .st       => none
  | .na       => some .voiceBare
  | .unmarked => some .voiceDOrBare
  | .ka       => some .vHead

/-- A marker is a *head exponent* when it spells out a Voice or v head — every
    marker except *-st*. -/
def AnticausativeMarking.IsHeadExponent (m : AnticausativeMarking) : Prop :=
  m.exponentOf.isSome = true

instance : DecidablePred AnticausativeMarking.IsHeadExponent :=
  fun _ => inferInstanceAs (Decidable (_ = true))

/-! ### Per-verb projections -/

/-- Wood's per-verb projection: the lexical entry plus the analytical apparatus
    the Fragment omits — the *-st* classification, the anticausative marker, and
    the [cuervo-2003]-style event decomposition. -/
structure StVerbInfo where
  /-- The lexical Fragment entry. -/
  verb : IcelandicStVerb
  /-- Wood's construction classification. -/
  stType : StType
  /-- The anticausative-marking morpheme (default *-st*). -/
  marking : AnticausativeMarking := .st
  /-- [cuervo-2003]-style lower event structure (without Voice's vDO). -/
  rootStructure : List VerbHead
  deriving Repr, BEq, DecidableEq

/-- *opna* / *opnast* 'open' — anticausative *-st* ([wood-2015] §3.5.1).
    Active *Jón opnaði dyrnar*; *-st* *Dyrnar opnuðust* 'the door opened'. -/
def opnast_info : StVerbInfo :=
  { verb := opnast, stType := .anticausative, rootStructure := [.vCAUSE, .vGO, .vBE] }

/-- *splundra* / *splundrast* 'shatter' — anticausative *-st* ([wood-2015]). -/
def splundrast_info : StVerbInfo :=
  { verb := splundrast, stType := .anticausative, rootStructure := [.vCAUSE, .vGO, .vBE] }

/-- *brjóta* / *brotna* 'break' — anticausative marked with *-na*, the exponent
    of Voice{∅} ([wood-2015] §3.3.2). Contrast with the *-st* anticausatives. -/
def brotna_info : StVerbInfo :=
  { verb := brotna, stType := .anticausative, marking := .na,
    rootStructure := [.vCAUSE, .vGO, .vBE] }

/-- *selja* / *seljast* 'sell' — generic middle *-st* ([wood-2015] §6.3). -/
def seljast_info : StVerbInfo :=
  { verb := seljast, stType := .middle, rootStructure := [.vCAUSE, .vGO, .vBE] }

/-- *lesa* / *lesast* 'read' — modal-passive *-st*, a generic-middle variant
    with an implicit agent ([wood-2015] §6.3: *Biblían á að lesast*). -/
def lesast_info : StVerbInfo :=
  { verb := lesast, stType := .middle, rootStructure := [.vCAUSE, .vGO, .vBE] }

/-- *setja* / *setjast* 'sit down' — figure reflexive *-st* in SpecpP, a posture
    verb ([wood-2015] §4). -/
def setjast_info : StVerbInfo :=
  { verb := setjast, stType := .figureReflexive, rootStructure := [.vGO, .vBE] }

/-- *klæða* / *klæðast* 'dress' — a (covert) figure reflexive, *-st* in SpecpP
    ([wood-2015] §6.6). -/
def klaedast_info : StVerbInfo :=
  { verb := klaedast, stType := .figureReflexive, rootStructure := [.vGO, .vBE] }

/-- *nálgast* 'approach' — inherent *-st*, lexicalized, no active variant
    ([wood-2015] §2.3.4). -/
def nalgast_info : StVerbInfo :=
  { verb := nalgast, stType := .inherent, rootStructure := [.vGO] }

/-- *minnast* 'remember' — inherent *-st*, no active variant ([wood-2015]). -/
def minnast_info : StVerbInfo :=
  { verb := minnast, stType := .inherent, rootStructure := [.vBE] }

/-- *leiðast* 'be bored' — dative-subject experiencer; Voice is non-thematic and
    the experiencer is an applied dative ([wood-2015] §5.4:
    *Henni leiddist Ólafur* 'she was bored by Ólafur'). -/
def leidast_info : StVerbInfo :=
  { verb := leidast, stType := .subjectExp, rootStructure := [.vBE] }

/-- *kyssa* / *kyssast* 'kiss' — reciprocal *-st* ([wood-2015] §6.5:
    *Jóna og Siggi kysstust* 'Jóna and Siggi kissed'). -/
def kyssast_info : StVerbInfo :=
  { verb := kyssast, stType := .reciprocal, rootStructure := [] }

/-- All *-st*-marked verb projections, in the order of the Fragment roster
    (excludes *brotna*, which is *-na*-marked). -/
def allStInfo : List StVerbInfo :=
  [opnast_info, splundrast_info, seljast_info, lesast_info,
   setjast_info, klaedast_info, nalgast_info, minnast_info,
   leidast_info, kyssast_info]

/-! ### *-st* is a specifier-occupant, not a Voice exponent -/

/-- Wood's thesis in one line: *-st* spells out no Voice or v head ([wood-2015]
    Ch. 2). It occupies a specifier; the head exponents are *-na* / *-Ø* / *-ka*. -/
theorem st_not_head_exponent : ¬ AnticausativeMarking.st.IsHeadExponent := by decide

/-- *-na* (Voice{∅}) and *-ka* (v) spell out different heads, so they never
    co-occur ([wood-2015] §3.3): the genuine exponents partition Voice/v space. -/
theorem na_ka_distinct_loci :
    AnticausativeMarking.na.exponentOf = some .voiceBare ∧
    AnticausativeMarking.ka.exponentOf = some .vHead ∧
    AnticausativeMarking.na.exponentOf ≠ AnticausativeMarking.ka.exponentOf := by
  decide

/-- On the same alternation class, *brotna* takes the head exponent *-na*
    (Voice{∅}) while *opnast* takes *-st*, which spells out no head — the
    *-st* / *-na* contrast read off real verbs ([wood-2015] §3.3.2). -/
theorem brotna_na_vs_opnast_st :
    brotna_info.marking.exponentOf = some .voiceBare ∧
    ¬ opnast_info.marking.IsHeadExponent := by decide

/-! ### Merge site, not Voice flavor, distinguishes the constructions -/

/-- An agentive Voice already fills SpecVoiceP with its agent, so under agentive
    Voice *-st* must merge *lower* than SpecVoiceP — in SpecpP, the figure
    reflexive ([wood-2015]: "since Voice is agentive, -st would not be able to
    merge in SpecVoiceP"). Derived from `site` / `voiceFlavor`, not stipulated. -/
theorem agentive_st_merges_low (t : StType) :
    t.voiceFlavor = .agentive → t.site ≠ .specVoiceD := by
  cases t <;> decide

/-- *-st* is not the exponent of a single Voice head: it co-occurs both with a
    θ-assigning Voice (figure reflexives have an agent) and with a non-θ Voice
    (anticausatives). No Voice head has both profiles, so the affixal view is
    refuted ([wood-2015] Ch. 4). -/
theorem st_not_single_voice_exponent :
    StType.figureReflexive.voiceFlavor.thetaRole.isSome = true ∧
    StType.anticausative.voiceFlavor.thetaRole = none := by decide

/-! ### Voice–CAUSE independence (Ch. 3) -/

/-- The causal head is shared across the causative/anticausative alternation of
    *opna* / *opnast*: agentive Voice prepends vDO (causative), non-thematic
    Voice does not (inchoative), but CAUSE is present in both ([wood-2015]
    Ch. 3, in [cuervo-2003] decomposition). -/
theorem opna_alternation :
    isCausative (buildDecomposition voiceAgent opnast_info.rootStructure) = true ∧
    isInchoative (buildDecomposition voiceAnticausative opnast_info.rootStructure) = true ∧
    hasCause (buildDecomposition voiceAnticausative opnast_info.rootStructure) = true := by
  decide

/-- The constructions occupy distinct cells of the ±D / ±λx Voice space
    ([alexiadou-schaefer-2015]): anticausative and
    subject-experiencer host a non-thematic [+D, −λx] Voice, figure reflexives a
    thematic [+D, +λx] Voice, the generic middle a specifierless [−D] Voice. -/
theorem parametric_diversity :
    (StType.anticausative.voiceFlavor.toParams).extArgSemantics = some .expletive ∧
    (StType.subjectExp.voiceFlavor.toParams).extArgSemantics = some .expletive ∧
    (StType.figureReflexive.voiceFlavor.toParams).extArgSemantics = some .thematicArgument ∧
    (StType.middle.voiceFlavor.toParams).selectsSpecifier = some false := by
  decide

/-! ### Applicatives and applied datives (Ch. 5) -/

/-- *-st* cannot occupy SpecApplP: Appl assigns dative and *-st* is caseless
    (`caseOf = none`), whereas a case-bearing DP can ([wood-2015] §5.3.2). This
    instantiates the substrate `ApplHead.SpecCanBearCase` mechanism for *-st*. -/
theorem st_blocked_from_specApplP :
    ¬ applLowRecipient.SpecCanBearCase (none : Option Case) ∧
    applLowRecipient.SpecCanBearCase (some Case.dat) := by decide

/-- Applied datives are otherwise retained under *-st*: Appl licenses its dative
    independently of Voice. The high/low asymmetry — a high (ethical) applicative
    needs an event-semantic Voice and is blocked in middles, a low (recipient)
    applicative is not — follows [pylkkanen-2008] / [schaefer-2008], not
    [wood-2015]'s Icelandic-specific claim that Icelandic lacks true high
    applicatives ([wood-2015] §5.2.1, §5.3.1). -/
theorem dative_voice_asymmetry :
    ¬ applHigh.Licensed voiceMiddle ∧
    applHigh.Licensed voiceAgent ∧
    applLowRecipient.Licensed voiceMiddle ∧
    applLowRecipient.Licensed voiceAnticausative := by decide

/-! ### Consistency over the verb roster -/

/-- Every anticausative *-st* verb has an inchoative event structure (change +
    result, no agentive vDO; [cuervo-2003]). -/
theorem anticausatives_inchoative :
    (allStInfo.filter (·.stType == .anticausative)).all
      (fun i => isInchoative i.rootStructure) = true := by decide

/-- Inherent and subject-experiencer *-st* verbs lack an active variant — their
    *-st* is lexicalized, or (for the psych verbs) the sole argument is a dative
    ([wood-2015] §2.3.4, §5.4). -/
theorem lexicalized_lack_active :
    (allStInfo.filter (fun i => i.stType == .inherent || i.stType == .subjectExp)).all
      (fun i => !i.verb.hasActiveVariant) = true := by decide

end Wood2015
