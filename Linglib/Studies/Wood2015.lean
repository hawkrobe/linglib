import Linglib.Syntax.Minimalist.Verbal.Voice
import Linglib.Syntax.Minimalist.Verbal.Applicative
import Linglib.Fragments.Icelandic.Predicates
import Linglib.Data.Examples.Wood2015

/-!
# Wood (2015): Icelandic Morphosyntax and Argument Structure

This file formalizes [wood-2015]'s thesis that the Icelandic clitic *-st* is not an exponent of
a Voice head. It is a defective person clitic, a featural subset of the reflexive pronoun, that
merges in a specifier position and cliticizes to the verb. Its uses (anticausative, generic
middle, figure reflexive, reflexive, subject experiencer, reciprocal, inherent) arise from where
it merges (`Site`), not from *-st* spelling out different Voice flavors; the genuine Voice and v
exponents are *-na*, the elsewhere *-Ø*, and *-ka* (`AnticausativeMarking.exponentOf`). Two
consequences are derived from the merge site and the host clause's Voice flavor. An agentive
Voice already fills SpecVoiceP with its agent, so under agentive Voice *-st* merges lower, in
SpecpP (`agentive_st_merges_low`); and since *-st* co-occurs both with a θ-assigning Voice
(figure reflexives) and with a non-thematic one (anticausatives), no single Voice head has its
profile (`st_not_single_voice_exponent`). Because Appl assigns dative and *-st* is caseless,
*-st* cannot occupy SpecApplP (`st_blocked_from_specApplP`).

## Implementation notes

The per-verb projections pair Fragment entries with the book's construction classification,
which is paper-specific apparatus and so lives here.

## TODO

The book's chapter and section locators are unverified; the examples follow the numbering of
the 2012 dissertation the book revises.

## References

* [wood-2015]
* [alexiadou-schaefer-2015]
* [kratzer-1996]
* [wood-marantz-2017]
-/

namespace Wood2015

open Minimalist Minimalist.Voice Icelandic.Predicates

/-! ### The *-st* clitic and its merge site -/

/-- Where the *-st* clitic merges: it occupies a specifier and checks its head's [D] feature. -/
inductive Site where
  /-- SpecVoiceP of Voice{D}: anticausatives and dative-subject experiencers. -/
  | specVoiceD
  /-- SpecpP of the figure/ground head p{D}: figure reflexives, including covert ones like
  *klæðast*. -/
  | specLittleP
  /-- A lower vP-internal specifier: reciprocals and the reflexive/middle residue. -/
  | specLow
  deriving DecidableEq, Repr

/-- The descriptive classification of *-st* constructions. -/
inductive Construction where
  | anticausative
  | middle
  | figureReflexive
  | reflexive
  | inherent
  | subjectExp
  | reciprocal
  deriving DecidableEq, Repr

/-- The specifier *-st* occupies in each construction. -/
def Construction.site : Construction → Site
  | .anticausative | .subjectExp => .specVoiceD
  | .figureReflexive | .reflexive => .specLittleP
  | .middle | .reciprocal | .inherent => .specLow

/-- The Voice flavor of the host clause in each construction, the flavor *-st* co-occurs with
rather than one it realizes: anticausative and subject-experiencer clauses have non-thematic
Voice, figure reflexives and reciprocals are agentive, the generic middle is expletive. -/
def Construction.voiceFlavor : Construction → Flavor
  | .anticausative | .subjectExp | .inherent => .nonThematic
  | .middle => .expletive
  | .figureReflexive | .reflexive | .reciprocal => .agentive

/-! ### The anticausative exponent inventory -/

/-- How an anticausative alternation is morphologically marked. -/
inductive AnticausativeMarking where
  | st
  | na
  | unmarked
  | ka
  deriving DecidableEq, Repr

/-- The head a marker spells out, if any: *-st* spells out no head, *-na* spells out
specifierless Voice{∅}, *-Ø* is the elsewhere Voice exponent, and *-ka* spells out v. -/
def AnticausativeMarking.exponentOf : AnticausativeMarking → Option ProjectionLocus
  | .st => none
  | .na => some .voiceBare
  | .unmarked => some .voiceDOrBare
  | .ka => some .vHead

/-- A marker is a head exponent when it spells out a Voice or v head. -/
def AnticausativeMarking.IsHeadExponent (m : AnticausativeMarking) : Prop :=
  m.exponentOf.isSome = true

instance : DecidablePred AnticausativeMarking.IsHeadExponent :=
  λ _ => inferInstanceAs (Decidable (_ = true))

/-! ### Per-verb projections -/

/-- A Fragment entry together with the book's classification of its *-st* form. -/
structure Projection where
  verb : IcelandicStVerb
  construction : Construction
  marking : AnticausativeMarking := .st
  deriving Repr, DecidableEq

/-- *opna* ~ *opnast* 'open', an anticausative. -/
def opnastInfo : Projection := { verb := opnast, construction := .anticausative }

/-- *splundra* ~ *splundrast* 'shatter', an anticausative. -/
def splundrastInfo : Projection := { verb := splundrast, construction := .anticausative }

/-- *brjóta* ~ *brotna* 'break', an anticausative marked with *-na*. -/
def brotnaInfo : Projection :=
  { verb := brotna, construction := .anticausative, marking := .na }

/-- *selja* ~ *seljast* 'sell', a generic middle. -/
def seljastInfo : Projection := { verb := seljast, construction := .middle }

/-- *lesa* ~ *lesast* 'read', a modal passive, a generic-middle variant. -/
def lesastInfo : Projection := { verb := lesast, construction := .middle }

/-- *setja* ~ *setjast* 'sit down', a figure reflexive. -/
def setjastInfo : Projection := { verb := setjast, construction := .figureReflexive }

/-- *klæða* ~ *klæðast* 'dress', a covert figure reflexive. -/
def klaedastInfo : Projection := { verb := klaedast, construction := .figureReflexive }

/-- *nálgast* 'approach', an inherent *-st* verb. -/
def nalgastInfo : Projection := { verb := nalgast, construction := .inherent }

/-- *minnast* 'remember', an inherent *-st* verb. -/
def minnastInfo : Projection := { verb := minnast, construction := .inherent }

/-- *leiðast* 'be bored', a dative-subject experiencer. -/
def leidastInfo : Projection := { verb := leidast, construction := .subjectExp }

/-- *kyssa* ~ *kyssast* 'kiss', a reciprocal. -/
def kyssastInfo : Projection := { verb := kyssast, construction := .reciprocal }

/-! ### *-st* is a specifier occupant, not a Voice exponent -/

/-- *-st* spells out no Voice or v head. -/
theorem st_not_head_exponent : ¬ AnticausativeMarking.st.IsHeadExponent := by decide

/-- *-na* and *-ka* spell out different heads, so they never co-occur. -/
theorem na_ka_distinct_loci :
    AnticausativeMarking.na.exponentOf ≠ AnticausativeMarking.ka.exponentOf := by decide

/-- On the same alternation class, *brotna* takes a head exponent while *opnast* takes *-st*,
which spells out no head. -/
theorem brotna_na_vs_opnast_st :
    brotnaInfo.marking.IsHeadExponent ∧ ¬ opnastInfo.marking.IsHeadExponent := by decide

/-! ### Merge site, not Voice flavor, distinguishes the constructions -/

/-- Under agentive Voice, whose agent fills SpecVoiceP, *-st* merges lower than SpecVoiceP. -/
theorem agentive_st_merges_low (t : Construction) :
    t.voiceFlavor = .agentive → t.site ≠ .specVoiceD := by
  cases t <;> decide

/-- *-st* co-occurs both with a θ-assigning Voice and with a non-thematic one, so it is not the
exponent of a single Voice head. -/
theorem st_not_single_voice_exponent :
    ∃ t t' : Construction, t.voiceFlavor.thetaRole.isSome ∧ t'.voiceFlavor.thetaRole = none :=
  ⟨.figureReflexive, .anticausative, rfl, rfl⟩

/-! ### Applicatives -/

/-- Appl assigns dative and *-st* is caseless, so *-st* cannot occupy SpecApplP, whereas a
case-bearing DP can. -/
theorem st_blocked_from_specApplP :
    ¬ applLowRecipient.SpecCanBearCase (none : Option Case) ∧
    applLowRecipient.SpecCanBearCase (some Case.dat) := by decide

end Wood2015
