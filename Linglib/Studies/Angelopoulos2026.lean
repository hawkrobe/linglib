import Linglib.Studies.Bondarenko2022
import Linglib.Studies.Roussou2010
import Linglib.Fragments.Greek.StandardModern.Complementizers
import Linglib.Syntax.Category.Verb.Selection
import Linglib.Data.Examples.Angelopoulos2026

/-!
# Angelopoulos 2026: On clausal complementation, once more

[angelopoulos-2026] derives the distribution of Greek *oti*- and
*pu*-clauses — near-complementary after verbs (ex. 1), free as internal
arguments and derived subjects yet banned as external arguments (§2.2),
stativity-restricted as *pu*-complements (§2.3) — from reversed
selection: *oti* and *pu* bear an uninterpretable [n]-feature checked
by a light noun in their specifier (partly adopting [arsenijevic-2009])
that must incorporate into a lexical verbal head, licit only from
complement position (§3.1). The *oti* ~ *pu* split follows from the
content/situation dichotomy (§3.2, adopting [bondarenko-2022]), the
stativity restriction from aspectual-head selection (§4.1), and §7.3
turns the §2 argumenthood diagnostics against Bondarenko's transparent
syntax–semantics mapping: bare *oti*-clauses sit in complement position
while composing via Predicate Modification (the explanans reading,
[elliott-2020-embedding]). Typed paradigm sentences (ex. 1, 31–34) live
in `Angelopoulos2026.Examples`.

## Main definitions

* `selectsLightNoun`, `otiOnlyVerbs`, `puOnlyVerbs`, `dualVerbs`: the
  §3.1 light-noun datum and the attested selection classes
* `NounHost`, `ClausePosition`, `licensedIn`: incorporation licensing
  by position
* `selectsClause`, `AspectualHead.ofVendler`: the §4.1 stativity locus
* `clauseSort`: *oti* = content, *pu* = situation
  (`Bondarenko2022.NominalSort`, §3.2)
* `bareOtiAttested`: the §7.3 (position, composition-path) attestations

## Main results

* `frames_underdetermine_distribution`: `Verb.realizes` admits both
  *oti* and *pu* on the whole sample — the §1 puzzle
* `factivity_anti_aligned`: verb-level and C-level factivity are
  anti-aligned on the sample
* `licensing_matches_judgments`: the position asymmetry against the
  ex. 31–32 judgments
* `pu_complement_verb_stative`: the §2.3 verb-level stativity
  generalization, derived from §4.1 selection
* `selectsLightNoun_iff_sorted`: the light-noun selectors are the
  sorted complementizers
* `transparency_conflates_axes`: the §7.3 counterclaim against
  `Bondarenko2022.transparentSSMapping`
-/

namespace Angelopoulos2026

open Greek.StandardModern.Complementizers
open Bondarenko2022 (NominalSort CompositionPath)
open Features (VendlerClass)

/-! ### Reversed selection: the light noun (§3.1) -/

/-- *oti* and *pu* select a light noun in their specifier, checking an
uninterpretable [n]-feature (§3.1); *na* does not (its licensing is
mood-driven). Paper-specific datum over the fragment entries; the paper
is neutral on the category of *oti* and *pu* (fn. 3). -/
def selectsLightNoun (c : Complementizer) : Prop := c = oti ∨ c = pu

instance : DecidablePred selectsLightNoun :=
  fun _ => inferInstanceAs (Decidable (_ ∨ _))

/-! ### The attested selection classes (§1–§2.3) -/

/-- Matrix verbs attested with *oti* only (ex. 1a, 3–4, 21): saying,
belief, knowledge. Study-local lists: the frame axes underdetermine the
split (`frames_underdetermine_distribution`), and the account derives
it semantically (§3.2, §4.1) rather than from a verb-level feature. -/
def otiOnlyVerbs : List Verb :=
  [leo, pistevo, ksero, katalaveno, sinidhitopio, eksigo]

/-- Matrix verbs attested with *pu* only (ex. 1b, 13–14, 20): the
emotive factives. -/
def puOnlyVerbs : List Verb := [metaniono, areso, xerome]

/-- Verbs attested with both (ex. 19, 22–23), as (eventive *oti*-sense,
stative *pu*-sense) pairs of sense-tagged fragment entries. -/
def dualVerbs : List (Verb × Verb) :=
  [(thimame, thimameStat), (thimono, thimonoStat)]

/-- The §1 puzzle through the `Verb.realizes` selection hom: every verb
in the sample types both *oti*- and *pu*-clauses on the coding/force
axes (both are finite indicative declaratives), while subjunctive *na*
is already excluded — the *oti* ~ *pu* residue is what the
content/situation account derives. -/
theorem frames_underdetermine_distribution :
    ∀ v ∈ otiOnlyVerbs ++ puOnlyVerbs,
      v.realizes oti ∧ v.realizes pu ∧ ¬ v.realizes na := by
  decide

/-- The emotive/cognitive factivity split: verb-level and C-level
factivity are anti-aligned on the sample. The complement-presupposing
*oti*-selectors are exactly the knowledge verbs, while *oti* records no
lexical factivity; no *pu*-only emotive factive presupposes lexically
(preferential rather than veridical-doxastic attitude), yet *pu* is
lexically factive. Complement factivity thus has two independent
sources — verb and complementizer — which the Greek data tease apart. -/
theorem factivity_anti_aligned :
    oti.factive = none ∧ pu.factive = some true ∧
    otiOnlyVerbs.filter (·.factivePresup) = [ksero, katalaveno, sinidhitopio] ∧
    puOnlyVerbs.filter (·.factivePresup) = [] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### Incorporation licensing and the argument asymmetry (§3.1) -/

/-- Heads adjacent to a clause's light noun. Only a lexical verbal
head licenses noun incorporation ([hale-keyser-1993]); functional T
and P do not (§3.1 ex. 29–32). -/
inductive NounHost where
  | vLex
  | t
  | p
  deriving DecidableEq, Repr

/-- Whether a host licenses light-noun incorporation. -/
def NounHost.licenses : NounHost → Prop
  | .vLex => True
  | .t    => False
  | .p    => False

instance : DecidablePred NounHost.licenses
  | .vLex => isTrue trivial
  | .t    => isFalse id
  | .p    => isFalse id

/-- Positions a bare oti/pu-clause can occupy, each with the nearest
potential incorporation host: internal arguments sit under an
aspectual v; incorporation precedes movement for derived subjects;
the nearest head above Spec,vP is T; P cannot host (§3.1 ex. 27–32). -/
inductive ClausePosition where
  | internalArgument
  | derivedSubject
  | externalArgument
  | pComplement
  deriving DecidableEq, Repr

/-- The nearest potential incorporation host from each position. -/
def ClausePosition.nearestHost : ClausePosition → NounHost
  | .internalArgument => .vLex
  | .derivedSubject   => .vLex
  | .externalArgument => .t
  | .pComplement      => .p

/-- A bare oti/pu-clause is licensed in a position iff the nearest
host licenses light-noun incorporation — the paper's derivation of
the distribution, not a stipulated table. -/
def licensedIn (pos : ClausePosition) : Prop := pos.nearestHost.licenses

instance : DecidablePred licensedIn := fun pos =>
  inferInstanceAs (Decidable pos.nearestHost.licenses)

/-- Internal arguments and derived subjects are licensed (§2.1–2.2). -/
theorem internal_and_derived_subject_licensed :
    licensedIn .internalArgument ∧ licensedIn .derivedSubject :=
  ⟨trivial, trivial⟩

/-- The external-argument ban (§2.2): T cannot host incorporation. -/
theorem external_argument_banned : ¬ licensedIn .externalArgument := id

/-- Bare clauses are excluded after P (ex. 31c, 32c). -/
theorem p_complement_banned : ¬ licensedIn .pComplement := id

/-- The licensing predictions match the ex. 31–32 paradigm judgments:
bare clauses are fine as internal arguments (31b, 32b) and out after
P (31c, 32c). -/
theorem licensing_matches_judgments :
    ∀ p ∈ [(ClausePosition.internalArgument, Examples.ex_31b),
           (.internalArgument, Examples.ex_32b),
           (.pComplement, Examples.ex_31c),
           (.pComplement, Examples.ex_32c)],
      licensedIn p.1 ↔ p.2.judgment ≠ .ungrammatical := by
  decide

/-! ### The stativity locus (§4.1) -/

/-- Aspectual heads introducing internal arguments (§4.1, following
Borer and Merchant as cited there). -/
inductive AspectualHead where
  | vState
  | vEvent
  deriving DecidableEq, Repr

/-- The aspectual head introducing a verb's internal argument tracks
the verb's Vendler class through its dynamicity (§4.1). -/
def AspectualHead.ofVendler (vc : VendlerClass) : AspectualHead :=
  match vc.dynamicity with
  | .stative => .vState
  | .dynamic => .vEvent

/-- §4.1: vState selects both otiP and puP as its complement; vEvent
selects only otiP. -/
def selectsClause : AspectualHead → Complementizer → Prop
  | .vState, c => c = oti ∨ c = pu
  | .vEvent, c => c = oti

/-- The stativity restriction (§2.3), derived: a *pu*-complement
forces the stative aspectual head. -/
theorem pu_requires_stative (h : AspectualHead)
    (hp : selectsClause h pu) : h = .vState := by
  cases h
  · rfl
  · exact absurd (show pu = oti from hp) (by decide)

/-- The §2.3 stativity generalization, derived: a verb whose aspectual
head licenses a *pu*-complement is Vendler-stative. -/
theorem pu_complement_verb_stative (vc : VendlerClass)
    (hp : selectsClause (.ofVendler vc) pu) : vc = .state := by
  cases vc
  · rfl
  all_goals exact absurd (show pu = oti from hp) (by decide)

/-- The verb-level reflex over the fragment sample: each *pu*-only
matrix verb's aspectual head is `vState`. -/
theorem pu_only_verbs_stative :
    ∀ v ∈ puOnlyVerbs,
      v.vendlerClass.map AspectualHead.ofVendler = some .vState := by
  decide

/-- The dual verbs realize the same restriction sense-internally:
`vState` for the *pu*-sense, `vEvent` for the *oti*-sense
(ex. 19, 22–23). -/
theorem dual_verbs_stative_with_pu :
    ∀ p ∈ dualVerbs,
      p.2.vendlerClass.map AspectualHead.ofVendler = some .vState ∧
      p.1.vendlerClass.map AspectualHead.ofVendler = some .vEvent := by
  decide

/-! ### Content vs situation (§3.2) -/

/-- The sort of clause each complementizer introduces — *oti* content,
*pu* situation — which must match the incorporating noun's sort
(§3.2). The sorts and their diagnostics ('true'/'mistaken' vs
'happen', ex. 33–34) are [bondarenko-2022]'s (`Bondarenko2022.NominalSort`,
§2.2.3); *na* is outside the dichotomy. -/
def clauseSort (c : Complementizer) : Option NominalSort :=
  if c = oti then some .content
  else if c = pu then some .situation
  else none

/-- The assigned sorts pass the §3.2 diagnostics: *oti*'s sort is
truth-evaluable, *pu*'s occurrence-compatible (ex. 33–34, matching
[bondarenko-2022] §2.2.3). -/
theorem clauseSort_matches_diagnostics :
    clauseSort oti = some .content ∧
    NominalSort.truthEvaluable .content ∧
    clauseSort pu = some .situation ∧
    NominalSort.occurrenceCompatible .situation := by
  decide

/-- The light-noun selectors are exactly the sorted complementizers:
incorporation presupposes a clause sort for the noun to match
(§3.1–§3.2); *an* and *na* fall outside both. -/
theorem selectsLightNoun_iff_sorted :
    ∀ c ∈ complementizers, (selectsLightNoun c ↔ (clauseSort c).isSome) := by
  decide

/-- fn. 17's rebuttal of a reviewer's oti ~ pu allomorphy alternative,
cross-checked against the rival lexical typology: both this account
and [roussou-2010]'s hold the two lexically distinct — content vs
situation sort here, indefinite vs definite propositional
quantification there (`Roussou2010.profile`). -/
theorem oti_pu_lexically_distinct :
    clauseSort oti ≠ clauseSort pu ∧
    Roussou2010.profile oti ≠ Roussou2010.profile pu := by
  decide

/-! ### Against the transparent syntax–semantics mapping (§7.3) -/

/-- Syntactic position of an embedded clause — one of the two axes
[bondarenko-2022]'s `ClauseStructurePath` conflates. -/
inductive SynPosition where
  | complement
  | adjunct
  deriving DecidableEq, Repr

/-- The paper's claim for bare *oti*-clauses (§2 diagnostics + §7.3),
on the composition axis of [bondarenko-2022]'s `CompositionPath` (PM
with the verb's situation argument = `viaSituation`, FA into a DP slot
= `viaDPArgument`): complement position composing via PM is attested
(the explanans reading); FA requires the nominalizing D (§7.3 ex. 57),
so bare clauses never compose via FA from either position. -/
def bareOtiAttested : SynPosition → CompositionPath → Prop
  | .complement, .viaSituation  => True
  | .complement, .viaDPArgument => False
  | .adjunct,    .viaSituation  => True
  | .adjunct,    .viaDPArgument => False

/-- Bare clauses never compose via FA from either position: FA requires
the nominalizing D (§7.3 ex. 57). -/
theorem bare_never_via_dp : ∀ p, ¬ bareOtiAttested p .viaDPArgument :=
  fun p => by cases p <;> exact id

/-- The §7.3 divergence: [bondarenko-2022] predicts the (bare, argument)
cell empty (`Bondarenko2022.bare_argument_predicted_impossible`),
identifying argument position with the FA path; Greek bare *oti*-clauses
realize syntactic argumenthood while composing via PM — the
identification of the two axes is what fails. Conditional on the paper's
premises: the clauses are BARE (no covert nominal shell — the analysis
rejects Arsenijević's DP layer and Faure's case-less-DP treatment, §3.1)
and are internal ARGUMENTS (clitic doubling, passivization, derived
subjects, §2.1–2.2). [bondarenko-2022] can deny either premise. -/
theorem transparency_conflates_axes :
    ¬ Bondarenko2022.transparentSSMapping .bareArgument ∧
    bareOtiAttested .complement .viaSituation :=
  ⟨Bondarenko2022.bare_argument_predicted_impossible, trivial⟩

end Angelopoulos2026
