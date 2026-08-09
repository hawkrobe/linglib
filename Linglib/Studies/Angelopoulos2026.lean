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
-/

namespace Angelopoulos2026

open Greek.StandardModern.Complementizers
open Bondarenko2022 (NominalSort CompositionPath)
open Features (VendlerClass)

/-! ### Reversed selection: the light noun (§3.1) -/

/-- *oti* and *pu* select a light noun in their specifier, checking an
uninterpretable [n]-feature; *na* does not (§3.1). -/
def selectsLightNoun (c : Complementizer) : Prop := c = oti ∨ c = pu

instance : DecidablePred selectsLightNoun :=
  fun _ => inferInstanceAs (Decidable (_ ∨ _))

/-! ### The attested selection classes (§1–§2.3) -/

/-- Matrix verbs attested with *oti* only: saying, belief, knowledge
(ex. 1a, 3–4, 21). -/
def otiOnlyVerbs : List Verb :=
  [leo, pistevo, ksero, katalaveno, sinidhitopio, eksigo]

/-- Matrix verbs attested with *pu* only: the emotive factives
(ex. 1b, 13–14, 20). -/
def puOnlyVerbs : List Verb := [metaniono, areso, xerome]

/-- Verbs attested with both, as (eventive *oti*-sense, stative
*pu*-sense) pairs (ex. 19, 22–23). -/
def dualVerbs : List (Verb × Verb) :=
  [(thimame, thimameStat), (thimono, thimonoStat)]

/-- Every sample verb's frames admit both *oti* and *pu* and already
exclude *na*: coding and force underdetermine the split (§1). -/
theorem frames_underdetermine_distribution :
    ∀ v ∈ otiOnlyVerbs ++ puOnlyVerbs,
      v.realizes oti ∧ v.realizes pu ∧ ¬ v.realizes na := by
  decide

/-- Verb-level and C-level factivity are anti-aligned: the
*oti*-selectors that presuppose their complement are exactly the
knowledge verbs, no *pu*-only emotive factive presupposes, and only
*pu* is lexically factive. -/
theorem factivity_anti_aligned :
    oti.factive = none ∧ pu.factive = some true ∧
    otiOnlyVerbs.filter (·.factivePresup) = [ksero, katalaveno, sinidhitopio] ∧
    puOnlyVerbs.filter (·.factivePresup) = [] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### Incorporation licensing and the argument asymmetry (§3.1) -/

/-- Heads adjacent to a clause's light noun: a lexical verbal head,
T, or P (§3.1). -/
inductive NounHost where
  | vLex
  | t
  | p
  deriving DecidableEq, Repr

/-- Only the lexical verbal head licenses light-noun incorporation
([hale-keyser-1993]); functional T and P do not. -/
def NounHost.licenses : NounHost → Prop
  | .vLex => True
  | .t    => False
  | .p    => False

instance : DecidablePred NounHost.licenses
  | .vLex => isTrue trivial
  | .t    => isFalse id
  | .p    => isFalse id

/-- Positions a bare oti/pu-clause can occupy (§3.1 ex. 27–32). -/
inductive ClausePosition where
  | internalArgument
  | derivedSubject
  | externalArgument
  | pComplement
  deriving DecidableEq, Repr

/-- The nearest potential incorporation host from each position. -/
def ClausePosition.nearestHost : ClausePosition → NounHost
  | .internalArgument => .vLex
  | .derivedSubject   => .vLex  -- incorporation precedes movement
  | .externalArgument => .t     -- nearest head above Spec,vP
  | .pComplement      => .p

/-- A bare oti/pu-clause is licensed in a position iff its nearest
host licenses light-noun incorporation (§3.1). -/
def licensedIn (pos : ClausePosition) : Prop := pos.nearestHost.licenses

instance : DecidablePred licensedIn := fun pos =>
  inferInstanceAs (Decidable pos.nearestHost.licenses)

/-- Bare clauses are licensed as internal arguments and derived
subjects (§2.1–2.2). -/
theorem internal_and_derived_subject_licensed :
    licensedIn .internalArgument ∧ licensedIn .derivedSubject :=
  ⟨trivial, trivial⟩

/-- Bare clauses are banned from external-argument position: T cannot
host incorporation (§2.2). -/
theorem external_argument_banned : ¬ licensedIn .externalArgument := id

/-- Bare clauses are excluded after P (ex. 31c, 32c). -/
theorem p_complement_banned : ¬ licensedIn .pComplement := id

/-- The licensing predictions match the ex. 31–32 judgments:
acceptable as internal arguments, ungrammatical after P. -/
theorem licensing_matches_judgments :
    ∀ p ∈ [(ClausePosition.internalArgument, Examples.ex_31b),
           (.internalArgument, Examples.ex_32b),
           (.pComplement, Examples.ex_31c),
           (.pComplement, Examples.ex_32c)],
      licensedIn p.1 ↔ p.2.judgment ≠ .ungrammatical := by
  decide

/-! ### The stativity locus (§4.1) -/

/-- Aspectual heads introducing internal arguments (§4.1). -/
inductive AspectualHead where
  | vState
  | vEvent
  deriving DecidableEq, Repr

/-- The aspectual head determined by a verb's Vendler class: `vState`
for stative classes, `vEvent` for dynamic ones (§4.1). -/
def AspectualHead.ofVendler (vc : VendlerClass) : AspectualHead :=
  match vc.dynamicity with
  | .stative => .vState
  | .dynamic => .vEvent

/-- vState selects both otiP and puP as its complement; vEvent selects
only otiP (§4.1). -/
def selectsClause : AspectualHead → Complementizer → Prop
  | .vState, c => c = oti ∨ c = pu
  | .vEvent, c => c = oti

/-- A *pu*-complement forces the stative aspectual head (§2.3). -/
theorem pu_requires_stative (h : AspectualHead)
    (hp : selectsClause h pu) : h = .vState := by
  cases h
  · rfl
  · exact absurd (show pu = oti from hp) (by decide)

/-- A verb whose aspectual head licenses a *pu*-complement is
Vendler-stative (§2.3). -/
theorem pu_complement_verb_stative (vc : VendlerClass)
    (hp : selectsClause (.ofVendler vc) pu) : vc = .state := by
  cases vc
  · rfl
  all_goals exact absurd (show pu = oti from hp) (by decide)

/-- Every *pu*-only matrix verb's aspectual head is `vState`. -/
theorem pu_only_verbs_stative :
    ∀ v ∈ puOnlyVerbs,
      v.vendlerClass.map AspectualHead.ofVendler = some .vState := by
  decide

/-- Each dual verb's *pu*-sense takes `vState` and its *oti*-sense
`vEvent` (ex. 19, 22–23). -/
theorem dual_verbs_stative_with_pu :
    ∀ p ∈ dualVerbs,
      p.2.vendlerClass.map AspectualHead.ofVendler = some .vState ∧
      p.1.vendlerClass.map AspectualHead.ofVendler = some .vEvent := by
  decide

/-! ### Content vs situation (§3.2) -/

/-- The sort of clause each complementizer introduces — *oti* content,
*pu* situation, *na* neither — which must match the incorporating
noun's sort (§3.2). -/
def clauseSort (c : Complementizer) : Option NominalSort :=
  if c = oti then some .content
  else if c = pu then some .situation
  else none

/-- The sort of the light noun a verb selects: stative senses and
stative preferential attitudes relate to situations; saying, belief,
and knowledge to content (§3.2). -/
def nounSort (v : Verb) : Option NominalSort :=
  if v.senseTag = .stative then some .situation
  else match v.attitude with
    | some (.preferential _) =>
        if v.vendlerClass = some .state then some .situation
        else some .content
    | _ => some .content

/-- The near-complementary distribution follows from sort matching:
each verb class pairs with exactly the complementizer whose clause
sort matches its noun sort (§3.2). -/
theorem distribution_from_sort_matching :
    (∀ v ∈ otiOnlyVerbs, nounSort v = clauseSort oti) ∧
    (∀ v ∈ puOnlyVerbs, nounSort v = clauseSort pu) ∧
    (∀ p ∈ dualVerbs,
      nounSort p.1 = clauseSort oti ∧ nounSort p.2 = clauseSort pu) := by
  decide

/-- The situation-sorted complementizer is the lexically factive one
(§3.2). -/
theorem situation_clause_factive :
    ∀ c ∈ complementizers,
      clauseSort c = some .situation → c.factive = some true := by
  decide

/-- The sorts pass the §3.2 diagnostics: *oti*'s is truth-evaluable
('true'/'mistaken'), *pu*'s occurrence-compatible ('happen')
(ex. 33–34). -/
theorem clauseSort_matches_diagnostics :
    clauseSort oti = some .content ∧
    NominalSort.truthEvaluable .content ∧
    clauseSort pu = some .situation ∧
    NominalSort.occurrenceCompatible .situation := by
  decide

/-- The light-noun selectors are exactly the sort-bearing
complementizers: the noun must match its clause's sort (§3.1–§3.2). -/
theorem selectsLightNoun_iff_sorted :
    ∀ c ∈ complementizers, (selectsLightNoun c ↔ (clauseSort c).isSome) := by
  decide

/-- *oti* and *pu* are lexically distinct on this account (content vs
situation) and on [roussou-2010]'s (indefinite vs definite), against
fn. 17's allomorphy alternative. -/
theorem oti_pu_lexically_distinct :
    clauseSort oti ≠ clauseSort pu ∧
    Roussou2010.profile oti ≠ Roussou2010.profile pu := by
  decide

/-! ### Against the transparent syntax–semantics mapping (§7.3) -/

/-- Syntactic position of an embedded clause: complement or adjunct
(§7.3). -/
inductive SynPosition where
  | complement
  | adjunct
  deriving DecidableEq, Repr

/-- The (position, composition-path) pairs attested for bare
*oti*-clauses: Predicate Modification from either position, Functional
Application from neither (§2, §7.3). -/
def bareOtiAttested : SynPosition → CompositionPath → Prop
  | .complement, .viaSituation  => True
  | .complement, .viaDPArgument => False
  | .adjunct,    .viaSituation  => True
  | .adjunct,    .viaDPArgument => False

/-- Bare clauses never compose via FA from either position: FA requires
the nominalizing D (§7.3 ex. 57). -/
theorem bare_never_via_dp : ∀ p, ¬ bareOtiAttested p .viaDPArgument :=
  fun p => by cases p <;> exact id

/-- Greek bare *oti*-clauses fill the cell [bondarenko-2022]'s
transparent mapping predicts empty: syntactic argumenthood without
Functional Application (§7.3). -/
theorem transparency_conflates_axes :
    ¬ Bondarenko2022.transparentSSMapping .bareArgument ∧
    bareOtiAttested .complement .viaSituation :=
  ⟨Bondarenko2022.bare_argument_predicted_impossible, trivial⟩

end Angelopoulos2026
