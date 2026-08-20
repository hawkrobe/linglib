/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.ConstructionGrammar.ArgumentStructure
import Linglib.Syntax.ConstructionGrammar.Idiom
import Linglib.Syntax.ConstructionGrammar.Inheritance
import Linglib.Data.Examples.FillmoreKayOConnor1988
import Linglib.Features.Polarity
import Linglib.Semantics.Polarity.Item
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Sum

/-!
# [fillmore-kay-oconnor-1988]: *Let Alone*

"Regularity and Idiomaticity in Grammatical Constructions: The Case of
*Let Alone*" (Language 64(3):501–538), the founding Construction Grammar
paper: *let alone* is a formal idiom — a productive syntactic pattern
F ⟨X A Y let alone B⟩ whose semantics requires a presupposed scalar model
(Appendix, definitions A1–A5) and whose pragmatics resolves a conflict
between Gricean Quantity (the informative full clause) and Relevance (the
contextually given reduced clause). The idiom typology of §1 lives in
`ConstructionGrammar.Idiom`; §2.1's conclusion that *let alone* is a
formal idiom is derived from the construction's typed form
(`let_alone_formal_idiom`).

The paper's scalar models are n-dimensional with n > 1 (definition A1;
fn. 16: "a scalar model must contain at least two dimensions"). The
military-rank model below is a deliberate one-dimensional simplification
of the paper's colonel/general example, not a paper-licit scalar model;
the linguists × languages model is the paper's own 2D example.

## Main declarations

- `FillmoreKayOConnor1988.IsScalarModel`: definition A3, over points in
  their product order and propositions ordered by entailment; `NegEntails`
  is definition A4
- `FillmoreKayOConnor1988.letAloneConstruction`, `LetAloneConditions`,
  `ex21Conditions`: the construction, its felicity conditions (p. 528),
  and their instantiation for ex. 21
- `FillmoreKayOConnor1988.let_alone_irreducible`: *let alone* is not fully
  compositional
- `FillmoreKayOConnor1988.MadeRank`, `CanRead`: the worked scalar
  models
- `Data.Examples.FillmoreKayOConnor1988`: the paper's judgment data
  (generated module; `Examples.all`)
-/

namespace FillmoreKayOConnor1988

open ConstructionGrammar
open Features (Polarity)

/-! ### Scalar models (§2.3.2, Appendix)

The argument space Dˣ is a product of scales carrying its product order:
definition A2's "dᵢ is lower than dⱼ" (p. 536) — no coordinate higher, at
least one strictly lower — is `di < dj` in that order. Propositions are
ordered by entailment — `P dj ≤ P di`, pointwise over states — so
definition A5's "stronger" (p. 537) is strict entailment `P dj < P di`.
Definition A3 (p. 536) then classifies propositional functions:
⟨S, T, Dˣ, P⟩ is a scalar model iff, for distinct dᵢ, dⱼ, P(dⱼ) entails
P(dᵢ) just in case dᵢ is lower than dⱼ. -/

variable {Point S : Type*}

instance {P Q : S → Prop} [Fintype S] [DecidablePred P] [DecidablePred Q] :
    Decidable (P ≤ Q) :=
  inferInstanceAs (Decidable (∀ s, P s → Q s))

instance {P Q : S → Prop} [Fintype S] [DecidablePred P] [DecidablePred Q] :
    Decidable (P < Q) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Definition A3 (p. 536): for distinct points, entailment of the
propositions reflects the reversed point order. The biconditional is
demanding: a state space too sparse to separate the points produces
artifact entailments between incomparable points and fails it (see
`ll_sparse_fails_A3`). -/
def IsScalarModel [Preorder Point] (P : Point → S → Prop) : Prop :=
  ∀ di dj : Point, di ≠ dj → (P dj ≤ P di ↔ di < dj)

instance [Preorder Point] [DecidableEq Point] [DecidableLT Point]
    [Fintype Point] [Fintype S] (P : Point → S → Prop)
    [∀ d, DecidablePred (P d)] : Decidable (IsScalarModel P) :=
  inferInstanceAs
    (Decidable (∀ di dj : Point, di ≠ dj → (P dj ≤ P di ↔ di < dj)))

/-- Definition A4 (p. 536): ¬P(dᵢ) entails ¬P(dⱼ) — the direction at work
in the canonical negative *let alone* sentences: "he didn't make colonel;
a fortiori, he didn't make general" (p. 523). -/
def NegEntails (P : Point → S → Prop) (di dj : Point) : Prop :=
  ∀ s, ¬ P di s → ¬ P dj s

instance [Fintype S] (P : Point → S → Prop) [∀ d, DecidablePred (P d)]
    (di dj : Point) : Decidable (NegEntails P di dj) :=
  inferInstanceAs (Decidable (∀ s, _ → _))

/-! ### The *let alone* construction (§2.1–2.4) -/

/-- The *let alone* construction: form F ⟨X A Y let alone B⟩ (ex. 20a,
p. 512), where F is a negative polarity operator, X and Y are shared
non-focused material, and the paired foci A and B are points in a
presupposed scalar model. The typed form is the paired-foci core,
eliding the shared X/Y material. -/
def letAloneConstruction : Construction Unit :=
  { name := "let alone"
  , form :=
      [ { filler := .open_ .NOUN }
      , { filler := .fixed "let" }
      , { filler := .fixed "alone" }
      , { filler := .open_ .NOUN } ]
  , meaning := ()
  , pragmaticPoint := true }

/-- *Let alone* is not fully compositional: a formal idiom with paired
focus, scalar entailment, and NPI licensing requirements that cannot be
derived from the universal combination schemata (see
`isFullyCompositional`). -/
theorem let_alone_irreducible :
    isFullyCompositional letAloneConstruction = false := rfl

/-- *Let alone* "must ... be given treatment as the kind of formal idiom
or special construction we have been discussing" (§2.1): the paired focus
slots A and B are open. -/
theorem let_alone_formal_idiom : letAloneConstruction.IsFormalIdiom := rfl

/-- Felicity conditions on *let alone* sentences (p. 528): (1) the two
clauses express propositions from the same scalar model; (2) the
propositions are of the same polarity; (3) the proposition expressed by
the initial, full clause is the stronger one.

The propositions include the polarity operator F, so condition (3) runs
through definition A4 in the negative case: in "he didn't make colonel,
let alone general" (ex. 21), ¬P(colonel) is stronger than ¬P(general)
because colonel is the *lower* point. The paper itself flags the potential
confusion between point-strength and clause-strength here (p. 532). -/
structure LetAloneConditions (Point S : Type*) where
  /-- The presupposed scalar model's propositional function -/
  P : Point → S → Prop
  /-- Argument point for the A focus (in the initial, full clause) -/
  focusA : Point
  /-- Argument point for the B focus (in the reduced clause) -/
  focusB : Point
  /-- Condition (2): shared polarity of the two clauses -/
  polarity : Polarity
  /-- Condition (3): the full clause expresses the stronger proposition —
      via A4 under negation, via A5's strict entailment directly under
      positive polarity (the attested positive cases, exx. 71–72,
      p. 519) -/
  fullClauseStronger :
    match polarity with
    | .negative => NegEntails P focusA focusB ∧ ¬ NegEntails P focusB focusA
    | .positive => P focusA < P focusB

/-- The *let alone* family (p. 533): conjunctions presupposing a scalar
model relating their conjuncts. "*Let alone*, together with *much less*
and *not to mention*, presents the stronger statement first"; *in fact*
and *if not* present it second. -/
inductive LetAloneFamily where
  /-- "He didn't make colonel, let alone general." -/
  | letAlone
  | muchLess
  | notToMention
  /-- "She didn't eat a BITE, never mind a WHOLE MEAL" (ex. 49). -/
  | neverMind
  /-- "I believe he made colonel, if not general" (ex. 132). -/
  | ifNot
  /-- Presents the stronger point second (ex. 131). -/
  | inFact
  deriving DecidableEq, Repr

/-- Clause ordering within the family (p. 533). The paper's explicit
stronger-first list is *let alone*, *much less*, *not to mention*; the
value for *never mind* is an inference from ex. 49, not stated there. -/
def presentsStrongerFirst : LetAloneFamily → Bool
  | .letAlone     => true
  | .muchLess     => true
  | .notToMention => true
  | .neverMind    => true
  | .ifNot        => false
  | .inFact       => false

/-- Environments licensing *let alone* (exx. 62–70, p. 518). The paper
names five types — "simple negation, *too* complementation, comparison of
inequality, *only* as determiner of the subject, and various minimal
attainment qualifiers, these and more" — over nine examples; the last
three cases are formalizer labels for the remaining illustrated
environments. -/
inductive LetAloneNPITrigger where
  /-- Ex. 62: "He didn't reach Denver, let alone Chicago." -/
  | simpleNegation
  /-- Ex. 63: "I'm too tired to get up, let alone go running with you." -/
  | tooComplementation
  /-- Ex. 64. -/
  | comparisonOfInequality
  /-- Ex. 65: "Only a linguist would BUY that book, let alone READ it." -/
  | onlyDeterminer
  /-- Ex. 66: "I barely got up in time for lunch, let alone breakfast." -/
  | minimalAttainment
  /-- Ex. 68. -/
  | conditionalSurprise
  /-- Ex. 69: "failed to reach the sixth GRADE … get a B.A.". -/
  | failureVerb
  /-- Ex. 70: "Anyone who'd been to HIGH SCHOOL, let alone GRADUATE
  students in MATH, should be able to solve that problem." -/
  | anyoneWhod
  deriving DecidableEq, Repr

open Polarity in
/-- Map the *let alone* licensing environments to the licensing contexts
catalogued in `Polarity`. -/
def npiTriggerToContext : LetAloneNPITrigger → LicensingContext
  | .simpleNegation         => .negation
  | .tooComplementation     => .tooTo
  | .comparisonOfInequality => .clausalComparative
  | .onlyDeterminer         => .onlyFocus
  | .minimalAttainment      => .negation              -- "barely" ≈ negation
  | .conditionalSurprise    => .conditionalAntecedent
  | .failureVerb            => .negation              -- "fail" ≈ implicit negation
  | .anyoneWhod             => .universalRestrictor

/-- The garden-variety coordination construction *let alone* is measured
against (§2.2.1): two like-category conjuncts joined by a coordinating
conjunction. Present as the parent node of the inheritance link below. -/
def coordinationConstruction : Construction Unit :=
  { name := "Coordinating conjunction"
  , form :=
      [ { filler := .phrasal }
      , { filler := .open_ .CCONJ }
      , { filler := .phrasal } ]
  , meaning := () }

/-- *Let alone* against the coordination diagnostics of §2.2.1 (p. 514–517).
Shared with coordinating conjunctions: joins like categories, right node
raising, gapping. Overridden: no VP ellipsis (exx. 39–41), no IT-clefting
of the full constituent (exx. 33–34), fragment second conjunct, scalar
requirement, NPI status. The inheritance-link framing is retrospective —
the 1988 paper predates Goldberg's link typology. -/
def letAloneInheritance : InheritanceLink :=
  { parent := "Coordinating conjunction"
  , child := "let alone"
  , mode := .normal
  , sharedProperties :=
      [ "joins like categories"
      , "permits right node raising"
      , "permits gapping" ]
  , overriddenProperties :=
      [ "does not permit VP ellipsis"
      , "does not permit IT-clefting of full constituent"
      , "second conjunct is a sentence fragment, not full clause"
      , "requires scalar relationship between conjuncts"
      , "is a negative polarity item" ] }

/-- The §2.2.1 comparison as a two-node network. -/
def letAloneNetwork : Constructicon Unit :=
  { constructions := [coordinationConstruction, letAloneConstruction]
  , links := [letAloneInheritance] }

/-- The link resolves: no dangling parent. -/
theorem letAloneNetwork_wellFormed : letAloneNetwork.WellFormed := by decide

/-! ### Other constructions of §1 -/

/-- The X-er the Y-er comparative correlative (exx. 1–2, introduced in
§1.1.3 as the flagship formal idiom). The construction's "the" is "not, so
far as we can tell, found generally elsewhere in the language" (p. 507;
fn. 4 notes relatives like "all the more reason" and the Old English
instrumental demonstrative source). -/
def comparativeCorrelative : Construction Unit :=
  { name := "the X-er the Y-er"
  , form :=
      [ { filler := .fixed "the" }
      , { filler := .open_ .ADJ }
      , { filler := .phrasal, level := some .phrase }
      , { filler := .fixed "the" }
      , { filler := .open_ .ADJ }
      , { filler := .phrasal, level := some .phrase } ]
  , meaning := () }

/-- The Incredulity Response construction ("Him be a doctor?", ex. 14h in
the §2 opening list, pp. 510–511; the type is introduced in §1.1.4): a
non-nominative subject with a bare-stem predicate, "used to challenge or
question a proposition just posed by an interlocutor" (p. 511). -/
def incredulityResponse : Construction Unit :=
  { name := "Incredulity Response"
  , form :=
      [ { filler := .open_ .PRON, gf := some .subj }
      , { filler := .phrasal, level := some .phrase
        , gf := some .pred } ]
  , meaning := ()
  , pragmaticPoint := true }

/-! ### A one-dimensional rank model (ex. 21)

Ex. 21 (p. 513): "I doubt he made COLONEL in World War II, let alone
GENERAL." The paper names only second lieutenant ("the lowest commissioned
rank"), colonel, and general; the intermediate ranks are world-knowledge
interpolation. States are the down-sets of the rank chain, so the model
separates every pair of ranks and satisfies full A3 — at the cost of being
one-dimensional, which definition A1 (n > 1) disallows for genuine scalar
models; see the module docstring. -/

/-- Commissioned military ranks (ex. 21's scale; intermediate members
interpolated). -/
inductive Rank where
  | secondLieutenant | lieutenant | captain | major
  | colonel | general
  deriving DecidableEq, Repr, Fintype

/-- Position of a rank on the scale. -/
def Rank.idx : Rank → Nat
  | .secondLieutenant => 0
  | .lieutenant => 1
  | .captain => 2
  | .major => 3
  | .colonel => 4
  | .general => 5

instance : LinearOrder Rank := .lift' Rank.idx (by decide)

/-- Career outcomes: the down-sets of the rank chain — either no
commission, or every rank up to some ceiling. -/
inductive AchievementState where
  | achievedNone
  | achievedUpTo (ceiling : Rank)
  deriving DecidableEq, Repr, Fintype

/-- "He made rank r": the career reached at least r. -/
def MadeRank (r : Rank) : AchievementState → Prop
  | .achievedNone => False
  | .achievedUpTo c => r ≤ c

instance (r : Rank) : DecidablePred (MadeRank r) := fun s =>
  match s with
  | .achievedNone => inferInstanceAs (Decidable False)
  | .achievedUpTo c => inferInstanceAs (Decidable (r ≤ c))

/-- The rank model satisfies full definition A3: for distinct ranks,
entailment holds exactly when the entailed point is lower. The down-set
state space is what makes the biconditional (not just its forward half)
go through. -/
theorem rank_model_satisfiesA3 : IsScalarModel MadeRank := by decide

/-- "He made general" entails "he made colonel" (A3, forward). -/
theorem general_entails_colonel :
    MadeRank .general ≤ MadeRank .colonel := by decide

/-- "He made colonel" does not entail "he made general" (A3, converse
direction for the higher point). -/
theorem colonel_does_not_entail_general :
    ¬ MadeRank .colonel ≤ MadeRank .general := by decide

/-- Making general is the stronger *positive* proposition (A5's strict
entailment). NB the paper's warning (p. 532): in ex. 21 the clauses are
negated, so the stronger *clause* is "didn't make colonel" — see
`ex21Conditions`. -/
theorem general_stronger_than_colonel :
    MadeRank .general < MadeRank .colonel := by decide

/-- The felicity conditions of p. 528, instantiated for ex. 21
"I doubt he made COLONEL, let alone GENERAL": negative polarity, A focus
*colonel*, B focus *general*; the full clause ¬P(colonel) is stronger by
definition A4 because colonel is the lower point. -/
def ex21Conditions : LetAloneConditions Rank AchievementState :=
  { P := MadeRank
  , focusA := .colonel
  , focusB := .general
  , polarity := .negative
  , fullClauseStronger := by
      show NegEntails MadeRank .colonel .general ∧
        ¬ NegEntails MadeRank .general .colonel
      decide }

/-- Second lieutenant is the lowest point: no rank is lower. This is the
paper's explanation (p. 526) of ex. 107's anomaly — with B the lowest
point, the a-fortiori inference has nothing to conclude. -/
theorem secondLieutenant_is_lowest :
    ∀ r : Rank, ¬ r < .secondLieutenant := by decide

/-! ### The linguists × languages model (§2.3.2, Tables 1–2)

The paper's own 2D example (pp. 526–527; Appendix Tables 3–4, p. 535):
four professors ordered by erudition, four languages ordered by
accessibility, and the propositional function "X can read L". -/

/-- Linguists ordered by erudition, most erudite lowest (definition A2's
worked example, p. 537): "Apotheosis reads English" is the easiest
proposition to satisfy. -/
inductive Linguist where
  | apotheosis | brilliant | competent | dimm
  deriving DecidableEq, Repr, Fintype

/-- Position on the erudition scale. -/
def Linguist.idx : Linguist → Nat
  | .apotheosis => 0
  | .brilliant => 1
  | .competent => 2
  | .dimm => 3

instance : LinearOrder Linguist := .lift' Linguist.idx (by decide)

/-- Languages ordered by accessibility, most accessible lowest. -/
inductive Lang where
  | english | french | greek | hittite
  deriving DecidableEq, Repr, Fintype

/-- Position on the accessibility scale. -/
def Lang.idx : Lang → Nat
  | .english => 0
  | .french => 1
  | .greek => 2
  | .hittite => 3

instance : LinearOrder Lang := .lift' Lang.idx (by decide)

/-- States of who-reads-what. Every state assigns each professor an
initial segment of the accessibility scale (`threshold`). -/
inductive LLState where
  /-- Table 2a (p. 527): nobody reads anything. -/
  | allFalse
  /-- Table 2b: only Apotheosis reads English. -/
  | topLeft
  /-- Table 2c: Apotheosis reads English and French, Brilliant English. -/
  | twoTrue
  /-- Table 2d: everybody reads everything. -/
  | allTrue
  /-- A constructed staircase state (not in the paper), included to
  refute converse entailments. -/
  | diagonal
  deriving DecidableEq, Repr, Fintype

/-- How many languages, in accessibility order, each professor reads in
a state. -/
def LLState.threshold : LLState → Linguist → Nat
  | .allFalse, _ => 0
  | .topLeft, .apotheosis => 1
  | .topLeft, _ => 0
  | .twoTrue, .apotheosis => 2
  | .twoTrue, .brilliant => 1
  | .twoTrue, _ => 0
  | .allTrue, _ => 4
  | .diagonal, .apotheosis => 4
  | .diagonal, .brilliant => 3
  | .diagonal, .competent => 2
  | .diagonal, .dimm => 1

/-- "Professor X can read language L" in a state: L falls within X's
initial segment of the accessibility scale. -/
def CanRead (p : Linguist × Lang) (s : LLState) : Prop :=
  p.2.idx < s.threshold p.1

instance (p : Linguist × Lang) : DecidablePred (CanRead p) := fun _ =>
  inferInstanceAs (Decidable (_ < _))

instance : DecidableLE (Linguist × Lang) := fun _ _ =>
  inferInstanceAs (Decidable (_ ∧ _))

instance : DecidableLT (Linguist × Lang) := fun _ _ =>
  inferInstanceAs (Decidable (_ ∧ _))

/-- The 2D model satisfies the forward half of A3 over the five states:
lower points' propositions are entailed. -/
theorem ll_model_satisfiesA3Forward :
    ∀ di dj : Linguist × Lang, di < dj → CanRead dj ≤ CanRead di := by
  decide

/-- The five-state space is too sparse for full A3: incomparable points
end up with artifact entailments (e.g. "Brilliant reads Hittite" entails
"Competent reads French" over these states, though the points are
incomparable), violating A3's only-if direction. A genuine model of the
paper's Table 2 universe would need the full space of nested states. -/
theorem ll_sparse_fails_A3 : ¬ IsScalarModel CanRead := by decide

/-- "Brilliant can read Hittite" entails "Brilliant can read English":
Hittite is less accessible, so reading it is the stronger claim. -/
theorem brilliant_hittite_entails_english :
    CanRead (.brilliant, .hittite) ≤ CanRead (.brilliant, .english) := by
  decide

/-- The paper's worked example (p. 537): (Brilliant, English) is lower
than (Brilliant, Greek). -/
theorem brilliant_english_lower_than_brilliant_greek :
    ((.brilliant, .english) : Linguist × Lang) < (.brilliant, .greek) := by
  decide

/-- (Competent, French) and (Brilliant, Hittite) are incomparable
(definition A2): Competent > Brilliant on erudition but French < Hittite
on accessibility. -/
theorem competent_french_incomparable_brilliant_hittite :
    ¬ ((.competent, .french) : Linguist × Lang) < (.brilliant, .hittite) ∧
    ¬ ((.brilliant, .hittite) : Linguist × Lang) < (.competent, .french) := by
  decide

/-! ### Judgment data

The paper's judgment data — basic *let alone* (exx. 15–16), NPI licensing
and the *barely*/*almost*/*only* contrast (exx. 62–66, 113–115),
constituency probes (topicalization, VP ellipsis, wh-extraction,
IT-clefting; exx. 31–34, 39–41), scalar anomalies (exx. 104, 106–107,
121–122), and the attested positive-polarity cases (exx. 71–72) — live in
the generated module `Data.Examples.FillmoreKayOConnor1988`
(`Examples.all`, `Examples.ex113`, ...), sourced from
`Linglib/Data/Examples/FillmoreKayOConnor1988.json`. -/

/-- The positive-polarity examples (exx. 71–72) are judged acceptable —
the attested cases `LetAloneConditions.polarity := .positive` covers,
challenging a purely syntactic NPI account. -/
theorem positive_polarity_attested :
    (Examples.ex71.judgment, Examples.ex72.judgment)
      = (.acceptable, .acceptable) := by decide

/-- The *barely*/*almost*/*only* minimal triple (exx. 113–115): *barely*
licenses *let alone*; *almost* and non-subject *only* do not. -/
theorem barely_almost_only_contrast :
    Examples.ex115.judgment = .acceptable ∧
    Examples.ex113.judgment = .ungrammatical ∧
    Examples.ex114.judgment = .ungrammatical := by decide

end FillmoreKayOConnor1988
