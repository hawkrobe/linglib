import Linglib.Syntax.ConstructionGrammar.ArgumentStructure
import Linglib.Syntax.ConstructionGrammar.Inheritance
import Linglib.Features.Acceptability
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
`ConstructionGrammar.IdiomTypology`.

The paper's scalar models are n-dimensional with n > 1 (definition A1;
fn. 16: "a scalar model must contain at least two dimensions"). The
military-rank model below is a deliberate one-dimensional simplification
of the paper's colonel/general example, not a paper-licit scalar model;
the linguists × languages model is the paper's own 2D example.

## Main declarations

- `FillmoreKayOConnor1988.ScalarModel`: argument points, `entails`,
  `strongerThan` (A5), `negEntails` (A4), `satisfiesA3`
- `FillmoreKayOConnor1988.letAloneConstruction`, `LetAloneConditions`,
  `ex21Conditions`: the construction, its felicity conditions (p. 528),
  and their instantiation for ex. 21
- `FillmoreKayOConnor1988.let_alone_irreducible`: *let alone* is not fully
  compositional
- `FillmoreKayOConnor1988.rankScalarModel`, `linguistLangModel`: worked
  scalar models
- `FillmoreKayOConnor1988.allExamples`: the paper's judgment data
-/

namespace FillmoreKayOConnor1988

open ConstructionGrammar
open Features (Acceptability Polarity)

/-! ### Scalar models (§2.3.2, Appendix)

The formal backbone of the paper: an n-dimensional argument space with a
monotonicity constraint on propositional functions. Definition A3 (p. 536):
⟨S, T, Dˣ, P⟩ is a scalar model iff, for distinct dᵢ, dⱼ in Dˣ, P(dⱼ)
entails P(dᵢ) just in case dᵢ is lower than dⱼ. -/

/-- An argument point in the n-dimensional argument space Dˣ. In the
paper's 2D example, (Brilliant, English) is an argument point in the
linguists × languages space. -/
structure ArgumentPoint (α : Type*) where
  /-- Coordinates, one per dimension -/
  coordinates : List α
  deriving DecidableEq, Repr

/-- dᵢ is LOWER than dⱼ (definition A2, p. 536): no coordinate of dᵢ has a
higher value than the corresponding coordinate of dⱼ, and at least one
coordinate is strictly lower. -/
def ArgumentPoint.isLower {α : Type*} (le : α → α → Bool)
    (di dj : ArgumentPoint α) : Bool :=
  (di.coordinates.zip dj.coordinates).all (λ ⟨a, b⟩ => le a b) &&
  (di.coordinates.zip dj.coordinates).any (λ ⟨a, b⟩ => le a b && !(le b a))

/-- A scalar model candidate: argument points, a propositional function,
and a per-dimension ordering. Definition A3's monotonicity constraint is
checked by `satisfiesA3` rather than carried as a field, so that
deliberately defective models can be discussed. -/
structure ScalarModel (S : Type*) (α : Type*) where
  /-- Argument points (elements of Dˣ) -/
  points : List (ArgumentPoint α)
  /-- Propositional function: argument point → proposition over states -/
  propFn : ArgumentPoint α → S → Bool
  /-- Ordering on individual dimension values -/
  dimLe : α → α → Bool

/-- Scalar entailment: P(dⱼ) entails P(dᵢ) iff every state verifying P(dⱼ)
verifies P(dᵢ). -/
def ScalarModel.entails {S α : Type*} (sm : ScalarModel S α)
    (dj di : ArgumentPoint α) : Prop :=
  ∀ s, sm.propFn dj s = true → sm.propFn di s = true

instance {S α : Type*} [Fintype S] (sm : ScalarModel S α)
    (dj di : ArgumentPoint α) : Decidable (sm.entails dj di) :=
  inferInstanceAs (Decidable (∀ _s, _ = true → _ = true))

/-- Informativeness/strength (definition A5, p. 537): p is MORE INFORMATIVE
(STRONGER) than q relative to a scalar model iff p entails q and q does not
entail p. -/
def ScalarModel.strongerThan {S α : Type*} (sm : ScalarModel S α)
    (dj di : ArgumentPoint α) : Prop :=
  sm.entails dj di ∧ ¬sm.entails di dj

instance {S α : Type*} [Fintype S] (sm : ScalarModel S α)
    (dj di : ArgumentPoint α) : Decidable (sm.strongerThan dj di) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Negative scalar entailment (definition A4, p. 536): ¬P(dᵢ) entails
¬P(dⱼ) just in case dᵢ is lower than dⱼ. This is the direction at work in
the canonical negative *let alone* sentences: "he didn't make colonel; a
fortiori, he didn't make general" (p. 523). -/
def ScalarModel.negEntails {S α : Type*} (sm : ScalarModel S α)
    (di dj : ArgumentPoint α) : Prop :=
  ∀ s, sm.propFn di s = false → sm.propFn dj s = false

instance {S α : Type*} [Fintype S] (sm : ScalarModel S α)
    (di dj : ArgumentPoint α) : Decidable (sm.negEntails di dj) :=
  inferInstanceAs (Decidable (∀ _s, _ = false → _ = false))

/-- A5 strength for negated propositions: ¬P(dᵢ) is stronger than ¬P(dⱼ)
iff it entails and is not entailed by it. -/
def ScalarModel.negStrongerThan {S α : Type*} (sm : ScalarModel S α)
    (di dj : ArgumentPoint α) : Prop :=
  sm.negEntails di dj ∧ ¬sm.negEntails dj di

instance {S α : Type*} [Fintype S] (sm : ScalarModel S α)
    (di dj : ArgumentPoint α) : Decidable (sm.negStrongerThan di dj) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Forward half of definition A3 over a finite state list: whenever dᵢ is
lower than dⱼ, P(dⱼ) entails P(dᵢ). -/
def ScalarModel.satisfiesA3Forward {S α : Type*}
    (sm : ScalarModel S α) (states : List S) : Bool :=
  sm.points.all λ di =>
    sm.points.all λ dj =>
      if di.isLower sm.dimLe dj then
        states.all λ s => !(sm.propFn dj s) || sm.propFn di s
      else true

/-- Full definition A3 over a finite state list: for *distinct* dᵢ, dⱼ,
P(dⱼ) entails P(dᵢ) **just in case** dᵢ is lower than dⱼ. The biconditional
is demanding: a state list too sparse to separate the points produces
artifact entailments between incomparable points and fails this check (see
`ll_sparse_fails_A3`). -/
def ScalarModel.satisfiesA3 {S α : Type*} [DecidableEq α]
    (sm : ScalarModel S α) (states : List S) : Bool :=
  sm.points.all λ di =>
    sm.points.all λ dj =>
      if di = dj then true
      else (states.all λ s => !(sm.propFn dj s) || sm.propFn di s)
             == di.isLower sm.dimLe dj

/-! ### The *let alone* construction (§2.1–2.4) -/

/-- The *let alone* construction: form F ⟨X A Y let alone B⟩ (ex. 20a,
p. 512), where F is a negative polarity operator, X and Y are shared
non-focused material, and the paired foci A and B are points in a
presupposed scalar model. The typed form is the paired-foci core
([dunn-2025]'s slot projection), eliding the shared X/Y material. -/
def letAloneConstruction : Construction :=
  { name := "let alone"
  , form :=
      [ { filler := .open_ .NOUN, role := some "focusA" }
      , { filler := .fixed "let" }
      , { filler := .fixed "alone" }
      , { filler := .open_ .NOUN, role := some "focusB" } ]
  , meaning := "F'⟨X A Y⟩; a fortiori F'⟨X B Y⟩ (scalar entailment)"
  , pragmaticFunction := "presupposes scalar model; A clause = informative (Quantity), B clause = relevant (Relevance)" }

/-- *Let alone* is not fully compositional: a formal idiom with paired
focus, scalar entailment, and NPI licensing requirements that cannot be
derived from the universal combination schemata (see
`isFullyCompositional`). -/
theorem let_alone_irreducible :
    isFullyCompositional letAloneConstruction = false := rfl

/-- Felicity conditions on *let alone* sentences (p. 528): (1) the two
clauses express propositions from the same scalar model; (2) the
propositions are of the same polarity; (3) the proposition expressed by
the initial, full clause is the stronger one.

The propositions include the polarity operator F, so condition (3) runs
through definition A4 in the negative case: in "he didn't make colonel,
let alone general" (ex. 21), ¬P(colonel) is stronger than ¬P(general)
because colonel is the *lower* point. The paper itself flags the potential
confusion between point-strength and clause-strength here (p. 532). -/
structure LetAloneConditions (S α : Type*) where
  /-- The presupposed scalar model -/
  scalarModel : ScalarModel S α
  /-- Argument point for the A focus (in the initial, full clause) -/
  focusA : ArgumentPoint α
  /-- Argument point for the B focus (in the reduced clause) -/
  focusB : ArgumentPoint α
  /-- Condition (2): shared polarity of the two clauses -/
  polarity : Polarity
  /-- Condition (3): the full clause expresses the stronger proposition —
      via A4 under negation, via A5 directly under positive polarity
      (the attested positive cases, exx. 71–72, p. 519) -/
  fullClauseStronger :
    match polarity with
    | .negative => scalarModel.negStrongerThan focusA focusB
    | .positive => scalarModel.strongerThan focusA focusB

/-- The *let alone* family (p. 533): conjunctions presupposing a scalar
model relating their conjuncts. "*Let alone*, together with *much less*
and *not to mention*, presents the stronger statement first"; *in fact*
and *if not* present it second. -/
inductive LetAloneFamily where
  | letAlone      -- "He didn't make colonel, let alone general"
  | muchLess      -- stronger first
  | notToMention  -- stronger first
  | neverMind     -- "She didn't eat a BITE, never mind a WHOLE MEAL" (ex. 49)
  | ifNot         -- "I believe he made colonel, if not general" (ex. 132)
  | inFact        -- stronger point second (ex. 131)
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
  | simpleNegation        -- ex. 62: "He didn't reach Denver, let alone Chicago"
  | tooComplementation    -- ex. 63: "I'm too tired to get up, let alone go running (with you)"
  | comparisonOfInequality -- ex. 64
  | onlyDeterminer        -- ex. 65: "Only a linguist would BUY that book, let alone READ it"
  | minimalAttainment     -- ex. 66: "I barely got up in time for lunch, let alone breakfast"
  | conditionalSurprise   -- ex. 68
  | failureVerb           -- ex. 69: "failed to reach the sixth GRADE … get a B.A."
  | anyoneWhod            -- ex. 70: "Anyone who'd been to HIGH SCHOOL, let alone GRADUATE students in MATH, should be able to solve that problem"
  deriving DecidableEq, Repr

open Semantics.Polarity in
/-- Map the *let alone* licensing environments to the licensing contexts
catalogued in `Semantics.Polarity`. -/
def npiTriggerToContext : LetAloneNPITrigger → LicensingContext
  | .simpleNegation         => .negation
  | .tooComplementation     => .tooTo
  | .comparisonOfInequality => .comparativeS
  | .onlyDeterminer         => .onlyFocus
  | .minimalAttainment      => .negation              -- "barely" ≈ negation
  | .conditionalSurprise    => .conditionalAntecedent
  | .failureVerb            => .negation              -- "fail" ≈ implicit negation
  | .anyoneWhod             => .universalRestrictor

/-- The garden-variety coordination construction *let alone* is measured
against (§2.2.1): two like-category conjuncts joined by a coordinating
conjunction. Present as the parent node of the inheritance link below. -/
def coordinationConstruction : Construction :=
  { name := "Coordinating conjunction"
  , form :=
      [ { filler := .phrasal, role := some "conjunct₁" }
      , { filler := .open_ .CCONJ }
      , { filler := .phrasal, role := some "conjunct₂" } ]
  , meaning := "joins two like-category constituents" }

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
def letAloneNetwork : Constructicon :=
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
def comparativeCorrelative : Construction :=
  { name := "the X-er the Y-er"
  , form :=
      [ { filler := .fixed "the" }
      , { filler := .open_ .ADJ, role := some "comparative₁" }
      , { filler := .phrasal, role := some "clause₁", level := some .phrase }
      , { filler := .fixed "the" }
      , { filler := .open_ .ADJ, role := some "comparative₂" }
      , { filler := .phrasal, role := some "clause₂", level := some .phrase } ]
  , meaning := "The degree to which X correlates with the degree to which Y"
  , pragmaticFunction := none }

/-- The Incredulity Response construction ("Him be a doctor?", ex. 14h in
the §2 opening list, pp. 510–511; the type is introduced in §1.1.4): a
non-nominative subject with a bare-stem predicate, "used to challenge or
question a proposition just posed by an interlocutor" (p. 511). -/
def incredulityResponse : Construction :=
  { name := "Incredulity Response"
  , form :=
      [ { filler := .open_ .PRON, role := some "subject", gf := some .subj }
      , { filler := .phrasal, role := some "predicate", level := some .phrase
        , gf := some .pred } ]
  , meaning := "Speaker challenges the just-posed proposition as incredible"
  , pragmaticFunction := "challenges or questions a proposition just posed by an interlocutor" }

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

/-- Rank ordering. -/
def rankLe (a b : Rank) : Bool := a.idx ≤ b.idx

/-- Career outcomes: the down-sets of the rank chain — either no
commission, or every rank up to some ceiling. -/
inductive AchievementState where
  | achievedNone
  | achievedUpTo (ceiling : Rank)
  deriving DecidableEq, Repr, Fintype

/-- "He made rank r" holds iff the career reached at least r. -/
def madeRank (r : Rank) : AchievementState → Bool
  | .achievedNone => false
  | .achievedUpTo c => rankLe r c

/-- All career outcomes. -/
def rankStates : List AchievementState :=
  [ .achievedNone
  , .achievedUpTo .secondLieutenant, .achievedUpTo .lieutenant
  , .achievedUpTo .captain, .achievedUpTo .major
  , .achievedUpTo .colonel, .achievedUpTo .general ]

/-- The military rank scalar model. -/
def rankScalarModel : ScalarModel AchievementState Rank :=
  { points := [⟨[.secondLieutenant]⟩, ⟨[.lieutenant]⟩, ⟨[.captain]⟩,
               ⟨[.major]⟩, ⟨[.colonel]⟩, ⟨[.general]⟩]
  , propFn := λ pt => match pt.coordinates.head? with
      | some r => madeRank r
      | none => λ _ => false
  , dimLe := rankLe }

/-- The rank model satisfies full definition A3: for distinct ranks,
entailment holds exactly when the entailed point is lower. The down-set
state space is what makes the biconditional (not just its forward half)
go through. -/
theorem rank_model_satisfiesA3 :
    rankScalarModel.satisfiesA3 rankStates = true := by decide

/-- "He made general" entails "he made colonel" (A3, forward). -/
theorem general_entails_colonel :
    rankScalarModel.entails ⟨[.general]⟩ ⟨[.colonel]⟩ := by decide

/-- "He made colonel" does not entail "he made general" (A3, converse
direction for the higher point). -/
theorem colonel_does_not_entail_general :
    ¬ rankScalarModel.entails ⟨[.colonel]⟩ ⟨[.general]⟩ := by decide

/-- Making general is the stronger *positive* proposition (A5). NB the
paper's warning (p. 532): in ex. 21 the clauses are negated, so the
stronger *clause* is "didn't make colonel" — see `ex21Conditions`. -/
theorem general_stronger_than_colonel :
    rankScalarModel.strongerThan ⟨[.general]⟩ ⟨[.colonel]⟩ := by
  exact ⟨general_entails_colonel, colonel_does_not_entail_general⟩

/-- The felicity conditions of p. 528, instantiated for ex. 21
"I doubt he made COLONEL, let alone GENERAL": negative polarity, A focus
*colonel*, B focus *general*; the full clause ¬P(colonel) is stronger by
definition A4 because colonel is the lower point. -/
def ex21Conditions : LetAloneConditions AchievementState Rank :=
  { scalarModel := rankScalarModel
  , focusA := ⟨[.colonel]⟩
  , focusB := ⟨[.general]⟩
  , polarity := .negative
  , fullClauseStronger := by
      show rankScalarModel.negStrongerThan ⟨[.colonel]⟩ ⟨[.general]⟩
      decide }

/-- Second lieutenant is the lowest point: no rank is lower. This is the
paper's explanation (p. 526) of ex. 107's anomaly — with B the lowest
point, the a-fortiori inference has nothing to conclude. -/
theorem secondLieutenant_is_lowest :
    ∀ pt ∈ rankScalarModel.points,
      ¬ pt.isLower rankLe ⟨[.secondLieutenant]⟩ = true := by decide

/-! ### The linguists × languages model (§2.3.2, Tables 1–2)

The paper's own 2D example (pp. 526–527; Appendix Tables 3–4, p. 535):
four professors ordered by erudition, four languages ordered by
accessibility, and the propositional function "X can read L". -/

/-- Linguists ordered by erudition (most → least). -/
inductive Linguist where
  | apotheosis | brilliant | competent | dimm
  deriving DecidableEq, Repr, Fintype

/-- Languages ordered by accessibility (most → least). -/
inductive Lang where
  | english | french | greek | hittite
  deriving DecidableEq, Repr, Fintype

/-- Dimension value: a linguist or a language. The argument space is
Linguist × Lang, encoded as 2-element coordinate lists. -/
inductive LingLangVal where
  | ling : Linguist → LingLangVal
  | lang : Lang → LingLangVal
  deriving DecidableEq, Repr

/-- Dimension ordering. A LOWER point yields a WEAKER proposition
(definition A2; worked example p. 537: "(B, E) is lower than (B, G)").
More erudite linguists and more accessible languages are lower: "Apotheosis
reads English" is the easiest proposition to satisfy. Cross-dimension
comparisons are false (dimensions are independent). -/
def lingLangLe : LingLangVal → LingLangVal → Bool
  | .ling .apotheosis, .ling _ => true
  | .ling .brilliant,  .ling .apotheosis => false
  | .ling .brilliant,  .ling _ => true
  | .ling .competent,  .ling .apotheosis => false
  | .ling .competent,  .ling .brilliant => false
  | .ling .competent,  .ling _ => true
  | .ling .dimm,       .ling .dimm => true
  | .ling .dimm,       .ling _ => false
  | .lang .english, .lang _ => true
  | .lang .french,  .lang .english => false
  | .lang .french,  .lang _ => true
  | .lang .greek,   .lang .english => false
  | .lang .greek,   .lang .french => false
  | .lang .greek,   .lang _ => true
  | .lang .hittite, .lang .hittite => true
  | .lang .hittite, .lang _ => false
  | .ling _, .lang _ => false
  | .lang _, .ling _ => false

/-- States of who-reads-what. The first four are Table 2's states a–d
(p. 527); `diagonal` is a constructed staircase state (not in the paper),
included to refute converse entailments. -/
inductive LLState where
  | allFalse    -- Table 2a: nobody reads anything
  | topLeft     -- Table 2b: only Apotheosis reads English
  | twoTrue     -- Table 2c: Apotheosis reads English & French, Brilliant reads English
  | allTrue     -- Table 2d: everybody reads everything
  | diagonal    -- constructed: Apotheosis reads all, Brilliant up to Greek, Competent up to French, Dimm only English
  deriving DecidableEq, Repr, Fintype

/-- "Professor X can read language L" in each state. -/
def canRead : Linguist → Lang → LLState → Bool
  | _, _, .allFalse => false
  | _, _, .allTrue  => true
  | .apotheosis, .english, .topLeft => true
  | _, _, .topLeft => false
  | .apotheosis, .english, .twoTrue => true
  | .apotheosis, .french, .twoTrue  => true
  | .brilliant, .english, .twoTrue  => true
  | _, _, .twoTrue => false
  | .apotheosis, _, .diagonal => true
  | .brilliant, .hittite, .diagonal => false
  | .brilliant, _, .diagonal => true
  | .competent, .english, .diagonal => true
  | .competent, .french, .diagonal  => true
  | .competent, _, .diagonal => false
  | .dimm, .english, .diagonal => true
  | .dimm, _, .diagonal => false

/-- Convenience constructor for 2D argument points. -/
def llPoint (l : Linguist) (lang : Lang) : ArgumentPoint LingLangVal :=
  ⟨[.ling l, .lang lang]⟩

/-- The linguists × languages scalar model. -/
def linguistLangModel : ScalarModel LLState LingLangVal :=
  { points := do
      let l ← [Linguist.apotheosis, .brilliant, .competent, .dimm]
      let lang ← [Lang.english, .french, .greek, .hittite]
      return llPoint l lang
  , propFn := λ pt =>
      match pt.coordinates with
      | [.ling l, .lang lang] => canRead l lang
      | _ => λ _ => false
  , dimLe := lingLangLe }

/-- All five states. -/
def llStates : List LLState :=
  [.allFalse, .topLeft, .twoTrue, .allTrue, .diagonal]

/-- The 2D model satisfies the forward half of A3 over the five states:
lower points' propositions are entailed. -/
theorem ll_model_satisfiesA3Forward :
    linguistLangModel.satisfiesA3Forward llStates = true := by decide

/-- The five-state list is too sparse for full A3: incomparable points end
up with artifact entailments (e.g. "Brilliant reads Hittite" entails
"Competent reads French" over these states, though the points are
incomparable), violating A3's only-if direction. A genuine model of the
paper's Table 2 universe would need the full space of nested states. -/
theorem ll_sparse_fails_A3 :
    linguistLangModel.satisfiesA3 llStates = false := by decide

/-- "Brilliant can read Hittite" entails "Brilliant can read English":
Hittite is less accessible, so reading it is the stronger claim. -/
theorem brilliant_hittite_entails_english :
    linguistLangModel.entails (llPoint .brilliant .hittite)
      (llPoint .brilliant .english) := by decide

/-- The paper's worked example (p. 537): (Brilliant, English) is lower
than (Brilliant, Greek). -/
theorem brilliant_english_lower_than_brilliant_greek :
    (llPoint .brilliant .english).isLower lingLangLe
      (llPoint .brilliant .greek) = true := by decide

/-- (Competent, French) and (Brilliant, Hittite) are incomparable
(definition A2): Competent > Brilliant on erudition but French < Hittite
on accessibility. -/
theorem competent_french_incomparable_brilliant_hittite :
    (llPoint .competent .french).isLower lingLangLe
      (llPoint .brilliant .hittite) = false ∧
    (llPoint .brilliant .hittite).isLower lingLangLe
      (llPoint .competent .french) = false := by decide

/-! ### Judgment data

Grammaticality judgments and contrasts from the paper, by example number.
Verified against the published text; judgments reproduce the paper's
markings (* ungrammatical, # anomalous, ? marginal). -/

/-- A single attested or judged example. -/
structure ExampleDatum where
  /-- Example number in the paper -/
  exNumber : String
  /-- The sentence -/
  sentence : String
  /-- Acceptability judgment -/
  judgment : Acceptability
  /-- What phenomenon this illustrates -/
  phenomenon : String
  deriving Repr, BEq

/-! #### Basic *let alone* (§2.1, exx. 15–16, p. 512) -/

def ex15b : ExampleDatum :=
  { exNumber := "15b"
  , sentence := "I barely got up in time to eat lunch, let alone cook breakfast"
  , judgment := .ok
  , phenomenon := "basic let alone with barely" }

def ex16b : ExampleDatum :=
  { exNumber := "16b"
  , sentence := "I doubt you could get Fred to eat shrimp, let alone Louise squid"
  , judgment := .ok
  , phenomenon := "let alone with multiple paired foci" }

/-! #### NPI licensing (§2.2.4, exx. 62–66, p. 518) -/

def ex62 : ExampleDatum :=
  { exNumber := "62"
  , sentence := "He didn't reach Denver, let alone Chicago"
  , judgment := .ok
  , phenomenon := "let alone licensed by simple negation" }

def ex63 : ExampleDatum :=
  { exNumber := "63"
  , sentence := "I'm too tired to get up, let alone go running with you"
  , judgment := .ok
  , phenomenon := "let alone licensed by too-complementation" }

def ex66 : ExampleDatum :=
  { exNumber := "66"
  , sentence := "I barely got up in time for lunch, let alone breakfast"
  , judgment := .ok
  , phenomenon := "let alone licensed by barely" }

/-! #### *Barely* vs. *almost*/*only* (§2.3.3, exx. 113–115, p. 529)

*Barely* licenses *let alone*; *almost* and non-subject *only* do not —
"*barely* is syntactically a negative polarity trigger while *almost* and
nonsubject *only* are not". -/

def ex113 : ExampleDatum :=
  { exNumber := "113"
  , sentence := "*He almost reached Denver let alone Chicago"
  , judgment := .unacceptable
  , phenomenon := "let alone NOT licensed by almost" }

def ex114 : ExampleDatum :=
  { exNumber := "114"
  , sentence := "*He only reached Denver let alone Chicago"
  , judgment := .unacceptable
  , phenomenon := "let alone NOT licensed by non-subject only" }

def ex115 : ExampleDatum :=
  { exNumber := "115"
  , sentence := "He barely reached Denver let alone Chicago"
  , judgment := .ok
  , phenomenon := "let alone licensed by barely (contrast with almost/only)" }

/-- NPI licensing contrasts: barely licenses, almost and only do not. -/
def npiContrasts : List ExampleDatum :=
  [ex113, ex114, ex115]

/-! #### Topicalization asymmetry (§2.2.1, exx. 31a–d, p. 515) -/

def ex31a : ExampleDatum :=
  { exNumber := "31a"
  , sentence := "Shrimp and squid Moishe won't eat"
  , judgment := .ok
  , phenomenon := "and-coordination permits topicalization" }

def ex31b : ExampleDatum :=
  { exNumber := "31b"
  , sentence := "*Shrimp let alone squid Moishe won't eat"
  , judgment := .unacceptable
  , phenomenon := "let alone blocks topicalization" }

def ex31c : ExampleDatum :=
  { exNumber := "31c"
  , sentence := "*Shrimp Moishe won't eat and squid"
  , judgment := .unacceptable
  , phenomenon := "and-coordination: can't split" }

def ex31d : ExampleDatum :=
  { exNumber := "31d"
  , sentence := "Shrimp Moishe won't eat, let alone squid"
  , judgment := .ok
  , phenomenon := "let alone permits parenthetical-like extraposition" }

/-- Topicalization asymmetry: *and* allows full topicalization,
*let alone* only allows extraposed second conjunct. -/
def topicalizationContrasts : List ExampleDatum :=
  [ex31a, ex31b, ex31d]

/-! #### VP ellipsis (§2.2.1, exx. 39–41, p. 516) -/

def ex39 : ExampleDatum :=
  { exNumber := "39"
  , sentence := "Max will eat shrimp more willingly than Minnie will"
  , judgment := .ok
  , phenomenon := "comparative permits VP ellipsis" }

def ex40 : ExampleDatum :=
  { exNumber := "40"
  , sentence := "Max won't eat shrimp but Minnie will"
  , judgment := .ok
  , phenomenon := "but-coordination permits VP ellipsis" }

def ex41 : ExampleDatum :=
  { exNumber := "41"
  , sentence := "*Max won't eat shrimp let alone Minnie will"
  , judgment := .unacceptable
  , phenomenon := "let alone blocks VP ellipsis" }

/-- VP ellipsis contrast: *and*/*but* allow it, *let alone* does not. -/
def vpEllipsisContrasts : List ExampleDatum :=
  [ex39, ex40, ex41]

/-! #### Wh-extraction (§2.2.1, exx. 32a–b, p. 515) -/

def ex32a : ExampleDatum :=
  { exNumber := "32a"
  , sentence := "*a man who Mary hasn't met or ridden in his car"
  , judgment := .unacceptable
  , phenomenon := "wh-extraction from and-coordination blocked" }

def ex32b : ExampleDatum :=
  { exNumber := "32b"
  , sentence := "?a man who Mary hasn't met, let alone ridden in his car"
  , judgment := .marginal
  , phenomenon := "wh-extraction from let alone is better" }

/-! #### Scalar anomaly (§2.3.2, exx. 104, 121–122, pp. 525, 530–531) -/

def ex104 : ExampleDatum :=
  { exNumber := "104"
  , sentence := "#Fred doesn't have an odd number of books, let alone seventy-five"
  , judgment := .anomalous
  , phenomenon := "scalar anomaly: odd-number doesn't form a scale with 75" }

def ex121 : ExampleDatum :=
  { exNumber := "121"
  , sentence := "You couldn't get a poor man to wash your car for $2, let alone a rich man to wax your truck for $1"
  , judgment := .ok
  , phenomenon := "multi-dimensional scalar model: four paired foci (ex. 120 adds a fifth dimension)" }

def ex122a : ExampleDatum :=
  { exNumber := "122a"
  , sentence := "#You couldn't get a rich man to wash your car for $2 let alone a poor man to wax your truck for $1"
  , judgment := .anomalous
  , phenomenon := "scalar anomaly: swapped foci on poor/rich dimension" }

def ex122b : ExampleDatum :=
  { exNumber := "122b"
  , sentence := "#You couldn't get a poor man to wax your car for $2 let alone a rich man to wash your truck for $1"
  , judgment := .anomalous
  , phenomenon := "scalar anomaly: swapped foci on wash/wax dimension" }

/-- Scalar anomaly contrasts: well-formed scalar ordering vs. swapped foci. -/
def scalarAnomalyContrasts : List ExampleDatum :=
  [ex121, ex122a, ex122b]

/-! #### IT-clefting (§2.2.1, exx. 33–34, pp. 515–516) -/

def ex33 : ExampleDatum :=
  { exNumber := "33"
  , sentence := "*It's shrimp let alone squid that Max won't eat"
  , judgment := .unacceptable
  , phenomenon := "IT-clefting blocked with let alone" }

def ex34 : ExampleDatum :=
  { exNumber := "34"
  , sentence := "It's shrimp and squid that Max won't eat"
  , judgment := .ok
  , phenomenon := "IT-clefting fine with and-coordination" }

/-! #### Lowest-point anomaly (§2.3.2, exx. 106–107, p. 526)

With B the lowest scale point, negating a non-lowest point yields no
a-fortiori conclusion about it (see `secondLieutenant_is_lowest`). -/

def ex106 : ExampleDatum :=
  { exNumber := "106"
  , sentence := "He wasn't even a commissioned officer, let alone a colonel"
  , judgment := .ok
  , phenomenon := "let alone with B higher on the scale" }

def ex107 : ExampleDatum :=
  { exNumber := "107"
  , sentence := "#He wasn't even a commissioned officer, let alone a second lieutenant"
  , judgment := .anomalous
  , phenomenon := "scalar anomaly: B is the lowest point on the scale" }

/-! #### Positive polarity (§2.2.4, exx. 71–72, p. 519)

Rare but attested; these challenge a purely syntactic NPI account and are
the cases `LetAloneConditions.polarity := .positive` covers. -/

def ex71 : ExampleDatum :=
  { exNumber := "71"
  , sentence := "You've got enough material there for a whole semester, let alone a week"
  , judgment := .ok
  , phenomenon := "let alone in positive polarity context (attested)" }

def ex72 : ExampleDatum :=
  { exNumber := "72"
  , sentence := "Penutian has been broken up, let alone Macro-Penutian"
  , judgment := .ok
  , phenomenon := "let alone in positive polarity context (attested)" }

/-- Positive polarity *let alone* examples challenge pure NPI analysis. -/
def positivePolarityExamples : List ExampleDatum :=
  [ex71, ex72]

/-- All judgment data from the paper. -/
def allExamples : List ExampleDatum :=
  [ ex15b, ex16b
  , ex62, ex63, ex66, ex113, ex114, ex115
  , ex31a, ex31b, ex31c, ex31d
  , ex39, ex40, ex41
  , ex32a, ex32b
  , ex104, ex121, ex122a, ex122b
  , ex33, ex34
  , ex106, ex107
  , ex71, ex72 ]

/-- All grammatical examples. -/
def grammaticalExamples : List ExampleDatum :=
  allExamples.filter (·.judgment == .ok)

/-- All ungrammatical examples. -/
def ungrammaticalExamples : List ExampleDatum :=
  allExamples.filter (·.judgment == .unacceptable)

/-- The data cover all four judgment types. -/
theorem has_all_judgment_types :
    (allExamples.any (·.judgment == .ok)) = true ∧
    (allExamples.any (·.judgment == .unacceptable)) = true ∧
    (allExamples.any (·.judgment == .marginal)) = true ∧
    (allExamples.any (·.judgment == .anomalous)) = true := by decide

end FillmoreKayOConnor1988
