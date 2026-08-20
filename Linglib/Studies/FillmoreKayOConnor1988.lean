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

- `FillmoreKayOConnor1988.ScalarModel`: argument points, `entails`,
  `strongerThan` (A5), `negEntails` (A4), `satisfiesA3`
- `FillmoreKayOConnor1988.letAloneConstruction`, `LetAloneConditions`,
  `ex21Conditions`: the construction, its felicity conditions (p. 528),
  and their instantiation for ex. 21
- `FillmoreKayOConnor1988.let_alone_irreducible`: *let alone* is not fully
  compositional
- `FillmoreKayOConnor1988.rankScalarModel`, `linguistLangModel`: worked
  scalar models
- `Data.Examples.FillmoreKayOConnor1988`: the paper's judgment data
  (generated module; `Examples.all`)
-/

namespace FillmoreKayOConnor1988

open ConstructionGrammar
open Features (Polarity)

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
