import Linglib.Core.Semantics.CommonGround
import Linglib.Core.Discourse.IllocutionaryForce
import Linglib.Theories.Morphology.DM.Categorizer
import Linglib.Theories.Interfaces.SyntaxSemantics.Linking
import Linglib.Theories.Pragmatics.RSA.LexicalUncertainty
import Mathlib.Data.Fintype.BigOperators

/-!
# Clark 1983 — Making Sense of Nonce Sense
@cite{clark-1983} @cite{clark-clark-1979}

Clark, Herbert H. (1983). Making sense of nonce sense. In G.B. Flores d'Arcais
& R.J. Jarvella (Eds.), *The Process of Language Understanding*, pp. 297–331.
John Wiley & Sons.

## Core Argument

Traditional parsers assume the **sense-selection assumption**: each word has a
finite list of senses in the lexicon, and the parser selects among them. Clark
argues this assumption is untenable because **contextual expressions** — words
used with nonce senses — are ubiquitous in ordinary language. Their possible
senses are **non-denumerable**: no finite list can capture them.

Clark proposes replacing sense-selection with **sense-creation**: listeners
construct meanings on-the-fly by inferring the speaker's intentions from mutual
knowledge. The central proposal is the **intentional view of parsing** (p. 324):
parsing is not selecting sentence meanings from a finite list, but
reconstructing the speaker's **hierarchy of goals** — the plan that maps each
constituent of the utterance to a subgoal the speaker accomplishes by uttering
it.

The argument proceeds in three stages:
1. Demonstrating that contextual expressions are ubiquitous and non-denumerable
2. Showing that contextual expressions share five properties with indirect
   illocutionary acts (simultaneous meanings, logical priority, literalness,
   non-denumerability, contextuality)
3. Proposing that both are understood via the same mechanism: goal hierarchies

## File organization

The Lean file uses local section headers `§A`–`§L` for navigation; these
**do not correspond to numbered sections in the paper** (the paper uses
named, unnumbered sections). Page citations were verified against the PDF
on 2026-04-24; example attributions for the contextual-expression taxonomy
in `§B` were corrected at the same time.

## Substrate hookup

The `IndirectAct` structure in `§K` consumes `Core.Discourse.PreparatoryCondition`
(Searle's hierarchy: ability / knowledge / memory / perception / permission /
willingness). Clark's canonical example *Do you know what time it is?* used
as a request projects to `prepCondition := some .knowledge` — the same
substrate `Phenomena/Politeness/Studies/FrancikClark1985.lean` and
`Phenomena/Directives/Studies/RuytenbeekEtAl2017.lean` consume.

The DM bridge in `§I` consumes `Theories.Morphology.DM.Categorizer`'s
`Recategorization.denominal` for the syntactic operation underlying nonce
verbs. The LU-RSA bridge in `§H` consumes
`Theories.Pragmatics.RSA.LexicalUncertainty.Lexicon`.

The shared mechanism Clark posits in `§K` is operationalized as a typed
projection: both `IndirectAct` and `DenominalVerbConvention` provide a
`toGoalHierarchy` function landing in the common `GoalHierarchy` schema.
The "same mechanism" claim is then a structural identity at the substrate
level rather than a vacuous law-of-excluded-middle.
-/

namespace Clark1983

open Core.CommonGround
open Core.Discourse (PreparatoryCondition)
open Morphology.DM (Categorizer Recategorization CategorizedRoot
  denominal_requires_n recategorization_changes_category)

/-! ## §A. Sense and reference: fixed vs shifting (Table 9.1, p. 300) -/

/-- Whether an aspect of meaning is fixed across contexts or shifts. -/
inductive Alterability where
  | fixed
  | shifting
  deriving DecidableEq, Repr

/-- The two aspects of meaning that can independently be fixed or shifting. -/
inductive MeaningAspect where
  | sense
  | reference
  deriving DecidableEq, Repr

/-- Clark's four-way classification of expressions (Table 9.1, p. 300).
    Each expression type occupies one cell of the
    `MeaningAspect × Alterability` matrix. -/
structure ExpressionClass where
  aspect : MeaningAspect
  alterability : Alterability
  deriving DecidableEq, Repr

/-- Purely intensional expressions: fixed **sense**.
    E.g., *bachelor*, *blue*, *colorful ball* (p. 300). -/
def purelyIntensional : ExpressionClass := ⟨.sense, .fixed⟩

/-- Proper names: fixed **reference**.
    E.g., *George Washington*, *the Second World War*, *France* (p. 300). -/
def properName : ExpressionClass := ⟨.reference, .fixed⟩

/-- Indexical expressions: shifting **reference**.
    E.g., *he*, *now*, *the bachelor over there*. The reference depends on
    context, but the rule for determining it (the character) is fixed (p. 300). -/
def indexical : ExpressionClass := ⟨.reference, .shifting⟩

/-- Contextual expressions: shifting **sense**.
    E.g., *to teapot*, *our electric typewriter*, *a quick crab*.
    The sense itself — not just the reference — depends on the time, place,
    and circumstances of utterance (p. 300). -/
def contextualExpression : ExpressionClass := ⟨.sense, .shifting⟩

/-- The four expression types in Table 9.1 are pairwise distinct. -/
theorem expression_types_distinct :
    purelyIntensional ≠ properName ∧
    purelyIntensional ≠ indexical ∧
    purelyIntensional ≠ contextualExpression ∧
    properName ≠ indexical ∧
    properName ≠ contextualExpression ∧
    indexical ≠ contextualExpression := by decide

/-! ## §B. Ten types of contextual expressions (Table 9.2, p. 304)

Examples were corrected against the PDF on 2026-04-24. The previous
draft included examples that don't appear in this paper (*Nixon*-based
eponymous verb; "*a waller*, *a cupper*" for denominal nouns) — Clark uses
*Napoleon* for eponymous verbs and *Nixonite, bicycler, saxophonist* for
denominal nouns. -/

/-- The form class of the derived contextual expression. -/
inductive DerivedCategory where
  | noun
  | verb
  | adjective
  deriving DecidableEq, Repr

/-- The 10 types of contextual expressions from Table 9.2 (p. 304). -/
inductive ContextualExprType where
  -- Noun-derived
  /-- *the horse*, *a Henry Moore*, *a Beethoven*, *a commercial*, *some water* (p. 302). -/
  | indirectNoun
  /-- *finger cup*, *apple-juice chair* (p. 302). -/
  | compoundNoun
  /-- *John's dog*, *my tree* (p. 303). -/
  | possessive
  /-- *Nixonite*, *bicycler*, *saxophonist* (p. 303). -/
  | denominalNoun
  -- Verb-derived
  /-- *to farewell*, *to Houdini*, *to teapot* (p. 303). -/
  | denominalVerb
  /-- *to do a Napoleon*; *They did a Manhattan* (p. 315). -/
  | eponymousVerb
  /-- *do the lawn*, *do the porch* (p. 303). -/
  | proActVerb
  -- Adjective-derived
  /-- *Churchillian*, *Shavian* (p. 304). -/
  | denominalAdjective
  /-- *atomic*, *manual*, *marine* (p. 304; cf. Levi 1978). -/
  | nonPredicatingAdj
  /-- *very San Francisco*, *very Picasso* (p. 304). -/
  | eponymousAdjective
  deriving DecidableEq, Repr

/-- The derived form class of each contextual expression type. -/
def ContextualExprType.derivedCategory : ContextualExprType → DerivedCategory
  | .indirectNoun       => .noun
  | .compoundNoun       => .noun
  | .possessive         => .noun
  | .denominalNoun      => .noun
  | .denominalVerb      => .verb
  | .eponymousVerb      => .verb
  | .proActVerb         => .verb
  | .denominalAdjective => .adjective
  | .nonPredicatingAdj  => .adjective
  | .eponymousAdjective => .adjective

/-! ## §C. Sense-selection vs sense-creation (paper pp. 297–299)

Clark's central distinction: traditional parsers **select** from a finite
pre-existing list of senses; an adequate parser must **create** senses
from speaker intentions and mutual knowledge.

Two failure modes (p. 299):
- **Non-parsing**: the parser rejects a string as ungrammatical because no
  composition of listed senses succeeds (e.g., *Our electric typewriter
  got married*).
- **Mis-parsing**: the parser finds an interpretation but the wrong one
  (e.g., *Stereos are a dime a dozen* parsed as "phonographs are common"
  rather than "people who own phonographs are common"). -/

/-- A sense-selection lexicon: a finite list of pre-specified senses for
    each word. This is what traditional parsers assume (p. 297). -/
structure FiniteLexicon (Word Sense : Type*) where
  senses : Word → List Sense

/-- Sense-selection succeeds iff the intended sense is in the lexicon. -/
def FiniteLexicon.canParse {Word Sense : Type*}
    (lex : FiniteLexicon Word Sense) (w : Word) (intended : Sense) : Prop :=
  intended ∈ lex.senses w

/-! ## §D. Non-denumerability of nonce senses (paper pp. 313–318) -/

/-- Clark's non-denumerability argument: for any finite type `S` of
    distinguishable situations, the space of `S → Bool` functions
    (= possible nonce senses as characteristic functions on situations)
    has 2^|S| members. Any list shorter than this is incomplete (p. 314). -/
theorem nonce_senses_not_exhaustible
    {S : Type*} [Fintype S] [DecidableEq S]
    (senses : List (S → Bool))
    (h_card : senses.length < 2 ^ Fintype.card S) :
    ∃ f : S → Bool, f ∉ senses := by
  by_contra h
  push Not at h
  have h_le : Fintype.card (S → Bool) ≤ senses.length := by
    calc Fintype.card (S → Bool)
        = Finset.univ.card := Finset.card_univ.symm
      _ ≤ senses.toFinset.card := by
          apply Finset.card_le_card
          intro f _
          exact List.mem_toFinset.mpr (h f)
      _ ≤ senses.length := senses.toFinset_card_le
  rw [Fintype.card_fun, Fintype.card_bool] at h_le
  omega

/-- Any finite lexicon fails to parse some nonce sense of a contextual
    expression when the sense space `S → Bool` has more members than the
    lexicon lists (paper pp. 313–318). -/
theorem finite_lexicon_incomplete
    {Word S : Type*} [Fintype S] [DecidableEq S]
    (lex : FiniteLexicon Word (S → Bool)) (w : Word)
    (h : (lex.senses w).length < 2 ^ Fintype.card S) :
    ∃ s : S → Bool, ¬ lex.canParse w s :=
  nonce_senses_not_exhaustible (lex.senses w) h

/-! ## §E. Five properties shared with indirect illocutionary acts (paper pp. 319–321)

Clark's structural observation: contextual expressions share five properties
with indirect illocutionary acts, motivating treatment via a shared mechanism
(goal hierarchies, `§F`).

The five properties (illustrated in the paper first for *Do you know what time
it is?* used as a request, pp. 319–320, then transposed to *Max teapotted a
policeman*, pp. 320–321):

1. **Simultaneous meanings** — the expression carries both a direct meaning
   (Ed using *teapot* to denote teapots; the asker's literal yes/no question)
   and an indirect meaning (the rubbing action; the request).
2. **Logical priority** — the direct act is logically prior; the indirect act
   is performed *by* performing the direct one, not vice versa.
3. **Literalness of the direct meaning** — the direct meaning follows from
   the literal sentence meaning via standard linguistic conventions.
4. **Non-denumerability of the indirect meanings** — the possible nonce
   readings cannot be enumerated (formalized as `nonce_senses_not_exhaustible`
   above for contextual expressions).
5. **Contextuality of the indirect meaning** — what is conveyed depends
   critically on shared knowledge between speaker and hearer.

These five properties are structural consequences of inhabiting the
`GoalHierarchy` schema (`§F`) — the `directMeaning` / `intendedMeaning` /
`commonGround` triple gives (1)/(2)/(3) directly, and the convention-recognition
field encodes Clark's claim that subgoal (2) is always implicitly present
(p. 326). The previous file declared an `IndirectUseProperty` enum naming
the five properties but never used it in any theorem; the names live in
this docstring instead. -/

/-! ## §F. Goal hierarchies: the three-tier intentional view (paper pp. 323–328)

Clark's central positive proposal: parsing reconstructs the speaker's
hierarchy of goals. Each constituent of an utterance accomplishes a
subgoal in the speaker's plan (p. 324).

The hierarchy is **three-tier** (paper pp. 325–326). Ed's hierarchy in
*Max teapotted a policeman*:

- Subgoal **(3)**: Ed wants me to recognize he is using *teapot* to denote
  teapots (the conventional, direct denotation).
- Subgoal **(2)**: Ed wants me to recognize that the nonce verb meaning is
  computable uniquely from our common ground, with the noun playing one
  role in the situation (= the Innovative Denominal Verb Convention is
  invoked).
- Subgoal **(1)**: Ed wants me to recognize the intended verb meaning
  (the rubbing action).

Crucially (p. 326), subgoals (2) and (3) are *always* implicitly present —
even for conventional uses. In conventional cases the convention-recognition
in subgoal (2) is trivial (the convention permits the intended meaning to
equal the direct meaning). In innovative cases it is substantive (the
convention licenses the inferred sense). -/

/-- A goal hierarchy for interpreting an expression in context.
    Three-tier per Clark pp. 325–326: a direct meaning (subgoal 3), a
    convention-recognition that licenses the inference (subgoal 2),
    and an intended meaning (subgoal 1). -/
structure GoalHierarchy (W : Type*) where
  /-- Subgoal (3): the direct/conventional meaning. -/
  directMeaning : W → Prop
  /-- Subgoal (1): the intended meaning on this occasion. -/
  intendedMeaning : W → Prop
  /-- The common ground used for the inference. -/
  commonGround : CG W
  /-- Subgoal (2): the meta-recognition that the speaker invokes a
      convention licensing the direct → intended inference. For
      conventional uses this is `True` (no specific convention required).
      For innovative uses this is the substantive convention assertion
      — whose specific content (the Innovative Denominal Verb Convention,
      a preparatory condition, etc.) is exposed at the source-class level
      (`DenominalVerbConvention`, `IndirectAct`, …) and projected through
      to this field. -/
  invokesConvention : Prop

/-- A **conventional** use: intended = direct (p. 326). -/
def GoalHierarchy.isConventional {W : Type*} (g : GoalHierarchy W) : Prop :=
  g.intendedMeaning = g.directMeaning

/-- An **innovative** use: intended ≠ direct. The listener must compute
    the nonce meaning via subgoal (2) (p. 326). -/
def GoalHierarchy.isInnovative {W : Type*} (g : GoalHierarchy W) : Prop :=
  g.intendedMeaning ≠ g.directMeaning

/-! ## §G. Innovative Denominal Verb Convention (paper p. 321)

Clark's central formal contribution (after @cite{clark-clark-1979}, restated
in @cite{clark-1983} p. 321):

> In using an innovative denominal verb sincerely, the speaker means to denote:
> (a) the kind of situation
> (b) that he has good reason to believe
> (c) that on this occasion the listener can readily compute
> (d) uniquely
> (e) on the basis of their mutual knowledge
> (f) in such a way that the parent noun denotes one role in the situation,
>     and the remaining surface arguments of the denominal verb denote
>     other roles in the situation.

Conditions (b)–(e) are unified as CG-entailment: the CG uniquely determines
the situation. Condition (f) requires the parent noun's denotation to hold
in every situation-world. -/

/-- The Innovative Denominal Verb Convention (@cite{clark-clark-1979};
    paper p. 321).

    Condition (f) — *"the parent noun denotes one role in the situation,
    and the remaining surface arguments of the denominal verb denote other
    roles in the situation"* (paper p. 321) — is encoded structurally by
    the role-typing fields `parentNounRole` and `otherArgRoles`. The paper
    makes the role assignment explicit for the running example *Max
    teapotted a policeman* on p. 325–326: "teapots play one role in the
    action, Max is the agent, and the policeman is the patient." -/
structure DenominalVerbConvention (W : Type*) where
  /-- (a) The kind of situation denoted by the innovative verb. -/
  situation : W → Prop
  /-- The conventional denotation of the parent noun. -/
  nounDenotation : W → Prop
  /-- (e) The common ground of speaker and listener. -/
  commonGround : CG W
  /-- (b–d) The speaker has good reason to believe the listener can
      readily compute the situation uniquely from mutual knowledge.
      Operationalized as: every CG-compatible world satisfies the
      situation. -/
  cgDeterminesSituation : ∀ w, commonGround.contextSet w → situation w
  /-- (f, extensional) The noun's denotation is realized in every
      situation-world — there is a teapot wherever a teapotting happens. -/
  nounParticipates : ∀ w, situation w → nounDenotation w
  /-- (f, role-typing) The thematic role the parent noun denotes in the
      situation (paper p. 321 + p. 325–326). For *Max teapotted a
      policeman*, this is `.instrument`. -/
  parentNounRole : ThetaRole
  /-- (f, role-typing) The thematic roles the **other** surface arguments
      denote in the situation (paper p. 321). For *Max teapotted a
      policeman*: `[.agent, .patient]` — Max is agent, policeman is
      patient. -/
  otherArgRoles : List ThetaRole
  /-- (f, distinctness) "*one role* … *other roles*" — the parent noun's
      role is distinct from every other surface argument's role
      (paper p. 321). -/
  rolesDistinct : parentNounRole ∉ otherArgRoles

/-- Project a denominal-verb convention to a goal hierarchy. The
    convention's six conditions become subgoal (2)'s `invokesConvention`
    Prop. -/
def DenominalVerbConvention.toGoalHierarchy {W : Type*}
    (conv : DenominalVerbConvention W) : GoalHierarchy W where
  directMeaning := conv.nounDenotation
  intendedMeaning := conv.situation
  commonGround := conv.commonGround
  invokesConvention :=
    -- (b–d): CG uniquely determines the situation
    -- (f, extensional): noun denotation realized in every situation-world
    -- (f, role-distinctness): parent noun role differs from other surface args' roles
    (∀ w, conv.commonGround.contextSet w → conv.situation w) ∧
      (∀ w, conv.situation w → conv.nounDenotation w) ∧
      conv.parentNounRole ∉ conv.otherArgRoles

theorem DenominalVerbConvention.toGoalHierarchy_invokesConvention {W : Type*}
    (conv : DenominalVerbConvention W) :
    conv.toGoalHierarchy.invokesConvention :=
  ⟨conv.cgDeterminesSituation, conv.nounParticipates, conv.rolesDistinct⟩

/-- Every denominal-verb-convention use whose noun denotation strictly
    differs from its situation projects to an innovative goal hierarchy. -/
theorem denominal_is_innovative {W : Type*}
    (conv : DenominalVerbConvention W)
    (h : conv.nounDenotation ≠ conv.situation) :
    conv.toGoalHierarchy.isInnovative := h.symm

/-! ### Worked example: *Max teapotted a policeman* (paper pp. 320–321, 325–326)

The paper's running example. Per p. 325–326, Ed's goal hierarchy in
uttering *Max teapotted a policeman* assigns the following thematic
roles in the situation:

- The parent noun *teapot* denotes the **instrument** role (the means
  of the rubbing action).
- The other surface arguments denote the **agent** role (Max, the
  rubber) and the **patient** role (the policeman, whose leg gets
  rubbed).

These three roles are distinct, satisfying condition (f) of the
Innovative Denominal Verb Convention. -/

/-- A toy world for the *Max teapotted a policeman* example. -/
structure TeapotWorld where
  /-- Did the rubbing-with-teapot action take place? -/
  rubbing : Bool
  /-- Is a teapot present in the situation? -/
  teapot : Bool
  deriving DecidableEq, Repr

/-- The teapotting situation per Clark's paraphrase: rubbing happened
    AND a teapot was involved (paper p. 320). -/
def teapotSituation (w : TeapotWorld) : Prop :=
  w.rubbing = true ∧ w.teapot = true

/-- The conventional denotation of the noun *teapot*: a teapot is
    present in the world. -/
def teapotNoun (w : TeapotWorld) : Prop := w.teapot = true

/-- Common ground: shared knowledge about Max's odd habits with teapots.
    For the worked example we model the CG as already entailing the
    rubbing-with-teapot situation; in a fuller formalization the CG
    would entail the relevant odd-habit knowledge from which the
    listener derives the situation. -/
def teapotCG : CG TeapotWorld :=
  CG.empty.add { w | w.rubbing = true ∧ w.teapot = true }

/-- The Innovative Denominal Verb Convention (paper p. 321) instantiated
    for *Max teapotted a policeman* (paper pp. 320–321, 325–326).
    The role assignment — teapot = instrument, Max = agent, policeman =
    patient — is read directly from p. 325. -/
def teapotConvention : DenominalVerbConvention TeapotWorld where
  situation := teapotSituation
  nounDenotation := teapotNoun
  commonGround := teapotCG
  cgDeterminesSituation := by
    intro w h
    simp [teapotCG] at h
    exact h
  nounParticipates := fun _ h => h.2
  parentNounRole := .instrument
  otherArgRoles := [.agent, .patient]
  rolesDistinct := by decide

/-- The full DM + Convention bundle for *to teapot* in this context.
    The DM-side `recategorized` step (n → v) is satisfied by some
    underlying `CategorizedRoot`; for downstream studies the `convention`
    field is the Clark-side substantive content. -/
def teapotDenominalConvention :
    DenominalVerbConvention TeapotWorld := teapotConvention

/-- The teapotting situation strictly extends the noun denotation:
    every teapotting-world has a teapot, but not every teapot-world is
    a teapotting (the noun's extension is wider than the verb's
    situation). This is the substrate witness that *to teapot* is an
    innovative denominal verb. -/
theorem teapot_is_innovative_denominal :
    teapotConvention.toGoalHierarchy.isInnovative := by
  apply denominal_is_innovative
  intro h
  -- nounDenotation = teapotNoun (teapot=true);
  -- situation = teapotSituation (rubbing=true ∧ teapot=true)
  -- Witness ⟨rubbing=false, teapot=true⟩: LHS True, RHS False.
  have h' := congr_fun h ⟨false, true⟩
  simp [teapotConvention, teapotNoun, teapotSituation] at h'

/-- The role assignment for *teapot* in *Max teapotted a policeman* is
    structurally distinct: instrument ≠ agent and ≠ patient (paper
    p. 325). This is the substrate witness for condition (f). -/
theorem teapot_role_assignment_distinct :
    teapotConvention.parentNounRole = .instrument ∧
    teapotConvention.otherArgRoles = [.agent, .patient] ∧
    teapotConvention.parentNounRole ∉ teapotConvention.otherArgRoles :=
  ⟨rfl, rfl, by decide⟩

/-! ## §H. Bridge to LU-RSA (@cite{bergen-levy-goodman-2016})

@cite{bergen-levy-goodman-2016}'s LU-RSA operationalizes one dimension of
Clark's sense-creation: the listener marginalizes over possible lexica.

  L1(w | u) ∝ Σ_L P(L) · S1(u | w, L) · P(w)

The marginalization captures the open-endedness of the sense space. Clark's
fuller proposal (the three-tier goal hierarchy, `§F`) is richer — LU-RSA
captures the "what" (multiple possible meanings) but not the "how"
(hierarchical goal structure). -/

/-- A sense-selection parser uses a fixed `Lexicon`. -/
def senseSelectionParser (U W : Type) := Lexicon U W

/-- A sense-creation parser marginalizes over a space of possible lexica. -/
structure SenseCreationParser (U W L : Type) where
  toLexicon : L → Lexicon U W
  lexiconPrior : L → ℚ

/-- Sense-selection is the singleton-lexicon special case of sense-creation. -/
def senseSelectionAsSenseCreation {U W : Type} (lex : Lexicon U W) :
    SenseCreationParser U W Unit where
  toLexicon := λ _ => lex
  lexiconPrior := λ _ => 1

/-- Sense-creation with a non-trivial lexicon space cannot be reduced to
    sense-selection when different lexica assign different meanings to the
    same utterance (paper pp. 297–299). -/
theorem sense_creation_strictly_generalizes
    {U W L : Type} (parser : SenseCreationParser U W L)
    (l₁ l₂ : L) (u : U) (w : W)
    (h_diff : (parser.toLexicon l₁).meaning u w ≠ (parser.toLexicon l₂).meaning u w) :
    ¬ ∃ lex : Lexicon U W, ∀ l : L, parser.toLexicon l = lex := by
  intro ⟨lex, h_all⟩
  have h1 := h_all l₁
  have h2 := h_all l₂
  rw [h1, h2] at h_diff
  exact h_diff rfl

/-! ## §I. Bridge to DM recategorization

DM's `Recategorization.denominal` captures the syntactic n → v step. The
hard part — what the resulting verb *means* — is what Clark's convention
(`§G`) and the goal hierarchy (`§F`) provide. -/

/-- A denominal verb has a syntactic component (DM recategorization) and a
    pragmatic component (Clark's convention). -/
structure DenominalVerb (W : Type*) where
  nominalRoot : CategorizedRoot
  recategorized : CategorizedRoot
  recatProof : nominalRoot.recategorize .denominal = some recategorized
  convention : DenominalVerbConvention W

theorem denominal_verb_is_verbal {W : Type*} (dv : DenominalVerb W) :
    dv.recategorized.categorizer = .v :=
  recategorization_changes_category
    dv.nominalRoot .denominal dv.recategorized dv.recatProof

theorem denominal_verb_source_is_nominal {W : Type*} (dv : DenominalVerb W) :
    dv.nominalRoot.categorizer = .n :=
  denominal_requires_n dv.nominalRoot dv.recategorized dv.recatProof

/-- DM tells us denominal verbs exist (recategorization succeeds) but says
    nothing about what they mean. Two denominal verbs from the same root
    always produce the same syntactic result yet can have arbitrarily
    different meanings — Clark's convention fills that gap. -/
theorem dm_underdetermines_meaning {W : Type*} (dv₁ dv₂ : DenominalVerb W) :
    dv₁.recategorized.categorizer = dv₂.recategorized.categorizer := by
  rw [denominal_verb_is_verbal dv₁, denominal_verb_is_verbal dv₂]

/-! ## §J. The *stereos* example (paper pp. 326–327)

Arlene tells Bill *Stereos are a dime a dozen* meaning "phonographs are
very common" (conventional). Bombeck writes the same sentence meaning
"people who possess phonographs are very common" (innovative). Same
direct meaning, different intended meanings. -/

/-- A world with two relevant features for the *stereos* example. -/
structure StereosWorld where
  phonographsCommon : Bool
  ownersCommon : Bool
  deriving DecidableEq, Repr

/-- The conventional denotation of *stereos* = phonographs.
    Same for both Arlene and Bombeck — the DIRECT meaning is the
    conventional one (property 3: literalness). -/
def stereosDirectMeaning : StereosWorld → Prop := λ w => w.phonographsCommon = true

/-- Arlene's goal hierarchy: conventional use (intended = direct). -/
def arlenesGoalHierarchy : GoalHierarchy StereosWorld where
  directMeaning := stereosDirectMeaning
  intendedMeaning := stereosDirectMeaning
  commonGround := .empty
  invokesConvention := True

/-- Bombeck's CG: discourse context establishes "owners are common." -/
def bombecksCG : CG StereosWorld :=
  CG.empty.add { w | w.ownersCommon = true }

/-- Bombeck's goal hierarchy: innovative use. The intended meaning is the
    nonce reading (owners are common). `invokesConvention` is left at `True`
    here so this hand-built example matches `stereosMeaning.evaluate
    bombecksCG`'s projection (`§L`) — the substantive convention assertion
    for this class of cases lives in `DenominalVerbConvention.toGoalHierarchy`
    and `IndirectAct.toGoalHierarchy`, not in occasion-specific
    `ContextualMeaning` evaluations. -/
def bombecksGoalHierarchy : GoalHierarchy StereosWorld where
  directMeaning := stereosDirectMeaning
  intendedMeaning := λ w => w.ownersCommon = true
  commonGround := bombecksCG
  invokesConvention := True

theorem arlene_is_conventional : arlenesGoalHierarchy.isConventional := rfl

theorem bombeck_is_innovative : bombecksGoalHierarchy.isInnovative := by
  intro h
  have h' := congr_fun h ⟨true, false⟩
  simp [bombecksGoalHierarchy, stereosDirectMeaning] at h'

/-! ## §K. Bridge to indirect speech acts (paper pp. 319–321)

Clark's structural argument: contextual expressions and indirect illocutionary
acts are understood by the same mechanism — reconstructing the speaker's
hierarchy of goals (paper pp. 319–321).

The substrate consolidation: the indirect-act side carries a typed
`prepCondition : Option PreparatoryCondition` consuming
`Core.Discourse.IllocutionaryForce`'s Searle hierarchy, and projects to
`GoalHierarchy` via `IndirectAct.toGoalHierarchy`. The "same mechanism"
claim is then a structural identity: both `IndirectAct` and
`DenominalVerbConvention` provide projections into the common
`GoalHierarchy` schema, and the corresponding subgoal-(2)
`invokesConvention` field is non-vacuously populated by each. -/

/-- An indirect illocutionary act: direct content + intended (indirect)
    content + the preparatory condition the indirect act exploits or
    questions. The canonical case is *Do you know what time it is?*
    used as a request — `prepCondition := some .knowledge`. -/
structure IndirectAct (W : Type*) where
  /-- The directly expressed content (e.g., the literal yes/no question). -/
  directContent : W → Prop
  /-- The intended indirect content (e.g., the request). -/
  intendedContent : W → Prop
  /-- The preparatory condition the indirect act questions or exploits.
      `none` for cases where the indirect mechanism is not preparatory-
      condition based (e.g., `It's cold in here` as a request to close the
      window — exploits the speaker's discomfort, not a Searle preparatory
      condition). -/
  prepCondition : Option PreparatoryCondition
  /-- Common ground licensing the inference. -/
  commonGround : CG W

/-- Project an indirect act to a goal hierarchy.

    The substrate-level `invokesConvention` field is `True`: any
    `IndirectAct` instance invokes *some* convention by virtue of being
    an indirect act, but the substrate doesn't formally distinguish
    Searle-style preparatory-condition-based conventions (which Clark
    1979 / FrancikClark1985 / Ruytenbeek2017 use, exposed here via
    `prepCondition`) from Clark-style goal-hierarchy-based conventions
    (which paper pp. 321–323 use for the *American Express vs Credit
    cards* contrast — see `amexQuestion` / `creditCardsQuestion` below).

    The specific convention content lives at the source-class level:
    `prepCondition` for Searle-style cases; the goal-hierarchy
    documentation in docstrings for Clark-style cases. -/
def IndirectAct.toGoalHierarchy {W : Type*} (act : IndirectAct W) :
    GoalHierarchy W where
  directMeaning := act.directContent
  intendedMeaning := act.intendedContent
  commonGround := act.commonGround
  invokesConvention := True

/-- Indirect acts whose direct and intended contents differ are innovative. -/
theorem indirect_act_innovative {W : Type*} (act : IndirectAct W)
    (h : act.directContent ≠ act.intendedContent) :
    act.toGoalHierarchy.isInnovative := h.symm

/-- Worked example: *Do you know what time it is?* used as a request.
    Direct content: the literal yes/no question (in our toy model, the
    proposition that the addressee knows the time). Intended content: the
    request that the addressee tell the speaker the time. Preparatory
    condition: `.knowledge` — Clark/Searle's canonical case. -/
def timeQuestionExample : IndirectAct Unit where
  directContent := λ _ => True   -- literal: "do you know X?" — toy stand-in
  intendedContent := λ _ => False -- intended: "tell me X" — distinct
  prepCondition := some .knowledge
  commonGround := .empty

/-- The time-question example projects via the `.knowledge` preparatory
    condition, exactly the substrate `Phenomena/Politeness/Studies/FrancikClark1985.lean`
    formalizes for `RequestForm.doYouKnow` and that
    `Phenomena/Directives/Studies/RuytenbeekEtAl2017.lean` consumes for its
    mechanism 2. -/
theorem time_question_routes_via_knowledge :
    timeQuestionExample.prepCondition = some .knowledge := rfl

/-- The time-question example is innovative (direct ≠ intended). -/
theorem time_question_is_innovative :
    timeQuestionExample.toGoalHierarchy.isInnovative := by
  intro h
  have h' := congr_fun h ()
  simp [timeQuestionExample, IndirectAct.toGoalHierarchy] at h'

/-! ### Worked example: *American Express cards?* vs *Credit cards?*
    (paper pp. 321–323)

The paper's only experimental result (Clark 1979 Experiment 5,
restated). An assistant called Palo Alto restaurants asking either
*Do you accept American Express cards?* or *Do you accept credit cards?*

**The contrast is striking** (paper p. 323): "the two questions are
identical except for the object of the verbs. It was the content of
those noun phrases that forced the restaurateurs to infer very
different goals and to construe *American Express cards?* as merely a
direct question while construing *Credit cards?* as both a direct
question and an indirect request for a list of acceptable credit
cards."

The mechanism is goal hierarchies (paper p. 322). For *AmEx?* the
restaurateur infers a 4-subgoal hierarchy:
1. She wants to decide whether to patronize this restaurant
2. She wants to know how to pay for her meal
3. She wants to know if she can pay with the credit cards she owns
   (almost certainly just the AmEx)
4. She wants to know if the restaurant accepts AmEx

The question reflects subgoal (4) directly; answering it with *Yes*
also fulfills subgoal (3). 100% answered *yes*-style.

For *Credit cards?* the inferred hierarchy has 5 subgoals:
1. She wants to decide whether to patronize this restaurant
2. She wants to know how to pay for her meal
3. She wants to know if she can pay with one of her credit cards
   (probably most or all of the major cards)
4. She wants to know if any cards acceptable to the restaurant are
   among the cards she owns
5. She wants to know if the restaurant accepts credit cards

The question reflects subgoal (5); answering with just *yes* satisfies
(5) but not (4) — hence the indirect-request layer. 84% answered *yes*;
46% additionally inferred and gave the list of accepted cards.

These are NOT preparatory-condition-based indirect acts (Searle 1975 /
Clark 1979's mechanism), so `prepCondition := none`. The convention
invoked is goal-hierarchy reconstruction from NP content + CG. -/

/-- AmEx case: the question is interpreted as direct only (paper p. 322:
    100% gave yes-answers; restaurateurs construed as direct question).
    Substrate witness: intended = direct (no indirect-request layer). -/
def amexQuestion : IndirectAct Unit where
  directContent := λ _ => True   -- "Do you accept AmEx?" — toy stand-in
  intendedContent := λ _ => True  -- intended = direct (4-subgoal hierarchy collapses to (4))
  prepCondition := none           -- Clark-style goal-hierarchy mechanism, not Searle-prep
  commonGround := .empty

/-- Credit cards case: the question carries BOTH a direct interpretation
    AND an indirect request for the list of acceptable cards (paper
    p. 322–323: 84% answered yes-able; 46% additionally inferred the
    indirect request and gave the list).

    Substrate witness: intended ≠ direct (the indirect-request layer
    means the speaker's communicative intent extends beyond the direct
    question's literal answer). -/
def creditCardsQuestion : IndirectAct Unit where
  directContent := λ _ => True    -- "Do you accept credit cards?"
  intendedContent := λ _ => False -- intended ≠ direct (5-subgoal hierarchy: (5) + indirect (4))
  prepCondition := none
  commonGround := .empty

/-- The AmEx and credit-cards questions are surface-identical in their
    direct content (both "Do you accept X?") but diverge in intended
    content. This is the substrate witness for paper p. 323's
    conclusion: "it is the content of those noun phrases that forced
    the restaurateurs to infer very different goals." -/
theorem amex_credit_cards_diverge_in_intent :
    amexQuestion.directContent = creditCardsQuestion.directContent ∧
    amexQuestion.intendedContent ≠ creditCardsQuestion.intendedContent := by
  refine ⟨rfl, ?_⟩
  intro h
  have h' := congr_fun h ()
  simp [amexQuestion, creditCardsQuestion] at h'

/-- AmEx is treated as conventional in the goal-hierarchy sense:
    intended = direct (no indirect layer needed; paper p. 322
    "100 per cent of the restaurateurs … gave this response. They
    interpreted the utterance as a direct question and nothing more"). -/
theorem amex_question_is_conventional :
    amexQuestion.toGoalHierarchy.isConventional := rfl

/-- Credit cards triggers the indirect-act layer (paper p. 322 "the
    caller's reason for asking the question couldn't have been just to
    attain subgoal (5) … She must be indirectly requesting the
    restaurant's list of acceptable credit cards"). Substrate witness:
    intended ≠ direct. -/
theorem credit_cards_question_is_innovative :
    creditCardsQuestion.toGoalHierarchy.isInnovative := by
  intro h
  have h' := congr_fun h ()
  simp [creditCardsQuestion, IndirectAct.toGoalHierarchy] at h'

/-! ## §K.bis Shared mechanism — structural identity

Clark's "same mechanism" claim is realized as a typed projection. Both
`IndirectAct` and `DenominalVerbConvention` have a `toGoalHierarchy`
function landing in the common `GoalHierarchy` schema. The shared
mechanism is the `GoalHierarchy` schema together with the
`isConventional` / `isInnovative` classification, which both projections
respect by construction. -/

/-- The `isInnovative` criterion at the substrate level reduces to direct
    ≠ intended regardless of source theory. -/
theorem goal_hierarchy_innovative_iff {W : Type*} (g : GoalHierarchy W) :
    g.isInnovative ↔ g.intendedMeaning ≠ g.directMeaning := Iff.rfl

/-- The shared mechanism: both indirect acts and denominal-verb conventions
    project to `GoalHierarchy`, and the `isInnovative` classification
    agrees with their source-level criterion (direct ≠ intended for
    indirect acts; nounDenotation ≠ situation for denominal-verb
    conventions). The two `Iff.rfl` proofs witness that the projections
    preserve the classification — the substrate is a uniform interface,
    not theory-specific. -/
theorem shared_innovativeness_criterion {W : Type*}
    (act : IndirectAct W) (conv : DenominalVerbConvention W) :
    (act.toGoalHierarchy.isInnovative ↔
      act.intendedContent ≠ act.directContent) ∧
    (conv.toGoalHierarchy.isInnovative ↔
      conv.situation ≠ conv.nounDenotation) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-! ## §L. Contextual meaning — meaning as a function from common ground

The deeper formal principle: a contextual expression's meaning is a function
from common ground to denotation, not a static denotation. The `GoalHierarchy`
of `§F` is what you get by **evaluating** this function at a specific CG. -/

/-- A contextual meaning: meaning is a function from common ground to
    denotation. `directMeaning` is the conventional denotation; `compute`
    maps a CG to the **intended** meaning on a given occasion. -/
structure ContextualMeaning (W : Type*) where
  directMeaning : W → Prop
  compute : CG W → (W → Prop)

/-- Evaluate a contextual meaning at a specific CG, producing a goal
    hierarchy. The convention-recognition is left at `True` here — the
    fuller treatment exposes a CG-dependence witness via the source-class
    projections (`DenominalVerbConvention.toGoalHierarchy` etc.). -/
def ContextualMeaning.evaluate {W : Type*}
    (cm : ContextualMeaning W) (cg : CG W) : GoalHierarchy W where
  directMeaning := cm.directMeaning
  intendedMeaning := cm.compute cg
  commonGround := cg
  invokesConvention := True

/-- A contextual meaning is **CG-independent** when the CG makes no
    difference. This is sense-selection. -/
def ContextualMeaning.isCGIndependent {W : Type*}
    (cm : ContextualMeaning W) : Prop :=
  ∀ cg : CG W, cm.compute cg = cm.directMeaning

/-- A contextual meaning is **CG-dependent** when there exists a CG that
    shifts the intended meaning away from the direct meaning. This is
    sense-creation. -/
def ContextualMeaning.isCGDependent {W : Type*}
    (cm : ContextualMeaning W) : Prop :=
  ∃ cg : CG W, cm.compute cg ≠ cm.directMeaning

theorem cg_independent_conventional {W : Type*}
    (cm : ContextualMeaning W) (h : cm.isCGIndependent) (cg : CG W) :
    (cm.evaluate cg).isConventional := h cg

theorem cg_dependent_innovative {W : Type*}
    (cm : ContextualMeaning W) (h : cm.isCGDependent) :
    ∃ cg, (cm.evaluate cg).isInnovative := h

noncomputable section
open Classical

/-- The contextual meaning of *stereos*: the SAME meaning function
    underlies both Arlene's and Bombeck's uses. The `compute` function
    models the inference from CG to intended meaning:
    if the CG entails owners-are-common, the intended meaning is
    `ownersCommon`; otherwise it falls back to the direct meaning.

    This is a simplified model of the pragmatic computation — the
    `bombecksCG` antecedent bakes in the inference target. A fuller
    treatment via LU-RSA marginalisation or the `ErkHerbelot2024`
    PMF-over-scenarios substrate is the natural extension. -/
def stereosMeaning : ContextualMeaning StereosWorld where
  directMeaning := stereosDirectMeaning
  compute := λ cg =>
    if ∀ w, cg.contextSet w → w.ownersCommon = true
    then λ w => w.ownersCommon = true
    else stereosDirectMeaning

end

private theorem bombecksCG_entails_owners :
    ∀ w, bombecksCG.contextSet w → w.ownersCommon = true := by
  intro w h
  exact h.1

private theorem emptyCG_not_entails_owners :
    ¬ ∀ w, (CG.empty : CG StereosWorld).contextSet w → w.ownersCommon = true := by
  intro h
  have := h ⟨true, false⟩ (by trivial)
  exact absurd this (by decide)

theorem stereos_arlene :
    stereosMeaning.evaluate .empty = arlenesGoalHierarchy := by
  unfold stereosMeaning ContextualMeaning.evaluate
  simp only [if_neg emptyCG_not_entails_owners, arlenesGoalHierarchy]

theorem stereos_bombeck :
    stereosMeaning.evaluate bombecksCG = bombecksGoalHierarchy := by
  unfold stereosMeaning ContextualMeaning.evaluate
  simp only [if_pos bombecksCG_entails_owners, bombecksGoalHierarchy]

theorem stereos_is_cg_dependent : stereosMeaning.isCGDependent := by
  refine ⟨bombecksCG, ?_⟩
  unfold stereosMeaning
  simp only [if_pos bombecksCG_entails_owners]
  intro h
  have h' := congr_fun h ⟨true, false⟩
  simp [stereosDirectMeaning] at h'

theorem cg_independent_lexicon_suffices {W : Type*}
    (cm : ContextualMeaning W) (h : cm.isCGIndependent) :
    ∀ cg, (FiniteLexicon.mk (λ _ : Unit => [cm.directMeaning])).canParse
      () (cm.compute cg) := by
  intro cg
  rw [h cg]
  exact List.Mem.head _

end Clark1983
