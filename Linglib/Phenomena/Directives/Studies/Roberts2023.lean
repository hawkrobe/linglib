import Linglib.Core.Discourse.Scoreboard
import Linglib.Core.Temporal.Time
import Linglib.Theories.Semantics.Modality.Kratzer.Flavor
import Linglib.Theories.Semantics.Modality.Temporal
import Linglib.Theories.Semantics.Modality.Directive
import Linglib.Theories.Semantics.Modality.Assert

/-!
# Roberts (2023): Imperatives in Dynamic Pragmatics
@cite{roberts-2023}

Imperatives in dynamic pragmatics. *Semantics & Pragmatics* 16, Article 7: 1–55.

## Core Contribution

A semantics and dynamic pragmatics for imperative mood that combines the
best features of @cite{kaufmann-2012} and @cite{portner-2004}:

1. **Semantic type**: Imperatives denote *de se* properties indexed to the
   addressee (type ⟨s, ⟨e, t⟩⟩), not propositions — following @cite{portner-2004}.
2. **Modal in semantic content**: The content includes a futurate circumstantial
   modal with Kratzerian modal base *f* and goal-based ordering source *g* —
   following @cite{kaufmann-2012}. But the modal is NOT deontic.
3. **Pragmatic deontic flavor**: The perceived deontic force arises entirely
   from the pragmatics of accepting a direction — updating G (the addressee's
   goals/plans on the scoreboard), not from the LF.

## Desiderata Satisfied

Roberts identifies 9 desiderata (a)–(i) for an imperative semantics (§1)
and shows the account satisfies all of them. See `section Desiderata` below.

## Formal Architecture

- **Circumstance** ⟨w, t⟩: world-time pair (§2.1.2, (45))
- **SameHistory**: w' agrees with w on all facts up to t (47)
- **FUT**: future circumstances — same history, later time (48)
- **Timely future**: FUT filtered for goal-relevance (50)
- **Futurate circumstantial modal base** *f*: (51)
- **Goal-based ordering source** *g*: (49)
- **Applicable circumstances** APPLIC: best timely futures (53)
- **Imperative character ¡**: (54)/(67)
- **Scoreboard updates**: assertion (57), interrogation (58), direction (59)
-/

namespace Roberts2023

open Core.Discourse
open Semantics.Modality.Kratzer
open Semantics.Attitudes.Intensional

/-! ## §2.1.2 Basic Ontology -/

/-- A **circumstance** is a world-time pair ⟨w, t⟩.

    @cite{roberts-2023} (45): "A circumstance is a world/time pair ⟨w, t⟩."

    Unified with `Core.Situation` from the temporal infrastructure —
    both are world-time pairs, differing only in field names. -/
abbrev Circumstance (W T : Type*) := Situation W T

/-- A **proposition** in the circumstantial sense: a set of circumstances. -/
abbrev CProp (W T : Type*) := Circumstance W T → Bool

/-- **SameHistory**: w' is exactly the same as w up to time t.

    @cite{roberts-2023} (47): "SameHistory(w', w, t) is true just in case
    world w' is exactly the same as world w in all matters of particular
    fact up to time t."

    Parametrized by a history-comparison function. -/
def SameHistory {W T : Type*} (histEq : W → W → T → Bool) (w' w : W) (t : T) : Bool :=
  histEq w' w t

/-- **FUT**: the future circumstances of ⟨w, t⟩.

    @cite{roberts-2023} (48): FUT(⟨w, t⟩) = {⟨w', t'⟩ | SameHistory(w, w', t) & t < t'}.
    These are the possible futures — worlds agreeing with w up to t,
    at times strictly after t. -/
def FUT {W T : Type*} [LT T] [DecidableRel (α := T) (· < ·)]
    (histEq : W → W → T → Bool) (allW : List W) (allT : List T)
    (c : Circumstance W T) : List (Circumstance W T) :=
  (allW.flatMap λ w' => allT.filterMap λ t' =>
    if SameHistory histEq w' c.world c.time && decide (c.time < t') then
      some ⟨w', t'⟩
    else
      none)

/-! ## §2.1.2 Goal-based ordering and applicable circumstances -/

/-- A **goal-based ordering source** maps a circumstance to a list of
    propositions reflecting the agent's hierarchically organized goals.

    @cite{roberts-2023} (49): "a goal_i-based ordering source g is a function
    that takes a circumstance ⟨w, t⟩ and yields an ordered set of propositions G
    reflecting x_i's hierarchically organized goals and intentions." -/
abbrev GoalOrderingSource (W T : Type*) := Circumstance W T → List ((W → Bool))

/-- A **futurate circumstantial modal base** maps circumstances to
    sets of propositions whose intersection gives the accessible worlds.

    @cite{roberts-2023} (51): constraints (a) w' = w, (b) t < t',
    (c) preconditions for realizing P hold in a timely fashion. -/
abbrev CircumstantialModalBase (W T : Type*) := Circumstance W T → List ((W → Bool))

/-! ## §2.1.2 The Imperative Character -/

/-- The **imperative character ¡** — the semantic contribution of
    imperative mood in English.

    @cite{roberts-2023} (54)/(67): Given context K, the imperative mood ¡
    presupposes x_i = ADDRESSEE(K), f is a futurate circumstantial modal
    base, g is an x_i-goal-dependent ordering source, and yields:
    "the property of being an addressee x s.t. in any applicable
    circumstances one comes to realize P in a timely fashion."

    We compose this from the existing Kratzer infrastructure: the applicable
    circumstances are the `bestWorlds` under the futurate modal base and
    goal ordering, and the prejacent must hold at all of them.

    The modal parameters are bundled as a `TeleologicalFlavor` — this
    makes Roberts' central claim structural: the imperative's modal is
    **teleological/circumstantial** (facts + goals), not deontic
    (facts + norms). -/
structure ImperativeCharacter where
  /-- The addressee (target of the directive) -/
  addressee : Nat
  /-- The prejacent: VP denotation (property the addressee should realize).
      Simplified to a world-predicate (the addressee is implicit). -/
  prejacent : (World → Bool)
  /-- The modal parameters: futurate circumstantial modal base + goal-based
      ordering source, bundled as a `TeleologicalFlavor`. -/
  flavor : TeleologicalFlavor World

/-- Convenience accessor: the futurate circumstantial modal base. -/
abbrev ImperativeCharacter.modalBase (ic : ImperativeCharacter) : ModalBase World :=
  ic.flavor.circumstances

/-- Convenience accessor: the goal-based ordering source. -/
abbrev ImperativeCharacter.orderingSource (ic : ImperativeCharacter) : OrderingSource World :=
  ic.flavor.goals

/-- Evaluate the imperative character at a world: the prejacent holds
    at all best (applicable) worlds under the futurate modal base and
    goal-based ordering.

    This is a **necessity** claim: ∀w' ∈ Best(f, g, w). P(w').
    The modal force is universal (not deontic — circumstantial). -/
def ImperativeCharacter.realize (ic : ImperativeCharacter) (w : World) : Bool :=
  decide (necessity ic.modalBase ic.orderingSource ic.prejacent w)

/-- The imperative character yields a Kratzer necessity over the
    futurate circumstantial modal base. -/
theorem imperativeCharacter_is_necessity (ic : ImperativeCharacter) (w : World) :
    (ic.realize w = true) ↔ necessity ic.modalBase ic.orderingSource ic.prejacent w := by
  simp only [ImperativeCharacter.realize, decide_eq_true_eq]

/-- The imperative character evaluates as `KratzerTheory` necessity
    under the teleological parameters. This connects Roberts' formalization
    directly to the Kratzer infrastructure. -/
theorem imperativeCharacter_eq_kratzerTheory (ic : ImperativeCharacter) (w : World) :
    ic.realize w = true ↔
    (KratzerTheory ic.flavor.toKratzerParams).eval .necessity ic.prejacent w := by
  simp only [ImperativeCharacter.realize, decide_eq_true_eq]
  rfl

/-- Roberts' imperative uses teleological (circumstantial) flavor.
    This is the structural encoding of her central claim:
    the modal is NOT deontic — contra @cite{kaufmann-2012}. -/
theorem imperativeCharacter_is_teleological :
    TeleologicalFlavor.flavorTag = .circumstantial := rfl

/-! ## §4 Imperative Subjects: Conservativity Presupposition -/

/-- **Conservativity constraint on imperative subjects** (@cite{roberts-2023} (65),
    after @cite{kaufmann-2012}):

    An imperative subject NP must live on the set of addressees.
    SL(Q) = ADDR(K) — the smallest set Q lives on is the addressee set.

    This is a presupposition constraining which NPs can serve as
    imperative subjects (you, everyone, nobody, somebody — all must
    quantify over (subsets of) addressees). -/
structure ConservativityPresup where
  /-- The subject's quantificational domain -/
  domain : List Nat
  /-- The addressee set -/
  addressees : List Nat
  /-- The presupposition: domain is a subset of addressees -/
  livesOn : ∀ e, e ∈ domain → e ∈ addressees

/-! ## §3 Desiderata Verification -/

/-- **(a) Not truth-evaluable**: Imperatives denote properties (type
    `indexedProperty`), not propositions. Properties require an
    individual argument and cannot be evaluated for truth or falsity. -/
theorem desideratum_a_not_truth_evaluable :
    SemanticType.indexedProperty ≠ SemanticType.proposition := nofun

/-- **(b) No evaluative adverbs**: Since imperatives are not propositional,
    evaluative sentential adverbs (which require propositional arguments)
    cannot modify them. "#Unfortunately, go to bed!" -/
theorem desideratum_b_type_mismatch :
    defaultSemanticType .imperative = .indexedProperty ∧
    defaultSemanticType .declarative = .proposition := ⟨rfl, rfl⟩

/-- **(c) Cannot be conditional antecedent**: Conditional antecedents
    require propositions. Imperatives denote properties → type mismatch.
    "*If eat your vegetables, then..." -/
theorem desideratum_c_conditional_antecedent :
    defaultSemanticType .imperative ≠ defaultSemanticType .declarative := nofun

/-- **(d) Differs from deontic declaratives**: The IFLP maps different
    semantic types to different speech acts. Imperatives update G;
    deontic declaratives update CG. -/
theorem desideratum_d_different_updates :
    forceLinkingPrinciple .indexedProperty ≠
    forceLinkingPrinciple .proposition := nofun

/-- **(e) Conditional imperatives** (@cite{roberts-2023} Table 1, §1):
    Imperatives may be explicitly or implicitly conditional.
    "If you're hungry, have some cheese and crackers." (17)

    Roberts' account handles this because the imperative's semantic content
    includes a Kratzerian modal with modal base *f* — the modal base
    restricts the circumstances under which the prejacent must be realized,
    making all imperatives inherently conditional. This is formalized by
    `ImperativeCharacter.modalBase`: the `bestWorlds` computation is
    parameterized by the modal base, which determines the applicable
    circumstances.

    Desiderata (e) and (f) are problems for @cite{portner-2004}'s account,
    which has no modal and therefore cannot use Kratzerian parameters *f*
    and *g* for modal interpretation. They favor @cite{kaufmann-2012}'s
    assumption of semantic modality in imperatives. -/
theorem desideratum_e_conditional :
    ∀ (ic : ImperativeCharacter),
    ic.realize = λ w => decide (necessity ic.modalBase ic.orderingSource ic.prejacent w) :=
  λ _ => rfl

/-- **(f) Range of modal flavors** (@cite{roberts-2023} Table 1, §1):
    Imperatives display a range of flavors, with two main types
    (@cite{kaufmann-2012}'s terminology):

    **Practical**: something the target can do. Only felicitous if it can
    be assumed that it's possible for the target to realize the property
    denoted by the VP. Sub-types include commands, prohibitions, permission,
    suggestions, pleas, advice, instructions, warnings, concessives.

    **Expressive**: nothing can be done; either the matter is already settled,
    or the target isn't in a position to do anything about it. Grounded in
    the wishes, hopes, etc. of the speaker. Sub-types: well-wishes
    ("Enjoy the movie!"), hopes ("Be the lady!").

    Roberts notes that expressives are bouletic, not deontic, and optative
    in mood rather than directive. The range of flavors follows from the
    Kratzerian architecture: different modal bases and ordering sources
    yield different flavors without lexical ambiguity. -/
inductive ImperativeUse where
  /-- Practical: the target can do something. Circumstantial modal base,
      goal-based ordering. Sub-types: command, prohibition, permission,
      suggestion, plea, advice, instruction, warning, concessive. -/
  | practical
  /-- Expressive: nothing can be done. Bouletic ordering, optative mood.
      Sub-types: well-wish ("Enjoy the movie!"), hope ("Be the lady!").

      @cite{roberts-2023} (p. 13): expressives "aren't deontic in import.
      They are instead buletic, pertaining to the speaker's preferences
      and priorities." She explicitly declines to formalize them: "I will
      assume that these uses of the imperative are optative in mood,
      rather than directive. [...] I will not address this use of the
      imperative in what follows."

      The `.bouletic` flavor mapping below is our extension of Roberts'
      remark — she identifies the flavor but does not provide a formal
      semantics for expressive imperatives. -/
  | expressive
  deriving DecidableEq, Repr

/-- Practical imperatives use a goal-based ordering (circumstantial flavor);
    expressive imperatives use a desire-based ordering (bouletic flavor).
    The Kratzer infrastructure generates the range without stipulation. -/
def ImperativeUse.flavorTag : ImperativeUse → Core.Modality.ModalFlavor
  | .practical => .circumstantial
  | .expressive => .bouletic

/-- Practical and expressive imperatives have different modal flavors —
    captured by the ordering source, not by the mood itself. -/
theorem desideratum_f_flavor_range :
    ImperativeUse.practical.flavorTag ≠ ImperativeUse.expressive.flavorTag := nofun

/-- **(g) Negation narrow scope**: Deontic force cannot occur under
    negation. "Don't go out!" = direction to not go out, NOT "there's
    no obligation." Two reasons: (1) property type blocks propositional
    negation; (2) deontic flavor is pragmatic, not semantic. -/
theorem desideratum_g_negation_type :
    defaultSemanticType .imperative = .indexedProperty := rfl

/-- **(h) Futurate flavor** (@cite{roberts-2023} Table 1, §1):
    Imperatives display evidence of temporal reference, always pertaining
    to a present or future time:

    - (33) "Relax!"
    - (34) "Please have this done by the time I get back."
    - (35a) "Vote tomorrow!" vs (35b) "#Please vote by last night!"

    Tags and rejections use futurate *will*: "Take out the garbage,
    will you?" / "No, I won't." (@cite{von-fintel-iatridou-2017})

    This follows from the futurate circumstantial modal base (51):
    the FUT operator (48) restricts applicable circumstances to those
    where the time is strictly later than the utterance time (`c.t < t'`).
    Past times are structurally excluded. -/
theorem desideratum_h_futurate {W T : Type*} [LT T] [DecidableRel (α := T) (· < ·)]
    (histEq : W → W → T → Bool) (allW : List W) (allT : List T)
    (c : Circumstance W T) :
    ∀ c' ∈ FUT histEq allW allT c, decide (c.time < c'.time) = true := by
  intro c' hc'
  unfold FUT at hc'
  simp only [List.mem_flatMap, List.mem_filterMap] at hc'
  obtain ⟨_, _, t', _, hif⟩ := hc'
  split at hif
  · next h =>
    simp only [Option.some.injEq] at hif; subst hif
    simp only [Bool.and_eq_true] at h; exact h.2
  · simp at hif

/-- **(i) Deontic parallels — pragmatic**: Direction update adds to G
    (not CG). The deontic inference arises because G contents are
    reflected in CG as deontic propositions. -/
theorem desideratum_i_direction_preserves_cg
    {W : Type*} (K : Scoreboard W) (p : (W → Bool)) (s t : Nat) :
    (K.directionUpdate p s t).cg = K.cg := rfl

/-- The three canonical speech acts update orthogonal scoreboard components:
    assertion → CG, interrogation → QUD, direction → G. -/
theorem desideratum_i_assertion_preserves_goals
    {W : Type*} (K : Scoreboard W) (p : (W → Bool)) (a : Nat) :
    (K.assertionUpdate p a).goals = K.goals := rfl

/-- Interrogation preserves CG (only QUD is updated). -/
theorem desideratum_i_interrogation_preserves_cg
    {W : Type*} (K : Scoreboard W) (q : (W → Bool)) (a : Nat) :
    (K.interrogationUpdate q a).cg = K.cg := rfl

/-- Interrogation preserves G (only QUD is updated). -/
theorem desideratum_i_interrogation_preserves_goals
    {W : Type*} (K : Scoreboard W) (q : (W → Bool)) (a : Nat) :
    (K.interrogationUpdate q a).goals = K.goals := rfl

/-- Direction preserves QUD (only G is updated). -/
theorem desideratum_i_direction_preserves_qud
    {W : Type*} (K : Scoreboard W) (p : (W → Bool)) (s t : Nat) :
    (K.directionUpdate p s t).qud = K.qud := rfl

/-! ## §2.2 The Force Linking Principle -/

/-- The IFLP round-trips for all three core moods:
    proposition → declarative, set of propositions → interrogative,
    indexed property → imperative. -/
theorem iflp_roundtrip :
    forceLinkingPrinciple (defaultSemanticType .declarative) = .declarative ∧
    forceLinkingPrinciple (defaultSemanticType .interrogative) = .interrogative ∧
    forceLinkingPrinciple (defaultSemanticType .imperative) = .imperative :=
  ⟨rfl, rfl, rfl⟩

/-- The three moods correspond to the three Searlean intentional states:
    assertion expresses belief, interrogation expresses desire (for answer),
    direction expresses desire (for action → intention upon acceptance). -/
theorem sincerity_triad :
    sincerityCondition .declarative = .belief ∧
    sincerityCondition .interrogative = .desire ∧
    sincerityCondition .imperative = .desire := ⟨rfl, rfl, rfl⟩

/-- Direction of fit matches across all three core moods. -/
theorem direction_of_fit_triad :
    (sincerityCondition .declarative).directionOfFit = .mindToWorld ∧
    (sincerityCondition .interrogative).directionOfFit = .worldToMind ∧
    (sincerityCondition .imperative).directionOfFit = .worldToMind :=
  ⟨rfl, rfl, rfl⟩

/-! ## §5 Comparison with Other Accounts -/

/-- Roberts agrees with @cite{portner-2004} on semantic type (property). -/
theorem agrees_with_portner_on_type :
    defaultSemanticType .imperative = .indexedProperty := rfl

/-- Roberts' imperative modal is circumstantial, not deontic
    (contra @cite{kaufmann-2012}). The deontic flavor is entirely pragmatic.

    The goal-based ordering source matches `TeleologicalFlavor` in the
    Kratzer infrastructure: circumstances + goals → circumstantial tag. -/
theorem roberts_modal_is_circumstantial :
    TeleologicalFlavor.flavorTag = .circumstantial := rfl

/-- @cite{kaufmann-2012} treats the imperative's modal as deontic.
    Roberts disagrees: the modal is circumstantial-futurate. -/
theorem modal_flavor_disagreement :
    TeleologicalFlavor.flavorTag ≠ DeonticFlavor.flavorTag := nofun

/-- Roberts' account predicts that the imperative modal flavor differs
    from what `Assert.primaryFlavor` assigns (which follows @cite{kaufmann-2012}).
    This is the central theoretical disagreement: Kaufmann says deontic,
    Roberts says circumstantial. @cite{ruytenbeek-etal-2017} provide
    experimental evidence for Kaufmann's view (Study 2). -/
theorem roberts_disagrees_with_assert :
    TeleologicalFlavor.flavorTag ≠
    Semantics.Modality.Assert.primaryFlavor .imperative := nofun

/-! ## Worked Examples -/

/-- Example: "Move!" (@cite{roberts-2023} (55))

    Trivial case: empty modal base, empty ordering. All worlds
    are accessible and best, so the imperative reduces to: the
    prejacent holds at all worlds. -/
def moveExample : ImperativeCharacter where
  addressee := 0
  prejacent := λ _w => true  -- MOVE simplified to always-true
  flavor := ⟨emptyBackground, emptyBackground⟩

theorem move_trivial : moveExample.realize = λ _ => true := by
  funext w; cases w <;> rfl

/-- Example: "Nobody move!" (@cite{roberts-2023} (42), attributed to
    @cite{veltman-2018})

    Negation is INTERNAL (predicate term negation ¬MOVE), not
    EXTERNAL (¬□ — "no obligation to move"). This follows from
    the property type: propositional negation can't scope over
    a property. -/
def nobodyMoveExample : ImperativeCharacter where
  addressee := 0
  prejacent := λ _w => false  -- ¬MOVE: nobody moves
  flavor := ⟨emptyBackground, emptyBackground⟩

/-- "Nobody move!" with trivial modality: the prejacent (¬MOVE)
    must hold at all worlds → nobody moves in any applicable
    circumstance. -/
theorem nobody_move_total_prohibition :
    nobodyMoveExample.realize = λ _ => false := by
  funext w; cases w <;> rfl

/-! ## Weak Imperatives: Suggestions and Advice

@cite{roberts-2023} §1 (example (38)): suggestions like "Hire an attorney"
carry weaker modal force than commands like "Finish your homework!" (37).
The difference is NOT in the mood or semantic type — both are imperatives
denoting properties. The difference is in the **ordering source**: suggestions
use a refined ordering where the prejacent itself serves as a secondary
ordering criterion, yielding weak necessity (should/ought).

This connects directly to the @cite{von-fintel-iatridou-2008} analysis
formalized in `Directive.lean`: WN ≡ SN_Xg — weak necessity IS strong
necessity with X-marked ordering source. -/

open Semantics.Modality.Directive in
/-- Evaluate a suggestion/advice imperative: weak necessity under the
    primary ordering + secondary ordering that favors the prejacent.

    @cite{roberts-2023} §1: "should in (38) is a weak modal, since the
    directive does not imply that the addressee is necessarily under an
    obligation." -/
def ImperativeCharacter.weakRealize
    (ic : ImperativeCharacter) (secondaryGoals : OrderingSource World)
    (w : World) : Prop :=
  weakNecessity ic.modalBase ic.orderingSource secondaryGoals ic.prejacent w

open Semantics.Modality.Directive in
/-- **Commands entail suggestions**: if a command holds (strong necessity),
    the corresponding suggestion holds a fortiori (weak necessity).

    This delegates to `Directive.strong_entails_weak` — the universal
    quantification over a *refined* best set is logically weaker. -/
theorem strong_imperative_entails_suggestion
    (ic : ImperativeCharacter) (secondaryGoals : OrderingSource World) (w : World)
    (h : ic.realize w = true) :
    ic.weakRealize secondaryGoals w :=
  strong_entails_weak ic.modalBase ic.orderingSource secondaryGoals ic.prejacent w
    (by simp only [ImperativeCharacter.realize, decide_eq_true_eq] at h; exact h)

/-- Example: "Have a cookie." (@cite{roberts-2023} §3, (60))

    An invitation, not a command. The hostess proposes that the guest
    adopt the goal of eating a cookie, but the guest is free to decline.
    Modeled as weak necessity: the primary ordering is empty (no
    obligation), and the secondary ordering favors cookie-eating worlds. -/
def haveCookieExample : ImperativeCharacter where
  addressee := 0
  prejacent := λ w => w == .w0  -- EAT-COOKIE holds at w0
  flavor := ⟨emptyBackground, emptyBackground⟩

/-- The invitation "Have a cookie" is NOT a strong command: with
    empty ordering, the prejacent fails at some best worlds. -/
theorem cookie_not_command :
    haveCookieExample.realize .w1 = false := by rfl

open Semantics.Modality.Directive in
/-- But "Have a cookie" IS a weak suggestion when the secondary
    ordering favors cookie-eating: among worlds that are otherwise
    tied, cookie-eating worlds are preferred. -/
theorem cookie_is_suggestion :
    haveCookieExample.weakRealize
      (λ _ => [λ w => w == .w0])  -- secondary: favor cookie-eating
      .w0 := by
  unfold ImperativeCharacter.weakRealize weakNecessity
  decide

end Roberts2023
