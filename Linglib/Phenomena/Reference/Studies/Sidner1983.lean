/-!
# @cite{sidner-1983}: Focusing in the Comprehension of Definite Anaphora
@cite{sidner-1979}

Chapter 5 of @cite{sidner-1983} (originally in Brady & Berwick eds.,
*Computational Models of Discourse*, MIT Press), based on
@cite{sidner-1979} (PhD thesis, MIT AI-TR-537).

## Architectural difference from @cite{grosz-joshi-weinstein-1995}

@cite{grosz-joshi-weinstein-1995} §9 (p. 222) describes Sidner's
account this way:

> In Sidner's theory, each utterance provides an immediate discourse
> focus, an actor focus, and a set of potential foci. The discourse
> and actor foci may coincide, but need not. Her potential foci are
> roughly analogous to our C_f.

This makes the architectural contrast precise. Sidner does **not**
have a Cf-ranker — she has a *two-slot* focus state (discourse focus +
actor focus) plus an unranked set of potential foci. The two slots
serve different roles in pronoun resolution: agent-position pronouns
prefer the actor focus; non-agent-position pronouns prefer the
discourse focus. This is fundamentally a different shape from GJW's
single ranked Cf list and single Cb.

For this reason, this file does **not** instantiate
`Discourse.Centering.CfRanker`. Sidner's account is a separate
formalization, structurally orthogonal to the Centering substrate.
The cross-framework comparison lives in
`Phenomena/Reference/Studies/GroszJoshiWeinstein1995.lean` §8 (the
chronologically-later paper, per linglib's chronological-dependency
convention), which imports this file and proves the disagreement on
GJW's example (34).

## Scope

This file formalizes:

* The two-slot focus state (discourse focus + actor focus).
* The expected-focus algorithm for the discourse focus, from
  @cite{sidner-1983} §5.2.3 (p. 287). The thematic preference order
  is `theme > other-non-agent > agent > VP` — note that **agent is
  ranked LAST among non-theme positions** for discourse focus, and is
  picked separately as the actor focus. This is the opposite of what
  one might expect from a label-only reading of "thematic-role
  ranking" and is what makes the two-slot architecture coherent.
* The expected-focus algorithm for the actor focus (an analogous
  algorithm picking the agent, §5.2.3 p. 287).
* Sidner's pronoun-resolution rule: agent-position pronouns
  co-specify the actor focus; non-agent pronouns co-specify the
  discourse focus (§5.2.6 step 3, p. 293).
* Application to GJW example (34) at the bottom of the file.

The full focusing algorithm has 10 steps (§5.2.6 pp. 292-294)
involving the alternate-focus list, focus stack, do-anaphora rule,
and implicit specification. That full machinery is **not** formalized
here — only the rules load-bearing for the GJW example (34)
disagreement. A future expansion could formalize the rest if it
becomes necessary for some downstream consumer.
-/

set_option autoImplicit false

namespace Sidner1983

-- ════════════════════════════════════════════════════
-- § 1. Phrase representation
-- ════════════════════════════════════════════════════

/-- A noun-phrase slot's syntactic position. Sidner's pronoun rule
    (§5.2.6 step 3) splits on agent vs. non-agent position, so the
    binary distinction is what matters for the formalization. -/
inductive Position where
  | agent
  | nonAgent
  deriving DecidableEq, Repr

/-- @cite{sidner-1983} §5.2.3 (p. 287) — thematic preference for
    expected discourse focus. The DEF list is ordered:

    > - theme unless the theme is a verb complement in which case
    >   the theme from the complement is used.
    > - all other thematic positions with the **agent last**
    > - the verb phrase

    `agent` is third in this order — it is *deprioritized* for
    discourse focus and instead picked separately as the actor focus
    (this file's `expectedActorFocus`). -/
inductive ThematicSlot where
  | theme
  | otherNonAgent
  | agent
  | verbPhrase
  deriving DecidableEq, Repr

/-- The DEF preference order from @cite{sidner-1983} §5.2.3 (p. 287),
    encoded as a ranking. Lower number = higher preference for
    discourse focus. -/
def ThematicSlot.defRank : ThematicSlot → Nat
  | .theme         => 0
  | .otherNonAgent => 1
  | .agent         => 2
  | .verbPhrase    => 3

/-- Sentence-form distinction used by the expected-focus algorithm
    (@cite{sidner-1983} §5.2.3 step 1 p. 287): is-a and there-insertion
    sentences pick the *subject* as expected focus; other sentences use
    the DEF preference order. -/
inductive SentenceForm where
  | isaOrThereInsertion
  | normal
  deriving DecidableEq, Repr

/-- A noun-phrase slot in a sentence. Carries the entity, its
    thematic position, its syntactic position (agent or non-agent),
    and whether the surface form is pronominal. -/
structure Phrase (E : Type) where
  entity : E
  thematic : ThematicSlot
  position : Position
  isPronoun : Bool
  deriving Repr

/-- A sentence as a flat list of noun-phrase slots, plus a form flag.
    The simplification mirrors the GJW substrate's
    `Discourse.Centering.Utterance`: we elide the syntactic tree and
    keep the slots that the focusing algorithm actually consults. -/
structure Sentence (E : Type) where
  form : SentenceForm
  phrases : List (Phrase E)
  deriving Repr

-- ════════════════════════════════════════════════════
-- § 2. Two-slot focus state
-- ════════════════════════════════════════════════════

/-- @cite{sidner-1983} §5.2 (p. 282): "An actor focus is a discourse
    item which is predicated as the agent in some event. It is
    distinct from the main focus, which will be called the discourse
    focus." Reasons given: "(1) the focus of the discourse is often
    distinguished from the actor … and (2) actors can be spoken of
    anaphorically at the same time that the discourse focus is
    pronominalized."

    The two slots are *independently* updated and queried — this is
    the architectural point that distinguishes Sidner from
    @cite{grosz-joshi-weinstein-1995}'s single-Cb account. -/
structure FocusState (E : Type) where
  discourseFocus : Option E
  actorFocus : Option E
  deriving Repr, DecidableEq

namespace FocusState

/-- The empty focus state, used as the discourse-initial state. -/
def empty {E : Type} : FocusState E := ⟨none, none⟩

end FocusState

-- ════════════════════════════════════════════════════
-- § 3. Expected-focus algorithm (§5.2.3, p. 287)
-- ════════════════════════════════════════════════════

/-- The expected discourse focus computed from a single sentence by
    the algorithm at @cite{sidner-1983} §5.2.3 (p. 287):

    * For an *is-a* or *there*-insertion sentence: the subject (modeled
      as the agent-position phrase).
    * Otherwise: the first phrase in DEF preference order
      (`theme > other-non-agent > agent > verbPhrase`). -/
def expectedDiscourseFocus {E : Type} (s : Sentence E) : Option E :=
  match s.form with
  | .isaOrThereInsertion =>
    (s.phrases.find? (fun p => p.position = .agent)).map (·.entity)
  | .normal =>
    -- pick the phrase whose `thematic.defRank` is minimal
    let withRank := s.phrases.map (fun p => (p.thematic.defRank, p))
    (withRank.foldl (init := none) (fun acc pair =>
      match acc with
      | none => some pair
      | some best => if pair.1 < best.1 then some pair else some best)).map (·.2.entity)

/-- The expected actor focus, by the analogous algorithm to the
    discourse-focus one but selecting the agent (@cite{sidner-1983}
    §5.2.3 p. 287, second algorithm sketch). -/
def expectedActorFocus {E : Type} (s : Sentence E) : Option E :=
  (s.phrases.find? (fun p => p.position = .agent)).map (·.entity)

/-- Update the focus state after a sentence. The discourse focus moves
    to the new sentence's expected discourse focus when one exists
    (otherwise retained); the actor focus moves to the new sentence's
    actor focus when one exists.

    This is a simplified version of the full focusing algorithm
    (@cite{sidner-1983} §5.2.6 pp. 292-294). It captures the
    discourse-initial step and the basic "movement on each new
    sentence" pattern, sufficient for the (34) example. -/
def updateState {E : Type} (state : FocusState E) (s : Sentence E) :
    FocusState E :=
  { discourseFocus := (expectedDiscourseFocus s).orElse (fun _ => state.discourseFocus)
    actorFocus := (expectedActorFocus s).orElse (fun _ => state.actorFocus) }

-- ════════════════════════════════════════════════════
-- § 4. Pronoun resolution (§5.2.6 step 3, p. 293)
-- ════════════════════════════════════════════════════

/-- @cite{sidner-1983} §5.2.6 step 3 (p. 293), the rule that drives
    the @cite{grosz-joshi-weinstein-1995} §9 example (34) disagreement:

    > If there is an anaphor co-specifying the CF and another
    > co-specifying some member of the ALFL, retain the CF as focus
    > **if the anaphor is not in agent position**. **If it is, take
    > the member of the ALFL as focus.**

    Distilled to the essential rule: an agent-position pronoun
    co-specifies the actor focus; a non-agent pronoun co-specifies the
    discourse focus. -/
def resolvePronoun {E : Type} (state : FocusState E) (p : Phrase E) :
    Option E :=
  match p.position with
  | .agent => state.actorFocus
  | .nonAgent => state.discourseFocus

-- ════════════════════════════════════════════════════
-- § 5. Application: @cite{grosz-joshi-weinstein-1995} example (34)
-- ════════════════════════════════════════════════════

/-! GJW (1995) §9 (p. 222) discusses this discourse to contrast their
    centering account with Sidner's two-focus account:

    (34) a. I haven't seen Jeff for several days.
         b. Carl thinks he's studying for his exams,
         c. but I think he went to the Cape with Linda.

    Sidner predicts that "he" in (34c) is Carl: Carl is the actor
    focus after (34b), and "he" in (34c) is in subject (agent)
    position, so by §5.2.6 step 3 the actor focus wins.

    The downstream comparison theorem lives in `GroszJoshiWeinstein1995.lean`
    §8 — that file imports this one to mechanize the disagreement. -/

namespace D34

/-- (34a) "I haven't seen Jeff for several days." Speaker = subject
    (agent of "see"); Jeff = theme (object of "see"). -/
def a : Sentence String :=
  { form := .normal
    phrases :=
      [⟨"speaker", .agent, .agent, true⟩,
       ⟨"Jeff", .theme, .nonAgent, false⟩] }

/-- (34b) "Carl thinks he's studying for his exams." Carl is the
    matrix subject (agent of "think"); the sentence is normal (not
    is-a / there-insertion). For the discourse-focus computation we
    treat the embedded subject "he" as the theme of the matrix verb
    "think" (the propositional theme), so Jeff (the entity "he"
    co-specifies, carried over from (34a)) becomes the new discourse
    focus. -/
def b : Sentence String :=
  { form := .normal
    phrases :=
      [⟨"Carl", .agent, .agent, false⟩,
       ⟨"Jeff", .theme, .nonAgent, true⟩] }

/-- The state of Sidner's focusing model after (34a) and (34b),
    starting from the empty state. -/
def stateAfterB : FocusState String :=
  updateState (updateState FocusState.empty a) b

/-- After (34b), the discourse focus is Jeff (the theme of "Carl
    thinks ___"; Jeff was already in focus from 34a and is reaffirmed
    by the embedded "he"). The actor focus is Carl (matrix agent).
    This matches GJW's gloss in §9 p. 222. -/
theorem state_after_b :
    stateAfterB = ⟨some "Jeff", some "Carl"⟩ := by decide

/-- The "he" in (34c) is in subject (agent) syntactic position. Per
    §5.2.6 step 3, it co-specifies the actor focus = Carl. -/
def heInC : Phrase String :=
  ⟨"_he_", .agent, .agent, true⟩

/-- **Sidner's prediction** for "he" in (34c): Carl. -/
def sidnerPredictedHe : String :=
  (resolvePronoun stateAfterB heInC).getD "_unresolved_"

theorem sidner_predicts_carl : sidnerPredictedHe = "Carl" := by decide

end D34

end Sidner1983
