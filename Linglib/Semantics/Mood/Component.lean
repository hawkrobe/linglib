import Linglib.Semantics.Mood.Illocutionary
import Linglib.Semantics.Mood.State

/-!
# Mood Components: Which Component a Mood Targets
[portner-2018]

Each mood-bearing object (verbal mood, sentence mood, modal flavor)
targets a specific component of a `POSW` (or, for the `inquisitive`
case, of our extended `State`; see `Semantics/Mood/State.lean`).
[portner-2018]'s unification thesis (Ch. 4) says: the surface
diversity of mood phenomena reduces to *which component gets touched*.

This file packages that thesis as a type-level enum `Component` and a
typeclass `HasTarget`, instantiated here for `Illocutionary`
(sentence mood) and in `Semantics/Mood/Verbal.lean` for
`VerbalOp` (verbal mood). The companion *value-level*
implementation lives in `Semantics/Mood/State.lean`: the `State`
structure exposes `info`, `order`, and `inquiry` as actual fields, and
the updates `assert`/`promote`/`inquire` do the work that this file's
enum labels. The link between the two views is the projection
`Component.boxOn` below, which sends each label to the necessity
modal quantifying over the labelled component.

"Target" is selection-side vocabulary: verbal mood in [portner-2018]
(Ch. 2) is *selected by* the embedding attitude, so a verbal mood's
target is the component the selecting predicate's modality quantifies
over — not an operation the mood morpheme itself performs.

Modal flavors would get their own instance if `Semantics/Modality/`
is ever rephrased over POSW.
-/

namespace Semantics.Mood

/-- The component of a `POSW` (or of `State`, for `.inquisitive`) that a
    mood-bearing object operates on. [portner-2018], Ch. 4.

    - `informational`: the context set `cs`. Targeted by indicative
      verbal mood (Ch. 2) and declarative force (Ch. 3): assertion via
      `+`-update, belief via `□_cs`.
    - `preferential`: the ordering `≤`. Targeted by subjunctive verbal
      mood (Ch. 2) and imperative force (Ch. 3): directive via
      `⋆`-update, desire via `□_≤`.
    - `inquisitive`: the inquiry component. Targeted by interrogative
      force. [portner-2018] offers a partition-variant pposw (his
      (10), replacing `cs`) and the alternative of a separate
      question-set coordinate ([roberts-1996]; [portner-2004]);
      `State` adopts the latter. Verbal mood does not select for the
      inquiry component in [portner-2018]; see
      `Semantics/Mood/Verbal.lean` for our extension. -/
inductive Component where
  | informational
  | preferential
  | inquisitive
  deriving DecidableEq, Repr

/-- Typeclass for mood-bearing types. `target m` says which POSW
    component `m` operates on. -/
class HasTarget (M : Type*) where
  target : M → Component

export HasTarget (target)

/-! ### Sentence-mood instance -/

/-- Sentence mood ([portner-2018], Ch. 3):
    - declarative `+`-updates `cs` of the discourse POSW
    - imperative `⋆`-updates the ordering (the addressee's To-Do List,
      [portner-2004])
    - interrogative refines the inquiry component

    The `promissive` (preferential) and `exclamative` (informational)
    assignments are linglib extensions; [portner-2018] treats only the
    declarative/imperative/interrogative trichotomy in detail. The
    exclamative assignment moreover sits in tension with its Searle
    classification (`Discourse/SpeechAct.lean`: expressive class,
    *null* direction of fit — no component to target); it is retained
    as a conjectural placeholder until an exclamative-force account is
    formalized. -/
instance : HasTarget Illocutionary where
  target
    | .declarative   => .informational
    | .imperative    => .preferential
    | .promissive    => .preferential
    | .interrogative => .inquisitive
    | .exclamative   => .informational

/-! ### Operational projection: from `Component` to a State modal

The `Component` enum is a typeclass-resolved label. To turn that
label into semantic work — the `□_cs`/`□_≤`/`boxAns` modal that
quantifies over the labelled component — we project into a function
`State W → (W → Prop) → Prop`. This makes "target is informational"
*operational*: it picks out exactly `boxCs` as the modal to use, by
definition. Downstream glosses write `(target m).boxOn c p` and get
the right quantification by enum-match instead of manual case
analysis (`VerbalOp.interp` in `Semantics/Mood/Verbal.lean`
is defined this way). -/

variable {W : Type*}

/-- The modal projection: each `Component` selects the necessity
    modal that quantifies over the labelled State component. -/
def Component.boxOn : Component → State W → (W → Prop) → Prop
  | .informational, c, p => c.toExpState.boxCs p
  | .preferential,  c, p => c.toExpState.boxLe p
  | .inquisitive,   c, p => c.boxAns p

@[simp] theorem boxOn_informational (c : State W) (p : W → Prop) :
    Component.informational.boxOn c p = c.toExpState.boxCs p := rfl

@[simp] theorem boxOn_preferential (c : State W) (p : W → Prop) :
    Component.preferential.boxOn c p = c.toExpState.boxLe p := rfl

@[simp] theorem boxOn_inquisitive (c : State W) (p : W → Prop) :
    Component.inquisitive.boxOn c p = c.boxAns p := rfl

end Semantics.Mood
