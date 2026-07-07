import Linglib.Semantics.Mood.IllocutionaryMood
import Linglib.Semantics.Mood.POSWQ

/-!
# POSWTarget: Which Component a Mood Targets
[portner-2018]

Each mood-bearing object (verbal mood, sentence mood, modal flavor)
targets a specific component of a `POSW` (or, for the `partition`
case, of our extended `POSWQ`; see `Semantics/Mood/POSWQ.lean`).
[portner-2018]'s unification thesis (Ch. 4) says: the surface
diversity of mood phenomena reduces to *which component gets touched*.

This file packages that thesis as a type-level enum `POSWTarget` and a
typeclass `HasPOSWTarget`, instantiated here for `IllocutionaryMood`
(sentence mood) and in `Semantics/Mood/VerbalMood.lean` for
`VerbalMoodOp` (verbal mood). The companion *value-level*
implementation lives in `Semantics/Mood/POSWQ.lean`: the `POSWQ`
structure exposes `cs`, `le`, and `inquiry` as actual fields, and the
updates `POSW.plus`/`POSW.star`/`POSWQ.inquire` do the work that this
file's enum labels. The link between the two views is the projection
`POSWTarget.boxOn` below, which sends each label to the necessity
modal quantifying over the labelled component.

"Target" is selection-side vocabulary: verbal mood in [portner-2018]
(Ch. 2) is *selected by* the embedding attitude, so a verbal mood's
target is the component the selecting predicate's modality quantifies
over — not an operation the mood morpheme itself performs.

Modal flavors would get their own instance if `Semantics/Modality/`
is ever rephrased over POSW.
-/

namespace Semantics.Mood

/-- The component of a `POSW` (or of `POSWQ`, for `.partition`) that a
    mood-bearing object operates on. [portner-2018], Ch. 4.

    - `informational`: the context set `cs`. Targeted by indicative
      verbal mood (Ch. 2) and declarative force (Ch. 3): assertion via
      `+`-update, belief via `□_cs`.
    - `preferential`: the ordering `≤`. Targeted by subjunctive verbal
      mood (Ch. 2) and imperative force (Ch. 3): directive via
      `⋆`-update, desire via `□_≤`.
    - `partition`: the inquiry component. Targeted by interrogative
      force. Portner's discourse model keeps the question component
      separate from the common ground ([portner-2004]'s Question Set);
      our `POSWQ` renders it as a third coordinate. Verbal mood does
      not select for partition in [portner-2018]; see
      `Semantics/Mood/VerbalMood.lean` for our extension. -/
inductive POSWTarget where
  | informational
  | preferential
  | partition
  deriving DecidableEq, Repr

/-- Typeclass for mood-bearing types. `target m` says which POSW
    component `m` operates on. -/
class HasPOSWTarget (M : Type*) where
  target : M → POSWTarget

export HasPOSWTarget (target)

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
instance : HasPOSWTarget IllocutionaryMood where
  target
    | .declarative   => .informational
    | .imperative    => .preferential
    | .promissive    => .preferential
    | .interrogative => .partition
    | .exclamative   => .informational

/-! ### Operational projection: from `POSWTarget` to a POSWQ modal

The `POSWTarget` enum is a typeclass-resolved label. To turn that
label into semantic work — the `□_cs`/`□_≤`/`boxAns` modal that
quantifies over the labelled component — we project into a function
`POSWQ W → (W → Prop) → Prop`. This makes "target is informational"
*operational*: it picks out exactly `boxCs` as the modal to use, by
definition. Downstream glosses write `(target m).boxOn c p` and get
the right quantification by enum-match instead of manual case
analysis (`VerbalMoodOp.interp` in `Semantics/Mood/VerbalMood.lean`
is defined this way). -/

variable {W : Type*}

/-- The modal projection: each `POSWTarget` selects the necessity
    modal that quantifies over the labelled POSWQ component. -/
def POSWTarget.boxOn : POSWTarget → POSWQ W → (W → Prop) → Prop
  | .informational, c, p => c.toPOSW.boxCs p
  | .preferential,  c, p => c.toPOSW.boxLe p
  | .partition,     c, p => c.boxAns p

@[simp] theorem boxOn_informational (c : POSWQ W) (p : W → Prop) :
    POSWTarget.informational.boxOn c p = c.toPOSW.boxCs p := rfl

@[simp] theorem boxOn_preferential (c : POSWQ W) (p : W → Prop) :
    POSWTarget.preferential.boxOn c p = c.toPOSW.boxLe p := rfl

@[simp] theorem boxOn_partition (c : POSWQ W) (p : W → Prop) :
    POSWTarget.partition.boxOn c p = c.boxAns p := rfl

end Semantics.Mood
