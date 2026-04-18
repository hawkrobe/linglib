import Linglib.Core.Mood.Basic
import Linglib.Core.Mood.IllocutionaryMood
import Linglib.Core.Mood.ClauseType
import Linglib.Core.Mood.POSWQ

/-!
# POSWTarget: Which Component a Mood Targets
@cite{portner-2018}

Each mood-bearing object (verbal mood, sentence mood, modal flavor)
targets a specific component of a `POSW` (or, for the `partition`
case, of our extended `POSWQ`; see `Core/Mood/POSWQ.lean`).
@cite{portner-2018}'s unification thesis says: the surface diversity
of mood phenomena reduces to *which component gets touched*.

This file packages that thesis as a type-level enum `POSWTarget` and
a typeclass `HasPOSWTarget`, instantiated for `GramMood` (verbal
mood) and `IllocutionaryMood` (sentence mood). The companion
*value-level* implementation lives in `Core/Mood/POSWQ.lean`: the
`POSWQ` structure exposes `cs`, `lt`, and `inquiry` as actual
fields, and the updates `POSW.plus`/`POSW.star`/`POSWQ.inquire` do
the work that this file's enum labels.

The two views are kept separate because they answer different
questions. `POSWTarget` is a *typeclass-resolved label* used by
typology code that wants to ask "what kind of thing is this mood?";
`POSWQ` and its updates are the *operational substrate* used by
semantic glosses. The link is the projection
`POSWTarget.toComponent` below, which sends each label to the
matching POSWQ-level operation type.

Modal flavors will get their own instance once
`Theories/Semantics/Modality/` is rephrased over POSW.
-/

namespace Core.Mood

/-- The component of a `POSW` (or of `POSWQ`, for `.partition`) that a
    mood-bearing object operates on. @cite{portner-2018}, Ch. 4.

    - `informational`: the context set `cs`. Targeted by indicative
      verbal mood and declarative force (assertion via `+`-update,
      belief via `□_cs`).
    - `preferential`: the ordering `≤`. Targeted by subjunctive verbal
      mood and imperative force (directive via `⋆`-update,
      desire via `□_≤`). The `.promissive` and `.exclamative`
      assignments below are extensions of @cite{portner-2018}'s
      core declarative/imperative/interrogative trichotomy and
      should be treated as conjectural.
    - `partition`: a refinement of `cs` into a partition.
      Targeted by interrogative force. @cite{portner-2018} formalizes
      this as PPOSW (a partition replaces `cs`); we instead represent
      it as a third coordinate of `POSWQ`. Verbal mood does not
      select for partition in @cite{portner-2018}; see
      `Theories/Semantics/Mood/VerbalMood.lean` for our extension. -/
inductive POSWTarget where
  | informational
  | preferential
  | partition
  deriving DecidableEq, Repr, Inhabited

/-- Typeclass for mood-bearing types. `target m` says which POSW
    component `m` operates on. -/
class HasPOSWTarget (M : Type) where
  target : M → POSWTarget

export HasPOSWTarget (target)

/-! ## Instances -/

/-- Verbal mood (@cite{portner-2018}, Ch. 4):
    - indicative selected by `believe`-class attitudes (`□_cs` on agent's POSW)
    - subjunctive selected by `want`-class attitudes (`□_≤` on agent's POSW) -/
instance : HasPOSWTarget GramMood where
  target
    | .indicative  => .informational
    | .subjunctive => .preferential

/-- Sentence mood (@cite{portner-2018}, Ch. 4):
    - declarative `+`-updates `cs` of the discourse POSW
    - imperative `⋆`-updates `<` of the addressee's To-Do List
    - interrogative partitions `cs` (PPOSW)
    The `promissive` (preferential) and `exclamative` (informational)
    assignments are linglib extensions; @cite{portner-2018} treats
    only the declarative/imperative/interrogative trichotomy in
    detail. They are included here for typological coverage and
    should be revisited when each is independently formalized. -/
instance : HasPOSWTarget IllocutionaryMood where
  target
    | .declarative   => .informational
    | .imperative    => .preferential
    | .promissive    => .preferential
    | .interrogative => .partition
    | .exclamative   => .informational

/-! ## Mood alignment

A canonical declarative-indicative clause exhibits a *target
agreement* between its illocutionary force and its grammatical mood:
both target the informational component. This is the type-level
shadow of @cite{portner-2018}'s **Indicative Principle**, which is
itself stated as a one-way conditional ("if a clause's matrix
operator is `□_cs`, the clause is indicative") rather than as
target-equality.

We state both: the target-equality version (`decl_ind_target_match`)
and the conditional version (`gram_mood_target_iff` and friends below).
The conditional version captures Portner's principle directly at the
type level: the GramMood enum is in bijection with the two POSW
components it can target, so "target = informational" and "mood =
indicative" are interchangeable (and similarly for subjunctive).
The full clause-level conditional ("if the matrix operator is `□_cs`,
the clause is indicative") would additionally require a syntax-side
mood-features infrastructure mapping operators to mood realizations,
which does not yet exist in linglib. -/

/-- The canonical declarative-indicative clause has matching
    POSW-target on its force and mood components. The type-level
    shadow of @cite{portner-2018}'s Indicative Principle. -/
theorem decl_ind_target_match :
    target ClauseType.declInd.force = target ClauseType.declInd.mood := by
  rfl

@[deprecated decl_ind_target_match (since := "2026-04-18")]
theorem mood_alignment_decl_ind :
    target ClauseType.declInd.force = target ClauseType.declInd.mood :=
  decl_ind_target_match

/-- A polar question targets a partition (force) over a clause whose
    verbal mood is indicative (informational). The two POSW targets
    are *intentionally distinct* — interrogative force reshapes the
    informational component into a partition. -/
theorem mood_misalignment_polar_question :
    target ClauseType.polarQuestion.force ≠ target ClauseType.polarQuestion.mood := by
  decide

/-! ## Indicative / Subjunctive Principles as biconditionals

The conditional form of @cite{portner-2018}'s Indicative Principle
("if the matrix operator is `□_cs`, the clause is indicative") and its
subjunctive counterpart, restricted to the verbal-mood layer (`GramMood`).
Because `GramMood` is in bijection with the two POSW components it
can target, the conditionals collapse to biconditionals: targeting the
informational component *exactly* picks out indicative; targeting the
preferential component *exactly* picks out subjunctive.

These are the strongest type-level statements of Portner's principles
available without a syntax-side mood-features infrastructure. -/

/-- **Indicative Principle** (@cite{portner-2018}, Ch. 4): a verbal
    mood targets the informational component iff it is indicative.
    The biconditional form available at the GramMood layer. -/
theorem gram_mood_target_informational_iff_indicative (m : GramMood) :
    target m = .informational ↔ m = .indicative := by
  cases m <;> decide

/-- **Subjunctive Principle** (@cite{portner-2018}, Ch. 4): a verbal
    mood targets the preferential component iff it is subjunctive.
    The biconditional form available at the GramMood layer. -/
theorem gram_mood_target_preferential_iff_subjunctive (m : GramMood) :
    target m = .preferential ↔ m = .subjunctive := by
  cases m <;> decide

/-- A `GramMood` never targets the partition component — the
    declarative-complement column is closed under the
    informational/preferential split. The complement of
    `IllocutionaryMood` (which can target `.partition` via
    `.interrogative`). -/
theorem gram_mood_target_ne_partition (m : GramMood) :
    target m ≠ .partition := by
  cases m <;> decide

/-! ## §3. Farkas-style alternative: target by update type

@cite{farkas-2003} (eq. 11) characterizes mood selection by the *update
type* — `+` for indicative, `⋆` for subjunctive — rather than by the
matrix modal operator. The target equality `decl_ind_target_match`
above is the type-level shadow of Farkas's principle as well: the
POSW component refined by the force-side update (`+` refines `cs`,
`⋆` refines `≤`) coincides with the POSW component quantified by the
mood-side modal (`boxCs` over `cs`, `boxLe` over best-of-`≤`).

The Farkas alternative and Portner's Indicative/Subjunctive Principles
agree on the canonical declarative-indicative and imperative-subjunctive
cases (which is why `decl_ind_target_match` works for both); they
differ in their predictions about non-canonical pairings, where this
substrate does not yet take a position. -/

/-! ## §2. Operational projection: from `POSWTarget` to a POSWQ modal

The `POSWTarget` enum is a *typeclass-resolved label*. To turn that
label into actual semantic work — the `□_cs`/`□_≤`/`boxAns` modal
that quantifies over the labelled component — we project into a
function `POSWQ W → (W → Prop) → Prop`. The projection is
exhaustive and uniformly typed across the three components: the
`partition` case uses `POSWQ.boxAns`, the other two factor through
`POSW`.

This makes "target is informational" *operational*: it picks out
exactly `boxCs` as the modal to use, by definition. Downstream
glosses can write `(target m).boxOn c p` and have the right
quantification chosen by enum-match instead of by manual case
analysis. -/

universe u
variable {W : Type u}

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

end Core.Mood
