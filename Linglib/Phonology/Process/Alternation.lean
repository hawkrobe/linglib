import Mathlib.Data.Fintype.Option
import Linglib.Core.StringHom
import Linglib.Core.Computability.Subregular.Function.Direction
import Linglib.Core.Computability.Subregular.Function.Subsequential

/-!
# Tier-Based Alternation Rules
@cite{belth-2026} @cite{goldsmith-1976}

The canonical operational schema for SPE-style phonological alternations
that factor through a tier projection. A rule has the shape

  `Rel(A, F) / C __ ∘ proj(·, T)`        (left-context, eq. 6 of @cite{belth-2026})
  `Rel(A, F) / __ C ∘ proj(·, T)`        (right-context, eq. 8)

where:

- `T ⊆ α` is a tier (an erasing string-homomorphism — see `Core.Tier`);
- `C ⊆ T` is the natural class of the *triggering* tier-adjacent segment;
- `A ⊆ α` is the natural class of *targets* (here: a single underspecified
  position identified by index, à la @cite{belth-2026});
- `F` is the agreed-or-disagreed feature; and
- `Rel` is `Agree` (assimilation) or `Disagree` (dissimilation).

This schema covers Belth-style D2L rules (Latin `-alis` / `-aris` liquid
dissimilation, Turkish vowel harmony, Finnish backness harmony with
neutral-vowel transparency — see @cite{belth-2026}), Rose-Walker harmony
systems (which structurally **contain** a `TierRule` as their value-prediction
core — see `Phonology.Harmony.HarmonySystem` in `Harmony/Defs.lean`), and
any SPE rule whose context is a single tier-adjacent segment.

The schema does **not** cover:

- multi-feature dependencies (e.g., Turkish back/round parasitic harmony) —
  would require generalising `featureValue : α → Option Bool` to a list;
- non-local context windows (e.g., "the second segment to the left on
  the tier") — would require a positional offset on top of `lastWith`.

Both extensions are admittable on demand following the project's
"infrastructure on demand" policy (see `CLAUDE.md`).

## Relation to `Process/LocalRewrite.lean`

`Phonology/Process/LocalRewrite.lean` defines `Rule` — full SPE
notation with arbitrary-length left/right contexts. The single-tier-
segment-context fragment of `Rule`s is structurally subsumed by `TierRule`
(via the trivial-tier specialisation theorem `id_tier_left_is_strict_local`
below). The formal subsumption *bridge theorem* between the two rule types
is deferred — it would state that for any `LocalRewrite.Rule` whose
left/right contexts are each a single `.seg` element, there exists a
`TierRule` computing the same string function. Lean-checkable formulation
is straightforward but requires careful threading of the trivial tier;
land it once a Studies file needs to invoke the bridge concretely.
-/

namespace Phonology.Alternation

open Core

-- ============================================================================
-- § 1: Schema
-- ============================================================================

/-- Belth's `Agree`/`Disagree` distinction (@cite{belth-2026} eq. 9). -/
inductive Relation where
  | agree     -- target's feature value matches the context's
  | disagree  -- target's feature value is the negation of the context's
  deriving DecidableEq, Repr

/-- The relation flipped: `.agree ↔ .disagree`. -/
def Relation.flip : Relation → Relation
  | .agree    => .disagree
  | .disagree => .agree

/-- Flipping the relation twice returns the original. -/
@[simp] theorem Relation.flip_flip : ∀ r : Relation, r.flip.flip = r
  | .agree | .disagree => rfl

/-- Which side the context lies on relative to the unspecified target slot.

    - `.left` — `Rel(A, F) / C __` : context precedes the target
    - `.right` — `Rel(A, F) / __ C` : context follows the target

    Aliased to `Core.Direction` so the same `.left` / `.right` cases used
    by `Function/Subsequential.lean::Direction` (FST scan direction) and
    by this file (context side of a tier rule) reduce to one inductive
    type. The two roles read differently in prose but are isomorphic in
    Lean. -/
abbrev Side := Core.Direction

/-- A tier-based alternation rule over alphabet `α`.

    - `tier`         : the erasing projection (@cite{goldsmith-1976}) onto
      which the context-class check is performed.
    - `side`         : whether the triggering context precedes (`.left`,
      eq. 6) or follows (`.right`, eq. 8) the unspecified target slot.
    - `targetIsContext` : the natural class `C` — the rule fires only when
      the tier-adjacent segment satisfies this predicate. Following
      mathlib's `Finset.filter` convention this is `Prop`-valued with
      `[DecidablePred]` carried as the instance field `decTarget`.
    - `relation`     : `.agree` (assimilation) or `.disagree` (dissimilation).
    - `featureValue` : the value of `F` extracted from a context segment.
      `none` means the segment is itself underspecified for `F`, in which
      case the rule defers to `default`.
    - `default`      : the Elsewhere value (@cite{belth-2026} §2.3.3,
      Finnish 52b). `none` means *no* default — when no context is found,
      `applyAt` returns `none`. `some v` is the concrete fallback. -/
structure TierRule (α : Type) where
  tier : Tier α α
  side : Side := .left
  targetIsContext : α → Prop
  [decTarget : DecidablePred targetIsContext]
  relation : Relation
  featureValue : α → Option Bool
  default : Option Bool := none

namespace TierRule

variable {α : Type}

attribute [instance] TierRule.decTarget

/-- The value the rule predicts at the unspecified slot, given the rule
    `r`, the *preceding* segments `pre`, and the *following* segments
    `post`. The chosen side (`r.side`) determines which list is consulted.

    Returns `none` only when there is no relevant context **and** no
    default — i.e., the rule has no opinion. -/
def apply (r : TierRule α) (pre post : List α) : Option Bool :=
  let ctx? :=
    match r.side with
    | .left  => Tier.lastWith  r.tier r.targetIsContext pre
    | .right => Tier.firstWith r.tier r.targetIsContext post
  match ctx? with
  | none     => r.default
  | some ctx =>
    match r.featureValue ctx with
    | none   => r.default
    | some v => some (match r.relation with
                      | .agree    => v
                      | .disagree => !v)

/-- Convenience for left-context rules: only the preceding string matters.
    The Belth Latin / Turkish-VH / Finnish-VH rules all use this form. -/
def applyAt (r : TierRule α) (pre : List α) : Option Bool :=
  apply r pre []

/-- The rule with its `relation` flipped (Agree ↔ Disagree). -/
def flipRelation (r : TierRule α) : TierRule α :=
  { r with relation := r.relation.flip }

-- ============================================================================
-- § 2: Generic Properties
-- ============================================================================

/-- Flipping the relation twice returns the original rule. -/
@[simp] theorem flipRelation_flipRelation (r : TierRule α) :
    r.flipRelation.flipRelation = r := by
  unfold flipRelation; simp

/-- **Strict locality is the trivial-tier special case.** When the tier
    is the identity (every segment projects), `apply` (left-context)
    reduces to scanning the raw input for the context class — i.e., a
    strictly local rule (@cite{belth-2026} §2.4 example: Turkish voicing
    assimilation eq. 49b is `Agree([?voice], {voice}) / [*] __` with the
    trivial projection). -/
theorem id_tier_left_is_strict_local (r : TierRule α)
    (h_id : r.tier = Tier.id) (h_side : r.side = .left) (pre : List α) :
    apply r pre [] =
      (match (pre.filter (fun x => decide (r.targetIsContext x))).getLast? with
        | none => r.default
        | some ctx => match r.featureValue ctx with
                      | none => r.default
                      | some v => some (match r.relation with
                                        | .agree => v | .disagree => !v)) := by
  unfold apply Tier.lastWith
  rw [h_side, h_id]
  simp [Tier.apply_id]

/-- Reify a `TierRule` as a string-to-string function: at each input
position, predict the feature value for the implicit "hole" using the
preceding context. The result is a `List α → List (Option Bool)`
function that consumers can classify subregularly.

Defined recursively (via `applyToStringAux`) for ease of induction; the
output at position i is `applyAt r (input.take i)` per the auxiliary's
past-threading. -/
def applyToString (r : TierRule α) (input : List α) : List (Option Bool) :=
  applyToStringAux r input []
where
  /-- Auxiliary: emit predictions over the suffix `input`, using `past`
  as the accumulated past. -/
  applyToStringAux (r : TierRule α) :
      (input : List α) → (past : List α) → List (Option Bool)
    | [], _ => []
    | x :: xs, past => r.applyAt past :: applyToStringAux r xs (past ++ [x])

end TierRule

end Phonology.Alternation

/-! ## Bridge to function-level subregular substrate

The `TierRule.applyToString` reification produces a string-to-string
function classifiable in the function-level subregular hierarchy
(`Core/Computability/Subregular/Function/`). The expected classification
per @cite{aksenova-rawski-graf-heinz-2020}:

* Identity-tier `TierRule`s → **Left-Subsequential** (the trivial-tier
  case lemma `id_tier_left_is_strict_local` above shows the structural
  equivalence to scanning the raw input for the context class).
* Non-trivial-tier `TierRule`s → **Tier-Subsequential** (a strictly
  larger class than Left-Subsequential, captured by the standard
  Heinz-Rawski-Tanner 2011 tier-strictly-local family applied to
  function classes).

This bridge theorem is **deferred** in this PR (substantive new
construction; the SFST witness needs to thread the tier projection's
state alongside the predicate-evaluation state). The substrate is in
place to receive it; the natural follow-up file is
`Phonology/Process/AlternationSubregular.lean` (or a small
addition here once a Studies file consumes the classification). -/
namespace Phonology.Alternation.TierRule

open Core
open Core.Computability.Subregular.Function

variable {α : Type}

/-- The prediction function shared by `applyAt` (under identity tier +
left side) and the SFST construction: given an "accumulated last
context" option, compute the feature value the rule predicts. -/
def predictFromCtx (r : TierRule α) : Option α → Option Bool
  | none => r.default
  | some ctx =>
    match r.featureValue ctx with
    | none => r.default
    | some v => some (match r.relation with
                      | .agree => v
                      | .disagree => !v)

/-- The `last context-matching segment` of a list as `Option α`. State
representation for the SFST below: the last input segment so far that
satisfies `targetIsContext`. -/
def lastContextOf (r : TierRule α) (xs : List α) : Option α :=
  (xs.filter (fun x => decide (r.targetIsContext x))).getLast?

/-- SFST witness for the identity-tier, left-side `applyToString`:
state tracks the last `targetIsContext`-matching input segment. -/
def toIdTierSFST (r : TierRule α) : SFST (Option α) α (Option Bool) where
  initial := none
  step st s :=
    let newSt := if r.targetIsContext s then some s else st
    (newSt, [predictFromCtx r st])
  finalOutput _ := []

/-- The SFST's state after one step matches the running `lastContextOf`. -/
@[simp] lemma toIdTierSFST_step_fst (r : TierRule α) (st : Option α) (s : α) :
    ((r.toIdTierSFST.step st s).1)
      = if r.targetIsContext s then some s else st := rfl

@[simp] lemma toIdTierSFST_step_snd (r : TierRule α) (st : Option α) (s : α) :
    ((r.toIdTierSFST.step st s).2) = [predictFromCtx r st] := rfl

/-- `lastContextOf` extends by one step: appending a single segment to
the past updates the running last-context exactly as the SFST step
does. -/
lemma lastContextOf_append_singleton (r : TierRule α) (past : List α) (x : α) :
    r.lastContextOf (past ++ [x])
      = if r.targetIsContext x then some x else r.lastContextOf past := by
  unfold lastContextOf
  rw [List.filter_append]
  by_cases h : r.targetIsContext x
  · simp [h]
  · simp [h]

/-- Under identity tier + left side, `applyAt` agrees with
`predictFromCtx ∘ lastContextOf` — the structural rephrasing of
`id_tier_left_is_strict_local`. -/
lemma applyAt_eq_predictFromCtx (r : TierRule α)
    (h_id : r.tier = Tier.id) (h_side : r.side = .left) (past : List α) :
    r.applyAt past = predictFromCtx r (r.lastContextOf past) := by
  unfold applyAt predictFromCtx lastContextOf
  exact id_tier_left_is_strict_local r h_id h_side past

/-- **The SFST computes `applyToString`.** Generalised over the SFST's
starting state (which represents the lastContextOf of some virtual
past) and the corresponding past. -/
lemma toIdTierSFST_runFrom_eq_applyToStringAux (r : TierRule α)
    (h_id : r.tier = Tier.id) (h_side : r.side = .left)
    (past : List α) (input : List α) :
    r.toIdTierSFST.runFrom (r.lastContextOf past) input
      = applyToString.applyToStringAux r input past := by
  induction input generalizing past with
  | nil => rfl
  | cons x xs ih =>
    show (r.toIdTierSFST.step (r.lastContextOf past) x).2
            ++ r.toIdTierSFST.runFrom (r.toIdTierSFST.step _ x).1 xs
         = r.applyAt past :: applyToString.applyToStringAux r xs (past ++ [x])
    rw [toIdTierSFST_step_snd, toIdTierSFST_step_fst]
    rw [show (if r.targetIsContext x then some x else r.lastContextOf past)
          = r.lastContextOf (past ++ [x]) from
        (r.lastContextOf_append_singleton past x).symm]
    rw [ih (past ++ [x])]
    rw [r.applyAt_eq_predictFromCtx h_id h_side]
    rfl

/-- **Identity-tier left-side TierRules reify to Left-Subsequential
functions.** Closes audit D6 with a real witness construction (not a
sorry): the SFST has state `Option α` (last-context-matching segment
seen) and emits the rule's prediction at each step. -/
theorem applyToString_isLeftSubsequential_of_id_tier [Fintype α]
    (r : TierRule α) (h_id : r.tier = Tier.id) (h_side : r.side = .left) :
    IsLeftSubsequential r.applyToString := by
  have h_run : r.toIdTierSFST.run = r.applyToString := by
    funext input
    show r.toIdTierSFST.runFrom none input = applyToString.applyToStringAux r input []
    -- `none = lastContextOf []` definitionally
    exact r.toIdTierSFST_runFrom_eq_applyToStringAux h_id h_side [] input
  exact h_run ▸ r.toIdTierSFST.isLeftSubsequential

end Phonology.Alternation.TierRule
