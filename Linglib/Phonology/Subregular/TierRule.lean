/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Fintype.Option
import Linglib.Core.Computability.TierProjection
import Linglib.Core.Computability.Subregular.Function.Subsequential
import Linglib.Core.Computability.Subregular.Function.SideDeterminacy

/-!
# TierProjection-based rules (`TierRule`)
[belth-2026] [goldsmith-1976]

The canonical operational schema for SPE-style phonological alternations
that factor through a tier projection. A rule has the shape

  `Rel(A, F) / C __ ∘ proj(·, T)`        (left-context)
  `Rel(A, F) / __ C ∘ proj(·, T)`        (right-context)

where:

- `T ⊆ α` is a tier (an erasing string-homomorphism — see `TierProjection`);
- `C ⊆ T` is the natural class of the *triggering* tier-adjacent segment;
- `A ⊆ α` is the natural class of *targets* (here: a single underspecified
  position identified by index, à la [belth-2026]);
- `F` is the agreed-or-disagreed feature; and
- `Rel` is `Agree` (assimilation) or `Disagree` (dissimilation).

This schema covers Belth-style D2L rules (Latin `-alis` / `-aris` liquid
dissimilation, Turkish vowel harmony, Finnish backness harmony with
neutral-vowel transparency — see [belth-2026]), Rose-Walker harmony
systems (which structurally **contain** a `TierRule` as their value-prediction
core — see `Subregular.Harmony.System` in `Subregular/Harmony.lean`), and
any SPE rule whose context is a single tier-adjacent segment.

The schema does **not** cover:

- multi-feature dependencies (e.g., Turkish back/round parasitic harmony) —
  would require generalising `featureValue : α → Option Bool` to a list;
- non-local context windows (e.g., "the second segment to the left on
  the tier") — would require a positional offset on top of `lastWith`.

Both extensions are admittable on demand following the project's
"infrastructure on demand" policy (see `CLAUDE.md`).

## Relation to `Subregular/LocalRewrite.lean`

`Phonology/Subregular/LocalRewrite.lean` defines `Rule` — full SPE
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

namespace Subregular


/-! ### Schema -/

/-- Belth's `Agree`/`Disagree` distinction ([belth-2026]). -/
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

    Aliased to `Subregular.Direction` so the same `.left` / `.right` cases used
    by `Function/Subsequential.lean::Direction` (FST scan direction) and
    by this file (context side of a tier rule) reduce to one inductive
    type. The two roles read differently in prose but are isomorphic in
    Lean. -/
abbrev Side := Subregular.Direction

/-- A tier-based alternation rule over alphabet `α`: project the word onto a tier,
    find the adjacent context segment on `side`, and fill the target's feature by
    `relation` to it, falling back to `default`. -/
structure TierRule (α : Type*) where
  /-- The erasing projection ([goldsmith-1976]) onto which the context-class check is
      performed. -/
  tier : TierProjection α α
  /-- Whether the triggering context precedes (`.left`) or follows (`.right`) the
      unspecified target slot. -/
  side : Side := .left
  /-- The natural class `C`: the rule fires only when the tier-adjacent segment
      satisfies this predicate. -/
  targetIsContext : α → Prop
  /-- Decidability of the context class, carried as an instance field (mathlib's
      `Finset.filter` convention). -/
  [decTarget : DecidablePred targetIsContext]
  /-- `.agree` (assimilation) or `.disagree` (dissimilation). -/
  relation : Relation
  /-- The value of the alternating feature extracted from a context segment; `none`
      means the segment is itself underspecified, deferring to `default`. -/
  featureValue : α → Option Bool
  /-- The Elsewhere value ([belth-2026]'s default fallback): `some v` is the concrete
      fallback when no context is found, `none` makes `applyAt` return `none`. -/
  default : Option Bool := none

namespace TierRule

variable {α : Type*}

attribute [instance] TierRule.decTarget

/-- The value the rule predicts at the unspecified slot, given the rule
    `r`, the *preceding* segments `pre`, and the *following* segments
    `post`. The chosen side (`r.side`) determines which list is consulted.

    Returns `none` only when there is no relevant context **and** no
    default — i.e., the rule has no opinion. -/
def apply (r : TierRule α) (pre post : List α) : Option Bool :=
  let ctx? :=
    match r.side with
    | .left  => TierProjection.lastWith  r.tier r.targetIsContext pre
    | .right => TierProjection.firstWith r.tier r.targetIsContext post
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

/-! ### Generic Properties -/

/-- Flipping the relation twice returns the original rule. -/
@[simp] theorem flipRelation_flipRelation (r : TierRule α) :
    r.flipRelation.flipRelation = r := by
  unfold flipRelation; simp

/-- **Strict locality is the trivial-tier special case.** When the tier
    is the identity (every segment projects), `apply` (left-context)
    reduces to scanning the raw input for the context class — i.e., a
    strictly local rule (e.g. Turkish voicing assimilation,
    `Agree([?voice], {voice}) / [*] __` over the trivial projection —
    [belth-2026]). -/
theorem id_tier_left_is_strict_local (r : TierRule α)
    (h_id : r.tier = TierProjection.id) (h_side : r.side = .left) (pre : List α) :
    apply r pre [] =
      (match (pre.filter (fun x => decide (r.targetIsContext x))).getLast? with
        | none => r.default
        | some ctx => match r.featureValue ctx with
                      | none => r.default
                      | some v => some (match r.relation with
                                        | .agree => v | .disagree => !v)) := by
  unfold apply TierProjection.lastWith
  rw [h_side, h_id]
  simp [TierProjection.apply_id]

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

end Subregular

/-! ## Function-level subregular classification

The `TierRule.applyToString` reification produces a string-to-string
function classifiable in the function-level subregular hierarchy
(`Core/Computability/Subregular/Function/`). The expected classification
per [aksenova-rawski-graf-heinz-2020]:

* Identity-tier `TierRule`s → **Left-Subsequential** (the trivial-tier
  case lemma `id_tier_left_is_strict_local` above shows the structural
  equivalence to scanning the raw input for the context class).
* Non-trivial-tier `TierRule`s → **TierProjection-Subsequential** (a strictly
  larger class than Left-Subsequential, captured by the standard
  Heinz-Rawski-Tanner 2011 tier-strictly-local family applied to
  function classes).

The non-trivial-tier classification is **deferred** (the SFST witness
needs to thread the tier projection's state alongside the
predicate-evaluation state); the identity-tier case is discharged below.
Land the general witness here once a Studies file consumes it. -/
namespace Subregular.TierRule


variable {α : Type*}

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
def toIdTierSFST (r : TierRule α) : SFST α (Option Bool) (Option α) where
  start := none
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
    (h_id : r.tier = TierProjection.id) (h_side : r.side = .left) (past : List α) :
    r.applyAt past = predictFromCtx r (r.lastContextOf past) := by
  unfold applyAt predictFromCtx lastContextOf
  exact id_tier_left_is_strict_local r h_id h_side past

/-- **The SFST computes `applyToString`.** Generalised over the SFST's
starting state (which represents the lastContextOf of some virtual
past) and the corresponding past. -/
lemma toIdTierSFST_runFrom_eq_applyToStringAux (r : TierRule α)
    (h_id : r.tier = TierProjection.id) (h_side : r.side = .left)
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
    (r : TierRule α) (h_id : r.tier = TierProjection.id) (h_side : r.side = .left) :
    IsLeftSubsequential r.applyToString := by
  have h_run : r.toIdTierSFST.run = r.applyToString := by
    funext input
    show r.toIdTierSFST.runFrom none input = applyToString.applyToStringAux r input []
    -- `none = lastContextOf []` definitionally
    exact r.toIdTierSFST_runFrom_eq_applyToStringAux h_id h_side [] input
  exact h_run ▸ r.toIdTierSFST.isLeftSubsequential

/-! ### Myopia: the tier-rule prediction has no look-ahead -/

/-- `applyToString`'s coordinate `i` is the rule's prediction over the strict input
prefix: `applyAt r (input.take i)` (in range; `none` otherwise). -/
theorem applyToStringAux_getElem? (r : TierRule α) :
    ∀ (input past : List α) (i : ℕ),
      (applyToString.applyToStringAux r input past)[i]?
        = if i < input.length then some (r.applyAt (past ++ input.take i)) else none
  | [], _, i => by simp [applyToString.applyToStringAux]
  | _ :: _, _, 0 => by simp [applyToString.applyToStringAux]
  | x :: xs, past, i + 1 => by
      simp only [applyToString.applyToStringAux, List.getElem?_cons_succ,
        List.length_cons, List.take_succ_cons, Nat.add_lt_add_iff_right]
      rw [applyToStringAux_getElem? r xs (past ++ [x]) i, List.append_assoc,
        List.singleton_append]

theorem applyToString_getElem? (r : TierRule α) (u : List α) (i : ℕ) :
    (r.applyToString u)[i]?
      = if i < u.length then some (r.applyAt (u.take i)) else none := by
  rw [applyToString, applyToStringAux_getElem?]; simp

/-- `applyToString` is **prefix-determined**: its `i`-th output is fixed by the input's
strict prefix `{k | k < i}`. -/
theorem applyToString_prefixDetermined (r : TierRule α) (i : ℕ) :
    OutputDependsOn r.applyToString i {k | k < i} := by
  intro u v hlen hag
  rw [applyToString_getElem?, applyToString_getElem?, hlen]
  have htake : u.take i = v.take i := by
    apply List.ext_getElem?
    intro k
    rcases lt_or_ge k i with hk | hk
    · simpa only [List.getElem?_take_of_lt hk] using hag k hk
    · simp [List.getElem?_take_eq_none hk]
  rw [htake]

/-- **The tier-rule prediction mechanism is right-myopic** — it has no look-ahead.
Consequently no tier-rule-based prediction (the formal core of a `Harmony.System`) can
compute a *non-myopic* harmony, such as an unbounded-circumambient pattern. -/
theorem applyToString_isRightMyopic (r : TierRule α) :
    IsMyopicTowards r.applyToString .right :=
  IsMyopicTowards.right_of_prefixDetermined (applyToString_prefixDetermined r)

end Subregular.TierRule
