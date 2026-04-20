import Linglib.Core.StringHom

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
    - `.right` — `Rel(A, F) / __ C` : context follows the target -/
inductive Side where
  | left
  | right
  deriving DecidableEq, Repr

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

end TierRule

end Phonology.Alternation
