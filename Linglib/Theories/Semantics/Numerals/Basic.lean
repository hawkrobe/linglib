import Linglib.Core.Scales.Scale
import Linglib.Theories.Semantics.Quantification.Quantifier

/-!
# Unified Numeral Semantics
@cite{blok-2015} @cite{chierchia-fox-spector-2012} @cite{fox-2007}
@cite{goodman-stuhlmuller-2013} @cite{horn-1972} @cite{kennedy-2015}
@cite{hackl-2000} @cite{link-1983} @cite{partee-1987} @cite{spector-2013}

The numeral surface forms ("three", "more than three", "at least three", "at
most three", "fewer than three") are five `Nat`-instantiations of
@cite{kennedy-2015}'s unified de-Fregean GQ
`λP. max{d | #P ≥ d} REL m`, captured in `Core.Scale.kennedyGQ`. Each named
meaning is the corresponding `Core.Scale.{...}Deg id` specialization, and so
inherits the scale infrastructure (maximal informativity, monotonicity,
density) by construction.

The only theory disagreement is the bare-numeral semantics:

| Theory      | Bare "three" | bare semantics    |
|-------------|--------------|-------------------|
| Lower-bound | ≥3           | `atLeastMeaning`  |
| Exact       | =3           | `bareMeaning`     |

Modified numerals are theory-independent — everyone agrees "more than 3"
means `> 3`. The Class A / Class B distinction (@cite{geurts-nouwen-2007},
@cite{nouwen-2010}) reduces to reflexivity vs irreflexivity of the modifier's
underlying relation; see `Core.Scale.kennedyGQ_refl_at_boundary` and
`Core.Scale.kennedyGQ_irrefl_at_boundary`.

## Sections

1. Modifier classification (Class A/B, Bound direction)
2. Numeral meaning functions (5 `def`s over `Core.Scale.{...}Deg id`)
3. `BareNumeral` and `NumeralExpr`
4. Alternative sets (Kennedy §4.1)
5. Class A/B corollaries, anti-Horn-scale corollaries
6. Type-shifting (Kennedy §3.1)
7. EXH–type-shift duality (Spector §6.2)
8. GQT bridge (Bylinina & Nouwen)

The `HasDegree`-based numeral predicates and `CardinalityDegree` instance
live in `Numerals/Degree.lean`; precision/halo machinery lives in
`Numerals/Precision.lean`.
-/

namespace Semantics.Numerals

-- ============================================================================
-- Section 1: Modifier Classification
-- ============================================================================

/-- Class A (strict) vs Class B (non-strict) modified numerals.

The distinction predicts ignorance implicature patterns:
- Class A (>, <): EXCLUDE the bare-numeral world → no ignorance
- Class B (≥, ≤): INCLUDE the bare-numeral world → ignorance

Structurally: Class B iff the underlying relation is reflexive (`Std.Refl`),
Class A iff irreflexive (`Std.Irrefl`); see
`Core.Scale.kennedyGQ_refl_at_boundary`. -/
inductive ModifierClass where
  | classA  -- strict: >, <
  | classB  -- non-strict: ≥, ≤
  deriving Repr, DecidableEq

/-- Upper vs lower bound direction.

- `.upper`: constrains from above (at most, fewer than)
- `.lower`: constrains from below (at least, more than) -/
inductive BoundDirection where
  | upper  -- at most, fewer than, up to
  | lower  -- at least, more than, from...on
  deriving Repr, DecidableEq

-- ============================================================================
-- Section 2: Numeral Meaning Functions
-- ============================================================================

/-! Five named meanings — one per surface form. Each is the `id`-instantiation
of the corresponding `Core.Scale` degree property. They capture
@cite{kennedy-2015}'s

  ⟦modifier m⟧ = λP. max{d | #P ≥ d} REL m

where `n` plays the role of `max{d | #P ≥ d}` and `m` is the numeral.
`bareMeaning` is the exact (Kennedy) reading; the lower-bound (Horn) reading
of bare numerals is `atLeastMeaning`. Grounding in `Core.Scale` makes the
density predictions (`atLeastDeg_downMono`, `moreThan_noMaxInf`,
`atLeast_hasMaxInf`, etc.) hold by construction. -/

/-- Bare numeral meaning (exact reading): `n = m`. -/
def bareMeaning : Nat → Nat → Prop := Core.Scale.eqDeg id

/-- "More than `m`": `n > m`. -/
def moreThanMeaning : Nat → Nat → Prop := Core.Scale.moreThanDeg id

/-- "Fewer than `m`": `n < m`. -/
def fewerThanMeaning : Nat → Nat → Prop := Core.Scale.lessThanDeg id

/-- "At least `m`": `n ≥ m`. -/
def atLeastMeaning : Nat → Nat → Prop := Core.Scale.atLeastDeg id

/-- "At most `m`": `n ≤ m`. -/
def atMostMeaning : Nat → Nat → Prop := Core.Scale.atMostDeg id

@[simp] theorem bareMeaning_def (m n : Nat) : bareMeaning m n ↔ n = m := Iff.rfl
@[simp] theorem moreThanMeaning_def (m n : Nat) : moreThanMeaning m n ↔ n > m := Iff.rfl
@[simp] theorem fewerThanMeaning_def (m n : Nat) : fewerThanMeaning m n ↔ n < m := Iff.rfl
@[simp] theorem atLeastMeaning_def (m n : Nat) : atLeastMeaning m n ↔ n ≥ m := Iff.rfl
@[simp] theorem atMostMeaning_def (m n : Nat) : atMostMeaning m n ↔ n ≤ m := Iff.rfl

instance (m n : Nat) : Decidable (bareMeaning m n) :=
  inferInstanceAs (Decidable (n = m))
instance (m n : Nat) : Decidable (moreThanMeaning m n) :=
  inferInstanceAs (Decidable (n > m))
instance (m n : Nat) : Decidable (fewerThanMeaning m n) :=
  inferInstanceAs (Decidable (n < m))
instance (m n : Nat) : Decidable (atLeastMeaning m n) :=
  inferInstanceAs (Decidable (n ≥ m))
instance (m n : Nat) : Decidable (atMostMeaning m n) :=
  inferInstanceAs (Decidable (n ≤ m))

-- ============================================================================
-- Section 3: BareNumeral and NumeralExpr
-- ============================================================================

/-- Bare numeral utterances (one through five). -/
inductive BareNumeral where
  | one | two | three | four | five
  deriving DecidableEq, Repr, Inhabited

/-- Convert `BareNumeral` to its numeric value. -/
def BareNumeral.toNat : BareNumeral → Nat
  | .one => 1 | .two => 2 | .three => 3 | .four => 4 | .five => 5

/-- Next-higher `BareNumeral` (for computing scalar alternatives). -/
def BareNumeral.succ : BareNumeral → Option BareNumeral
  | .one => some .two
  | .two => some .three
  | .three => some .four
  | .four => some .five
  | .five => none

instance : ToString BareNumeral where
  toString
    | .one => "one" | .two => "two" | .three => "three"
    | .four => "four" | .five => "five"

/-- A numeral expression: a bare numeral or one of the four modifications.
    Used both as a surface form and (via `kennedyAlternatives`) as an
    element of Kennedy's single alternative set. -/
inductive NumeralExpr where
  | bare (n : Nat)
  | atLeast (n : Nat)
  | moreThan (n : Nat)
  | atMost (n : Nat)
  | fewerThan (n : Nat)
  deriving Repr, DecidableEq

/-- The numeric argument: the `m` in "more than `m`", "exactly `m`", etc. -/
def NumeralExpr.argument : NumeralExpr → Nat
  | .bare m | .atLeast m | .moreThan m | .atMost m | .fewerThan m => m

/-- Strict (Class A) vs. non-strict (Class B) classification per
    @cite{geurts-nouwen-2007} / @cite{nouwen-2010}. Bare numerals carry
    no modifier and return `none`. -/
def NumeralExpr.modifierClass : NumeralExpr → Option ModifierClass
  | .bare _ => none
  | .moreThan _ | .fewerThan _ => some .classA
  | .atLeast _ | .atMost _ => some .classB

/-- Lower-bound vs. upper-bound modifier direction. Bare numerals return `none`. -/
def NumeralExpr.boundDirection : NumeralExpr → Option BoundDirection
  | .bare _ => none
  | .atLeast _ | .moreThan _ => some .lower
  | .atMost _ | .fewerThan _ => some .upper

/-- Meaning of a numeral expression, parameterized by the bare-numeral
    semantics (theory choice: Kennedy `bareMeaning` or Horn `atLeastMeaning`). -/
def NumeralExpr.meaning (bare : Nat → Nat → Prop) : NumeralExpr → Nat → Prop
  | .bare m, n => bare m n
  | .atLeast m, n => atLeastMeaning m n
  | .moreThan m, n => moreThanMeaning m n
  | .atMost m, n => atMostMeaning m n
  | .fewerThan m, n => fewerThanMeaning m n

instance (bare : Nat → Nat → Prop) [∀ m n, Decidable (bare m n)]
    (e : NumeralExpr) (n : Nat) : Decidable (e.meaning bare n) := by
  cases e <;> unfold NumeralExpr.meaning <;> infer_instance

-- ============================================================================
-- Section 4: Alternative Set (@cite{kennedy-2015} §4.1)
-- ============================================================================

/-- @cite{kennedy-2015}'s single alternative set for numeral `n` —
    bare plus all four surface modifications. The point is
    **anti-Horn-scale**: there is no fixed scale direction. The
    Class A / Class B split is read off asymmetric entailment
    (cf. `classA_excludes_bare_world`, `classB_includes_bare_world`),
    not from membership in a pre-split sublist. -/
def kennedyAlternatives (n : Nat) : List NumeralExpr :=
  [.bare n, .moreThan n, .fewerThan n, .atLeast n, .atMost n]

-- ============================================================================
-- Section 5: Class A/B Corollaries and Anti-Horn-Scale Corollaries
-- ============================================================================

/-! Class A/B is the central typological generalization (@cite{geurts-nouwen-2007},
    @cite{nouwen-2010}): strict modifiers (`>`, `<`) exclude the bare-numeral
    world; non-strict modifiers (`≥`, `≤`) include it. The classification is
    derived from `NumeralExpr.modifierClass`; the inclusion/exclusion theorems
    below apply the corresponding general lemmas
    `Core.Scale.kennedyGQ_irrefl_at_boundary` and
    `Core.Scale.kennedyGQ_refl_at_boundary`, instantiated at `μ = id`. -/

/-- **Class A excludes the bare-numeral world** (universal). For every
    `e : NumeralExpr` whose modifier class is A, the meaning fails at
    `n = e.argument`, regardless of which bare-numeral semantics is chosen.

    Each non-vacuous branch delegates to
    `Core.Scale.kennedyGQ_irrefl_at_boundary` at `μ = id`. -/
theorem classA_excludes_bare_world (bare : Nat → Nat → Prop) (e : NumeralExpr)
    (h : e.modifierClass = some .classA) :
    ¬ e.meaning bare e.argument := by
  cases e with
  | bare _      => simp [NumeralExpr.modifierClass] at h
  | atLeast _   => simp [NumeralExpr.modifierClass] at h
  | atMost _    => simp [NumeralExpr.modifierClass] at h
  | moreThan _  => exact Core.Scale.kennedyGQ_irrefl_at_boundary (rel := (· > ·)) id rfl
  | fewerThan _ => exact Core.Scale.kennedyGQ_irrefl_at_boundary (rel := (· < ·)) id rfl

/-- **Class B includes the bare-numeral world** (universal). For every
    `e : NumeralExpr` whose modifier class is B, the meaning holds at
    `n = e.argument`, regardless of which bare-numeral semantics is chosen.

    Each non-vacuous branch delegates to
    `Core.Scale.kennedyGQ_refl_at_boundary` at `μ = id`. -/
theorem classB_includes_bare_world (bare : Nat → Nat → Prop) (e : NumeralExpr)
    (h : e.modifierClass = some .classB) :
    e.meaning bare e.argument := by
  cases e with
  | bare _      => simp [NumeralExpr.modifierClass] at h
  | moreThan _  => simp [NumeralExpr.modifierClass] at h
  | fewerThan _ => simp [NumeralExpr.modifierClass] at h
  | atLeast _   => exact Core.Scale.kennedyGQ_refl_at_boundary (rel := (· ≥ ·)) id rfl
  | atMost _    => exact Core.Scale.kennedyGQ_refl_at_boundary (rel := (· ≤ ·)) id rfl

/-- Bare numeral pointwise entails "at least `m`" — the `id`-specialization
    of `Core.Scale.eqDeg_imp_atLeastDeg`. -/
theorem classB_entailed_by_bare (m n : Nat) :
    bareMeaning m n → atLeastMeaning m n :=
  Core.Scale.eqDeg_imp_atLeastDeg id m n

/-- Exact bare numerals are not upward-monotone: the `id`-specialization of
    `Core.Scale.eqDeg_not_upward_monotone` (witness `d = 3`, `d' = 4`). -/
theorem bare_not_upward_monotone :
    ¬ ∀ m m' n, m ≤ m' → bareMeaning m n → bareMeaning m' n := by
  intro h
  exact Core.Scale.eqDeg_not_upward_monotone (W := Nat) id (d := 3) (d' := 4)
    (by decide) (by decide) (w := 3) rfl
    (fun x y hxy hex => h x y 3 hxy hex)

/-- Bare numerals are not downward-monotone either, so they fail the
    Horn-scale criterion in both directions. The `id`-specialization of
    `Core.Scale.eqDeg_not_downward_monotone`. -/
theorem bare_not_downward_monotone :
    ¬ ∀ m m' n, m' ≤ m → bareMeaning m n → bareMeaning m' n := by
  intro h
  exact Core.Scale.eqDeg_not_downward_monotone (W := Nat) id (d := 3) (d' := 2)
    (by decide) (by decide) (w := 3) rfl
    (fun x y hyx hex => h x y 3 hyx hex)

/-- "At least `m`" is strictly weaker than "bare `m`" — the `id`-specialization
    of `Core.Scale.atLeastDeg_strictly_weaker_than_eqDeg` (witness `d' = m+1`). -/
theorem atLeast_strictly_weaker_than_bare (m : Nat) :
    atLeastMeaning m (m + 1) ∧ ¬ bareMeaning m (m + 1) :=
  Core.Scale.atLeastDeg_strictly_weaker_than_eqDeg id (Nat.lt_succ_self m) (w := m + 1) rfl

/-- "More than `m`" and "bare `m`" have disjoint denotations — the
    `id`-specialization of `Core.Scale.moreThanDeg_disjoint_eqDeg`. -/
theorem moreThan_disjoint_from_bare (m n : Nat) :
    ¬ (bareMeaning m n ∧ moreThanMeaning m n) :=
  Core.Scale.moreThanDeg_disjoint_eqDeg id m n

-- ============================================================================
-- Section 6: Type-Shifting (@cite{kennedy-2015} §3.1)
-- ============================================================================

/-! ## De-Fregean type-shifting: exact → lower-bound

The general operation `Core.Scale.typeLower` (`∃ d' ≥ d, exact d' w`) and
its collapse `typeLower_eqDeg_iff : typeLower (eqDeg μ) d w ↔ atLeastDeg μ d w`
live in `Core/Scales/Scale.lean`. Numerals are the `id`-instantiation:
`typeLower bareMeaning m n ↔ atLeastMeaning m n` follows by definitional
unfolding (`bareMeaning ≡ eqDeg id`, `atLeastMeaning ≡ atLeastDeg id`).

The general theorem `Core.Scale.distinct_no_universal_witness` rules out
the alternative universal-closure reading of Partee's iota. -/

/-- The numeral instantiation of `Core.Scale.typeLower_eqDeg_iff`. -/
theorem typeLower_bareMeaning_iff (m n : Nat) :
    Core.Scale.typeLower bareMeaning m n ↔ atLeastMeaning m n :=
  Core.Scale.typeLower_eqDeg_iff id m n

-- ============================================================================
-- Section 7: EXH–Type-Shift Duality (@cite{spector-2013} §6.2 vs @cite{kennedy-2015})
-- ============================================================================

/-! ## EXH and type-shifting are inverses

@cite{spector-2013} (§6.2) presents an approach (from
@cite{chierchia-fox-spector-2012}) where the exact reading of bare numerals
arises from a covert exhaustivity operator: `EXH(≥n) = ≥n ∧ ¬(≥n+1) = (=n)`.
@cite{kennedy-2015} proposes the reverse: the lower-bound reading arises
from type-shifting the exact meaning: `typeShift(=n) = (≥n)`.

Both directions are general theorems on ℕ — the duality is not a
spot-check, it follows from the linear order. For RSA the **pair**
{exact, lower-bound} is what matters; type-shifting is preferable to EXH
because it is independently motivated (Partee's universal),
parameter-free, and grammatically always available (no insertion-site
stipulation). The two halves of the duality are
`exhNumeral_iff_bare` (EXH(≥n) = (=n)) and `typeLower_bareMeaning_iff`
(typeShift(=n) = (≥n)). -/

/-- Scalar exhaustification for numerals: "at least `m` AND NOT at least
    `m+1`" — i.e., "exactly `m`". -/
def exhNumeral (m n : Nat) : Prop :=
  atLeastMeaning m n ∧ ¬ atLeastMeaning (m + 1) n

instance (m n : Nat) : Decidable (exhNumeral m n) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- **EXH(lower-bound) = exact** (general). Exhaustifying the lower-bound
    meaning produces the exact meaning at every world. -/
theorem exhNumeral_iff_bare (m n : Nat) :
    exhNumeral m n ↔ bareMeaning m n := by
  unfold exhNumeral
  show n ≥ m ∧ ¬ n ≥ m + 1 ↔ n = m
  omega

-- ============================================================================
-- Section 8: GQT Bridge (@cite{bylinina-nouwen-2020})
-- ============================================================================

/-! The GQT numeral quantifiers in `Quantifier.lean` (`exactly_n_sem`,
`at_least_n_sem`, `at_most_n_sem`) compute the same truth values as the
named numeral meanings applied to the intersection cardinality. This
connects B&N's quantifier view (type ⟨⟨e,t⟩,⟨e,t⟩,t⟩) to the Kennedy
maximality view (type ⟨d,t⟩). -/

section GQTBridge
open Classical Core.IntensionalLogic Semantics.Quantification

/-- GQT "at least `n`" agrees with `atLeastMeaning` on intersection cardinality. -/
theorem gqt_atLeast_agrees (m : Frame) [Fintype m.Entity]
    (n : Nat) (R S : m.Entity → Prop) :
    Quantifier.at_least_n_sem m n R S ↔
    atLeastMeaning n (Quantifier.count (fun x : m.Entity => R x ∧ S x)) :=
  Iff.rfl

/-- GQT "at most `n`" agrees with `atMostMeaning` on intersection cardinality. -/
theorem gqt_atMost_agrees (m : Frame) [Fintype m.Entity]
    (n : Nat) (R S : m.Entity → Prop) :
    Quantifier.at_most_n_sem m n R S ↔
    atMostMeaning n (Quantifier.count (fun x : m.Entity => R x ∧ S x)) :=
  Iff.rfl

/-- GQT "exactly `n`" agrees with `bareMeaning` on intersection cardinality. -/
theorem gqt_exactly_agrees (m : Frame) [Fintype m.Entity]
    (n : Nat) (R S : m.Entity → Prop) :
    Quantifier.exactly_n_sem m n R S ↔
    bareMeaning n (Quantifier.count (fun x : m.Entity => R x ∧ S x)) :=
  Iff.rfl

end GQTBridge

end Semantics.Numerals
