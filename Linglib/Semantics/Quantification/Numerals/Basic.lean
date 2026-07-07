/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Order.Comparison
import Linglib.Semantics.Exhaustification.Chain
import Linglib.Semantics.Degree.Predicate
import Linglib.Semantics.Quantification.Quantifier
import Linglib.Syntax.Numeral.Basic
import Mathlib.Order.Interval.Set.Basic

/-!
# Unified Numeral Semantics
[blok-2015] [chierchia-fox-spector-2012] [fox-2007]
[goodman-stuhlmuller-2013] [horn-1972] [kennedy-2015]
[hackl-2000] [link-1983] [partee-1987] [spector-2013]

The numeral surface forms ("three", "more than three", "at least three", "at
most three", "fewer than three") are five `Nat`-instantiations of
[kennedy-2015]'s unified de-Fregean GQ
`λP. max{d | #P ≥ d} REL m`, captured by `Core.Order.Comparison.over`. Each named
meaning is the corresponding `Core.Order.Comparison.{eq,gt,lt,ge,le}.over id`
specialization, and so inherits the scale infrastructure (maximal informativity,
monotonicity, density) by construction.

The only theory disagreement is the bare-numeral semantics:

| Theory      | Bare "three" | bare semantics    |
|-------------|--------------|-------------------|
| Lower-bound | ≥3           | `atLeastMeaning`  |
| Exact       | =3           | `bareMeaning`     |

Modified numerals are theory-independent — everyone agrees "more than 3"
means `> 3`. The Class A / Class B distinction ([geurts-nouwen-2007],
[nouwen-2010]) reduces to whether the modifier's comparison keeps its
interval endpoint; see `Core.Order.Comparison.boundary_mem`.

## Sections

1. Modifier classification (Class A/B, Bound direction)
2. Numeral meaning functions (5 `def`s over `Core.Order.Comparison.{...}.over id`)
3. `BareNumeral`; `Comparison` interpretation (`Entry.denoteUnder`)
4. Alternative sets (Kennedy §4.1)
5. Class A/B corollaries, anti-Horn-scale corollaries
6. Type-shifting (Kennedy §3.1)
7. EXH–type-shift duality (Spector §6.2)
8. GQT bridge (Bylinina & Nouwen)

Precision/halo machinery lives in `Numerals/Precision.lean`.
-/

namespace Semantics.Numerals

-- ============================================================================
-- Section 1: Modifier Classification
-- ============================================================================

/-- Class A (strict `>`, `<`) vs Class B (non-strict `≥`, `≤`) modified
numerals — a descriptive split due to [nouwen-2010].

Truth-conditionally the split is the reflexive/irreflexive boundary behavior:
Class A EXCLUDES the bare-numeral world, Class B INCLUDES it (Class B iff the
comparison's interval keeps its endpoint; see
`Core.Order.Comparison.boundary_mem`). The further claim that this predicts
a *categorical* ignorance-implicature pattern (Class B carries ignorance, Class
A not) is contested: [schwarz-buccola-hamilton-2012] show *at most* and *up
to* dissociate (so "Class B" is not one class), and
[cremers-coppock-dotlacil-roelofsen-2022] find the ignorance contrast
graded and QUD-dependent rather than categorical; [enguehard-2018] derives
comparative-numeral inferences from granularity scales rather than from the
strict/non-strict relation type.

Truth-conditionally the split is `Core.Order.Comparison.boundary_mem` (the
non-strict comparison's interval keeps its endpoint). -/
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
of the corresponding `Core.Order.Comparison.over` degree property. They capture
[kennedy-2015]'s

  ⟦modifier m⟧ = λP. max{d | #P ≥ d} REL m

where `n` plays the role of `max{d | #P ≥ d}` and `m` is the numeral.
`bareMeaning` is the exact (Kennedy) reading; the lower-bound (Horn) reading
of bare numerals is `atLeastMeaning`. Grounding in `Comparison.over` makes the
density predictions (`Comparison.antitone_ge_over`, `moreThan_noMaxInf`,
`atLeast_hasMaxInf`, etc.) hold by construction. -/

/-- Bare numeral meaning (exact reading): `n = m`. -/
def bareMeaning : Nat → Nat → Prop := fun m n => n ∈ Core.Order.Comparison.eq.over id m

/-- "More than `m`": `n > m`. -/
def moreThanMeaning : Nat → Nat → Prop := fun m n => n ∈ Core.Order.Comparison.gt.over id m

/-- "Fewer than `m`": `n < m`. -/
def fewerThanMeaning : Nat → Nat → Prop := fun m n => n ∈ Core.Order.Comparison.lt.over id m

/-- "At least `m`": `n ≥ m`. -/
def atLeastMeaning : Nat → Nat → Prop := fun m n => n ∈ Core.Order.Comparison.ge.over id m

/-- "At most `m`": `n ≤ m`. -/
def atMostMeaning : Nat → Nat → Prop := fun m n => n ∈ Core.Order.Comparison.le.over id m

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
-- Section 3: BareNumeral and Comparison interpretation
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

/-! The five numeral forms are the five `Core.Order.Comparison`s applied to an
    argument; the object lives in `Typology/Numeral/Basic.lean`. Here we give the
    semantics: the order relation each comparison names, and the theory-choice
    meaning. -/

/-- Denotation of a numeral word `e`: the predicate over cardinalities it is true
    of, under a choice of bare-numeral semantics (`bareMeaning` exact vs.
    `atLeastMeaning` lower-bound — only the bare `.eq` form consults `bare`; the
    four modified forms are theory-independent `Comparison.over` denotations). A
    method on the numeral object, mirroring `PersonalPronoun.denote`. -/
def _root_.Numeral.Entry.denoteUnder (e : Numeral.Entry) (bare : Nat → Nat → Prop) :
    Nat → Prop :=
  match e.comparison with
  | .eq => bare e.argument
  | c   => fun n => n ∈ c.over id e.argument

instance (e : Numeral.Entry) (bare : Nat → Nat → Prop)
    [∀ m n, Decidable (bare m n)] (n : Nat) : Decidable (e.denoteUnder bare n) := by
  obtain ⟨_, c, _⟩ := e
  cases c <;>
    simp only [Numeral.Entry.denoteUnder] <;>
    infer_instance

/-- The bare-world meaning of a *modified* numeral word (`comparison ≠ .eq`) is
    endpoint membership in the comparison's interval — connecting `meaning` to
    the interval form. -/
theorem _root_.Numeral.Entry.denoteUnder_boundary (e : Numeral.Entry) (bare : Nat → Nat → Prop)
    (h : e.comparison ≠ .eq) :
    e.denoteUnder bare e.argument ↔ e.argument ∈ e.comparison.interval e.argument := by
  obtain ⟨_, c, _⟩ := e
  cases c <;>
    simp_all [Numeral.Entry.denoteUnder, Core.Order.Comparison.over,
      Core.Order.Comparison.interval]

-- ============================================================================
-- Section 4: Alternative Set ([kennedy-2015] §4.1)
-- ============================================================================

/-- [kennedy-2015]'s single alternative set — the five numeral forms (bare
    plus four modifications) as `Core.Order.Comparison`s. The point is
    **anti-Horn-scale**: there is no fixed scale direction. The Class A / Class B
    split is read off asymmetric entailment (cf. `classA_excludes_bare_world`,
    `classB_includes_bare_world`), not from membership in a pre-split sublist. -/
def kennedyAlternatives : List Core.Order.Comparison :=
  [.eq, .gt, .lt, .ge, .le]

-- ============================================================================
-- Section 5: Class A/B Corollaries and Anti-Horn-Scale Corollaries
-- ============================================================================

/-! Class A/B is the central typological generalization ([geurts-nouwen-2007],
    [nouwen-2010]): strict modifiers (`>`, `<`) exclude the bare-numeral
    world; non-strict modifiers (`≥`, `≤`) include it. Both theorems below are
    now corollaries of `Core.Order.Comparison.boundary_mem` (Class A/B = whether the
    comparison's interval is closed at its endpoint) via `meaning_boundary`. -/

/-- **Class A excludes the bare-numeral world** (universal). A strict comparison
    (`>`, `<`) fails at the boundary `n = m`, regardless of which bare-numeral
    semantics is chosen. Corollary of `boundary_mem`. -/
theorem classA_excludes_bare_world (e : Numeral.Entry) (bare : Nat → Nat → Prop)
    (h : e.comparison.isStrict) :
    ¬ e.denoteUnder bare e.argument := by
  have hne : e.comparison ≠ .eq := by intro heq; rw [heq] at h; exact h
  rw [e.denoteUnder_boundary bare hne, Core.Order.Comparison.boundary_mem]
  exact not_not_intro h

/-- **Class B includes the bare-numeral world** (universal). A non-strict
    *modifier* (`≥`, `≤`) holds at the boundary `n = m`, regardless of which
    bare-numeral semantics is chosen. Corollary of `boundary_mem`. -/
theorem classB_includes_bare_world (e : Numeral.Entry) (bare : Nat → Nat → Prop)
    (h : ¬ e.comparison.isStrict) (hne : e.comparison ≠ .eq) :
    e.denoteUnder bare e.argument := by
  rw [e.denoteUnder_boundary bare hne, Core.Order.Comparison.boundary_mem]
  exact h

/-- Bare numeral pointwise entails "at least `m`" — the `id`-specialization
    of `Degree.eqOver_imp_geOver`. -/
theorem classB_entailed_by_bare (m n : Nat) :
    bareMeaning m n → atLeastMeaning m n :=
  Degree.eqOver_imp_geOver id m n

/-- Exact bare numerals are not upward-monotone: the `id`-specialization of
    `Degree.eqOver_not_upward_monotone` (witness `d = 3`, `d' = 4`). -/
theorem bare_not_upward_monotone :
    ¬ ∀ m m' n, m ≤ m' → bareMeaning m n → bareMeaning m' n := by
  intro h
  exact Degree.eqOver_not_upward_monotone (W := Nat) id (d := 3) (d' := 4)
    (by decide) (by decide) (w := 3) rfl
    (fun x y hxy hex => h x y 3 hxy hex)

/-- Bare numerals are not downward-monotone either, so they fail the
    Horn-scale criterion in both directions. The `id`-specialization of
    `Degree.eqOver_not_downward_monotone`. -/
theorem bare_not_downward_monotone :
    ¬ ∀ m m' n, m' ≤ m → bareMeaning m n → bareMeaning m' n := by
  intro h
  exact Degree.eqOver_not_downward_monotone (W := Nat) id (d := 3) (d' := 2)
    (by decide) (by decide) (w := 3) rfl
    (fun x y hyx hex => h x y 3 hyx hex)

/-- "At least `m`" is strictly weaker than "bare `m`" — the `id`-specialization
    of `Degree.geOver_strictly_weaker_than_eqOver` (witness `d' = m+1`). -/
theorem atLeast_strictly_weaker_than_bare (m : Nat) :
    atLeastMeaning m (m + 1) ∧ ¬ bareMeaning m (m + 1) :=
  Degree.geOver_strictly_weaker_than_eqOver id (Nat.lt_succ_self m) (w := m + 1) rfl

/-- "More than `m`" and "bare `m`" have disjoint denotations — the
    `id`-specialization of `Degree.gtOver_disjoint_eqOver`. -/
theorem moreThan_disjoint_from_bare (m n : Nat) :
    ¬ (bareMeaning m n ∧ moreThanMeaning m n) :=
  Degree.gtOver_disjoint_eqOver id m n

-- ============================================================================
-- Section 6: Type-Shifting ([kennedy-2015] §3.1)
-- ============================================================================

/-! ## De-Fregean type-shifting: exact → lower-bound

The general operation `Degree.typeLower` (`∃ d' ≥ d, exact d' w`) and
its collapse `typeLower_eqOver_iff` (existentially lowering `Comparison.eq.over μ`
yields `Comparison.ge.over μ`) live in `Semantics/Degree/Predicate.lean`.
Numerals are the `id`-instantiation: `typeLower bareMeaning m n ↔ atLeastMeaning m n`
follows by definitional unfolding (`bareMeaning ≡ Comparison.eq.over id`,
`atLeastMeaning ≡ Comparison.ge.over id`).

The general theorem `Degree.distinct_no_universal_witness` rules out
the alternative universal-closure reading of Partee's iota. -/

/-- The numeral instantiation of `Degree.typeLower_eqOver_iff`. -/
theorem typeLower_bareMeaning_iff (m n : Nat) :
    Degree.typeLower bareMeaning m n ↔ atLeastMeaning m n :=
  Degree.typeLower_eqOver_iff id m n

-- ============================================================================
-- Section 7: EXH–Type-Shift Duality ([spector-2013] §6.2 vs [kennedy-2015])
-- ============================================================================

/-! ## EXH and type-shifting are inverses

[spector-2013] (§6.2) presents an approach (from
[chierchia-fox-spector-2012]) where the exact reading of bare numerals
arises from a covert exhaustivity operator: `EXH(≥n) = ≥n ∧ ¬(≥n+1) = (=n)`.
[kennedy-2015] proposes the reverse: the lower-bound reading arises
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

/-- `exhNumeral` is chain-exhaustification against the full Horn scale of
stronger numerals (`Exhaustification.exhChain`): the scale is an entailment
chain, so negating the next-stronger alternative negates them all
(`Exhaustification.exhChain_iff_succ`). -/
theorem exhNumeral_eq_exhChain (m n : Nat) :
    exhNumeral m n ↔
      Exhaustification.exhChain (fun k => atLeastMeaning (m + k)) 0 n := by
  rw [Exhaustification.exhChain_iff_succ
      (fun j k hjk d hd => by
        simp only [atLeastMeaning_def, ge_iff_le] at hd ⊢; omega)
      Nat.zero_lt_one fun j hj => hj]
  simp [exhNumeral]

-- ============================================================================
-- Section 8: GQT Bridge ([bylinina-nouwen-2020])
-- ============================================================================

/-! The GQT numeral quantifiers in `Quantifier.lean` (`exactly_n_sem`,
`at_least_n_sem`, `at_most_n_sem`) compute the same truth values as the
named numeral meanings applied to the intersection cardinality. This
connects B&N's quantifier view (type ⟨⟨e,t⟩,⟨e,t⟩,t⟩) to the Kennedy
maximality view (type ⟨d,t⟩). -/

section GQTBridge
open Classical Intensional Quantification

/-- GQT "at least `n`" agrees with `atLeastMeaning` on intersection cardinality. -/
theorem gqt_atLeast_agrees {α : Type*} [Fintype α]
    (n : Nat) (R S : α → Prop) :
    at_least_n_sem n R S ↔
    atLeastMeaning n (count (fun x : α => R x ∧ S x)) :=
  Iff.rfl

/-- GQT "at most `n`" agrees with `atMostMeaning` on intersection cardinality. -/
theorem gqt_atMost_agrees {α : Type*} [Fintype α]
    (n : Nat) (R S : α → Prop) :
    at_most_n_sem n R S ↔
    atMostMeaning n (count (fun x : α => R x ∧ S x)) :=
  Iff.rfl

/-- GQT "exactly `n`" agrees with `bareMeaning` on intersection cardinality. -/
theorem gqt_exactly_agrees {α : Type*} [Fintype α]
    (n : Nat) (R S : α → Prop) :
    exactly_n_sem n R S ↔
    bareMeaning n (count (fun x : α => R x ∧ S x)) :=
  Iff.rfl

end GQTBridge

/-! ### Denotation of the `Numeral` object

The lexical numeral object (`Core.Order.Comparison`, `Numeral.Entry`) is owned by
`Typology/Numeral/Basic.lean`; this section is the *semantics* side — it imports
that object and provides its `Comparison.over` denotation, mirroring how
`Semantics/Reference/PronounDenotation.lean` denotes the `PersonalPronoun` object.
The denotation is **by construction** a `Core.Order.Comparison.over`, so every lemma
about `Comparison.over` transfers to every numeral entry. `Entry.denoteUnder` (the
cardinal, theory-parameterized reading) is in Section 3. -/

/-- Denotation of a numeral entry against a measure `μ : E → α` and a magnitude
    `m`: [kennedy-2015]'s de-Fregean GQ `λx. REL (μ x) m`. The measure and
    magnitude are supplied compositionally; bare cardinals take `μ = id`,
    `α = ℕ`. -/
def _root_.Numeral.Entry.denote {E α : Type*} [LinearOrder α]
    (e : Numeral.Entry) (μ : E → α) (m : α) : E → Prop :=
  e.comparison.over μ m

/-- Bare cardinal denotation: count with `μ = id` and the entry's own argument. -/
def _root_.Numeral.Entry.denoteCard (e : Numeral.Entry) : Nat → Prop :=
  e.denote id e.argument

/-- The bare-comparison cardinal recovers `bareMeaning` (definitionally). -/
theorem denoteCard_eq_bareMeaning (e : Numeral.Entry) (h : e.comparison = .eq) :
    e.denoteCard = bareMeaning e.argument := by
  simp only [Numeral.Entry.denoteCard, Numeral.Entry.denote, h]; rfl

/-- The "at least" cardinal recovers `atLeastMeaning`. -/
theorem denoteCard_eq_atLeastMeaning (e : Numeral.Entry) (h : e.comparison = .ge) :
    e.denoteCard = atLeastMeaning e.argument := by
  simp only [Numeral.Entry.denoteCard, Numeral.Entry.denote, h]; rfl

/-- **Class A/B boundary behaviour, free for every numeral entry.** At an entity
    whose measure equals the magnitude, the numeral holds iff its comparison is
    non-strict (bare `=`, Class B `≥`/`≤`) and fails for the strict Class A
    comparisons (`>`/`<`). Inherited from `Comparison.over`, no per-entry proof. -/
theorem denote_at_boundary {E α : Type*} [LinearOrder α]
    (e : Numeral.Entry) (μ : E → α) (m : α) {x : E} (h : μ x = m) :
    e.denote μ m x ↔ ¬ e.comparison.isStrict := by
  show x ∈ e.comparison.over μ m ↔ ¬ e.comparison.isStrict
  rw [Core.Order.Comparison.mem_over, ← Core.Order.Comparison.mem_interval, h,
    Core.Order.Comparison.boundary_mem]

end Semantics.Numerals
