import Linglib.Core.Scales.Scale
import Linglib.Semantics.Quantification.Quantifier
import Linglib.Typology.Numeral.Basic
import Mathlib.Order.Interval.Set.Basic

/-!
# Unified Numeral Semantics
@cite{blok-2015} @cite{chierchia-fox-spector-2012} @cite{fox-2007}
@cite{goodman-stuhlmuller-2013} @cite{horn-1972} @cite{kennedy-2015}
@cite{hackl-2000} @cite{link-1983} @cite{partee-1987} @cite{spector-2013}

The numeral surface forms ("three", "more than three", "at least three", "at
most three", "fewer than three") are five `Nat`-instantiations of
@cite{kennedy-2015}'s unified de-Fregean GQ
`λP. max{d | #P ≥ d} REL m`, captured in `Core.Scale.relationalGQ`. Each named
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
underlying relation; see `Core.Scale.relationalGQ_refl_at_boundary` and
`Core.Scale.relationalGQ_irrefl_at_boundary`.

## Sections

1. Modifier classification (Class A/B, Bound direction)
2. Numeral meaning functions (5 `def`s over `Core.Scale.{...}Deg id`)
3. `BareNumeral`; `Comparison` interpretation (`Entry.denoteUnder`)
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

/-- Class A (strict `>`, `<`) vs Class B (non-strict `≥`, `≤`) modified
numerals — a descriptive split due to @cite{nouwen-2010}.

Truth-conditionally the split is the reflexive/irreflexive boundary behavior:
Class A EXCLUDES the bare-numeral world, Class B INCLUDES it (Class B iff the
underlying relation is reflexive; see `Core.Scale.relationalGQ_refl_at_boundary`
and `Core.Scale.Comparison.boundary_mem`). The further claim that this predicts
a *categorical* ignorance-implicature pattern (Class B carries ignorance, Class
A not) is contested: @cite{schwarz-buccola-hamilton-2012} show *at most* and *up
to* dissociate (so "Class B" is not one class), and
@cite{cremers-coppock-dotlacil-roelofsen-2022} find the ignorance contrast
graded and QUD-dependent rather than categorical; @cite{enguehard-2018} derives
comparative-numeral inferences from granularity scales rather than from the
strict/non-strict relation type. -/
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

/-! The five numeral forms are the five `Core.Scale.Comparison`s applied to an
    argument; the object lives in `Typology/Numeral/Basic.lean`. Here we give the
    semantics: the order relation each comparison names, and the theory-choice
    meaning. -/

/-- Denotation of a numeral word `e`: the predicate over cardinalities it is true
    of, under a choice of bare-numeral semantics (`bareMeaning` exact vs.
    `atLeastMeaning` lower-bound — only the bare `.eq` form consults `bare`; the
    four modified forms are theory-independent `relationalGQ` denotations). A
    method on the numeral object, mirroring `Pronoun.Entry.denote`. -/
def _root_.Numeral.Entry.denoteUnder (e : Numeral.Entry) (bare : Nat → Nat → Prop) :
    Nat → Prop :=
  match e.comparison with
  | .eq => bare e.argument
  | c   => Core.Scale.relationalGQ c.rel id e.argument

instance (e : Numeral.Entry) (bare : Nat → Nat → Prop)
    [∀ m n, Decidable (bare m n)] (n : Nat) : Decidable (e.denoteUnder bare n) := by
  obtain ⟨_, c, _⟩ := e
  cases c <;>
    simp only [Numeral.Entry.denoteUnder, Core.Scale.Comparison.rel, Core.Scale.relationalGQ] <;>
    infer_instance

/-- The bare-world meaning of a *modified* numeral word (`comparison ≠ .eq`) is
    endpoint membership in the comparison's interval — connecting `meaning` to
    the interval form. -/
theorem _root_.Numeral.Entry.denoteUnder_boundary (e : Numeral.Entry) (bare : Nat → Nat → Prop)
    (h : e.comparison ≠ .eq) :
    e.denoteUnder bare e.argument ↔ e.argument ∈ e.comparison.interval e.argument := by
  obtain ⟨_, c, _⟩ := e
  cases c <;>
    simp_all [Numeral.Entry.denoteUnder, Core.Scale.Comparison.interval,
      Core.Scale.relationalGQ, Core.Scale.Comparison.rel]

-- ============================================================================
-- Section 4: Alternative Set (@cite{kennedy-2015} §4.1)
-- ============================================================================

/-- @cite{kennedy-2015}'s single alternative set — the five numeral forms (bare
    plus four modifications) as `Core.Scale.Comparison`s. The point is
    **anti-Horn-scale**: there is no fixed scale direction. The Class A / Class B
    split is read off asymmetric entailment (cf. `classA_excludes_bare_world`,
    `classB_includes_bare_world`), not from membership in a pre-split sublist. -/
def kennedyAlternatives : List Core.Scale.Comparison :=
  [.eq, .gt, .lt, .ge, .le]

-- ============================================================================
-- Section 5: Class A/B Corollaries and Anti-Horn-Scale Corollaries
-- ============================================================================

/-! Class A/B is the central typological generalization (@cite{geurts-nouwen-2007},
    @cite{nouwen-2010}): strict modifiers (`>`, `<`) exclude the bare-numeral
    world; non-strict modifiers (`≥`, `≤`) include it. Both theorems below are
    now corollaries of `Core.Scale.Comparison.boundary_mem` (Class A/B = whether the
    comparison's interval is closed at its endpoint) via `meaning_boundary`. -/

/-- **Class A excludes the bare-numeral world** (universal). A strict comparison
    (`>`, `<`) fails at the boundary `n = m`, regardless of which bare-numeral
    semantics is chosen. Corollary of `boundary_mem`. -/
theorem classA_excludes_bare_world (e : Numeral.Entry) (bare : Nat → Nat → Prop)
    (h : e.comparison.isStrict) :
    ¬ e.denoteUnder bare e.argument := by
  have hne : e.comparison ≠ .eq := by intro heq; rw [heq] at h; exact h
  rw [e.denoteUnder_boundary bare hne, Core.Scale.Comparison.boundary_mem]
  exact not_not_intro h

/-- **Class B includes the bare-numeral world** (universal). A non-strict
    *modifier* (`≥`, `≤`) holds at the boundary `n = m`, regardless of which
    bare-numeral semantics is chosen. Corollary of `boundary_mem`. -/
theorem classB_includes_bare_world (e : Numeral.Entry) (bare : Nat → Nat → Prop)
    (h : ¬ e.comparison.isStrict) (hne : e.comparison ≠ .eq) :
    e.denoteUnder bare e.argument := by
  rw [e.denoteUnder_boundary bare hne, Core.Scale.Comparison.boundary_mem]
  exact h

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
open Classical Core.Logic.Intensional Semantics.Quantification

/-- GQT "at least `n`" agrees with `atLeastMeaning` on intersection cardinality. -/
theorem gqt_atLeast_agrees {α : Type*} [Fintype α]
    (n : Nat) (R S : α → Prop) :
    Quantifier.at_least_n_sem n R S ↔
    atLeastMeaning n (Quantifier.count (fun x : α => R x ∧ S x)) :=
  Iff.rfl

/-- GQT "at most `n`" agrees with `atMostMeaning` on intersection cardinality. -/
theorem gqt_atMost_agrees {α : Type*} [Fintype α]
    (n : Nat) (R S : α → Prop) :
    Quantifier.at_most_n_sem n R S ↔
    atMostMeaning n (Quantifier.count (fun x : α => R x ∧ S x)) :=
  Iff.rfl

/-- GQT "exactly `n`" agrees with `bareMeaning` on intersection cardinality. -/
theorem gqt_exactly_agrees {α : Type*} [Fintype α]
    (n : Nat) (R S : α → Prop) :
    Quantifier.exactly_n_sem n R S ↔
    bareMeaning n (Quantifier.count (fun x : α => R x ∧ S x)) :=
  Iff.rfl

end GQTBridge

/-! ### Denotation of the `Typology.Numeral` object

The lexical numeral object (`Core.Scale.Comparison`, `Numeral.Entry`) is owned by
`Typology/Numeral/Basic.lean`; this section is the *semantics* side — it imports
that object and provides its `relationalGQ` denotation, mirroring how
`Semantics/Reference/PronounDenotation.lean` denotes the `Pronoun.Entry` object.
The denotation is **by construction** a `Core.Scale.relationalGQ`, so every lemma
about `relationalGQ` transfers to every numeral entry. `Comparison.rel` lives in
`Core.Scale`; `Entry.denoteUnder` (the cardinal, theory-parameterized reading) is
in Section 3. -/

/-- Denotation of a numeral entry against a measure `μ : E → α` and a magnitude
    `m`: @cite{kennedy-2015}'s de-Fregean GQ `λx. REL (μ x) m`. The measure and
    magnitude are supplied compositionally; bare cardinals take `μ = id`,
    `α = ℕ`. -/
def _root_.Numeral.Entry.denote {E α : Type*} [LinearOrder α]
    (e : Numeral.Entry) (μ : E → α) (m : α) : E → Prop :=
  Core.Scale.relationalGQ e.comparison.rel μ m

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
    comparisons (`>`/`<`). Inherited from `relationalGQ`, no per-entry proof. -/
theorem denote_at_boundary {E α : Type*} [LinearOrder α]
    (e : Numeral.Entry) (μ : E → α) (m : α) {x : E} (h : μ x = m) :
    e.denote μ m x ↔ ¬ e.comparison.isStrict := by
  obtain ⟨_, c, _⟩ := e
  cases c <;>
    simp [Numeral.Entry.denote, Core.Scale.Comparison.rel, Core.Scale.Comparison.isStrict,
      Core.Scale.relationalGQ, h]

end Semantics.Numerals
