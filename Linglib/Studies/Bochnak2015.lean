import Linglib.Semantics.Degree.Delineation

/-!
# Bochnak 2015: the Degree Semantics Parameter and Washo

[bochnak-2015] (Semantics and Pragmatics 8) argues that Washo systematically
lacks degree morphology — comparatives, measure phrases, equatives,
superlatives, degree adverbs — and analyzes its gradable predicates as
[klein-1980]-style vague predicates (5): type ⟨e,t⟩ relative to a comparison
class, with no degree variable, the negative setting of [beck-2009]'s Degree
Semantics Parameter (7). Comparison is the conjoined construction (14): one
clause asserts the positive and the other denies it (with -e:s) or asserts an
antonym, and the truth conditions (27) entail a comparison through the
Consistency Constraints (28), rendered by the sound and complete delineations
of `Semantics/Degree/Delineation.lean`. Both of [kennedy-2007a]'s implicitness
diagnostics follow: incompatibility with absolute-standard predicates (24),
and the crisp-judgment effect (21) under the Similarity Constraint (20),
stated here with the margin-of-error order (60) from the paper's van Rooij
alternative ([van-rooij-2011a]).

## Main definitions

* `tallEnglish`, `washoConjoined` — the degree-based entry (1) and the
  per-context conjoined-comparison truth conditions (27).
* `bentPred`, `straightPred` — [kennedy-2007] min- and max-standard absolute
  predicates.
* `marginOrder` — the margin-of-error order (60): implicit comparison at
  margin `ε`, explicit comparison at `ε = 0`.

## Main results

* `washoConjoined_witnesses_comparativeSem`,
  `comparativeSem_measureDelineation_iff_degree` — (27) closes existentially
  to [klein-1980]'s comparative, and coincides with height comparison for a
  measure-induced delineation, without a degree variable in the entry.
* `washoConjoined_norm_related` — (29): conjoined comparison is obligatorily
  norm-related.
* `eq24a_bent_straight_fails`, `eq24b_bent_notbent_fails`,
  `eq24c_straight_notstraight_fails`, `english_more_bent_succeeds` — the
  absolute-standard diagnostic: every conjoined pairing fails on two bent
  rods where the explicit comparative succeeds.
* `marginOrder_irrefl`, `marginOrder_intervalOrder`,
  `marginOrder_semitransitive` — (60) satisfies the semi-order axioms (58);
  `marginOrder_zero_iff` and `marginOrder_zero_almostConnected` — at `ε = 0`
  it is the strict weak order (59) of explicit comparison.
* `crisp_pair_not_marginOrder`, `crisp_pair_marginOrder_zero` — a
  minimally-different pair defeats implicit comparison at any positive margin
  and satisfies explicit comparison, the (21) contrast.
* `cc_b_requires_shared_class` — footnote 11: the comparison entailment needs
  a single comparison class shared by both conjuncts.

## References

* [bochnak-2015] — the paper.
* [beck-2009] — the Degree Semantics Parameter, proposed for Motu.
* [klein-1980] — the vague-predicate semantics and Consistency Constraints.
* [kennedy-2007a], [kennedy-2007] — implicit vs. explicit comparison; the
  relative vs. absolute standard typology.
* [fara-2000] — the Similarity Constraint, with [klein-1980].
* [van-rooij-2011a] — semi-orders and the margin of error.
-/

namespace Bochnak2015

open Degree.Delineation

variable {E : Type*}

/-! ### The two lexical shapes ((1), (5))

The paper's proposal is a contrast in lexical type. English *tall* (1) takes
a degree argument for degree morphology to bind; Washo entries (5) are
delineations, type `ComparisonClass E → E → Prop`, with — p. 6:4 — "no
measure function, and no degree variable at all". No Washo constant is
defined: the theorems below quantify over delineations, keeping the
no-measure discipline visible in the types. -/

/-- (1): degree-based `[[tall]] = λd λx. height(x) ≥ d`, type ⟨d,⟨e,t⟩⟩. -/
def tallEnglish (height : E → ℕ) (d : ℕ) (x : E) : Prop :=
  height x ≥ d

/-! ### Conjoined comparison ((14), (27)–(29)) -/

/-- (27): the conjoined comparison (14) in context `C` — `x` counts as G and
`y` does not. No comparative morpheme, overt or covert, is involved. -/
def washoConjoined (del : ComparisonClass E → E → Prop)
    (C : ComparisonClass E) (x y : E) : Prop :=
  del C x ∧ ¬ del C y

/-- [klein-1980]'s existential comparative is the closure of (27) over
contexts: a conjoined comparison witnesses the discriminating class. -/
theorem washoConjoined_witnesses_comparativeSem
    (del : ComparisonClass E → E → Prop) {C : ComparisonClass E} {x y : E}
    (h : washoConjoined del C x y) : comparativeSem del x y :=
  ⟨C, h⟩

/-- (29): where the target does not count as G — both individuals short, in
the paper's context — the conjoined comparison is simply false. Conjoined
comparison is obligatorily norm-related. -/
theorem washoConjoined_norm_related (del : ComparisonClass E → E → Prop)
    {C : ComparisonClass E} {x y : E} (h : ¬ del C x) :
    ¬ washoConjoined del C x y :=
  fun ⟨hx, _⟩ => h hx

/-- For a measure-induced delineation the closure of (27) coincides with
height comparison — the (28) entailment, through `IsSoundDelineation` and
`IsCompleteDelineation` (the paper's Consistency Constraints in
`Semantics/Degree/Delineation.lean`), with no degree variable in the entry. -/
theorem comparativeSem_measureDelineation_iff_degree (height : E → ℕ) (a b : E) :
    comparativeSem (measureDelineation height) a b ↔ height b < height a :=
  comparativeSem_iff_of_sound_and_complete (R := fun a b => height b < height a)

/-! ### Test 1: absolute standards ((23)–(24))

Two rods, both slightly bent, one more than the other. The English explicit
comparative (23a) is true; each Washo conjoined attempt (24a–c) requires
*straight* or *not bent* to hold of one rod, which is false. -/

section AbsoluteStandard

variable (curvature : E → ℕ) (x y : E)

/-- [kennedy-2007] min-standard predicate (*bent*, *wet*): the measure
exceeds the scale's bottom. The standard is the endpoint, not a comparison
class. -/
def bentPred : Prop := curvature x > 0

/-- [kennedy-2007] max-standard predicate (*straight*, *dry*): the measure
sits at the endpoint. The lexical antonym of `bentPred`. -/
def straightPred : Prop := curvature x = 0

/-- (24a): *bent ∧ straight* fails — both rods have nonzero curvature. -/
theorem eq24a_bent_straight_fails (_hx : bentPred curvature x)
    (hy : bentPred curvature y) :
    ¬ (bentPred curvature x ∧ straightPred curvature y) :=
  fun ⟨_, h⟩ => absurd h (Nat.pos_iff_ne_zero.mp hy)

/-- (24b): *bent ∧ ¬bent* fails — the second rod is bent too. -/
theorem eq24b_bent_notbent_fails (_hx : bentPred curvature x)
    (hy : bentPred curvature y) :
    ¬ (bentPred curvature x ∧ ¬ bentPred curvature y) :=
  fun ⟨_, h⟩ => h hy

/-- (24c): *straight ∧ ¬straight* fails — the first rod is not straight. -/
theorem eq24c_straight_notstraight_fails (hx : bentPred curvature x)
    (_hy : bentPred curvature y) :
    ¬ (straightPred curvature x ∧ ¬ straightPred curvature y) :=
  fun ⟨h, _⟩ => absurd h (Nat.pos_iff_ne_zero.mp hx)

/-- (23a): the explicit comparative succeeds in the same scenario — any
nonzero difference suffices. -/
theorem english_more_bent_succeeds (hmore : curvature x > curvature y) :
    ∃ d, tallEnglish curvature d x ∧ ¬ tallEnglish curvature d y :=
  ⟨curvature x, le_refl _, by simp [tallEnglish]; omega⟩

end AbsoluteStandard

/-! ### Test 2: crisp judgments and the margin of error ((20)–(22), (58)–(60))

The Similarity Constraint (20) bars separating a minimally-different pair,
so the conjoined form is infelicitous on two nearly-equal ladders (21) —
salvageable with hedges like *wewš* 'almost' (22). The paper's van Rooij
section makes the margin formal: implicit comparison rests on the
margin-of-error order (60), a semi-order (58); explicit comparison is its
`ε = 0` case, the strict weak order (59). -/

section MarginOfError

variable (μ : E → ℕ) (ε : ℕ) {x y z v w : E}

/-- (60): `x` exceeds `y` by more than the margin of error `ε`. -/
def marginOrder (x y : E) : Prop := μ y + ε < μ x

/-- (58a): irreflexivity. -/
theorem marginOrder_irrefl : ¬ marginOrder μ ε x x := by
  simp [marginOrder]

/-- (58b): the interval-order condition. -/
theorem marginOrder_intervalOrder (h₁ : marginOrder μ ε x y)
    (h₂ : marginOrder μ ε v w) :
    marginOrder μ ε x w ∨ marginOrder μ ε v y := by
  simp only [marginOrder] at *; omega

/-- (58c): semi-transitivity. -/
theorem marginOrder_semitransitive (h₁ : marginOrder μ ε x y)
    (h₂ : marginOrder μ ε y z) (v : E) :
    marginOrder μ ε x v ∨ marginOrder μ ε v z := by
  simp only [marginOrder] at *; omega

/-- At `ε = 0` the margin order is plain measure comparison. -/
theorem marginOrder_zero_iff : marginOrder μ 0 x y ↔ μ y < μ x := by
  simp [marginOrder]

/-- (59c): at `ε = 0` the order is almost connected — with (58a) and
transitivity, the strict weak order of explicit comparison. -/
theorem marginOrder_zero_almostConnected (h : marginOrder μ 0 x y) (z : E) :
    marginOrder μ 0 x z ∨ marginOrder μ 0 z y := by
  simp only [marginOrder] at *; omega

/-- (21): a minimally-different pair never clears a positive margin — the
crisp-judgment infelicity of the conjoined form. -/
theorem crisp_pair_not_marginOrder (hε : 1 ≤ ε) (hclose : μ x = μ y + 1) :
    ¬ marginOrder μ ε x y := by
  simp only [marginOrder]; omega

/-- The same pair satisfies explicit comparison: `-er` needs only a nonzero
difference. -/
theorem crisp_pair_marginOrder_zero (hclose : μ x = μ y + 1) :
    marginOrder μ 0 x y := by
  simp only [marginOrder]; omega

end MarginOfError

/-! ### Footnote 11: the shared comparison class -/

/-- Footnote 11: the (28) entailment requires one comparison class shared by
both conjuncts of (27). Soundness constrains only same-class separations, so
a delineation sound for `R` can separate `x` from `y` across two distinct
classes while `R x y` fails. -/
theorem cc_b_requires_shared_class :
    ∃ (Entity : Type) (del : ComparisonClass Entity → Entity → Prop)
      (R : Entity → Entity → Prop),
      IsSoundDelineation del R ∧
      ∃ (C₁ C₂ : ComparisonClass Entity) (x y : Entity),
        del C₁ x ∧ ¬ del C₂ y ∧ ¬ R x y := by
  refine ⟨Bool, fun C x => x = true ∧ true ∈ C, fun a b => a = true ∧ b = false,
    ⟨?_⟩, {true}, {false}, true, true, ⟨rfl, rfl⟩, ?_, ?_⟩
  · rintro C x y ⟨rfl, htC⟩ hneg
    refine ⟨rfl, ?_⟩
    cases y with
    | true => exact absurd ⟨rfl, htC⟩ hneg
    | false => rfl
  · rintro ⟨_, h⟩
    simp at h
  · rintro ⟨_, h⟩
    exact Bool.noConfusion h

end Bochnak2015
