import Linglib.Semantics.Reference.Rigidity
import Linglib.Semantics.Degree.Basic
import Linglib.Semantics.Degree.MeasurePhrase
import Linglib.Semantics.Degree.Delineation
import Linglib.Data.Examples.VonStechow1984
import Mathlib.Tactic.Linarith

/-!
# von Stechow (1984): Comparing Semantic Theories of Comparison

This file formalizes the parts of [von-stechow-1984]'s comparison of eight semantic theories
of the comparative that turn on its own synthesis, Russellian definite descriptions of degrees
with an ACTUALLY operator. Russell's yacht ambiguity (1) is the presence or absence of ACTUALLY
in the than-clause: the de re reading compares the believed length with the actual one and the
de dicto reading compares a length with itself, hence is contradictory (`deReComparative`,
`deDictoComparative`), and the ambiguous counterfactual (26) is read the same way. A
disjunctive than-clause entails both disjuncts (v), the downward entailingness that licenses
its negative polarity items (§VI); a modal comparative (x) compares maxima over the accessible
worlds (§VIII); and Klein's degree-free ordering agrees with degree comparison on simple
comparatives and parts from it on the differential and factor constructions (171) (§XI). The
synthesis rules make *more* additive and *as* multiplicative in their differential (R4, R5,
`moreSem`, `asSem`), and *too* a comparative against a counterfactually determined threshold
(R13), so that a pack too heavy to lift is heavier than in every world where it can be lifted
(227).

## Implementation notes

Degrees form a linear order, with the additive or multiplicative structure the rule at hand
needs; measures are world-indexed where ACTUALLY matters and extensional otherwise. The
descriptive-adequacy table (xvii) over the eight theories is not transcribed, and the rules R6
to R12 for the positive, nominal, mass and adverbial comparatives are not formalized. The
paper's examples are the rows of `Data.Examples.VonStechow1984`.

## References

* [von-stechow-1984]
* [russell-1905]
* [klein-1980]
-/

namespace VonStechow1984

open Degree

variable {W Entity D : Type*} [LinearOrder D]

/-! ### Intensional degree semantics (§§II–V)

`deReComparative` vs `deDictoComparative` is von Stechow's analysis of
Russell's ambiguity ((1), `Examples.yacht`): the than-clause standard is
either ACTUALLY-anchored to the actual world or evaluated in the belief
world — no degree-operator scope is involved. The ambiguous counterfactual
((26), `Examples.ex26`, §III) works the same way: its trivial reading's
clauses are de dicto self-comparisons, contradictory by `deDicto_absurd`. -/

/-- Comparative between world-indexed measures (R3): `a` exceeds `b` at `w`. -/
def intensionalComparative (μ : W → Entity → D) (w : W) (a b : Entity) : Prop :=
  μ w a > μ w b

/-- A rigid measure reduces `intensionalComparative` to the extensional
`comparativeSem`. -/
theorem intensionalComparative_rigid (μe : Entity → D) (w : W) (a b : Entity) :
    intensionalComparative (λ _ => μe) w a b ↔
      comparativeSem μe a b .positive :=
  Iff.rfl

/-- De re reading of "I thought your yacht was larger than it is": the
than-clause standard is ACTUALLY-anchored — evaluated at the actual world
`w₀` — while the matrix is evaluated at the belief world `wBel`. -/
def deReComparative (μ : W → Entity → D) (w₀ wBel : W) (x : Entity) : Prop :=
  μ wBel x > μ w₀ x

/-- De dicto reading: no ACTUALLY, so standard and matrix are both evaluated
at `wBel`. -/
def deDictoComparative (μ : W → Entity → D) (wBel : W) (x : Entity) : Prop :=
  μ wBel x > μ wBel x

/-- The de dicto reading is contradictory. -/
theorem deDicto_absurd (μ : W → Entity → D) (wBel : W) (x : Entity) :
    ¬ deDictoComparative μ wBel x :=
  lt_irrefl _

-- Russell's yacht ((1), `Examples.yacht`): actual length 5, believed length 8.
private def yachtLength : Bool → Unit → ℕ
  | true,  () => 5
  | false, () => 8

-- De re: the believed length exceeds the actual length. Consistent.
example : deReComparative yachtLength true false () := by
  simp [deReComparative, yachtLength]

-- De dicto: contradictory.
example : ¬ deDictoComparative yachtLength false () :=
  deDicto_absurd yachtLength false ()

/-- (v) (`Examples.exV`; §§VI–VII): a disjunctive standard entails both
disjuncts — the downward-entailingness of the than-clause that also
licenses its NPIs (`Degree.comparative_than_DE`;
`Ladusaw1979.IsDownwardEntailing .clausalComparative`). -/
theorem disjunction_to_conjunction_in_than (μa μb μc : D)
    (h : μb ⊔ μc < μa) : μb < μa ∧ μc < μa :=
  sup_lt_iff.mp h

/-- "A polar bear could be bigger than a grizzly bear could be" ((x),
`Examples.exX`; §VIII): if the greatest possible A-degree over the
accessible worlds exceeds the greatest possible B-degree, some accessible
A-world beats every B-world. -/
theorem maxDeg_witness {acc : Set W} {μA μB : W → D} {maxA maxB : D}
    (hmaxA : IsGreatest (μA '' acc) maxA) (hmaxB : IsGreatest (μB '' acc) maxB)
    (hgt : maxB < maxA) :
    ∃ w ∈ acc, ∀ v ∈ acc, μB v < μA w := by
  obtain ⟨w, hw, rfl⟩ := hmaxA.1
  exact ⟨w, hw, λ v hv => lt_of_le_of_lt (hmaxB.2 ⟨v, hv, rfl⟩) hgt⟩

/-- Klein's degree-free ordering ([klein-1980]; §XI) matches degree
comparison on simple comparatives via `measureDelineation`; the divergence
is confined to differential and factor constructions ((171a)–(171c)). -/
theorem klein_agrees_on_simple (μ : Entity → D) (cc : Set Entity)
    (a b : Entity) (ha : a ∈ cc) (hb : b ∈ cc) :
    comparativeSem μ a b .positive ↔
      Delineation.ordering (Delineation.measureDelineation μ) cc a b :=
  (Delineation.ordering_iff_degree μ cc a b ha hb).symm

/-! ### Synthesis rules R4 (`moreSem`), R5 (`asSem`), R13 (*too*) (§XIII) -/

/-- R4: `⟦more⟧(d₁)(A⁰)(d₂)(x)` iff `A⁰(x, d₁ + d₂)` with monotone `A⁰` —
the differential `d₁` plus the than-clause maximum `d₂`. -/
def moreSem [Add D] (μ : Entity → D) (x : Entity) (d₁ d₂ : D) : Prop :=
  d₁ + d₂ ≤ μ x

/-- R5: `⟦as⟧` multiplies where R4 adds ("twice as fat", (171b)). -/
def asSem [Mul D] (μ : Entity → D) (x : Entity) (d₁ d₂ : D) : Prop :=
  d₁ * d₂ ≤ μ x

/-- R4 with a positive differential and `d₂ = μ b` yields the bare
comparative. -/
theorem moreSem_comparative_bridge [AddCommMonoid D] [IsOrderedCancelAddMonoid D]
    (μ : Entity → D) (a b : Entity) {d₁ : D} (hd₁ : 0 < d₁)
    (h : moreSem μ a d₁ (μ b)) : comparativeSem μ a b .positive :=
  (lt_add_of_pos_left (μ b) hd₁).trans_le h

/-- An exact differential entails R4's at-least semantics. -/
theorem moreSem_differential_bridge [AddCommGroup D] [IsOrderedAddMonoid D]
    (μ : Entity → D) (a b : Entity) (diff : D)
    (h : differentialComparative μ a b diff) : moreSem μ a diff (μ b) :=
  le_of_eq (by rw [← h, sub_add_cancel])

/-- R5 at factor 1 is the equative. -/
theorem asSem_equative_bridge [MulOneClass D] (μ : Entity → D) (a b : Entity) :
    asSem μ a 1 (μ b) ↔ equativeSem μ a b .positive := by
  simp [asSem, equativeSem, one_mul]

/-- A tight factor phrase entails R5's at-least semantics. -/
theorem asSem_factor_bridge [Mul D] (μ : Entity → D) (a b : Entity)
    (factor : D) (h : factorEquative μ a b factor) : asSem μ a factor (μ b) :=
  le_of_eq h.symm

/-- R13 (§XIII): `⟦too⟧(d₁)(A⁰)(p)(x) = the max.d [x is d-A⁰]
λd₂ [p □→ A⁰(x, d₂ − d₁)]` — *too* is R4's `moreSem` with a
counterfactually determined threshold (DegP head `Degree.Head.excessive`):
when the threshold is greatest over the accessible worlds, being `excess`
too `A` puts the actual degree above every accessible world's degree. -/
theorem moreSem_exceeds_counterfactual_worlds
    [AddCommMonoid D] [IsOrderedCancelAddMonoid D]
    (μ : W → Entity → D) (w₀ : W) (acc : Set W) (x : Entity)
    {threshold excess : D} (hexcess : 0 < excess)
    (hmax : IsGreatest ((λ w => μ w x) '' acc) threshold)
    (htoo : moreSem (μ w₀) x excess threshold) :
    ∀ w ∈ acc, μ w x < μ w₀ x :=
  λ w hw => (hmax.2 ⟨w, hw, rfl⟩).trans_lt
    ((lt_add_of_pos_left threshold hexcess).trans_le htoo)

-- (227) (`Examples.ex227`): an 80 kg pack with a 30 kg liftable
-- threshold is at least 50 kg too heavy.
example : moreSem (λ _ : Unit => (80 : ℚ)) () 50 30 := by
  norm_num [moreSem]

end VonStechow1984
