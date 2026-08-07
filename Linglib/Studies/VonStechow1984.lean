import Linglib.Semantics.Intensional.Rigidity
import Linglib.Semantics.Degree.Basic
import Linglib.Semantics.Degree.MeasurePhrase
import Linglib.Semantics.Degree.Delineation
import Linglib.Data.Examples.VonStechow1984
import Mathlib.Tactic.Linarith

/-!
# Von Stechow 1984: Comparing Semantic Theories of Comparison

[von-stechow-1984] evaluates eight semantic theories of the comparative —
[russell-1905], [postal-1974], [williams-1977], [seuren-1973],
[lewis-1970], [klein-1980], [cresswell-1976], [hellan-1981] — against
nine phenomena (table (xvii)) and synthesizes them: Russellian definite
descriptions of degrees plus an ACTUALLY operator. Russell's ambiguity
("I thought your yacht was larger than it is") is the presence or
absence of ACTUALLY in the than-clause, not degree-operator scope.
Example stimuli live in `Data.Examples.VonStechow1984` (`Examples.*`).

## Main definitions

* `deReComparative`, `deDictoComparative`: Russell's ambiguity as an
  ACTUALLY-anchored vs belief-world than-clause standard (§§II–V)
* `moreSem`, `asSem`, `tooSem`: synthesis rules R4 (additive *more*),
  R5 (multiplicative *as*), R13 (counterfactual *too*) (§XIII)

## Main results

* `deDicto_absurd`: the ACTUALLY-less reading is contradictory
* `maxDeg_witness`: modal comparatives as `IsGreatest` over accessible
  worlds (§VIII)
* `klein_agrees_on_simple`: the degree-free ordering matches degree
  comparison on simple comparatives, not on differentials (§XI)
-/

namespace VonStechow1984

open Degree Intensional

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
    intensionalComparative (Intension.rigid μe) w a b ↔
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
`Ladusaw1979.licensingStrength .comparativeS = .antiAdditive`). -/
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
  exact ⟨w, hw, fun v hv => lt_of_le_of_lt (hmaxB.2 ⟨v, hv, rfl⟩) hgt⟩

/-- Klein's degree-free ordering ([klein-1980]; §XI) matches degree
comparison on simple comparatives via `measureDelineation`; the divergence
is confined to differential and factor constructions ((171a)–(171c)). -/
theorem klein_agrees_on_simple (μ : Entity → D) (cc : Set Entity)
    (a b : Entity) (ha : a ∈ cc) (hb : b ∈ cc) :
    comparativeSem μ a b .positive ↔
      Delineation.ordering (Delineation.measureDelineation μ) cc a b :=
  (Delineation.ordering_iff_degree μ cc a b ha hb).symm

/-! ### Synthesis rules R4 (`moreSem`), R5 (`asSem`), R13 (`tooSem`) (§XIII) -/

/-- R4: `⟦more⟧(d₁)(A⁰)(d₂)(x)` iff `A⁰(x, d₁ + d₂)` with monotone `A⁰` —
the differential `d₁` plus the than-clause maximum `d₂`. -/
def moreSem (μ : Entity → ℚ) (x : Entity) (d₁ d₂ : ℚ) : Prop :=
  μ x ≥ d₁ + d₂

/-- R5: `⟦as⟧` multiplies where R4 adds ("twice as fat", (171b)). -/
def asSem (μ : Entity → ℚ) (x : Entity) (d₁ d₂ : ℚ) : Prop :=
  μ x ≥ d₁ * d₂

/-- R4 with a positive differential and `d₂ = μ b` yields the bare
comparative. -/
theorem moreSem_comparative_bridge (μ : Entity → ℚ) (a b : Entity)
    {d₁ : ℚ} (hd₁ : 0 < d₁) (h : moreSem μ a d₁ (μ b)) :
    comparativeSem μ a b .positive :=
  (lt_add_of_pos_left (μ b) hd₁).trans_le h

/-- An exact differential entails R4's at-least semantics. -/
theorem moreSem_differential_bridge (μ : Entity → ℚ) (a b : Entity) (diff : ℚ)
    (h : differentialComparative μ a b diff) : moreSem μ a diff (μ b) := by
  simp only [moreSem, differentialComparative] at *
  linarith

/-- R5 at factor 1 is the equative. -/
theorem asSem_equative_bridge (μ : Entity → ℚ) (a b : Entity) :
    asSem μ a 1 (μ b) ↔ equativeSem μ a b .positive := by
  simp [asSem, equativeSem, one_mul]

/-- A tight factor phrase entails R5's at-least semantics. -/
theorem asSem_factor_bridge (μ : Entity → ℚ) (a b : Entity) (factor : ℚ)
    (h : factorEquative μ a b factor) : asSem μ a factor (μ b) := by
  simp only [asSem, factorEquative] at *
  linarith

/-- R13 (p. 69, §XIII.6): `⟦too⟧(d₁)(A⁰)(p)(x) = the max.d [x is d-A⁰]
λd₂ [p □→ A⁰(x, d₂ − d₁)]`. The additive skeleton is definitionally
`moreSem` (*too* and *-er* share R4's structure; DegP head
`Degree.Head.excessive`); the counterfactual threshold is
`tooSem_exceeds_counterfactual_worlds`. -/
def tooSem (μ : Entity → ℚ) (x : Entity) (excess threshold : ℚ) : Prop :=
  moreSem μ x excess threshold

/-- If `x` is `excess` too `A` for a threshold greatest over the accessible
worlds, `x`'s actual degree exceeds its degree in every such world. -/
theorem tooSem_exceeds_counterfactual_worlds
    (μ : W → Entity → ℚ) (w₀ : W) (acc : Set W) (x : Entity)
    {threshold excess : ℚ} (hexcess : 0 < excess)
    (hmax : IsGreatest ((fun w => μ w x) '' acc) threshold)
    (htoo : tooSem (μ w₀) x excess threshold) :
    ∀ w ∈ acc, μ w x < μ w₀ x :=
  fun w hw => (hmax.2 ⟨w, hw, rfl⟩).trans_lt
    ((lt_add_of_pos_left threshold hexcess).trans_le htoo)

-- (227) (`Examples.ex227`): an 80 kg pack with a 30 kg liftable
-- threshold is at least 50 kg too heavy.
example : tooSem (fun _ : Unit => (80 : ℚ)) () 50 30 := by
  norm_num [tooSem, moreSem]

end VonStechow1984
