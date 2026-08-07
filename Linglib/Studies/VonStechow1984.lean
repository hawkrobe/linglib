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

* `actuallyDeg`, `deReComparative`, `deDictoComparative`: the ACTUALLY
  analysis of Russell's ambiguity (§§II–V)
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

open Degree (comparativeSem equativeSem differentialComparative factorEquative)

variable {W Entity D : Type*}

/-! ### Intensional degree semantics (§§II–V) -/

/-- The ACTUALLY operator: the extension of an intension at the actual
world `w₀` (`Intension.evalAt`, world first) — not [kaplan-1989]'s
indexical ACTUALLY. -/
def actuallyDeg (w₀ : W) (f : W → D) : D :=
  Intensional.Intension.evalAt f w₀

variable [LinearOrder D]

/-- Comparative between world-indexed measures (R3): `a` exceeds `b` at `w`. -/
def intensionalComparative (μ : W → Entity → D) (w : W) (a b : Entity) : Prop :=
  μ w a > μ w b

/-- A rigid measure reduces `intensionalComparative` to the extensional
`comparativeSem`. -/
theorem intensionalComparative_rigid (μe : Entity → D) (w : W) (a b : Entity) :
    intensionalComparative (Intensional.Intension.rigid μe) w a b ↔
      comparativeSem μe a b .positive :=
  Iff.rfl

/-- De re reading of "I thought your yacht was larger than it is": ACTUALLY
anchors the than-clause standard to `w₀`; the matrix is evaluated at `wBel`. -/
def deReComparative (μ : W → Entity → D) (w₀ wBel : W) (x : Entity) : Prop :=
  μ wBel x > actuallyDeg w₀ (fun w => μ w x)

/-- De dicto reading: no ACTUALLY, so standard and matrix are both evaluated
at `wBel`. -/
def deDictoComparative (μ : W → Entity → D) (wBel : W) (x : Entity) : Prop :=
  μ wBel x > μ wBel x

/-- The de dicto reading is contradictory. -/
theorem deDicto_absurd (μ : W → Entity → D) (wBel : W) (x : Entity) :
    ¬ deDictoComparative μ wBel x :=
  lt_irrefl _

/-- The de re reading compares `x`'s degrees at `w₀` and `wBel`. -/
theorem deRe_unfolds (μ : W → Entity → D) (w₀ wBel : W) (x : Entity) :
    deReComparative μ w₀ wBel x ↔ μ w₀ x < μ wBel x :=
  Iff.rfl

-- Russell's yacht ((1), `Examples.yacht`): actual length 5, believed length 8.
private def yachtLength : Bool → Unit → ℕ
  | true,  () => 5
  | false, () => 8

-- De re: the believed length exceeds the actual length. Consistent.
example : deReComparative yachtLength true false () :=
  (deRe_unfolds yachtLength true false ()).mpr (by decide)

-- De dicto: contradictory.
example : ¬ deDictoComparative yachtLength false () :=
  deDicto_absurd yachtLength false ()

/-! ### Ambiguous counterfactuals (§III)

"If Mary had smoked less (than she did), she would be healthier (than she
is)" ((26), `Examples.ex26`): the trivial reading evaluates the than-clauses
in the counterfactual world (contradictory by `deDicto_absurd`); the
informative reading anchors them with ACTUALLY. -/

-- Health degrees: actual world `true` (3), counterfactual world `false` (7).
private def health : Bool → Unit → ℕ
  | true,  () => 3
  | false, () => 7

-- Informative reading of (26)'s consequent: coherent.
example : deReComparative health true false () :=
  (deRe_unfolds health true false ()).mpr (by decide)

-- Trivial reading: contradictory.
example : ¬ deDictoComparative health false () :=
  deDicto_absurd health false ()

/-! ### NPI licensing in than-clauses (§VI)

The Max operator makes the than-clause downward-entailing: Cresswell-style
λ-abstraction over degrees is DE and predicts (70)–(72) (`Examples.ex70` –
`Examples.ex72b`, including the exclusion of the positive polarity item
*already*), while Russell's and Hellan's accounts are not. Substrate:
`Degree.comparative_than_DE`;
`Ladusaw1979.licensingStrength .comparativeS = .antiAdditive`. -/

/-! ### Quantifiers, connectives, and blocked inferences (§VII)

(vii) (`Examples.exVII`) must not entail "fatter than everyone": Russell's
description ιd[everyone is d-fat] fails to denote when people differ. In
(99a), (99b) (`Examples.ex99a`, `Examples.ex99b`) a negative quantifier makes
the description fail to denote (Russell) or the sentence a logical falsehood
(Cresswell). -/

/-- (v): exceeding the maximum of a disjunctive standard entails exceeding
both disjuncts — "nicer than Düsseldorf or Stuttgart" entails "nicer than
Düsseldorf and Stuttgart" (`Examples.exV`). -/
theorem disjunction_to_conjunction_in_than (μa μb μc : D) (h : μa > μb ⊔ μc) :
    μa > μb ∧ μa > μc :=
  ⟨lt_of_le_of_lt le_sup_left h, lt_of_le_of_lt le_sup_right h⟩

/-! ### Modal comparatives (§VIII) -/

/-- "A polar bear could be bigger than a grizzly bear could be" ((x),
`Examples.exX`): if the greatest possible A-degree over the accessible
worlds exceeds the greatest possible B-degree, some accessible A-world
beats every B-world. -/
theorem maxDeg_witness {acc : Set W} {μA μB : W → D} {maxA maxB : D}
    (hmaxA : IsGreatest (μA '' acc) maxA) (hmaxB : IsGreatest (μB '' acc) maxB)
    (hgt : maxB < maxA) :
    ∃ w ∈ acc, ∀ v ∈ acc, μB v < μA w := by
  obtain ⟨w, hw, rfl⟩ := hmaxA.1
  exact ⟨w, hw, fun v hv => lt_of_le_of_lt (hmaxB.2 ⟨v, hv, rfl⟩) hgt⟩

/-! ### Klein criticism (§XI) -/

/-- Klein's degree-free ordering ([klein-1980], via `measureDelineation`)
matches degree comparison on simple comparatives; the divergence is confined
to differential and factor constructions ((171a)–(171c)). -/
theorem klein_agrees_on_simple (μ : Entity → D) (cc : Set Entity)
    (a b : Entity) (ha : a ∈ cc) (hb : b ∈ cc) :
    comparativeSem μ a b .positive ↔
      Degree.Delineation.ordering
        (Degree.Delineation.measureDelineation μ) cc a b := by
  simp only [comparativeSem,
    Degree.Delineation.ordering_iff_degree μ cc a b ha hb]

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
    (d₁ : ℚ) (hd₁ : d₁ > 0) :
    moreSem μ a d₁ (μ b) → comparativeSem μ a b .positive := by
  intro h
  simp only [moreSem] at h
  show μ b < μ a
  linarith

/-- An exact differential entails R4's at-least semantics. -/
theorem moreSem_differential_bridge (μ : Entity → ℚ) (a b : Entity) (diff : ℚ) :
    differentialComparative μ a b diff → moreSem μ a diff (μ b) := by
  intro h
  simp only [moreSem, differentialComparative] at *
  linarith

/-- R5 at factor 1 is the equative. -/
theorem asSem_equative_bridge (μ : Entity → ℚ) (a b : Entity) :
    asSem μ a 1 (μ b) ↔ equativeSem μ a b .positive := by
  simp [asSem, equativeSem, one_mul]

/-- A tight factor phrase entails R5's at-least semantics. -/
theorem asSem_factor_bridge (μ : Entity → ℚ) (a b : Entity) (factor : ℚ) :
    factorEquative μ a b factor → asSem μ a factor (μ b) := by
  intro h
  simp only [asSem, factorEquative] at *
  linarith

/-! #### Cross-category comparatives (§XIII.4)

The comparative morpheme is category-blind — only the measure varies:
cardinality for plural nouns (217), amount for mass nouns (218), an event
measure for adverbs (224c) (`Examples.ex217` – `Examples.ex224c`). -/

/-! #### *too* as counterfactual comparative (§XIII.6)

R13 (p. 69): `⟦too⟧(d₁)(A⁰)(p)(x) = the max.d [x is d-A⁰]
λd₂ [p □→ A⁰(x, d₂ − d₁)]`; "at least fifty kilos too heavy to lift"
((227), `Examples.ex227`). In the DegP head inventory *too* is
`Degree.Head.excessive`. -/

/-- R13's additive skeleton, definitionally `moreSem` — *too* and *-er*
share R4's additive structure. The counterfactual threshold is
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
    ∀ w ∈ acc, μ w x < μ w₀ x := by
  intro w hw
  have hle : μ w x ≤ threshold := hmax.2 ⟨w, hw, rfl⟩
  simp only [tooSem, moreSem] at htoo
  linarith

-- An 80 kg pack with a 30 kg liftable threshold is at least 50 kg too heavy.
example : tooSem (fun _ : Unit => (80 : ℚ)) () 50 30 := by
  norm_num [tooSem, moreSem]

end VonStechow1984
