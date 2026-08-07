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

/-! ### Intensional degree semantics (§§II–V)

World-indexed degree semantics for the constructions that need intensional
infrastructure: Russell's ambiguity, ambiguous counterfactuals, modal
comparatives. The central claim: the ambiguity of "I thought your yacht was
larger than it is" ((1), `Examples.yacht`) is the presence or absence of an
ACTUALLY operator fixing the than-clause to the actual world — not a scope
difference of degree operators or definite descriptions. -/

/-- Evaluate an intension at the actual world `w₀`. NOT [kaplan-1989]'s
tower-based indexical ACTUALLY (which manipulates context-index pairs for
demonstratives) — von Stechow's operator just extracts the extension at
`w₀`, via `Intensional.Intension.evalAt` with arguments flipped (world
first, matching the actual world's syntactic prominence in comparatives). -/
def actuallyDeg {W D : Type*} (w₀ : W) (f : W → D) : D :=
  Intensional.Intension.evalAt f w₀

section IntensionalCore

variable {W Entity D : Type*} [LinearOrder D]

/-- Comparative with world-indexed measure functions.
Adjectives denote 2-place relations between individuals and degrees,
evaluated at a world (R3). -/
def intensionalComparative
    (μ : W → Entity → D) (w : W) (a b : Entity) : Prop :=
  μ w a > μ w b

/-- With a rigid measure (`Intension.rigid`), `intensionalComparative`
reduces to the extensional `comparativeSem`. -/
theorem intensionalComparative_rigid
    (μe : Entity → D) (w : W) (a b : Entity) :
    intensionalComparative (Intensional.Intension.rigid μe) w a b ↔
      comparativeSem μe a b .positive :=
  Iff.rfl

/-- De re reading: "I thought your yacht was larger than it ACTUALLY is."
The than-clause contains ACTUALLY, so the standard is evaluated at the
actual world `w₀` while the matrix is evaluated in the belief world
`wBel`. This reading is consistent — one can coherently believe an
object exceeds its actual size. -/
def deReComparative
    (μ : W → Entity → D) (w₀ wBel : W) (x : Entity) : Prop :=
  μ wBel x > actuallyDeg w₀ (fun w => μ w x)

/-- De dicto reading: "I thought your yacht was larger than it is."
No ACTUALLY — both matrix and standard evaluated in the belief world.
Yields a contradictory thought: `μ(wBel,x) > μ(wBel,x)`. -/
def deDictoComparative
    (μ : W → Entity → D) (wBel : W) (x : Entity) : Prop :=
  μ wBel x > μ wBel x

/-- The de dicto reading is contradictory: no entity can exceed its own
degree in any world. -/
theorem deDicto_absurd
    (μ : W → Entity → D) (wBel : W) (x : Entity) :
    ¬ deDictoComparative μ wBel x :=
  lt_irrefl _

/-- The de re reading compares the belief-world degree against the
ACTUALLY-extracted actual-world degree. -/
theorem deRe_unfolds
    (μ : W → Entity → D) (w₀ wBel : W) (x : Entity) :
    deReComparative μ w₀ wBel x ↔ μ w₀ x < μ wBel x :=
  Iff.rfl

end IntensionalCore

/-! #### Russell's yacht -/

section RussellExample

-- The two readings of (1), instantiated at `World := Bool`
-- (actual = `true`, belief = `false`) for concreteness.
private def yachtLength : Bool → Unit → ℕ
  | true,  () => 5   -- actual length
  | false, () => 8   -- believed length (the guest's overestimate)

/-- De re reading (with ACTUALLY): the belief-world length (8) exceeds the
actual length (5). Consistent thought. -/
example : deReComparative yachtLength true false () :=
  (deRe_unfolds yachtLength true false ()).mpr (by decide)

/-- De dicto reading: contradictory by `deDicto_absurd`. -/
example : ¬ deDictoComparative yachtLength false () :=
  deDicto_absurd yachtLength false ()

end RussellExample

/-! ### Ambiguous counterfactuals (§III)

"If Mary had smoked less (than she did), she would be healthier (than she
is)" ((26), `Examples.ex26`). Without ACTUALLY, the than-clauses are
evaluated in the counterfactual world and each clause compares a degree
with itself — the trivial reading, contradictory by `deDicto_absurd`. With
ACTUALLY, the standards are the actual-world values and the reading is
informative — an instance of `deReComparative`. -/

section AmbiguousCounterfactual

-- Health degrees: actual world `true` (3), counterfactual
-- less-smoking world `false` (7).
private def health : Bool → Unit → ℕ
  | true,  () => 3
  | false, () => 7

/-- Informative reading of (26)'s consequent: counterfactual health
exceeds the ACTUALLY-anchored actual health. Coherent. -/
example : deReComparative health true false () :=
  (deRe_unfolds health true false ()).mpr (by decide)

/-- Trivial reading of the consequent: both degrees evaluated in the
counterfactual world. Contradictory. -/
example : ¬ deDictoComparative health false () :=
  deDicto_absurd health false ()

end AmbiguousCounterfactual

/-! ### NPI licensing in than-clauses (§VI)

The Max operator makes the than-clause a downward-entailing environment:
replacing the than-clause with a more informative one is a valid inference.
Von Stechow shows that Cresswell-style λ-abstraction over degrees is DE —
predicting the licensing pattern of (70)–(72) (`Examples.ex70` –
`Examples.ex72b`), including the exclusion of the *positive* polarity item
*already* from the than-clause — while Russell's, Postal's, and Hellan's
accounts are not.

Substrate connections: `Degree.comparative_than_DE` (downward-entailingness
of the than-position under max-quantification), and
`Features/LicensingContext`, which classifies clausal *than*
(`.comparativeS`) as anti-additive, hence DE
(`Ladusaw1979.licensingStrength .comparativeS = .antiAdditive`). -/

/-! ### Quantifiers, connectives, and blocked inferences (§VII)

(v) and (vi) (`Examples.exV`, `Examples.exVI`): disjunctions and
existentials in the than-clause strengthen to conjunctions and universals —
downward-entailingness, formalized as `disjunction_to_conjunction_in_than`.
(vii) (`Examples.exVII`): "Ede is fatter than Max" must not entail "Ede is
fatter than everyone"; on Russell's account the description
ιd[everyone is d-fat] fails to denote when people differ in fatness.
(99a), (99b) (`Examples.ex99a`, `Examples.ex99b`): negative quantifiers in
the than-clause are semantically odd — the description fails to denote
(Russell), or the sentence is a logical falsehood (Cresswell). -/

/-- "Konstanz is nicer than Düsseldorf or Stuttgart" entails "Konstanz is
nicer than Düsseldorf and Stuttgart" ((v)): exceeding the maximum of a
disjunctive standard entails exceeding both disjuncts. -/
theorem disjunction_to_conjunction_in_than {D : Type*} [LinearOrder D]
    (μa μb μc : D) (h : μa > μb ⊔ μc) :
    μa > μb ∧ μa > μc :=
  ⟨lt_of_le_of_lt le_sup_left h, lt_of_le_of_lt le_sup_right h⟩

/-! ### Modal comparatives (§VIII) -/

/-- "A polar bear could be bigger than a grizzly bear could be" ((x),
`Examples.exX`): if the greatest possible A-degree across the accessible
worlds exceeds the greatest possible B-degree, some accessible world's
A-degree beats every accessible world's B-degree. Modal degree maxima are
`IsGreatest` on the image of the world-indexed measure — the than-clause
Max operator (R2) lifted to worlds. -/
theorem maxDeg_witness {W D : Type*} [LinearOrder D]
    {acc : Set W} {μA μB : W → D} {maxA maxB : D}
    (hmaxA : IsGreatest (μA '' acc) maxA)
    (hmaxB : IsGreatest (μB '' acc) maxB)
    (hgt : maxB < maxA) :
    ∃ w ∈ acc, ∀ v ∈ acc, μB v < μA w := by
  obtain ⟨w, hw, rfl⟩ := hmaxA.1
  exact ⟨w, hw, fun v hv => lt_of_le_of_lt (hmaxB.2 ⟨v, hv, rfl⟩) hgt⟩

/-! ### Klein criticism (§XI)

[klein-1980]'s degree-free semantics agrees with degree semantics on simple
comparatives, but has no degree ontology, so metric information cannot be
expressed: differential readings ((171a), `Examples.ex171a`), factor
equatives ((171b), `Examples.ex171b`), and cross-dimensional comparison
((171c), `Examples.ex171c`) are all beyond it. R4/R5's degree arithmetic
below is exactly what the comparison-class ontology lacks. -/

/-- Klein agrees with the synthesis on simple comparatives: the degree
comparison μ(a) > μ(b) coincides with Klein's ordering under the induced
delineation (`ordering_iff_degree`). The divergence is confined to
differential and factor constructions. -/
theorem klein_agrees_on_simple {Entity D : Type*} [LinearOrder D]
    (μ : Entity → D) (cc : Set Entity) (a b : Entity)
    (ha : a ∈ cc) (hb : b ∈ cc) :
    comparativeSem μ a b .positive ↔
      Degree.Delineation.ordering
        (Degree.Delineation.measureDelineation μ) cc a b := by
  simp only [comparativeSem,
    Degree.Delineation.ordering_iff_degree μ cc a b ha hb]

/-! ### Synthesis rules R4 (`moreSem`), R5 (`asSem`), R13 (`tooSem`) (§XIII) -/

section Synthesis

variable {Entity : Type*}

/-- R4: `⟦more⟧(d₁)(A⁰)(d₂)(x)` iff `A⁰(x, d₁ + d₂)`. *more* / *-er* is
a 4-place relation. The differential `d₁` specifies the gap; `d₂` is
the standard's maximal degree (from the than-clause via Max). Plain
comparatives have `d₁ > 0` supplied by context; measure-phrase
differentials make `d₁` explicit. -/
def moreSem (μ : Entity → ℚ) (x : Entity) (d₁ d₂ : ℚ) : Prop :=
  μ x ≥ d₁ + d₂

/-- R5: `⟦as⟧` uses multiplication instead of addition. "Ede is twice
as fat as Angelika" ((171b)) = `μ(Ede) ≥ 2 · μ(Angelika)`. -/
def asSem (μ : Entity → ℚ) (x : Entity) (d₁ d₂ : ℚ) : Prop :=
  μ x ≥ d₁ * d₂

/-- R4 with `d₁ > 0` and `d₂ = μ(b)` yields `comparativeSem .positive`. -/
theorem moreSem_comparative_bridge
    (μ : Entity → ℚ) (a b : Entity) (d₁ : ℚ) (hd₁ : d₁ > 0) :
    moreSem μ a d₁ (μ b) → comparativeSem μ a b .positive := by
  intro h
  simp only [moreSem] at h
  show μ b < μ a
  linarith

/-- Exact differential entails R4's "at least" semantics. -/
theorem moreSem_differential_bridge
    (μ : Entity → ℚ) (a b : Entity) (diff : ℚ) :
    differentialComparative μ a b diff → moreSem μ a diff (μ b) := by
  intro h
  simp only [moreSem, differentialComparative] at *
  linarith

/-- R5 with `factor = 1` reduces to equative literal semantics. -/
theorem asSem_equative_bridge (μ : Entity → ℚ) (a b : Entity) :
    asSem μ a 1 (μ b) ↔ equativeSem μ a b .positive := by
  simp [asSem, equativeSem, one_mul]

/-- R5 reduces to `factorEquative` when the inequality is tight. -/
theorem asSem_factor_bridge
    (μ : Entity → ℚ) (a b : Entity) (factor : ℚ) :
    factorEquative μ a b factor → asSem μ a factor (μ b) := by
  intro h
  simp only [asSem, factorEquative] at *
  linarith

/-! #### Cross-category comparatives (§XIII.4)

The comparative morpheme is category-blind — only the measure function
varies: plural nouns take cardinality ((217), `Examples.ex217`), mass nouns
the amount of the totality ((218), `Examples.ex218`), adverbs an event
measure ((224c), `Examples.ex224c`). The multihead comparative (xi)
(`Examples.exXI`) needs no new machinery. -/

/-! #### *too* as counterfactual comparative (§XIII.6)

R13 (p. 69): `⟦too⟧(d₁)(A⁰)(p)(x) = the max.d [x is d-A⁰]
λd₂ [p □→ A⁰(x, d₂ − d₁)]`. "This pack is at least fifty kilos too heavy
to lift" ((227), `Examples.ex227`) paraphrases as (229): were the pack
liftable, it would be at least 50 kg less heavy than it actually is. In
the DegP head inventory, *too* is `Degree.Head.excessive`. -/

/-- R13's additive skeleton: `x` is `excess` too `A` for `threshold` iff
`μ x ≥ excess + threshold`. The definitional delegation to `moreSem` is
the paper's point that *too* and *-er* share R4's additive structure;
R13's counterfactual content — the threshold as greatest degree over the
accessible worlds — is `tooSem_exceeds_counterfactual_worlds`. -/
def tooSem (μ : Entity → ℚ) (x : Entity) (excess threshold : ℚ) : Prop :=
  moreSem μ x excess threshold

/-- If `x` is (positively) too `A` for a counterfactually determined
threshold, `x`'s actual degree exceeds its degree in every accessible
world: in every world where you can lift the pack, it weighs strictly
less than it actually does. -/
theorem tooSem_exceeds_counterfactual_worlds {W : Type*}
    (μ : W → Entity → ℚ) (w₀ : W) (acc : Set W) (x : Entity)
    {threshold excess : ℚ} (hexcess : 0 < excess)
    (hmax : IsGreatest ((fun w => μ w x) '' acc) threshold)
    (htoo : tooSem (μ w₀) x excess threshold) :
    ∀ w ∈ acc, μ w x < μ w₀ x := by
  intro w hw
  have hle : μ w x ≤ threshold := hmax.2 ⟨w, hw, rfl⟩
  simp only [tooSem, moreSem] at htoo
  linarith

/-- A pack weighing 80 kg with a liftable threshold of 30 kg is at least
50 kg too heavy (80 ≥ 50 + 30). -/
example : tooSem (fun _ : Unit => (80 : ℚ)) () 50 30 := by
  norm_num [tooSem, moreSem]

end Synthesis

end VonStechow1984
