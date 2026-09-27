module

public import Mathlib.Data.Fintype.Prod
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Linglib.Semantics.Modality.Kratzer.Operators
public import Linglib.Logic.ComparativeProbability.WorldOrdering

/-!
# Kratzer (2012): Modals and Conditionals

This file formalizes the distinction the book's second chapter draws, in its typology of
conversational backgrounds, between realistic backgrounds representing evidence of things and
informational backgrounds representing the propositional content of a source of information.
A rumor that Roger was elected chief can feed either. As evidence of things it determines the
worlds that contain a counterpart of the rumor, produced the same way; whether Roger's
counterpart was elected there depends on how reliable the source is, so *given the rumor,
Roger must have been elected chief* is false when the rumor rests on shaky evidence and true
only when the source is reliable. As a source of information it determines the worlds
compatible with what it says, so the German reportative *sollen* in *dem Gerücht nach soll
Roger zum Häuptling gewählt worden sein* is true whatever the rumor's provenance, even a lie.
The informational background is therefore not realistic, since the actual world need not be
among the worlds the rumor describes.

The chapter's toy example of graded possibility ranks four worlds strictly by an ordering
source of nested propositions. On it the revised comparative possibility of §2.4, which compares
two propositions only on the worlds where they differ, agrees with a probability measure giving
the world `wᵢ` the probability `2ⁱ/15`, in that one proposition is a better possibility than
another exactly when it is more probable. Since the ranking has a single best world, necessity and
possibility coincide, both holding of the propositions of probability at least `8/15` (§2.5).

## Implementation notes

The worlds record whether Roger was elected and whether the rumor exists, so every claim is
decided over `Bool × Bool`. The evidence-of-things background at a world lists the status of
the rumor there; the informational background lists the rumor's content. Reliability is stated
generally, as a proposition of the background entailing the content wherever the rumor
exists, rather than as an extra coordinate. Counterparts are identified with the rumor's
status, since the model has no other individuals.

The toy example's worlds are `Fin 4`, the index of `wᵢ` being `i`, and all of them are
accessible, so comparative possibility is `KratzerLift` of the induced ordering with no modal
base to restrict it.

## References

* [kratzer-2012]
* [kratzer-1981] — the original typology of conversational backgrounds
* [rullmann-matthewson-davis-2008] — the St'át'imcets reportative the chapter contrasts with
  German *sollen*
-/

@[expose] public section

namespace Kratzer2012

open Modality

/-- A world records whether Roger was elected chief and whether the rumor that he was exists. -/
abbrev World := Bool × Bool

/-- Roger was elected chief. -/
def chief : World → Prop := (·.1 = true)

/-- The rumor exists. -/
def rumor : World → Prop := (·.2 = true)

/-- As evidence of things, the rumor makes the background at `w` record its status in `w`, so
the accessible worlds are those with a counterpart of the actual rumor, or with none if there is
none. -/
def evidence : ModalBase World := fun w ↦ [fun v ↦ v.2 = w.2]

/-- As a source of information, the rumor makes the background list its content. -/
def content : ModalBase World := Function.const World [chief]

/-- Decide a claim about the backgrounds over the four worlds. -/
scoped macro "decide_worlds" : tactic =>
  `(tactic| ((try simp only [simpleNecessity, simplePossibility, ModalLogic.box,
      ModalLogic.diamond, ModalBase.Accessible, ModalBase.accessibleWorlds, mem_propIntersection,
      ConvBackground.IsRealistic, evidence, content, chief, rumor, Function.const_apply,
      List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true]) <;>
      decide))

/-- The evidence-of-things background is realistic, since every world has the rumor's status
it has. -/
theorem evidence_realistic : evidence.IsRealistic := by decide_worlds

/-- The informational background is not realistic, since at a world where the rumor is a lie
the world itself is not among those compatible with the rumor's content. -/
theorem content_not_realistic : ¬ content.IsRealistic := by decide_worlds

/-- The reportative reading of (8b) holds at every world, a lie included, because it reports
the rumor's content. -/
theorem sollen_holds (w : World) : simpleNecessity content chief w := by
  decide_worlds

/-- On shaky evidence (8a) fails, since where the rumor exists the worlds with a counterpart
of it include one where Roger was not elected, so Roger need not have been elected chief. -/
theorem not_must_chief (w : World) : ¬ simpleNecessity evidence chief w := by
  revert w; decide_worlds

/-- Yet the rumor leaves Roger's election possible wherever it exists. -/
theorem can_chief (w : World) (h : rumor w) : simplePossibility evidence chief w := by
  revert h w; decide_worlds

/-- From a reliable source (8a) holds. If the background also records that the rumor is
reliable, a proposition entailing its content wherever the rumor exists, then Roger must have
been elected chief, for any worlds and backgrounds. -/
theorem must_of_reliable {W : Type*} (rumor chief reliable : W → Prop) (f : ModalBase W)
    (hf : ∀ w, rumor w → rumor ∈ f w ∧ reliable ∈ f w)
    (hrel : ∀ v, reliable v → rumor v → chief v) (w : W) (hw : rumor w) :
    simpleNecessity f chief w := fun v hv ↦
  hrel v (hv reliable (hf w hw).2) (hv rumor (hf w hw).1)

/-! ### Grades of possibility (§2.4–§2.5)

The toy example of §2.4 has four worlds, all accessible, and the ordering source `{w₃}`,
`{w₂, w₃}`, `{w₁, w₂, w₃}`, which ranks them `w₃ < w₂ < w₁ < w₀`. A probability measure giving
`wᵢ` the probability `2ⁱ/15` preserves comparative possibility exactly, and since the ranking
has a single best world, necessity and possibility coincide (§2.5). -/

namespace Grades

open MeasureTheory ComparativeProbability
open scoped ENNReal

/-- The worlds `w₀`, `w₁`, `w₂`, `w₃` of the toy example. -/
abbrev World := Fin 4

/-- The ordering source of the toy example, `{w₃}`, `{w₂, w₃}` and `{w₁, w₂, w₃}` at every
world. -/
def ideal : OrderingSource World := fun _ ↦ [(3 ≤ ·), (2 ≤ ·), (1 ≤ ·)]

/-- The ranking `w₃ < w₂ < w₁ < w₀` is connected and has no ties, one world being at least as
good as another exactly when its index is at least the other's. -/
theorem atLeastAsGoodAs_ideal_iff (v w z : World) : (w ≤[ideal v] z) ↔ z ≤ w := by
  simp only [atLeastAsGoodAs_iff, ideal, List.forall_mem_cons, List.not_mem_nil,
    IsEmpty.forall_iff, implies_true, and_true]
  fin_omega

/-- `p` is a better possibility than `q` when it is at least as good a possibility, in the
revised sense of §2.4, and not conversely. -/
def BetterPossibility (p q : Set World) : Prop :=
  KratzerLift (atLeastAsGoodAs (ideal 0)) p q ∧ ¬ KratzerLift (atLeastAsGoodAs (ideal 0)) q p

/-- Kratzer's probability measure gives `wᵢ` the probability `2ⁱ/15`. -/
noncomputable def prob : Measure World :=
  ∑ i : World, (2 ^ (i : ℕ) / 15 : ℝ≥0∞) • Measure.dirac i

/-- The probability of a proposition is the sum of `2ⁱ` over its worlds `wᵢ`, divided by 15,
which is the table of p. 42. -/
theorem prob_coe (s : Finset World) : prob s = ((∑ i ∈ s, 2 ^ (i : ℕ) : ℕ) : ℝ≥0∞) / 15 := by
  simp [prob, Set.indicator_apply, Finset.sum_ite_mem, ENNReal.sum_div]

/-- Kratzer's measure is a probability measure. -/
instance : IsProbabilityMeasure prob where
  measure_univ := by
    rw [← Finset.coe_univ, prob_coe, show (∑ i : World, 2 ^ (i : ℕ) : ℕ) = 15 from rfl]
    exact ENNReal.div_self (by norm_num) (by norm_num)

/-- One proposition is a better possibility than another exactly when it is more probable, so
the measure preserves comparative possibility (p. 43). -/
theorem betterPossibility_iff (p q : Set World) : BetterPossibility p q ↔ prob q < prob p := by
  classical
  have hr : atLeastAsGoodAs (ideal 0) = fun w z ↦ z ≤ w :=
    funext₂ fun w z ↦ propext (atLeastAsGoodAs_ideal_iff 0 w z)
  rw [← Set.coe_toFinset p, ← Set.coe_toFinset q, prob_coe, prob_coe,
    ENNReal.div_lt_div_iff_left (by norm_num) (by norm_num), Nat.cast_lt]
  simp only [BetterPossibility, KratzerLift, hr, ← Finset.coe_sdiff, Finset.mem_coe]
  generalize p.toFinset = s
  generalize q.toFinset = t
  revert s t
  decide

/-- A proposition has probability at least `8/15` exactly when it holds at `w₃`. -/
private theorem le_prob_iff (p : World → Prop) : 8 / 15 ≤ prob {w | p w} ↔ p 3 := by
  classical
  have h : ∀ s : Finset World, 8 ≤ ∑ i ∈ s, 2 ^ (i : ℕ) ↔ 3 ∈ s := by decide
  rw [← Set.coe_toFinset {w | p w}, prob_coe, ← not_lt,
    ENNReal.div_lt_div_iff_left (by norm_num) (by norm_num),
    ← Nat.cast_ofNat (R := ℝ≥0∞) (n := 8), Nat.cast_lt,
    not_lt, h, Set.mem_toFinset, Set.mem_ofPred_eq]

/-- Necessity is truth at `w₃`, the single best world. -/
private theorem humanNecessity_ideal_iff (p : World → Prop) :
    humanNecessity emptyBackground ideal p 0 ↔ p 3 := by
  simp only [humanNecessity, accessibleWorlds_emptyBackground, Set.mem_univ, true_and,
    forall_const, atLeastAsGoodAs_ideal_iff]
  refine ⟨fun h ↦ ?_, fun h u ↦ ⟨3, Fin.le_last u, fun z hz ↦ Fin.last_le_iff.mp hz ▸ h⟩⟩
  obtain ⟨v, -, hv⟩ := h 3
  exact hv 3 (Fin.le_last v)

/-- A proposition is necessary exactly when its probability is at least `8/15` (§2.5). -/
theorem humanNecessity_iff (p : World → Prop) :
    humanNecessity emptyBackground ideal p 0 ↔ 8 / 15 ≤ prob {w | p w} := by
  rw [humanNecessity_ideal_iff, le_prob_iff]

/-- A proposition is possible exactly when its probability is at least `8/15`, so possibility
collapses with necessity (§2.5). -/
theorem humanPossibility_iff (p : World → Prop) :
    humanPossibility emptyBackground ideal p 0 ↔ 8 / 15 ≤ prob {w | p w} := by
  rw [humanPossibility, humanNecessity_ideal_iff, not_not, le_prob_iff]

end Grades

end Kratzer2012
