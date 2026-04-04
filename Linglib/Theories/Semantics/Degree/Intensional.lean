import Linglib.Core.Semantics.Intension
import Linglib.Theories.Semantics.Degree.Comparative
import Linglib.Theories.Semantics.Degree.Differential
import Linglib.Theories.Semantics.Degree.Equative
import Linglib.Theories.Semantics.Degree.DegreeAbstraction
import Mathlib.Tactic.Linarith

/-!
# Intensional Degree Semantics
@cite{von-stechow-1984}

World-indexed degree semantics for comparative constructions requiring
intensional infrastructure: Russell's ambiguity, modal comparatives,
ambiguous counterfactuals.

## Core Insight

@cite{von-stechow-1984}'s central contribution is that Russell's ambiguity
("I thought your yacht was larger than it is") is explained by presence or
absence of an ACTUALLY operator that fixes evaluation to the actual world,
NOT by scope differences of degree operators or definite descriptions.

## Synthesis Rules

R4 (*more* / *-er*): `w ∈ ⟦more⟧(d₁)(A⁰)(d₂)(x) iff w ∈ A⁰(x, d₁ + d₂)`.
This unifies plain comparatives (d₁ > 0, d₂ contextual) and differentials
("6 inches taller" = d₁ ≥ 6 inches) in a single 4-place relation.

R5 (*as*): same structure but with multiplication: `d₁ · d₂`.

These connect to existing `comparativeSem`, `differentialComparative`,
`factorEquative`, and `equativeLiteral` via bridge theorems.

-/

namespace Semantics.Degree.Intensional

open Semantics.Degree.Comparative (comparativeSem ScaleDirection)
open Semantics.Degree.Differential (differentialComparative factorEquative)
open Semantics.Degree.Equative (equativeLiteral)
open Semantics.Degree.DegreeAbstraction (IsMaxDeg)

-- ════════════════════════════════════════════════════
-- § 1. ACTUALLY Operator for Degrees
-- ════════════════════════════════════════════════════

/-- Evaluate an intension at the actual world w₀.

    This is NOT @cite{kaplan-1989}'s tower-based indexical ACTUALLY
    (which manipulates context-index pairs for demonstratives).
    @cite{von-stechow-1984}'s operator is simpler: given a world-dependent
    value, extract its extension at w₀. Defined via `Core.Intension.evalAt`
    with arguments flipped (world first, for readability in comparative
    constructions where the actual world is syntactically prominent).

    The key role is in comparative constructions: presence of ACTUALLY in
    the than-clause yields the de re (consistent) reading; absence yields
    the de dicto (potentially contradictory) reading. -/
def actuallyDeg {W D : Type*} (w₀ : W) (f : W → D) : D :=
  Core.Intension.evalAt f w₀

-- ════════════════════════════════════════════════════
-- § 2. World-Indexed Comparatives
-- ════════════════════════════════════════════════════

variable {W Entity D : Type*} [LinearOrder D]

/-- Comparative with world-indexed measure functions.
    Adjectives denote 2-place relations between individuals and degrees,
    evaluated at a world (R3). -/
def intensionalComparative
    (μ : W → Entity → D) (w : W) (a b : Entity) : Prop :=
  μ w a > μ w b

/-- When μ is rigid (world-invariant), `intensionalComparative` reduces
    to the extensional `comparativeSem`. -/
theorem intensional_extensional_bridge
    (μe : Entity → D) (w : W) (a b : Entity) :
    intensionalComparative (λ _ => μe) w a b ↔
      comparativeSem μe a b .positive := by
  simp [intensionalComparative, comparativeSem]

-- ════════════════════════════════════════════════════
-- § 3. Russell's Ambiguity
-- ════════════════════════════════════════════════════

/-- De re reading: "I thought your yacht was larger than it ACTUALLY is."
    The than-clause contains ACTUALLY, so the standard is evaluated at
    the actual world w₀, while the matrix is evaluated in the belief
    world wBel. This reading is consistent — one can coherently believe
    that an object exceeds its actual size. -/
def deReComparative
    (μ : W → Entity → D) (w₀ wBel : W) (x : Entity) : Prop :=
  μ wBel x > actuallyDeg w₀ (λ w => μ w x)

/-- De dicto reading: "I thought your yacht was larger than it is."
    No ACTUALLY — both matrix and standard evaluated in the belief world.
    This yields a contradictory thought: μ(wBel,x) > μ(wBel,x). -/
def deDictoComparative
    (μ : W → Entity → D) (wBel : W) (x : Entity) : Prop :=
  μ wBel x > μ wBel x

/-- The de dicto reading is contradictory: no entity can exceed its own
    degree in any world. -/
theorem deDicto_absurd
    (μ : W → Entity → D) (wBel : W) (x : Entity) :
    ¬ deDictoComparative μ wBel x :=
  lt_irrefl _

/-- The de re reading reduces to comparing belief-world degree against
    the ACTUALLY-extracted actual-world degree. -/
theorem deRe_unfolds
    (μ : W → Entity → D) (w₀ wBel : W) (x : Entity) :
    deReComparative μ w₀ wBel x ↔ μ wBel x > μ w₀ x := by
  simp [deReComparative, actuallyDeg, Core.Intension.evalAt]

-- ════════════════════════════════════════════════════
-- § 4. Max Degree Over Accessible Worlds
-- ════════════════════════════════════════════════════

/-- Maximal degree across a set of accessible worlds.
    "The biggest a polar bear could be" = max over ◇-accessible worlds
    of μ(polar bear). Used for modal comparatives (§VIII).

    The `acc` parameter is a set of worlds (typically `{w | R w₀ w = true}`
    for some `Core.ModalLogic.AccessRel R` and base world `w₀`). -/
def IsMaxDegOverWorlds
    (acc : Set W) (μw : W → D) (d : D) : Prop :=
  (∃ w ∈ acc, μw w = d) ∧ ∀ w ∈ acc, μw w ≤ d

/-- `IsMaxDegOverWorlds` is `IsGreatest` on the degree image:
    d is the greatest element of `μw '' acc`. -/
theorem isMaxDegOverWorlds_iff_isGreatest
    (acc : Set W) (μw : W → D) (d : D) :
    IsMaxDegOverWorlds acc μw d ↔ IsGreatest (μw '' acc) d := by
  constructor
  · rintro ⟨hmem, hle⟩
    refine ⟨?_, fun d' hd' => ?_⟩
    · obtain ⟨w, hw, rfl⟩ := hmem
      exact Set.mem_image_of_mem μw hw
    · obtain ⟨w', hw', rfl⟩ := hd'
      exact hle w' hw'
  · rintro ⟨himg, hle⟩
    exact ⟨himg, fun w' hw' => hle (Set.mem_image_of_mem μw hw')⟩

/-- If the max possible A-degree exceeds the max possible B-degree,
    then the A-witness world beats every B-world. -/
theorem maxDeg_witness {W D : Type*} [LinearOrder D]
    (acc : Set W) (μA μB : W → D) (maxA maxB : D)
    (hmaxA : IsMaxDegOverWorlds acc μA maxA)
    (hmaxB : IsMaxDegOverWorlds acc μB maxB)
    (hgt : maxA > maxB) :
    ∃ w ∈ acc, ∀ v ∈ acc, μA w > μB v := by
  obtain ⟨⟨w, hw, heq⟩, _⟩ := hmaxA
  exact ⟨w, hw, fun v hv => by rw [heq]; exact lt_of_le_of_lt (hmaxB.2 v hv) hgt⟩

-- ════════════════════════════════════════════════════
-- § 5. Von Stechow's Synthesis Rules R4 and R5
-- ════════════════════════════════════════════════════

/-- R4: ⟦more⟧(d₁)(A⁰)(d₂)(x) iff A⁰(x, d₁ + d₂).

    *more* / *-er* is a 4-place relation. The "differential" degree d₁
    specifies the gap; d₂ is the standard's maximal degree (from the
    than-clause via Max). Plain comparatives have d₁ > 0 supplied by
    context; measure phrase differentials make d₁ explicit.

    The positive and equative arise as special cases:
    - Comparative: d₁ > 0 (some positive degree), d₂ = max than-clause
    - Positive: d₁ > 0, d₂ = 0 (no standard)
    - Equative: d₁ = 1 (factor), d₂ = standard (via multiplication in R5) -/
def moreSem {Entity : Type*}
    (μ : Entity → ℚ) (x : Entity) (d₁ d₂ : ℚ) : Prop :=
  μ x ≥ d₁ + d₂

/-- R5: ⟦as⟧ uses multiplication instead of addition.

    "Ede is twice as fat as Angelika" = μ(Ede) ≥ 2 · μ(Angelika).
    The "at least" semantics explains equative vagueness: context supplies
    the factor (exactly 1 for "exactly as", at least 1 for "at least as"). -/
def asSem {Entity : Type*}
    (μ : Entity → ℚ) (x : Entity) (d₁ d₂ : ℚ) : Prop :=
  μ x ≥ d₁ * d₂

-- ════════════════════════════════════════════════════
-- § 6. Bridge Theorems
-- ════════════════════════════════════════════════════

/-- R4 with d₁ > 0 and d₂ = μ(b) yields `comparativeSem .positive`. -/
theorem moreSem_comparative_bridge {Entity : Type*}
    (μ : Entity → ℚ) (a b : Entity) (d₁ : ℚ) (hd₁ : d₁ > 0) :
    moreSem μ a d₁ (μ b) → comparativeSem μ a b .positive := by
  intro h
  simp only [moreSem] at h
  simp only [comparativeSem]
  linarith

/-- Exact differential entails R4's "at least" semantics:
    if μ(a) - μ(b) = diff, then μ(a) ≥ diff + μ(b). -/
theorem moreSem_differential_bridge {Entity : Type*}
    (μ : Entity → ℚ) (a b : Entity) (diff : ℚ) :
    differentialComparative μ a b diff → moreSem μ a diff (μ b) := by
  intro h
  simp only [moreSem, differentialComparative] at *
  linarith

/-- R5 with factor = 1 reduces to equative literal semantics:
    "as tall as B" = μ(a) ≥ 1 · μ(b) = μ(a) ≥ μ(b). -/
theorem asSem_equative_bridge {Entity : Type*}
    (μ : Entity → ℚ) (a b : Entity) :
    asSem μ a 1 (μ b) ↔ equativeLiteral μ a b := by
  simp [asSem, equativeLiteral, one_mul]

/-- R5 reduces to factorEquative when the inequality is tight. -/
theorem asSem_factor_bridge {Entity : Type*}
    (μ : Entity → ℚ) (a b : Entity) (factor : ℚ) :
    factorEquative μ a b factor → asSem μ a factor (μ b) := by
  intro h
  simp only [asSem, factorEquative] at *
  linarith

-- ════════════════════════════════════════════════════
-- § 7. *too* as Counterfactual Comparative (R13)
-- ════════════════════════════════════════════════════

/-- R13: *too* is a counterfactual comparative morpheme.

    ⟦too⟧(d₁)(A⁰)(p)(x) = the max.d [x is d-A⁰] λd₂ [p □→ A⁰(x, d₂ − d₁)]

    The counterfactual threshold is the max degree d such that
    p □→ A⁰(x, d). The actual degree exceeds this threshold by
    at least `excess` (= d₁, the differential).

    Definitionally equal to `moreSem` — *too* and *-er* share the
    same additive structure, differing only in where the standard
    comes from (counterfactual vs. than-clause). -/
def tooSem {Entity : Type*}
    (μ : Entity → ℚ) (x : Entity) (excess threshold : ℚ) : Prop :=
  moreSem μ x excess threshold

/-- *too* and *-er* are the same additive operator (R4 = R13
    structurally). The only difference is the standard source. -/
theorem tooSem_eq_moreSem {Entity : Type*}
    (μ : Entity → ℚ) (x : Entity) (excess threshold : ℚ) :
    tooSem μ x excess threshold ↔ moreSem μ x excess threshold :=
  Iff.rfl

/-- If x is (positively) too A for some counterfactual, then x's
    actual degree exceeds x's degree in every counterfactual world.

    Content: "50 kg too heavy to lift" means in every world where
    you can lift the pack, it weighs strictly less than it actually
    does. The excess d₁ > 0 creates the strict gap. -/
theorem tooSem_exceeds_counterfactual_worlds {W Entity : Type*}
    (μ : W → Entity → ℚ) (w₀ : W) (acc : Set W) (x : Entity)
    (threshold excess : ℚ) (hexcess : excess > 0)
    (hmax : IsMaxDegOverWorlds acc (λ w => μ w x) threshold)
    (htoo : tooSem (μ w₀) x excess threshold) :
    ∀ w ∈ acc, μ w₀ x > μ w x := by
  intro w hw
  simp only [tooSem, moreSem] at htoo
  have hle := hmax.2 w hw
  linarith

-- ════════════════════════════════════════════════════
-- § 8. Bridge to Kripke Modality
-- ════════════════════════════════════════════════════

/-- Convert a binary accessibility relation to a set of worlds.
    When `R` is a `Core.ModalLogic.AccessRel`, this gives the set
    of R-accessible worlds from w₀, suitable for `IsMaxDegOverWorlds`
    and `maxDeg_witness`.

    This bridges the abstract intensional degree infrastructure to
    concrete Kripke frames used in `Core.Logic.ModalLogic` and
    `Theories.Semantics.Modality.Kratzer`. -/
def accessibleSet {W : Type*} (R : W → W → Bool) (w₀ : W) : Set W :=
  {w | R w₀ w = true}

/-- Modal comparatives grounded in Kripke accessibility.

    "A polar bear could be bigger than a grizzly bear could be"
    means: the max A-degree over ◇-accessible worlds exceeds the
    max B-degree. The conclusion is stated in terms of the raw
    accessibility relation R, not the set wrapper. -/
theorem modalComparative_kripke {W D : Type*} [LinearOrder D]
    (R : W → W → Bool) (w₀ : W)
    (μA μB : W → D) (maxA maxB : D)
    (hmaxA : IsMaxDegOverWorlds (accessibleSet R w₀) μA maxA)
    (hmaxB : IsMaxDegOverWorlds (accessibleSet R w₀) μB maxB)
    (hgt : maxA > maxB) :
    ∃ w, R w₀ w = true ∧ ∀ v, R w₀ v = true → μA w > μB v := by
  obtain ⟨w, hw, hwitness⟩ :=
    maxDeg_witness (accessibleSet R w₀) μA μB maxA maxB hmaxA hmaxB hgt
  exact ⟨w, hw, hwitness⟩

-- ════════════════════════════════════════════════════
-- § 9. LITTLE–□ Non-Commutativity (De Morgan)
-- ════════════════════════════════════════════════════

-- The algebraic core of @cite{buring-2007} §6: degree negation
-- (LITTLE) does not commute with modal operators (□/◇). The two
-- orderings are:
--
--   Analysis 1: LITTLE(□(P))  = ¬(∀w. P(w))  = "exceeds the min"
--   Analysis 2: □(LITTLE(P))  = ∀w. ¬P(w)    = "exceeds every complement"
--
-- These differ by De Morgan's inequality for infinite meets:
-- ¬⋀ Pᵢ ≠ ⋀ ¬Pᵢ  (in general).
--
-- For degree predicates on a linear order:
--   Analysis 1: d > min{μ(w) | w ∈ acc}  (exceeds minimum)
--   Analysis 2: ∀w ∈ acc. d > μ(w)       (exceeds all = exceeds maximum)
--
-- Analysis 2 is STRICTLY STRONGER — it requires exceeding the max,
-- not just the min. When min < max (non-trivial accessible set),
-- there exist degrees between them: satisfying Analysis 1 but not 2.

/-- **Analysis 1**: LITTLE scopes over □.
    "shorter than it has to be wide" = bridge-length < min-required-width.
    The comparative takes the minimum over the modal base, then negates:
    LITTLE(□(λd. d ≤ μ_w(x))) extracts the min degree across worlds. -/
def littleOverBox {W D : Type*} [LinearOrder D]
    (acc : Set W) (μw : W → D) (d : D) : Prop :=
  ∃ w ∈ acc, d > μw w

/-- **Analysis 2**: □ scopes over LITTLE.
    "shorter than it has to be narrow" = bridge-length < max-permitted-narrowness.
    The modal quantifies over complements:
    □(LITTLE(λd. d ≤ μ_w(x))) requires exceeding μ_w(x) in EVERY world. -/
def boxOverLittle {W D : Type*} [LinearOrder D]
    (acc : Set W) (μw : W → D) (d : D) : Prop :=
  ∀ w ∈ acc, d > μw w

/-- Analysis 2 (□ over LITTLE) entails Analysis 1 (LITTLE over □),
    but not vice versa. This is the non-trivial direction of De Morgan:
    ⋀(¬Pᵢ) → ¬(⋀Pᵢ), i.e., "exceeds all" → "exceeds some". -/
theorem boxOverLittle_implies_littleOverBox {W D : Type*} [LinearOrder D]
    (acc : Set W) (μw : W → D) (d : D)
    (hne : ∃ w, w ∈ acc) :
    boxOverLittle acc μw d → littleOverBox acc μw d := by
  intro hall
  obtain ⟨w, hw⟩ := hne
  exact ⟨w, hw, hall w hw⟩

/-- The converse fails: Analysis 1 does NOT entail Analysis 2. There
    exist accessible sets where exceeding the minimum does not require
    exceeding the maximum.

    Witness: acc = {w₁, w₂} with μ(w₁) = 5, μ(w₂) = 10, d = 7.
    Then d > min(5,10) = 5 (Analysis 1 holds) but d ≯ max(5,10) = 10
    (Analysis 2 fails).

    This is the formal content of @cite{buring-2007} §6: the two
    analyses make different predictions when the accessible set is
    non-trivial (multiple permitted worlds with different degrees). -/
theorem littleOverBox_not_implies_boxOverLittle :
    ¬ (∀ (acc : Set Bool) (μw : Bool → ℚ) (d : ℚ),
        littleOverBox acc μw d → boxOverLittle acc μw d) := by
  intro h
  have := h {true, false} (fun b => if b then 5 else 10) 7
  simp only [littleOverBox, boxOverLittle] at this
  have h1 : ∃ w ∈ ({true, false} : Set Bool), (7 : ℚ) > (if w then 5 else 10) :=
    ⟨true, Set.mem_insert _ _, by norm_num⟩
  have h2 := this h1 false (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton _)))
  norm_num at h2

/-- When all accessible worlds agree on degree (trivial modal base),
    the two analyses collapse — scope is undetectable. This is
    @cite{heim-2001}'s monotone collapse at the modal level. -/
theorem littleBox_collapse_when_uniform {W D : Type*} [LinearOrder D]
    (acc : Set W) (μw : W → D) (d : D)
    (hne : ∃ w, w ∈ acc)
    (hunif : ∀ w₁ ∈ acc, ∀ w₂ ∈ acc, μw w₁ = μw w₂) :
    littleOverBox acc μw d ↔ boxOverLittle acc μw d := by
  constructor
  · rintro ⟨w, hw, hgt⟩
    intro v hv
    rw [hunif v hv w hw]
    exact hgt
  · exact boxOverLittle_implies_littleOverBox acc μw d hne

end Semantics.Degree.Intensional
