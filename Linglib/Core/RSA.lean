/-
# Linglib.Core.RSA

Core RSA (Rational Speech Acts) infrastructure.

## Architecture

RSA uses exact rational arithmetic (ℚ) for all probability computations.
This enables mathematical proofs about pragmatic reasoning.

### Key Types

- `RSAScenario`: Scenario specifying utterances, worlds, and meanings
- `ParametricRSAScenario`: For lifted-variable RSA (scope ambiguity)

### RSA Model

RSA models communication as recursive reasoning between speakers and listeners:
- L0: Literal interpretation (semantic denotation)
- S1: Pragmatic speaker (chooses utterances to maximize informativity)
- L1: Pragmatic listener (reasons about what speaker meant)

Reference: Frank & Goodman (2012), Goodman & Frank (2016)
-/

import Mathlib.Data.Rat.Defs

-- ============================================================================
-- RSAScenario: Core Interface
-- ============================================================================

/--
RSA scenario: specifies utterances, worlds, and how they relate.

## Fields

- `φ`: Agreement function (meaning). Values in [0,1] where 1 = fully true.
- `prior`: Prior distribution over worlds (default: uniform)
- `α`: Rationality parameter (default: 1)

## Usage

```lean
def myScenario : RSAScenario :=
  RSAScenario.ofBool [.some_, .all_] [.w0, .w1, .w2] mySatisfies
```
-/
structure RSAScenario where
  /-- Type of utterances -/
  Utterance : Type
  /-- Type of possible worlds -/
  World : Type
  /-- Agreement function: how well does utterance describe world? -/
  φ : Utterance → World → ℚ
  /-- Enumeration of all utterances -/
  utterances : List Utterance
  /-- Enumeration of all worlds -/
  worlds : List World
  /-- Prior distribution over worlds (default: uniform) -/
  prior : World → ℚ := fun _ => 1
  /-- Rationality parameter (default: 1) -/
  α : ℚ := 1
  /-- BEq instance for utterances -/
  [uttBEq : BEq Utterance]
  /-- BEq instance for worlds -/
  [worldBEq : BEq World]

attribute [instance] RSAScenario.uttBEq RSAScenario.worldBEq

-- ============================================================================
-- Boolean Semantics Helper
-- ============================================================================

/-- Convert Bool to ℚ (1 if true, 0 if false) -/
def boolToRat (b : Bool) : ℚ := if b then 1 else 0

/--
Build RSAScenario from a Boolean satisfaction relation.

This is the primary way to create scenarios from classical semantics.
The φ function becomes an indicator function: 1 if true, 0 if false.
-/
def RSAScenario.ofBool {Utterance World : Type} [BEq Utterance] [BEq World]
    (utterances : List Utterance) (worlds : List World)
    (satisfies : World → Utterance → Bool) : RSAScenario where
  Utterance := Utterance
  World := World
  φ u w := boolToRat (satisfies w u)
  utterances := utterances
  worlds := worlds

/-- Property: a scenario has Boolean semantics (φ only returns 0 or 1) -/
def RSAScenario.isBoolean (S : RSAScenario) : Prop :=
  ∀ u w, S.φ u w = 0 ∨ S.φ u w = 1

-- ============================================================================
-- RSA Computations
-- ============================================================================

namespace RSA

/-- Sum a list of rationals -/
def sumScores (scores : List ℚ) : ℚ :=
  scores.foldl (· + ·) 0

/-- Look up score in distribution -/
def getScore {α : Type} [BEq α] (dist : List (α × ℚ)) (x : α) : ℚ :=
  match dist.find? (·.1 == x) with
  | some (_, s) => s
  | none => 0

/-- Normalize a distribution (divide each score by total) -/
def normalize {α : Type} (dist : List (α × ℚ)) : List (α × ℚ) :=
  let total := sumScores (dist.map (·.2))
  dist.map fun (x, s) =>
    (x, if total ≠ 0 then s / total else 0)

/--
Helper: getScore on a normalized list returns 0 when the pre-normalized score is 0.
-/
theorem getScore_normalize_zero {α : Type} [BEq α] [LawfulBEq α]
    (dist : List (α × ℚ)) (x : α)
    (hzero : getScore dist x = 0) :
    getScore (normalize dist) x = 0 := by
  unfold getScore normalize at *
  simp only [List.find?_map, Function.comp_def]
  -- Case split on whether find? finds something in the normalized list
  split
  · -- some case: found x in the normalized list
    rename_i result p heq
    rw [Option.map_eq_some_iff] at heq
    obtain ⟨⟨x', s⟩, hfind, heq'⟩ := heq
    simp only [Prod.mk.injEq] at heq'
    obtain ⟨_, hp⟩ := heq'
    rw [← hp]
    -- hfind : find? ... dist = some (x', s)
    -- hzero is about the same find?, so s = 0
    -- We need to show s / total = 0 (or 0 if total = 0)
    -- Since the same find? returns (x', s), hzero tells us s = 0
    -- Goal: (if total ≠ 0 then s / total else 0) = 0
    split at hzero
    · -- In hzero, find? returned some
      rename_i fst' s' heq''
      -- heq'' : find? ... dist = some (fst', s'), and hzero : s' = 0
      -- hfind : find? ... dist = some (x', s)
      -- Since both are the same find?, (x', s) = (fst', s'), so s = s' = 0
      have h_eq : some (x', s) = some (fst', s') := hfind ▸ heq''
      simp only [Option.some.injEq, Prod.mk.injEq] at h_eq
      obtain ⟨_, hs_eq⟩ := h_eq
      rw [hs_eq, hzero, Rat.div_def, Rat.zero_mul]
      simp only [ite_self]
    · -- In hzero, find? returned none
      rename_i heq''
      -- But hfind says find? returned some, contradiction
      rw [hfind] at heq''
      simp at heq''
  · -- none case: not found, return 0
    rfl

-- ============================================================================
-- L0: Literal Listener
-- ============================================================================

/--
L0: Literal listener distribution.

P(w | u) ∝ P(w) · φ(u, w)

The literal listener updates prior beliefs by the meaning function,
uniformly distributing probability over worlds where utterance is true
(for Boolean semantics) or proportionally to φ (for graded semantics).
-/
def L0 (S : RSAScenario) (u : S.Utterance) : List (S.World × ℚ) :=
  let scores := S.worlds.map fun w => (w, S.prior w * S.φ u w)
  normalize scores

-- ============================================================================
-- S1: Pragmatic Speaker
-- ============================================================================

/--
S1: Pragmatic speaker distribution.

P(u | w) ∝ L0(w | u)^α

The speaker chooses utterances proportional to how well L0 recovers
the intended world. For α=1 (default), this is just L0(w|u) normalized.

More informative (less ambiguous) utterances are preferred.
-/
def S1 (S : RSAScenario) (w : S.World) : List (S.Utterance × ℚ) :=
  let scores := S.utterances.map fun u => (u, getScore (L0 S u) w)
  normalize scores

-- ============================================================================
-- L1: Pragmatic Listener
-- ============================================================================

/--
L1: Pragmatic listener distribution.

P(w | u) ∝ P(w) · S1(u | w)

The pragmatic listener reasons about what world would make a rational
speaker choose this utterance.
-/
def L1 (S : RSAScenario) (u : S.Utterance) : List (S.World × ℚ) :=
  let scores := S.worlds.map fun w => (w, S.prior w * getScore (S1 S w) u)
  normalize scores

-- ============================================================================
-- Convenience Probability Accessors
-- ============================================================================

/-- Get L0 probability for a specific world -/
def L0_prob (S : RSAScenario) (u : S.Utterance) (w : S.World) : ℚ :=
  getScore (L0 S u) w

/-- Get S1 probability for a specific utterance -/
def S1_prob (S : RSAScenario) (w : S.World) (u : S.Utterance) : ℚ :=
  getScore (S1 S w) u

/-- Get L1 probability for a specific world -/
def L1_prob (S : RSAScenario) (u : S.Utterance) (w : S.World) : ℚ :=
  getScore (L1 S u) w

-- ============================================================================
-- Helpers
-- ============================================================================

/-- Count worlds compatible with an utterance -/
def compatibleCount (S : RSAScenario) (u : S.Utterance) : Nat :=
  (S.worlds.filter fun w => S.φ u w > 0).length

/-- Informativity of an utterance = 1 / (compatible worlds) -/
def informativity (S : RSAScenario) (u : S.Utterance) : ℚ :=
  let n := compatibleCount S u
  if n > 0 then 1 / n else 0

-- ============================================================================
-- Theorems
-- ============================================================================

/--
L0 assigns zero probability to worlds where utterance has zero φ.

When φ(u,w) = 0:
1. Pre-normalization score is `prior(w) * 0 = 0`
2. After normalization, `0 / total = 0`
-/
theorem L0_zero_when_false (S : RSAScenario) (u : S.Utterance) (w : S.World)
    (hfalse : S.φ u w = 0) :
    ∀ p, (w, p) ∈ (L0 S u) → p = 0 := by
  intro p hmem
  unfold L0 normalize at hmem
  -- Combine the two maps into one
  rw [List.map_map] at hmem
  simp only [List.mem_map, Function.comp_def] at hmem
  obtain ⟨w', hw', heq⟩ := hmem
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, hp⟩ := heq
  -- Now w' = w, and hp tells us what p equals
  rw [← hp, hfalse, Rat.mul_zero, Rat.div_def, Rat.zero_mul]
  simp only [ite_self]

/--
L0_prob is zero when φ is zero.

This is a key grounding theorem: when the semantic meaning function
returns false (φ = 0), the literal listener assigns zero probability.

Requires LawfulBEq to convert `w' == w = true` to `w' = w`.
-/
theorem L0_prob_zero_when_false (S : RSAScenario)
    [LawfulBEq S.World]
    (u : S.Utterance) (w : S.World)
    (hfalse : S.φ u w = 0) :
    L0_prob S u w = 0 := by
  unfold L0_prob L0 getScore normalize
  simp only [List.find?_map, Function.comp_def]
  split
  · -- some case: found w in the list
    rename_i result p heq
    rw [Option.map_eq_some_iff] at heq
    obtain ⟨⟨w', s⟩, hfind, heq'⟩ := heq
    -- hfind : Option.map ... = some (w', s)
    rw [Option.map_eq_some_iff] at hfind
    obtain ⟨w'', hfind', hw''_eq⟩ := hfind
    -- hfind' : List.find? (fun x => x == w) S.worlds = some w''
    have hw''_beq := List.find?_some hfind'
    rw [beq_iff_eq] at hw''_beq
    -- hw''_beq : w'' = w
    -- hw''_eq : (w'', S.prior w'' * S.φ u w'') = (w', s)
    cases heq'
    cases hw''_eq
    -- Now goal is about (if ... then s/total else 0) = (if ... then (prior * φ)/total else 0)
    rw [hw''_beq, hfalse, Rat.mul_zero, Rat.div_def, Rat.zero_mul]
    simp only [ite_self]
  · -- none case: w not found
    rfl

/--
S1 assigns zero probability to utterances with zero φ at the world.

Note: This theorem requires LawfulBEq to convert BEq equality to Prop equality.
For scenarios with decidable equality (most practical cases), this holds automatically.
-/
theorem S1_zero_when_false (S : RSAScenario)
    [LawfulBEq S.World] [LawfulBEq S.Utterance]
    (w : S.World) (u : S.Utterance)
    (hfalse : S.φ u w = 0) :
    S1_prob S w u = 0 := by
  -- First establish that L0_prob S u w = 0
  have hL0 : L0_prob S u w = 0 := L0_prob_zero_when_false S u w hfalse
  -- Unfold S1_prob and S1
  unfold S1_prob S1
  -- S1 = normalize (map (..., getScore (L0 S u) w) S.utterances)
  -- We need: getScore (normalize ...) u = 0
  -- The pre-normalized list has (u, getScore (L0 S u) w) = (u, 0) by hL0
  -- By getScore_normalize_zero, after normalization it's still 0
  apply getScore_normalize_zero
  -- Show the pre-normalized score is 0
  -- Goal: getScore (map (fun u => (u, getScore (L0 S u) w)) S.utterances) u = 0
  unfold getScore
  simp only [List.find?_map, Function.comp_def]
  split
  · -- some case: found u in the list
    rename_i heq
    rw [Option.map_eq_some_iff] at heq
    obtain ⟨u', hfind, heq'⟩ := heq
    have hu'_beq := List.find?_some hfind
    rw [beq_iff_eq] at hu'_beq
    simp only [Prod.mk.injEq] at heq'
    obtain ⟨_, hp⟩ := heq'
    -- u' = u, and the score is getScore (L0 S u') w = getScore (L0 S u) w = 0
    rw [← hp, hu'_beq]
    -- Goal: getScore (L0 S u) w = 0
    -- This is exactly L0_prob S u w = 0, which is hL0
    unfold L0_prob at hL0
    exact hL0
  · -- none case: u not found
    rfl

end RSA

-- ============================================================================
-- ParametricRSAScenario (for Lifted-Variable RSA)
-- ============================================================================

namespace ParametricRSA

/--
RSA scenario with an interpretation parameter.

Supports "lifted-variable" RSA models where:
- **Interp** represents different ways to interpret an utterance
  (e.g., scope readings: surface vs inverse)
- **φ** is parameterized by interpretation

## Example: Scope Ambiguity

"Every horse didn't jump"
- Interp = {surface, inverse}
- φ surface u w = ∀x.¬jump(x) in w
- φ inverse u w = ¬∀x.jump(x) in w

Reference: Scontras & Pearl (2021)
-/
structure ParametricRSAScenario where
  Utterance : Type
  World : Type
  Interp : Type
  /-- Parameterized agreement function -/
  φ : Interp → Utterance → World → ℚ
  utterances : List Utterance
  worlds : List World
  interps : List Interp
  /-- Prior over worlds -/
  prior : World → ℚ := fun _ => 1
  /-- Prior over interpretations -/
  interpPrior : Interp → ℚ := fun _ => 1
  /-- Rationality parameter -/
  α : ℚ := 1
  [uttBEq : BEq Utterance]
  [worldBEq : BEq World]
  [interpBEq : BEq Interp]

attribute [instance] ParametricRSAScenario.uttBEq ParametricRSAScenario.worldBEq ParametricRSAScenario.interpBEq

-- ============================================================================
-- Parametric L0, S1, L1
-- ============================================================================

/--
L0 given a fixed interpretation.

P(w | u, i) ∝ P(w) · φ(i, u, w)
-/
def L0 (S : ParametricRSAScenario) (i : S.Interp) (u : S.Utterance) : List (S.World × ℚ) :=
  let scores := S.worlds.map fun w => (w, S.prior w * S.φ i u w)
  RSA.normalize scores

/--
S1 given a fixed interpretation.

P(u | w, i) ∝ L0(w | u, i)
-/
def S1 (S : ParametricRSAScenario) (i : S.Interp) (w : S.World) : List (S.Utterance × ℚ) :=
  let scores := S.utterances.map fun u => (u, RSA.getScore (L0 S i u) w)
  RSA.normalize scores

/--
L1 joint distribution over (World × Interp).

P(w, i | u) ∝ P(w) · P(i) · S1(u | w, i)

Returns unnormalized scores over all (world, interpretation) pairs.
-/
def L1_joint (S : ParametricRSAScenario) (u : S.Utterance) : List ((S.World × S.Interp) × ℚ) :=
  let pairs := S.worlds.flatMap fun w => S.interps.map fun i => (w, i)
  let scores := pairs.map fun (w, i) =>
    let priorScore := S.prior w * S.interpPrior i
    let s1Score := RSA.getScore (S1 S i w) u
    ((w, i), priorScore * s1Score)
  RSA.normalize scores

/--
L1 marginal over worlds.

P(w | u) = Σ_i P(w, i | u)
-/
def L1_world (S : ParametricRSAScenario) (u : S.Utterance) : List (S.World × ℚ) :=
  let joint := L1_joint S u
  S.worlds.map fun w =>
    let wScores := joint.filter (·.1.1 == w) |>.map (·.2)
    (w, RSA.sumScores wScores)

/--
L1 marginal over interpretations.

P(i | u) = Σ_w P(w, i | u)
-/
def L1_interp (S : ParametricRSAScenario) (u : S.Utterance) : List (S.Interp × ℚ) :=
  let joint := L1_joint S u
  S.interps.map fun i =>
    let iScores := joint.filter (·.1.2 == i) |>.map (·.2)
    (i, RSA.sumScores iScores)

-- ============================================================================
-- Boolean Semantics Helper
-- ============================================================================

/--
Build ParametricRSAScenario from a Boolean satisfaction relation.
-/
def ParametricRSAScenario.ofBool {Utterance World Interp : Type}
    [BEq Utterance] [BEq World] [BEq Interp]
    (utterances : List Utterance) (worlds : List World) (interps : List Interp)
    (satisfies : Interp → World → Utterance → Bool) : ParametricRSAScenario where
  Utterance := Utterance
  World := World
  Interp := Interp
  φ i u w := boolToRat (satisfies i w u)
  utterances := utterances
  worlds := worlds
  interps := interps

-- ============================================================================
-- Helpers
-- ============================================================================

/-- Count worlds compatible with utterance under interpretation -/
def compatibleCount (S : ParametricRSAScenario)
    (i : S.Interp) (u : S.Utterance) : Nat :=
  (S.worlds.filter fun w => S.φ i u w > 0).length

/-- Informativity under interpretation -/
def informativity (S : ParametricRSAScenario)
    (i : S.Interp) (u : S.Utterance) : ℚ :=
  let n := compatibleCount S i u
  if n > 0 then 1 / n else 0

end ParametricRSA

-- ============================================================================
-- Legacy Aliases (for backward compatibility)
-- ============================================================================

/-- RSAScenario with exact rational arithmetic -/
abbrev ExactRSAScenario := RSAScenario

/-- Parametric RSA scenario with exact rational arithmetic -/
abbrev ExactParametricRSAScenario := ParametricRSA.ParametricRSAScenario

namespace ParametricRSA
/-- Alias within namespace for backward compatibility -/
abbrev ExactParametricRSAScenario := ParametricRSAScenario
end ParametricRSA
