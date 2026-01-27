/-
# Linglib.Core.RSA

Core RSA (Rational Speech Acts) infrastructure.

## Architecture

RSA uses exact rational arithmetic (ℚ) for all probability computations.
This enables mathematical proofs about pragmatic reasoning.

### Key Type

- `RSAScenario`: Unified type supporting all RSA variants

### RSA Model

RSA models communication as recursive reasoning between speakers and listeners:
- L0: Literal interpretation (semantic denotation)
- S1: Pragmatic speaker (chooses utterances to maximize informativity)
- L1: Pragmatic listener (reasons about what speaker meant)
- S2: Second-level pragmatic speaker

### Smart Constructors

- `RSAScenario.basic`: Simple reference games (no interp, no QUD)
- `RSAScenario.basicBool`: Boolean version of basic
- `RSAScenario.ambiguous`: Scope/interpretation ambiguity (Scontras & Pearl)
- `RSAScenario.ambiguousBool`: Boolean version of ambiguous
- `RSAScenario.qud`: QUD-sensitive models (Kao et al.)
- `RSAScenario.qudBool`: Boolean version of qud

Reference: Frank & Goodman (2012), Goodman & Frank (2016)
-/

import Mathlib.Data.Rat.Defs
import Linglib.Core.Distribution

-- ============================================================================
-- Utility Functions
-- ============================================================================

/-- Convert Bool to ℚ (1 if true, 0 if false) -/
def boolToRat (b : Bool) : ℚ := if b then 1 else 0

-- ============================================================================
-- RSAScenario: Unified Type (supports all RSA variants)
-- ============================================================================

/--
Unified RSA scenario supporting all RSA model variants.

This is the unified type supporting:
- Basic models (Interp = Unit, QUD = Unit)
- Scope ambiguity models (QUD = Unit)
- QUD-sensitive models (Interp = Unit)
- Full models (with both Interp and QUD)

## Fields

- `Utterance`, `World`, `Interp`, `QUD`: Domain types
- `φ`: Agreement function parameterized by interpretation
- `qudProject`: QUD equivalence relation on worlds
- `worldPrior`, `interpPrior`, `qudPrior`: Prior distributions
- `α`: Rationality parameter

## Smart Constructors

Use the smart constructors for common patterns:
- `RSAScenario.basic`: Simple reference games
- `RSAScenario.ambiguous`: Scope ambiguity
- `RSAScenario.qud`: QUD-sensitive models (hyperbole, metaphor)
-/
structure RSAScenario where
  /-- Type of utterances -/
  Utterance : Type
  /-- Type of world states -/
  World : Type
  /-- Type of interpretations (e.g., scope readings). Use Unit for basic models. -/
  Interp : Type := Unit
  /-- Type of QUDs. Use Unit for non-QUD models. -/
  QUD : Type := Unit
  /-- Agreement function: φ(interp, utterance, world) ∈ [0,1] -/
  φ : Interp → Utterance → World → ℚ
  /-- QUD projection: are two worlds equivalent under this QUD? -/
  qudProject : QUD → World → World → Bool
  /-- Enumeration of utterances -/
  utterances : List Utterance
  /-- Enumeration of worlds -/
  worlds : List World
  /-- Enumeration of interpretations -/
  interps : List Interp
  /-- Enumeration of QUDs -/
  quds : List QUD
  /-- Prior over worlds -/
  worldPrior : World → ℚ := fun _ => 1
  /-- Prior over interpretations -/
  interpPrior : Interp → ℚ := fun _ => 1
  /-- Prior over QUDs -/
  qudPrior : QUD → ℚ := fun _ => 1
  /-- Rationality parameter. Higher = more informative speaker. -/
  α : ℕ := 1
  /-- BEq instance for utterances -/
  [uttBEq : BEq Utterance]
  /-- BEq instance for worlds -/
  [worldBEq : BEq World]
  /-- BEq instance for interpretations -/
  [interpBEq : BEq Interp]
  /-- BEq instance for QUDs -/
  [qudBEq : BEq QUD]

attribute [instance] RSAScenario.uttBEq RSAScenario.worldBEq
  RSAScenario.interpBEq RSAScenario.qudBEq

-- ============================================================================
-- Smart Constructors for RSAScenario
-- ============================================================================

/--
Build a basic RSA scenario (no interpretation ambiguity, no QUD).

This is for simple reference games like Frank & Goodman (2012).

## Example

```lean
def myScenario : RSAScenario :=
  RSAScenario.basic [.blue, .square] [.obj1, .obj2] myMeaning
```
-/
def RSAScenario.basic {U W : Type} [BEq U] [BEq W] [DecidableEq W]
    (utterances : List U) (worlds : List W)
    (φ : U → W → ℚ)
    (prior : W → ℚ := fun _ => 1)
    (α : ℕ := 1) : RSAScenario where
  Utterance := U
  World := W
  Interp := Unit
  QUD := Unit
  φ _ u w := φ u w
  qudProject _ w w' := w == w'
  utterances := utterances
  worlds := worlds
  interps := [()]
  quds := [()]
  worldPrior := prior
  interpPrior := fun _ => 1
  qudPrior := fun _ => 1
  α := α

/--
Build a basic RSA scenario from Boolean semantics.
-/
def RSAScenario.basicBool {U W : Type} [BEq U] [BEq W] [DecidableEq W]
    (utterances : List U) (worlds : List W)
    (satisfies : W → U → Bool)
    (prior : W → ℚ := fun _ => 1)
    (α : ℕ := 1) : RSAScenario :=
  RSAScenario.basic utterances worlds (fun u w => boolToRat (satisfies w u)) prior α

/--
Build a scenario with interpretation ambiguity (e.g., scope readings).

This is for lifted-variable RSA like Scontras & Pearl (2021).

## Example

```lean
def scopeScenario : RSAScenario :=
  RSAScenario.ambiguous
    [.everyHorseNotJump]
    [0, 1, 2]  -- worlds
    [.surface, .inverse]  -- interpretations
    scopeMeaning
```
-/
def RSAScenario.ambiguous {U W I : Type} [BEq U] [BEq W] [BEq I] [DecidableEq W]
    (utterances : List U) (worlds : List W) (interps : List I)
    (φ : I → U → W → ℚ)
    (worldPrior : W → ℚ := fun _ => 1)
    (interpPrior : I → ℚ := fun _ => 1)
    (α : ℕ := 1) : RSAScenario where
  Utterance := U
  World := W
  Interp := I
  QUD := Unit
  φ i u w := φ i u w
  qudProject _ w w' := w == w'
  utterances := utterances
  worlds := worlds
  interps := interps
  quds := [()]
  worldPrior := worldPrior
  interpPrior := interpPrior
  qudPrior := fun _ => 1
  α := α

/--
Build a scenario with interpretation ambiguity from Boolean semantics.
-/
def RSAScenario.ambiguousBool {U W I : Type} [BEq U] [BEq W] [BEq I] [DecidableEq W]
    (utterances : List U) (worlds : List W) (interps : List I)
    (satisfies : I → W → U → Bool)
    (worldPrior : W → ℚ := fun _ => 1)
    (interpPrior : I → ℚ := fun _ => 1)
    (α : ℕ := 1) : RSAScenario :=
  RSAScenario.ambiguous utterances worlds interps
    (fun i u w => boolToRat (satisfies i w u)) worldPrior interpPrior α

/--
Build a QUD-sensitive scenario (e.g., hyperbole, metaphor).

This is for QUD-RSA like Kao et al. (2014).

## Example

```lean
def hyperboleScenario : RSAScenario :=
  RSAScenario.qud
    allUtterances allMeanings allGoals
    extendedSemantics
    qudEquiv
    meaningPrior
    goalPrior
```
-/
def RSAScenario.qud {U W Q : Type} [BEq U] [BEq W] [BEq Q]
    (utterances : List U) (worlds : List W) (quds : List Q)
    (φ : U → W → ℚ)
    (qudProject : Q → W → W → Bool)
    (worldPrior : W → ℚ := fun _ => 1)
    (qudPrior : Q → ℚ := fun _ => 1)
    (α : ℕ := 1) : RSAScenario where
  Utterance := U
  World := W
  Interp := Unit
  QUD := Q
  φ _ u w := φ u w
  qudProject := qudProject
  utterances := utterances
  worlds := worlds
  interps := [()]
  quds := quds
  worldPrior := worldPrior
  interpPrior := fun _ => 1
  qudPrior := qudPrior
  α := α

/--
Build a QUD-sensitive scenario from Boolean semantics.
-/
def RSAScenario.qudBool {U W Q : Type} [BEq U] [BEq W] [BEq Q]
    (utterances : List U) (worlds : List W) (quds : List Q)
    (satisfies : W → U → Bool)
    (qudProject : Q → W → W → Bool)
    (worldPrior : W → ℚ := fun _ => 1)
    (qudPrior : Q → ℚ := fun _ => 1)
    (α : ℕ := 1) : RSAScenario :=
  RSAScenario.qud utterances worlds quds
    (fun u w => boolToRat (satisfies w u)) qudProject worldPrior qudPrior α

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

-- ============================================================================
-- L0: Literal Listener
-- ============================================================================

/--
L0: Literal listener distribution.

P(w | u, i) ∝ P(w) · φ(i, u, w)

For basic scenarios (Interp = Unit), pass `()` for interpretation.
-/
def L0 (S : RSAScenario) (u : S.Utterance) (i : S.Interp) : List (S.World × ℚ) :=
  let scores := S.worlds.map fun w => (w, S.worldPrior w * S.φ i u w)
  normalize scores

/--
L0 projected by QUD.

P_q(w | u, i) ∝ Σ_{w' ~ w under q} P(w') · φ(i, u, w')

Returns the summed probability mass of the equivalence class containing w.
-/
def L0_projected (S : RSAScenario) (u : S.Utterance) (i : S.Interp) (q : S.QUD)
    : List (S.World × ℚ) :=
  let l0 := L0 S u i
  S.worlds.map fun w =>
    -- Sum over all worlds equivalent to w under this QUD
    let eqClassScore := l0.filter (fun (w', _) => S.qudProject q w w') |>.map (·.2) |> sumScores
    (w, eqClassScore)

-- ============================================================================
-- S1: Pragmatic Speaker
-- ============================================================================

/--
S1: Pragmatic speaker distribution.

P(u | w, i, q) ∝ L0_q(w | u, i)^α

For basic scenarios, pass `()` for interpretation and QUD.
For QUD models, the speaker optimizes informativity w.r.t. the projected meaning.
-/
def S1 (S : RSAScenario) (w : S.World) (i : S.Interp) (q : S.QUD)
    : List (S.Utterance × ℚ) :=
  let scores := S.utterances.map fun u =>
    let l0Score := getScore (L0_projected S u i q) w
    (u, l0Score ^ S.α)
  normalize scores

-- ============================================================================
-- L1: Pragmatic Listener
-- ============================================================================

/--
L1 joint distribution over (World × Interp × QUD).

P(w, i, q | u) ∝ P(w) · P(i) · P(q) · S1(u | w, i, q)
-/
def L1_joint (S : RSAScenario) (u : S.Utterance)
    : List ((S.World × S.Interp × S.QUD) × ℚ) :=
  let triples := S.worlds.flatMap fun w =>
    S.interps.flatMap fun i =>
      S.quds.map fun q => (w, i, q)
  let scores := triples.map fun (w, i, q) =>
    let priorScore := S.worldPrior w * S.interpPrior i * S.qudPrior q
    let s1Score := getScore (S1 S w i q) u
    ((w, i, q), priorScore * s1Score)
  normalize scores

/--
L1 marginal over worlds.

P(w | u) = Σ_{i,q} P(w, i, q | u)
-/
def L1_world (S : RSAScenario) (u : S.Utterance) : List (S.World × ℚ) :=
  let joint := L1_joint S u
  S.worlds.map fun w =>
    let wScores := joint.filter (fun ((w', _, _), _) => w' == w) |>.map (·.2)
    (w, sumScores wScores)

/--
L1 marginal over interpretations.

P(i | u) = Σ_{w,q} P(w, i, q | u)
-/
def L1_interp (S : RSAScenario) (u : S.Utterance) : List (S.Interp × ℚ) :=
  let joint := L1_joint S u
  S.interps.map fun i =>
    let iScores := joint.filter (fun ((_, i', _), _) => i' == i) |>.map (·.2)
    (i, sumScores iScores)

/--
L1 marginal over QUDs.

P(q | u) = Σ_{w,i} P(w, i, q | u)
-/
def L1_qud (S : RSAScenario) (u : S.Utterance) : List (S.QUD × ℚ) :=
  let joint := L1_joint S u
  S.quds.map fun q =>
    let qScores := joint.filter (fun ((_, _, q'), _) => q' == q) |>.map (·.2)
    (q, sumScores qScores)

-- ============================================================================
-- S2: Second-Level Pragmatic Speaker
-- ============================================================================

/--
S2: Second-level pragmatic speaker.

P(u | w) ∝ L1_world(w | u)^α

This can be used for modeling truth-value judgments (endorsement).
-/
def S2 (S : RSAScenario) (w : S.World) : List (S.Utterance × ℚ) :=
  let scores := S.utterances.map fun u =>
    let l1Score := getScore (L1_world S u) w
    (u, l1Score ^ S.α)
  normalize scores

-- ============================================================================
-- Helpers
-- ============================================================================

/-- Count worlds compatible with an utterance under interpretation -/
def compatibleCount (S : RSAScenario) (u : S.Utterance) (i : S.Interp) : Nat :=
  (S.worlds.filter fun w => S.φ i u w > 0).length

/-- Informativity under interpretation -/
def informativity (S : RSAScenario) (u : S.Utterance) (i : S.Interp) : ℚ :=
  let n := compatibleCount S u i
  if n > 0 then 1 / n else 0

end RSA

-- ============================================================================
-- Legacy Aliases (for backward compatibility during migration)
-- ============================================================================

/-- Deprecated: use RSAScenario.basicBool instead -/
structure SimpleRSAScenario (U : Type) (W : Type) [BEq U] [BEq W] where
  φ : U → W → ℚ
  utterances : List U
  worlds : List W
  prior : W → ℚ := fun _ => 1
  α : ℕ := 1

/-- Deprecated: use RSAScenario.basicBool instead -/
def SimpleRSAScenario.ofBool {U W : Type} [BEq U] [BEq W]
    (utterances : List U) (worlds : List W)
    (satisfies : W → U → Bool) : SimpleRSAScenario U W where
  φ u w := boolToRat (satisfies w u)
  utterances := utterances
  worlds := worlds

-- Deprecated RSA namespace for SimpleRSAScenario - maps to unified API
namespace RSA

/-- Deprecated: use RSA.L0 with RSAScenario instead -/
def L0_legacy {U W : Type} [BEq U] [BEq W] [DecidableEq W]
    (S : SimpleRSAScenario U W) (u : U) : List (W × ℚ) :=
  let scenario := RSAScenario.basic S.utterances S.worlds S.φ S.prior S.α
  RSA.L0 scenario u ()

/-- Deprecated: use RSA.S1 with RSAScenario instead -/
def S1_legacy {U W : Type} [BEq U] [BEq W] [DecidableEq W]
    (S : SimpleRSAScenario U W) (w : W) : List (U × ℚ) :=
  let scenario := RSAScenario.basic S.utterances S.worlds S.φ S.prior S.α
  RSA.S1 scenario w () ()

/-- Deprecated: use RSA.L1_world with RSAScenario instead -/
def L1_legacy {U W : Type} [BEq U] [BEq W] [DecidableEq W]
    (S : SimpleRSAScenario U W) (u : U) : List (W × ℚ) :=
  let scenario := RSAScenario.basic S.utterances S.worlds S.φ S.prior S.α
  RSA.L1_world scenario u

end RSA

-- ============================================================================
-- ParametricRSA Legacy Namespace
-- ============================================================================

namespace ParametricRSA

/-- Deprecated: use RSAScenario.ambiguousBool instead -/
structure ParametricRSAScenario where
  Utterance : Type
  World : Type
  Interp : Type
  φ : Interp → Utterance → World → ℚ
  utterances : List Utterance
  worlds : List World
  interps : List Interp
  prior : World → ℚ := fun _ => 1
  interpPrior : Interp → ℚ := fun _ => 1
  α : ℕ := 1
  [uttBEq : BEq Utterance]
  [worldBEq : BEq World]
  [interpBEq : BEq Interp]

attribute [instance] ParametricRSAScenario.uttBEq ParametricRSAScenario.worldBEq
  ParametricRSAScenario.interpBEq

/-- Deprecated: use RSAScenario.ambiguousBool instead -/
def ParametricRSAScenario.ofBool {Utterance World Interp : Type}
    [BEq Utterance] [DecidableEq World] [BEq World] [BEq Interp]
    (utterances : List Utterance) (worlds : List World) (interps : List Interp)
    (satisfies : Interp → World → Utterance → Bool) : ParametricRSAScenario where
  Utterance := Utterance
  World := World
  Interp := Interp
  φ i u w := boolToRat (satisfies i w u)
  utterances := utterances
  worlds := worlds
  interps := interps

/-- Deprecated: use RSA.L0 with RSAScenario instead -/
def L0 (S : ParametricRSAScenario) [DecidableEq S.World]
    (i : S.Interp) (u : S.Utterance) : List (S.World × ℚ) :=
  let scenario := RSAScenario.ambiguous S.utterances S.worlds S.interps S.φ S.prior S.interpPrior S.α
  RSA.L0 scenario u i

/-- Deprecated: use RSA.S1 with RSAScenario instead -/
def S1 (S : ParametricRSAScenario) [DecidableEq S.World]
    (i : S.Interp) (w : S.World) : List (S.Utterance × ℚ) :=
  let scenario := RSAScenario.ambiguous S.utterances S.worlds S.interps S.φ S.prior S.interpPrior S.α
  RSA.S1 scenario w i ()

/-- Deprecated: use RSA.L1_joint with RSAScenario instead -/
def L1_joint (S : ParametricRSAScenario) [DecidableEq S.World]
    (u : S.Utterance) : List ((S.World × S.Interp) × ℚ) :=
  let scenario := RSAScenario.ambiguous S.utterances S.worlds S.interps S.φ S.prior S.interpPrior S.α
  let joint := RSA.L1_joint scenario u
  -- Convert from (W × I × Unit) to (W × I)
  joint.map fun ((w, i, _), p) => ((w, i), p)

/-- Deprecated: use RSA.L1_world with RSAScenario instead -/
def L1_world (S : ParametricRSAScenario) [DecidableEq S.World]
    (u : S.Utterance) : List (S.World × ℚ) :=
  let scenario := RSAScenario.ambiguous S.utterances S.worlds S.interps S.φ S.prior S.interpPrior S.α
  RSA.L1_world scenario u

/-- Deprecated: use RSA.L1_interp with RSAScenario instead -/
def L1_interp (S : ParametricRSAScenario) [DecidableEq S.World]
    (u : S.Utterance) : List (S.Interp × ℚ) :=
  let scenario := RSAScenario.ambiguous S.utterances S.worlds S.interps S.φ S.prior S.interpPrior S.α
  RSA.L1_interp scenario u

end ParametricRSA

-- ============================================================================
-- Additional Legacy Aliases
-- ============================================================================

/-- RSAScenario with exact rational arithmetic (deprecated alias) -/
abbrev ExactRSAScenario := RSAScenario

/-- Parametric RSA scenario with exact rational arithmetic (deprecated alias) -/
abbrev ExactParametricRSAScenario := ParametricRSA.ParametricRSAScenario

namespace ParametricRSA
/-- Alias within namespace for backward compatibility -/
abbrev ExactParametricRSAScenario := ParametricRSAScenario
end ParametricRSA
