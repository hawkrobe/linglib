/-
# RSA Integration with Discourse State

Provides functions to connect Farkas & Bruce (2010) discourse state
components to RSA model computations.

RSA presupposition models all use the same mathematical structure:

```
L1(w, D | u, Q) ∝ S1(u | w, D, Q) · P(w) · P(D)
```

Where D is a "discourse" latent variable. The difference is interpretation:

| Model | D represents | F&B component |
|-------|-------------|---------------|
| S&T 2025 | Speaker's private assumptions | dcS |
| Warstadt 2022 | Common ground state | cg |
| Qing 2016 | Context set | cg |

This module provides credence functions that bridge DiscourseState
to RSA's `speakerCredence` parameter.

## Usage

```lean
-- For S&T-style models (infer dcS)
def speakerCredence := dcSCredence dcSOptions baseCG

-- For Warstadt-style models (infer cg)
def contextCredence := cgCredence cgOptions
```

## References

- Farkas & Bruce (2010). On Reacting to Assertions and Polar Questions.
- Scontras & Tonhauser (2025). Projection without lexically-specified presupposition.
- Warstadt (2022). Presupposition accommodation through pragmatic inference.
- Qing, Goodman & Lassiter (2016). A rational speech-act model of projective content.
-/

import Linglib.Theories.Semantics.Dynamic.State
import Linglib.Theories.Pragmatics.RSA.Core.Basic

namespace RSA.DiscourseIntegration

open Semantics.Dynamic.State
open Core.Proposition


/--
Credence function from a full discourse state.

Returns 1 if the world is compatible with the common ground, 0 otherwise.
This is the simplest bridge from DiscourseState to RSA.
-/
def discourseCredence {W : Type*} (ds : DiscourseState W) (w : W) : ℚ :=
  _root_.boolToRat (ds.compatible w)

/--
Speaker credence from discourse state.

Returns 1 if the world is compatible with speaker's discourse commitments (dcS).
This is what S&T (2025) call the speaker's "private assumptions."
-/
def speakerDcSCredence {W : Type*} (ds : DiscourseState W) (w : W) : ℚ :=
  _root_.boolToRat (ds.speakerCompatible w)


/--
For models with uncertainty over dcS (Scontras & Tonhauser style):
Each latent variable value determines speaker's private assumptions.

In F&B terms: L1 is inferring what the speaker privately takes for granted,
which may extend beyond the common ground.

Parameters:
- `dcSOptions`: Function mapping latent variable to list of dcS propositions
- `baseCG`: The fixed common ground
- `a`: The latent variable value (BeliefState in S&T)
- `w`: The world to check

Returns 1 if w satisfies all of speaker's assumed propositions under a.
-/
def dcSCredence {A W : Type*}
    (dcSOptions : A → List (BProp W))
    (_baseCG : List (BProp W))
    (a : A) (w : W) : ℚ :=
  -- Speaker credence: w must satisfy speaker's private assumptions
  let compatible := (dcSOptions a).all (λ p => p w)
  _root_.boolToRat compatible

/--
Boolean version of dcSCredence for pattern matching.
-/
def dcSCredenceBool {A W : Type*}
    (dcSOptions : A → List (BProp W))
    (_baseCG : List (BProp W))
    (a : A) (w : W) : Bool :=
  (dcSOptions a).all (λ p => p w)


/--
For models with uncertainty over cg (Warstadt/Qing style):
Each latent variable value determines what's in the common ground.

In F&B terms: L1 is inferring what propositions are mutually accepted
as common ground.

Parameters:
- `cgOptions`: Function mapping latent variable to list of CG propositions
- `c`: The latent variable value (Context in Warstadt)
- `w`: The world to check

Returns 1 if w satisfies all common ground propositions under c.
-/
def cgCredence {C W : Type*}
    (cgOptions : C → List (BProp W))
    (c : C) (w : W) : ℚ :=
  let compatible := (cgOptions c).all (λ p => p w)
  _root_.boolToRat compatible

/--
Boolean version of cgCredence for pattern matching.
-/
def cgCredenceBool {C W : Type*}
    (cgOptions : C → List (BProp W))
    (c : C) (w : W) : Bool :=
  (cgOptions c).all (λ p => p w)


/--
Unified credence function that works with any discourse component.

This is a generic interface that can be specialized to dcS or cg inference
depending on how the options function is defined.
-/
def discourseComponentCredence {D W : Type*}
    (componentOptions : D → List (BProp W))
    (d : D) (w : W) : ℚ :=
  _root_.boolToRat ((componentOptions d).all (λ p => p w))


/-!
## Usage Patterns

### Pattern 1: S&T-Style (Infer Speaker's dcS)

```lean
-- Define BeliefState as in S&T
inductive BeliefState where
  | cTrue   -- Speaker assumes C is true
  | cFalse  -- Speaker assumes C is false
  | all     -- No assumptions

-- Map to propositions
def dcSOptions : BeliefState → List (BProp World)
  | .cTrue => [λ w => w.c]
  | .cFalse => [λ w => !w.c]
  | .all => []

-- Use with RSA
def speakerCredence := dcSCredence dcSOptions baseCG
```

### Pattern 2: Warstadt-Style (Infer Common Ground)

```lean
-- Define Context as in Warstadt
inductive Context where
  | presupEstablished
  | presupNotEstablished

-- Map to propositions
def cgOptions : Context → List (BProp World)
  | .presupEstablished => [presuppositionProp]
  | .presupNotEstablished => []

-- Use with RSA
def contextCredence := cgCredence cgOptions
```

### Pattern 3: Full Discourse State

```lean
-- Create explicit discourse state
def ds : DiscourseState World :=
  DiscourseState.forDcSInference baseCG speakerAssumptions

-- Get credence directly
def cred := discourseCredence ds
```
-/


/-!
## Theoretical Connection

### The Mathematical Equivalence

All three models (S&T, Warstadt, Qing) compute the same thing:

```
L1(w, D | u) ∝ S1(u | w, D) · P(w) · P(D)
```

The credence functions in this module show that:
- `dcSCredence` = what S&T call `speakerCredence`
- `cgCredence` = what Warstadt calls `contextCredence`

Both are instances of `discourseComponentCredence` with different
interpretations of what D represents.

### Why the Interpretation Matters

The interpretation affects:
1. Prior choice: P(D) should reflect beliefs about dcS vs cg
2. Experimental predictions: Different measures are appropriate
3. Theoretical framing: "Speaker belief inference" vs "accommodation"

The computation, however, is identical.
-/

/--
The credence functions are equivalent when given the same options.

This shows that S&T-style and Warstadt-style credence are both
special cases of the generic `discourseComponentCredence`.
-/
theorem dcS_cg_same_structure {A W : Type*}
    (options : A → List (BProp W))
    (baseCG : List (BProp W))
    (a : A) (w : W) :
    dcSCredence options baseCG a w = discourseComponentCredence options a w := by
  simp only [dcSCredence, discourseComponentCredence]

/--
For Warstadt-style models, same equivalence holds.
-/
theorem cg_matches_generic {C W : Type*}
    (options : C → List (BProp W))
    (c : C) (w : W) :
    cgCredence options c w = discourseComponentCredence options c w := by
  simp only [cgCredence, discourseComponentCredence]

end RSA.DiscourseIntegration
