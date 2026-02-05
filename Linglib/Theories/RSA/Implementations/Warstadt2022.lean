/-
# Warstadt (2022): RSA Presupposition Accommodation Model

"Presupposition accommodation through pragmatic inference"

## Farkas & Bruce (2010) Connection

In F&B terms, this model has L1 infer the common ground (cg).

The `Context` type represents different possible cg values—what propositions
are mutually accepted. Unlike S&T (2025), this model treats the latent variable
as a property of the shared conversational state, not the speaker's private beliefs.

| F&B Component | This Implementation |
|---------------|---------------------|
| dcS | = cg (speaker committed to what's in CG) |
| dcL | = cg (listener committed to what's in CG) |
| cg | `Context` (latent variable) |
| table | Not modeled (stable state) |

The `contextCredence` function returns 1 for worlds compatible with cg.
This captures accommodation as updating one's model of the common ground.

Presupposition accommodation emerges from L1 performing joint inference
over (world, context), where context represents the shared common ground.

## Theoretical Relationship: Qing-S&T-Warstadt Equivalence

This model is mathematically identical to:
- Qing, Goodman & Lassiter (2016) - the original formulation
- Scontras & Tonhauser (2025) - applied to factives

All three papers implement the same RSA equations (from Qing et al.):
```
L0(Q(w) | u, C, Q) ∝ Σ_{w' ∈ C ∩ ⟦u⟧} δ_{Q(w)=Q(w')} · P(w')
S1(u | w, C, Q) ∝ P(u) · L0(Q(w) | u, C, Q)^α
L1(w, C | u, Q) ∝ P(w) · P(C) · S1(u | w, C, Q)
```

The only difference is interpretation of the latent variable C:

| Paper | Name | Interpretation |
|-------|------|----------------|
| Qing et al. 2016 | Context set | Common ground |
| S&T 2025 | Private assumptions A | Speaker's beliefs |
| Warstadt 2022 | Context | Common ground |

S&T footnote 10: "Qing et al. (2016) call these subsets the 'common ground,'
but we think 'private assumptions' better captures this component."

## Implementation Strategy

We reuse the BToM-style infrastructure from RSA.Core, treating Context
analogously to how ScontrasTonhauser2025 treats BeliefState:
- `BeliefState` slot holds our `Context` type (common ground states)
- `speakerCredence` encodes P(w | C) - worlds compatible with context
- `L1_beliefState` marginal gives the accommodation measure

This demonstrates that the unified RSAScenario API can express both:
- Speaker belief inference (BToM projection)
- Common ground inference (accommodation)

## Example: Possessive Presupposition

Utterances:
- "Mary's dog is sick" (presupposes: Mary has a dog)
- "Mary has a sick dog" (no presupposition)
- silence

Contexts:
- hasDogEstablished = true: "Mary has a dog" is in common ground
- hasDogEstablished = false: Not established

Prediction: Hearing "Mary's dog is sick" causes L1 to infer the presupposition
is established (accommodation), even if it wasn't before the utterance.

## Connection to Core.CommonGround

This implementation connects to `Core.CommonGround` conceptually:
- Our `Context` type corresponds to different context sets
- `compatible c w` ↔ `w` is in the context set determined by `c`
- Accommodation = updating the context set model

Future work could make this connection more explicit by using `ContextSet`
directly from `Core.CommonGround`.

## References

- Warstadt (2022). Presupposition accommodation through pragmatic inference.
- Stalnaker (1974). Pragmatic Presuppositions.
- Lewis (1979). Scorekeeping in a Language Game.
- Scontras & Tonhauser (2025). Projection without lexically-specified presupposition.
-/

import Linglib.Theories.RSA.Core.Basic
import Linglib.Theories.RSA.Core.Eval
import Linglib.Theories.RSA.Core.Discourse
import Linglib.Core.CommonGround

namespace RSA.Warstadt2022

open RSA.Eval


/--
World state: tracks what's actually true.

For the possessive presupposition example:
- maryHasDog: Mary has (at least one) dog
- dogIsSick: The (salient) dog is sick
-/
structure WorldState where
  maryHasDog : Bool
  dogIsSick : Bool
  deriving DecidableEq, Repr, BEq, Inhabited

/-- All four world states -/
def allWorlds : List WorldState := [
  ⟨true, true⟩,    -- Mary has a dog, dog is sick
  ⟨true, false⟩,   -- Mary has a dog, dog is not sick
  ⟨false, true⟩,   -- Mary doesn't have a dog (dog sick = vacuous)
  ⟨false, false⟩   -- Mary doesn't have a dog
]


/--
Context represents which presuppositions are established in the common ground.

This plays the role that `BeliefState` plays in Scontras & Tonhauser (2025),
but with a different interpretation:
- S&T: BeliefState = speaker's private assumptions
- Here: Context = mutually accepted common ground

Connection to `Core.CommonGround`:
- Each `Context` value determines a `ContextSet` (set of compatible worlds)
- `hasDogEstablished = true` means CG ⊨ maryHasDog
-/
inductive Context where
  | hasDogEstablished    -- "Mary has a dog" is in CG
  | hasDogNotEstablished -- "Mary has a dog" is NOT in CG
  deriving DecidableEq, Repr, BEq, Inhabited

/-- All contexts -/
def allContexts : List Context := [.hasDogEstablished, .hasDogNotEstablished]


/--
A world is compatible with a context iff all presuppositions
established in the context hold in the world.

If "Mary has a dog" is established in CG, then worlds where Mary
doesn't have a dog get probability 0.

This function plays the role of `speakerCredenceBool` in ScontrasTonhauser2025,
but with a different interpretation:
- S&T: Does the speaker consider world w possible given belief state a?
- Here: Is world w compatible with context c?
-/
def compatibleBool (c : Context) (w : WorldState) : Bool :=
  match c with
  | .hasDogEstablished => w.maryHasDog       -- CG entails hasDog, so w must satisfy it
  | .hasDogNotEstablished => true            -- No constraint on w

/-- Credence function: P(w | C) indicator.
    This will be normalized in the RSA computations. -/
def contextCredence (c : Context) (w : WorldState) : ℚ :=
  boolToRat (compatibleBool c w)


/--
Utterances differing in presuppositional content.

- marysDogIsSick: "Mary's dog is sick" (presupposes: Mary has a dog)
- maryHasASickDog: "Mary has a sick dog" (asserts: Mary has a dog)
- silence: Null utterance
-/
inductive Utterance where
  | marysDogIsSick     -- Presuppositional: Mary's dog is sick
  | maryHasASickDog    -- Non-presuppositional: Mary has a sick dog
  | silence            -- Null utterance
  deriving DecidableEq, Repr, BEq, Inhabited

def allUtterances : List Utterance := [.marysDogIsSick, .maryHasASickDog, .silence]


/--
Truth conditions for each utterance.

"Mary's dog is sick": True iff Mary has a dog AND the dog is sick.
  - Note: When presupposition fails (no dog), we treat as false.
  - Alternative: trivalent semantics (undefined when presup fails)

"Mary has a sick dog": True iff Mary has a dog AND dog is sick.
  - Same truth conditions, but asserts rather than presupposes hasDog

"silence": True everywhere (vacuously informative)
-/
def literalMeaning : Utterance → WorldState → Bool
  | .marysDogIsSick, w => w.maryHasDog && w.dogIsSick
  | .maryHasASickDog, w => w.maryHasDog && w.dogIsSick
  | .silence, _ => true

/--
Same at-issue content for presuppositional and non-presuppositional
versions, but different presuppositional content.
-/
theorem same_atissue_content :
    ∀ w, literalMeaning .marysDogIsSick w = literalMeaning .maryHasASickDog w := by
  intro w; simp [literalMeaning]


/--
For this model, we use a simple QUD that partitions by world state.
Accommodation emerges from context inference, not from QUD variation.
-/
inductive QUD where
  | dogStatus   -- Is Mary's dog sick?
  deriving DecidableEq, Repr, BEq, Inhabited

def allQUDs : List QUD := [.dogStatus]

/--
QUD projection: two worlds are equivalent if they agree on the QUD dimension.
For the dogStatus QUD, we care about the full world state.
-/
def qudProject : QUD → WorldState → WorldState → Bool
  | .dogStatus, w1, w2 => w1.maryHasDog == w2.maryHasDog && w1.dogIsSick == w2.dogIsSick


/--
World prior: uniform over all worlds.
The conditional prior P(w | C) arises from speakerCredence (contextCredence),
not from the base world prior.
-/
def worldPrior (_w : WorldState) : ℚ := 1 / 4

/--
Context prior: uniform over contexts.
This represents the listener's uncertainty about what's in the CG.
-/
def contextPrior (_c : Context) : ℚ := 1 / 2


/--
Projection computation: P(C=hasDogEstablished | u)

Measures accommodation: how strongly does L1 infer that the presupposition
is established in the common ground?
-/
def accommodationStrength (u : Utterance) (α : ℕ := 10) : ℚ :=
  -- Get L1 distribution over belief states (= contexts) GIVEN the QUD
  let contextDist := RSA.Eval.L1_beliefState_givenGoal
    allUtterances allWorlds [()] [()] allContexts allQUDs
    (λ _ _ u' w => if literalMeaning u' w then 1 else 0)
    worldPrior (λ _ => 1) (λ _ => 1) contextPrior (λ _ => 1)
    contextCredence qudProject (λ _ => 0) α u .dogStatus
  -- Get probability of hasDogEstablished context
  contextDist.foldl (λ acc (c, p) =>
    if c == .hasDogEstablished then acc + p else acc) 0

/--
Accommodation shift: Change from prior context probability.

accommodationShift(u) = P(hasDog ∈ CG | u) - P(hasDog ∈ CG)

Positive shift = utterance triggers accommodation.
-/
def accommodationShift (u : Utterance) (α : ℕ := 10) : ℚ :=
  accommodationStrength u α - (1 / 2)  -- Prior is 1/2

/--
World inference: P(w | u)

L1's posterior over worlds after hearing utterance u.
-/
def L1_world (u : Utterance) (α : ℕ := 10) : List (WorldState × ℚ) :=
  RSA.Eval.L1_world_givenGoal
    allUtterances allWorlds [()] [()] allContexts allQUDs
    (λ _ _ u' w => if literalMeaning u' w then 1 else 0)
    worldPrior (λ _ => 1) (λ _ => 1) contextPrior (λ _ => 1)
    contextCredence qudProject (λ _ => 0) α u .dogStatus


/--
Prediction 1: Presuppositional utterance triggers accommodation.

Hearing "Mary's dog is sick" causes L1 to infer that "Mary has a dog"
is established in the common ground (accommodation).
-/
def prediction_presup_triggers_accommodation (α : ℕ := 10) : Bool :=
  accommodationShift .marysDogIsSick α > 0

/--
Prediction 2: Non-presuppositional alternative triggers less accommodation.

"Mary has a sick dog" triggers less accommodation than "Mary's dog is sick"
because it doesn't presuppose that Mary has a dog -- it asserts it.
-/
def prediction_nonpresup_less_accommodation (α : ℕ := 10) : Bool :=
  accommodationStrength .marysDogIsSick α >
  accommodationStrength .maryHasASickDog α

/--
Prediction 3: Silence is uninformative about context.

With no utterance, L1 doesn't update on context (stays near prior).
-/
def prediction_silence_uninformative (α : ℕ := 10) : Bool :=
  -- Accommodation strength for silence should be close to prior (0.5)
  let strength := accommodationStrength .silence α
  strength > 1/4 && strength < 3/4


-- Uncomment to evaluate predictions:
-- #eval accommodationStrength .marysDogIsSick
-- #eval accommodationStrength .maryHasASickDog
-- #eval accommodationStrength .silence
-- #eval accommodationShift .marysDogIsSick
-- #eval prediction_presup_triggers_accommodation
-- #eval prediction_nonpresup_less_accommodation


/-!
## Connection to Core.CommonGround

This implementation relates to `Core.CommonGround` as follows:

### ContextSet Correspondence

Each `Context` value defines a `ContextSet`:
- `hasDogEstablished` → { w | w.maryHasDog = true }
- `hasDogNotEstablished` → W (all worlds)

Our `compatibleBool c w` corresponds to `ContextSet.mem`:

```lean
def toContextSet (c : Context) : ContextSet WorldState :=
  λ w => compatibleBool c w
```

### Entailment

When `c = .hasDogEstablished`, the context set entails the proposition
"Mary has a dog":

```lean
theorem established_entails_hasDog :
    (toContextSet .hasDogEstablished) ⊧ (λ w => w.maryHasDog) := by
  intro w hw
  simp [toContextSet, compatibleBool] at hw
  exact hw
```

### Accommodation as Context Update

Lewis (1979): When a presupposition is not satisfied, listeners
accommodate by adding it to the common ground.

In our model:
- Prior: P(hasDogEstablished) = 0.5
- After hearing presuppositional utterance: P(hasDogEstablished | u) > 0.5
- This increase is accommodation: L1 updates their model of CG

### Future Integration

A deeper integration with `Core.CommonGround` would:
1. Use `ContextSet WorldState` instead of `Context`
2. Use `ContextSet.update` for dynamic context change
3. Connect to Heim's satisfaction theory via local contexts
-/


/-!
## Structural Comparison

Both models use the same RSA infrastructure but with different interpretations:

### Shared Structure
- Both use `L1_beliefState_givenGoal` to compute marginal over latent variable
- Both use `speakerCredence` (here: `contextCredence`) to constrain world-latent pairs
- Both derive projection/accommodation from this marginal

### Different Interpretation

Scontras & Tonhauser 2025:
- BeliefState = speaker's private assumptions A
- speakerCredence a w = "speaker considers w possible given A"
- L1 infers: "What does the speaker privately assume about C?"
- Projection = P(speaker assumes C | utterance)

Warstadt 2022:
- BeliefState = context (common ground state) C
- contextCredence c w = "w is compatible with CG state c"
- L1 infers: "What is established in our shared common ground?"
- Accommodation = P(presup ∈ CG | utterance)

### When They Diverge

The models make different predictions when:
1. Asymmetric knowledge: Speaker knows more than listener
   - S&T: L1 infers speaker's private beliefs (may exceed CG)
   - Warstadt: L1 infers shared CG (speaker beliefs don't matter directly)

2. Informational vs social presupposition:
   - S&T: Better for cognitive/epistemic presuppositions
   - Warstadt: Better for conventional presuppositions that modify CG

### Unification

Both models can be seen as special cases of a more general theory:
- Latent variable X representing conversational state
- L1 performs joint inference over (world, X)
- Different X interpretations give different theories

See `Comparisons.PresuppositionProjection` for formal comparison.
-/


/-!
## Migration to DiscourseConfig API

The new `DiscourseConfig` and `RSAScenario.discourse` constructors provide
a cleaner interface that makes the F&B connection explicit.
-/

-- Fintype instances (needed for DiscourseConfig)
instance : Fintype WorldState where
  elems := { ⟨true, true⟩, ⟨true, false⟩, ⟨false, true⟩, ⟨false, false⟩ }
  complete := λ ⟨a, b⟩ => by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    cases a <;> cases b <;> simp

instance : Fintype Context where
  elems := { .hasDogEstablished, .hasDogNotEstablished }
  complete := λ c => by cases c <;> simp

instance : Fintype Utterance where
  elems := { .marysDogIsSick, .maryHasASickDog, .silence }
  complete := λ u => by cases u <;> simp

instance : Fintype QUD where
  elems := { .dogStatus }
  complete := λ q => by cases q <;> simp

open Theories.DynamicSemantics.State in
/--
Discourse configuration for this model.

This bundles the Context type with its compatibility function and prior,
making explicit that we're doing cg inference (not dcS inference).
-/
def discourseConfig : DiscourseConfig WorldState where
  D := Context
  compatible := compatibleBool
  prior := contextPrior
  prior_nonneg := λ _ => by simp only [contextPrior]; norm_num

/--
QUD configuration for this model.
-/
def qudConfig : RSA.QUDConfig WorldState where
  G := QUD
  project := qudProject
  prior := λ _ => 1
  prior_nonneg := λ _ => by decide

/-
## Demo: Using the Unified Discourse API

The following shows how to use `RSAScenario.discourseWithQUD` to create
a scenario from bundled configurations. This is commented out because
the BeliefState type becomes opaque when bundled, requiring explicit
type annotations in some contexts.

```lean
def scenario (α : ℕ := 10) : RSAScenario :=
  RSAScenario.discourseWithQUD
    (φ := λ u w => if literalMeaning u w then 1 else 0)
    (discourse := discourseConfig)
    (qud := qudConfig)
    (worldPrior := worldPrior)
    (α := α)
    (φ_nonneg := λ u w => by split_ifs <;> decide)
```

The explicit `accommodationStrength` function above shows the working pattern.
-/

end RSA.Warstadt2022
