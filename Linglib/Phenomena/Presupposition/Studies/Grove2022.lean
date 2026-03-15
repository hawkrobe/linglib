import Linglib.Theories.Semantics.Composition.MaybeMonad
import Linglib.Phenomena.Presupposition.Studies.Heim1992

/-!
# Grove 2022: Presupposition Projection as a Scope Phenomenon
@cite{grove-2022}

Presupposition projection as a scope phenomenon. *Semantics and Pragmatics*
15, Article 15: 1–39.

## Core Claim

The proviso problem — where @cite{heim-1983}'s satisfaction theory
predicts weak conditional presuppositions for sentences that intuitively
have unconditional ones — dissolves when presupposition projection is
treated as **scope-taking**. Presupposition triggers have `Option`-typed
denotations and interact with their context via monadic bind, exactly
paralleling @cite{charlow-2020}'s treatment of indefinites.

## Key Predictions

For "If Theo has a brother, he'll bring his wetsuit":

- **Local reading** (narrow scope): the trigger "his wetsuit" stays inside
  the consequent → presupposition is `hasBrother → hasWetsuit` (conditional)
- **Global reading** (wide scope): the trigger scopes over the conditional
  → presupposition is `hasWetsuit` (unconditional)

The two readings are a genuine **scope ambiguity**, not a semantic +
pragmatic strengthening. The proviso problem does not arise because the
unconditional presupposition is semantically available.

## Connection to @cite{heim-1992}

For attitude verbs ("Theo believes he lost his wetsuit"), the same
scope mechanism predicts:
- **Local** (de dicto): presupposition is that Theo *believes* he has a wetsuit
- **Global** (de re): presupposition is that Theo *has* a wetsuit

This connects to `Heim1992.lean`'s know/believe asymmetry but derives it
from scope rather than from local-context filtering.

## Empirical Data

- (1) If Theo has a brother, he'll bring his wetsuit. ↝ Theo has a wetsuit.
- (2) If Theo is a scuba diver, he'll bring his wetsuit.
      ↝ If Theo is a scuba diver, he has a wetsuit.
- (6) John: I am already in bed.
      Mary: My parents think I am also in bed. ↝ John is in bed.
- (22) Theo believes he lost his wetsuit.
       ↝ Theo has a wetsuit / Theo believes he has a wetsuit.
-/

set_option autoImplicit false

namespace Phenomena.Presupposition.Studies.Grove2022

open Semantics.Composition.MaybeMonad

-- ════════════════════════════════════════════════════════════════
-- §1 World Model for Conditionals
-- ════════════════════════════════════════════════════════════════

/-! ### §1 World model

Four worlds varying two properties: whether Theo has a brother, and
whether Theo has a (unique) wetsuit. -/

/-- Worlds for the conditional examples. -/
inductive CWorld where
  | broSuit   -- has brother, has wetsuit
  | broNoSuit -- has brother, no wetsuit
  | noBroSuit -- no brother, has wetsuit
  | noBro     -- no brother, no wetsuit
  deriving DecidableEq, BEq, Repr

open CWorld

def hasBrother : CWorld → Bool
  | .broSuit | .broNoSuit => true
  | .noBroSuit | .noBro => false

def hasWetsuit : CWorld → Bool
  | .broSuit | .noBroSuit => true
  | .broNoSuit | .noBro => false

/-- Whether Theo brings his wetsuit (only meaningful when he has one). -/
def bringsWetsuit : CWorld → Bool
  | .broSuit => true
  | _ => false

-- ════════════════════════════════════════════════════════════════
-- §2 Presupposition Trigger: "his wetsuit"
-- ════════════════════════════════════════════════════════════════

/-! ### §2 The presupposition trigger

"His wetsuit" denotes type `e_#` (= `Option Entity`): defined when
Theo has a unique wetsuit, undefined otherwise. In our simplified
model, the entity is irrelevant — what matters is the definedness
condition. So we model the trigger's contribution to the truth value
as `Option Bool`: defined (with value `bring(t)`) when `hasWetsuit`,
undefined otherwise. -/

/-- "his wetsuit" contributes definedness + the `bring` predicate.

    Modeling the trigger's contribution to the sentential truth value:
    - At worlds where Theo has a wetsuit: `some (bringsWetsuit w)`
    - At worlds where he doesn't: `none` (presupposition failure) -/
def hisWetsuit : CWorld → Option Bool :=
  λ w => if hasWetsuit w then some (bringsWetsuit w) else none

-- ════════════════════════════════════════════════════════════════
-- §3 Local Reading: Conditional Presupposition
-- ════════════════════════════════════════════════════════════════

/-! ### §3 Local reading (narrow scope)

The trigger takes scope within the consequent clause. The conditional's
interpretation uses `materialCond`, which checks the consequent only
when the antecedent is true. Result: the presupposition is conditional
(`hasBrother → hasWetsuit`). -/

/-- Local reading of "If Theo has a brother, he'll bring his wetsuit."

    The trigger stays inside the consequent. The conditional filters:
    `materialCond (some (hasBrother w)) (hisWetsuit w)`. -/
def localReading : CWorld → Option Bool :=
  λ w => materialCond (some (hasBrother w)) (hisWetsuit w)

/-- At `broSuit`: brother ✓, wetsuit ✓, brings ✓ → `some true`. -/
theorem local_broSuit : localReading .broSuit = some true := rfl

/-- At `broNoSuit`: brother ✓, no wetsuit → `none` (presup failure). -/
theorem local_broNoSuit : localReading .broNoSuit = none := rfl

/-- At `noBroSuit`: no brother → `some true` (conditional vacuously true). -/
theorem local_noBroSuit : localReading .noBroSuit = some true := rfl

/-- At `noBro`: no brother → `some true` (vacuously true). -/
theorem local_noBro : localReading .noBro = some true := rfl

/-- The local reading is defined iff `hasBrother → hasWetsuit`.

    This is the **conditional presupposition** that @cite{geurts-1996}
    observed satisfaction accounts predict — and which Grove argues is
    merely one of two available readings. -/
theorem local_definedness (w : CWorld) :
    (localReading w).isSome = (!hasBrother w || hasWetsuit w) := by
  cases w <;> rfl

-- ════════════════════════════════════════════════════════════════
-- §4 Global Reading: Unconditional Presupposition
-- ════════════════════════════════════════════════════════════════

/-! ### §4 Global reading (wide scope)

The trigger takes scope over the entire conditional via cyclic
scope-taking (roll-up pied-piping). The trigger's definedness is
checked first; only then does the conditional apply. Result: the
presupposition is unconditional (`hasWetsuit`). -/

/-- Global reading: the trigger scopes over the conditional.

    `hisWetsuit w >>= (λ b => materialCond (some (hasBrother w)) (some b))`

    First check definedness of the trigger; then, if defined, evaluate the
    conditional with a fully-defined consequent. -/
def globalReading : CWorld → Option Bool :=
  λ w => hisWetsuit w >>= (λ b => materialCond (some (hasBrother w)) (some b))

/-- At `broSuit`: wetsuit ✓ → defined. Brother ✓, brings ✓ → `some true`. -/
theorem global_broSuit : globalReading .broSuit = some true := rfl

/-- At `broNoSuit`: no wetsuit → `none` (presup failure). -/
theorem global_broNoSuit : globalReading .broNoSuit = none := rfl

/-- At `noBroSuit`: wetsuit ✓ → defined. No brother → `some true`. -/
theorem global_noBroSuit : globalReading .noBroSuit = some true := rfl

/-- At `noBro`: no wetsuit → `none` (presup failure). -/
theorem global_noBro : globalReading .noBro = none := rfl

/-- The global reading is defined iff `hasWetsuit`.

    This is the **unconditional presupposition** that speakers actually
    accommodate for "If Theo has a brother, he'll bring his wetsuit."
    The proviso problem does not arise: this reading is semantically
    available without pragmatic strengthening. -/
theorem global_definedness (w : CWorld) :
    (globalReading w).isSome = hasWetsuit w := by
  cases w <;> rfl

-- ════════════════════════════════════════════════════════════════
-- §5 The Proviso Problem Dissolves
-- ════════════════════════════════════════════════════════════════

/-! ### §5 Scope ambiguity = no proviso problem

The two readings differ only in scope. At worlds where both readings
are defined, they agree on truth value — the readings differ only in
their **presuppositions** (definedness conditions). -/

/-- Where both readings are defined, they agree on truth value. -/
theorem readings_agree_when_defined (w : CWorld)
    (hl : (localReading w).isSome = true)
    (hg : (globalReading w).isSome = true) :
    localReading w = globalReading w := by
  cases w <;> simp_all [localReading, globalReading, hisWetsuit,
    materialCond, hasBrother, hasWetsuit, bringsWetsuit]

/-- The global presupposition is strictly stronger than the local one:
    `hasWetsuit → (hasBrother → hasWetsuit)` but not vice versa. -/
theorem global_stronger_than_local :
    (∀ w, hasWetsuit w = true → (!hasBrother w || hasWetsuit w) = true)
    ∧ ¬(∀ w, (!hasBrother w || hasWetsuit w) = true → hasWetsuit w = true) := by
  constructor
  · intro w hw; simp [hw, Bool.or_true]
  · intro h; have := h .noBro (by rfl); simp [hasWetsuit] at this

/-- Left Identity ensures that `η`-shifting inside the trigger's scope and
    then binding is the same as not shifting at all — this is why the narrow-
    scope derivation is equivalent to the standard satisfaction-theory
    prediction (Grove fn. 13). -/
theorem eta_bind_reconstructs (w : CWorld) :
    (some (hisWetsuit w) >>= id) = hisWetsuit w := by
  cases hisWetsuit w <;> rfl

-- ════════════════════════════════════════════════════════════════
-- §6 Attitude Verbs
-- ════════════════════════════════════════════════════════════════

/-! ### §6 Attitude verb example: "Theo believes he lost his wetsuit"

We reuse the world model from @cite{heim-1992} (`AttWorld` with
`actual` and `believed`) and show that the scope theory derives the
same empirical predictions via different machinery. -/

open Phenomena.Presupposition.Studies.Heim1992 (AttWorld believesR)

/-- The complement "he lost his wetsuit" as an `Iₚ`-typed meaning.

    Presupposes Theo has a wetsuit at the evaluation world. When defined,
    asserts he lost it. At `believed`: has wetsuit ✓, lost it ✓.
    At `actual`: no wetsuit → undefined. -/
def lostWetsuit : Iₚ AttWorld Bool
  | .believed => some true   -- has wetsuit, lost it
  | .actual => none          -- no wetsuit: presupposition failure

/-- Local reading of "Theo believes he lost his wetsuit."

    The complement stays in situ; `believe` quantifies over doxastic
    alternatives with the complement evaluated locally. -/
def believeLocal : Iₚ AttWorld Bool :=
  believe (λ _ => believesR) [AttWorld.actual, AttWorld.believed]
    lostWetsuit () -- () stands for Theo (single-agent model)

/-- Local reading at `actual`: Theo's only belief-world is `believed`,
    where the complement is defined and true → `some true`. -/
theorem believe_local_actual : believeLocal .actual = some true := rfl

/-- Local reading at `believed`: same → `some true`. -/
theorem believe_local_believed : believeLocal .believed = some true := rfl

/-- The local reading is always defined.

    The presupposition is that Theo **believes** he has a wetsuit
    (= the complement is defined at all doxastic alternatives).
    Since `believed` is the only belief-accessible world from either
    world, and the complement is defined there, this always holds.
    No projection to the actual world. -/
theorem believe_local_always_defined (w : AttWorld) :
    (believeLocal w).isSome = true := by
  cases w <;> rfl

/-- Global reading: the complement scopes out.

    The complement's definedness is evaluated at the actual world
    (not within the scope of `believe`). -/
def believeGlobal : Iₚ AttWorld Bool :=
  λ i => lostWetsuit i >>= (λ b =>
    believe (λ _ => believesR) [AttWorld.actual, AttWorld.believed]
      (ηI b) () i)

/-- Global reading at `actual`: complement is undefined → `none`.

    The presupposition projects globally: Theo must *actually* have
    a wetsuit at the evaluation world. -/
theorem believe_global_actual : believeGlobal .actual = none := rfl

/-- Global reading at `believed`: complement defined → `some true`. -/
theorem believe_global_believed : believeGlobal .believed = some true := rfl

/-- The global reading is defined iff the complement is defined at the
    evaluation world — the presupposition projects past `believe`. -/
theorem believe_global_definedness (w : AttWorld) :
    (believeGlobal w).isSome = (lostWetsuit w).isSome := by
  cases w <;> rfl

-- ════════════════════════════════════════════════════════════════
-- §7 Bridge to Heim 1992
-- ════════════════════════════════════════════════════════════════

/-! ### §7 Connection to @cite{heim-1992}

@cite{heim-1992}'s know/believe asymmetry is derived in `Heim1992.lean`
via local-context filtering and KD45 frame conditions. The scope theory
provides an alternative explanation: the asymmetry arises because the
trigger can take different scopes relative to the attitude verb.

The **local** reading corresponds to Heim's standard satisfaction-theory
prediction. The **global** reading is what the satisfaction theory
cannot derive — and what the scope theory adds. -/

/-- The local reading's definedness matches Heim's belief-embedding
    prediction: the presupposition is filtered (projected into the
    attitude holder's beliefs, not to the actual world). -/
theorem local_matches_heim_belief :
    -- Local reading defined at actual (no projection to actual world)
    (believeLocal .actual).isSome = true
    -- Even though the complement's presupposition fails at actual
    ∧ (lostWetsuit .actual).isSome = false := by
  exact ⟨rfl, rfl⟩

/-- The global reading adds what Heim's account lacks: a reading where
    the presupposition projects past the attitude verb entirely. -/
theorem global_projects_past_attitude :
    -- Global reading undefined at actual (projects to actual world)
    (believeGlobal .actual).isSome = false
    -- Because the complement's presupposition fails at actual
    ∧ (lostWetsuit .actual).isSome = false := by
  exact ⟨rfl, rfl⟩

end Phenomena.Presupposition.Studies.Grove2022
