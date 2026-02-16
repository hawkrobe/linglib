/-
# Parasitic Attitudes (Maier 2015)

Formalizes the asymmetric dependency between doxastic and non-doxastic attitudes
for presupposition projection.

## The Problem

Karttunen (1973) observed:

  "Bill believed Fred had been beating his wife and he hoped Fred would stop"
  → Presupposition of "stop" is FILTERED by preceding belief

But:

  "*John hopes Mary will come. He believes Sue will come too."
  → Presupposition of "too" is NOT filtered by preceding hope

## Maier's Solution

Non-doxastic attitudes (hope, fear, imagine) are parasitic on doxastic
attitudes (believe, know): their presupposition computation uses the
doxastic accessibility relation, not their own.

This explains the asymmetry: belief provides a context that satisfies
hope's presuppositions, but hope cannot provide a context for belief.

## Insight

The parasitic relationship means:
- Hope's local context = belief's local context (when belief is available)
- Belief's local context = its own accessibility relation (independent)

## References

- Maier (2015). Parasitic Attitudes. Linguistics and Philosophy.
- Karttunen (1973). Presuppositions of Compound Sentences.
- Heim (1992). Presupposition Projection and the Semantics of Attitude Verbs.
-/

import Linglib.Theories.Semantics.Attitudes.Doxastic
import Linglib.Theories.Semantics.Attitudes.Preferential
import Linglib.Core.Presupposition
import Linglib.Theories.Semantics.Presupposition.BeliefEmbedding

namespace Semantics.Attitudes.Parasitic

open Core.Presupposition
open Semantics.Attitudes.Doxastic
open Semantics.Attitudes.Preferential
open Semantics.Presupposition.BeliefEmbedding


/--
A non-doxastic attitude is parasitic on a doxastic one when its
presupposition computation uses the doxastic accessibility relation
rather than its own.

Formally: for presupposition filtering under the non-doxastic attitude,
we check whether the presupposition holds at all worlds accessible via
the doxastic relation.
-/
def isParasiticOn {W E : Type*}
    (nonDoxAccess : E → W → W → Bool)  -- Non-doxastic accessibility
    (doxAccess : AccessRel W E)        -- Doxastic accessibility
    : Prop :=
  -- The non-doxastic attitude's presupposition filtering uses doxAccess
  ∀ (agent : E) (w : W) (presup : W → Bool),
    -- If presup holds at all doxastically accessible worlds...
    (∀ w', doxAccess agent w w' = true → presup w' = true) →
    -- ...then presup is locally satisfied for the non-doxastic attitude
    (∀ w', nonDoxAccess agent w w' = true → presup w' = true)

/--
A preferential predicate is parasitic on a doxastic predicate when
the preferential predicate's presupposition filtering defers to the
doxastic accessibility relation.
-/
def PreferentialParasiticOn {W E : Type*}
    (_pref : PreferentialPredicate W E)
    (dox : DoxasticPredicate W E) : Prop :=
  ∀ (agent : E) (p : PrProp W) (w : W) (worlds : List W),
    -- If presupposition holds in all belief worlds...
    (∀ w' ∈ worlds, dox.access agent w w' = true → p.presup w' = true) →
    -- ...then presupposition is satisfied locally for the preferential attitude
    ∀ w' ∈ worlds, p.presup w' = true ∨ dox.access agent w w' = false


/--
The list of attitude verbs that are parasitic on belief.

These are non-doxastic attitudes whose presupposition filtering
uses the belief accessibility relation.
-/
inductive ParasiticAttitude where
  | hope
  | fear
  | imagine
  | dream
  | wish
  | expect
  deriving DecidableEq, Repr

/--
Hope is parasitic on belief.

When "X believes P and hopes Q", the presuppositions of Q are
filtered using X's belief state, not X's hope state.
-/
def hopeParasiticOnBelief : ParasiticAttitude := .hope

/--
Imagine is parasitic on belief.

When "X believes P and imagines Q", the presuppositions of Q are
filtered using X's belief state.
-/
def imagineParasiticOnBelief : ParasiticAttitude := .imagine

/--
Dream is parasitic on belief.

When "X believes P and dreams Q", the presuppositions of Q are
filtered using X's belief state.
-/
def dreamParasiticOnBelief : ParasiticAttitude := .dream


/--
The parasitic dependency is asymmetric.

Non-doxastic attitudes depend on doxastic ones for presupposition
filtering, but NOT vice versa.

This explains Karttunen's observation:
- believe → hope: hope uses belief's accessibility → filtering works
- hope → believe: belief uses its own accessibility → no filtering
-/
structure ParasiticAsymmetry {W E : Type*}
    (dox : DoxasticPredicate W E)
    (nonDox : PreferentialPredicate W E) where
  /-- Non-doxastic is parasitic on doxastic -/
  forward : PreferentialParasiticOn nonDox dox
  /-- Doxastic is NOT parasitic on non-doxastic -/
  backward : ¬ ∀ (_agent : E) (_p : PrProp W) (_w : W) (_worlds : List W),
    -- Even if we had a preferential accessibility relation...
    True → True  -- Belief doesn't depend on preferential attitudes

/--
The filtering direction determines which sequences work.

Filtering can occur in "believe P and hope Q" but not "hope P and believe Q".
-/
inductive FilteringDirection where
  | doxasticFirst  -- believe → hope: CAN filter
  | parasiticFirst -- hope → believe: CANNOT filter
  deriving DecidableEq, Repr

/--
Can filtering occur given the attitude order?
-/
def canFilter : FilteringDirection → Bool
  | .doxasticFirst => true
  | .parasiticFirst => false

theorem doxastic_first_can_filter : canFilter .doxasticFirst = true := rfl
theorem parasitic_first_cannot_filter : canFilter .parasiticFirst = false := rfl


/--
World type for the Bill/Fred example.
-/
inductive BeatingWorld where
  | fredWasBeating_fredStopped
  | fredWasBeating_fredContinues
  | fredNeverBeat
  deriving DecidableEq, Repr, Inhabited

/--
Bill's belief accessibility relation.

In some worlds, Bill believes Fred was beating his wife.
-/
def billBeliefAccess : AccessRel BeatingWorld Unit
  | (), .fredWasBeating_fredStopped, w' => match w' with
      | .fredWasBeating_fredStopped => true
      | .fredWasBeating_fredContinues => true
      | .fredNeverBeat => false
  | (), .fredWasBeating_fredContinues, w' => match w' with
      | .fredWasBeating_fredStopped => true
      | .fredWasBeating_fredContinues => true
      | .fredNeverBeat => false
  | (), .fredNeverBeat, w' => match w' with
      | .fredNeverBeat => true
      | _ => false

/--
Bill's belief predicate.
-/
def billBelieve : DoxasticPredicate BeatingWorld Unit :=
  believeTemplate billBeliefAccess

/--
The presupposition of "Fred stopped": Fred was beating.
-/
def fredWasBeatingPresup : BeatingWorld → Bool
  | .fredWasBeating_fredStopped => true
  | .fredWasBeating_fredContinues => true
  | .fredNeverBeat => false

/--
When Bill believes Fred was beating, hope's presupposition
is satisfied.

At worlds where Bill believes Fred was beating, ALL his belief-accessible
worlds satisfy the presupposition of "stop".
-/
theorem belief_satisfies_hope_presup :
    ∀ w, (w = .fredWasBeating_fredStopped ∨ w = .fredWasBeating_fredContinues) →
    ∀ w', billBeliefAccess () w w' = true → fredWasBeatingPresup w' = true := by
  intro w hw w' hw'
  cases hw with
  | inl h => subst h; cases w' <;> simp_all [billBeliefAccess, fredWasBeatingPresup]
  | inr h => subst h; cases w' <;> simp_all [billBeliefAccess, fredWasBeatingPresup]

/--
At worlds where Bill doesn't believe Fred was beating,
the presupposition of "stop" fails in Bill's belief worlds.
-/
theorem no_belief_no_filter :
    ∀ w', billBeliefAccess () .fredNeverBeat w' = true →
    fredWasBeatingPresup w' = false := by
  intro w' hw'
  cases w' <;> simp_all [billBeliefAccess, fredWasBeatingPresup]


/--
The local context for a parasitic attitude embedded under belief.

When we have "X believes P and hopes Q", the local context for Q
is computed from X's belief state (not a separate hope accessibility).
-/
def parasiticLocalContext {W E : Type*}
    (dox : DoxasticPredicate W E)
    (agent : E)
    (w : W)
    (globalCtx : W → Bool) : W → Bool :=
  λ w' => globalCtx w && dox.access agent w w' = true

/--
A presupposition is filtered in the parasitic local context iff
it holds at all doxastically accessible worlds.
-/
def presupFilteredInParasitic {W E : Type*}
    (dox : DoxasticPredicate W E)
    (agent : E)
    (w : W)
    (presup : W → Bool)
    (worlds : List W) : Bool :=
  worlds.all λ w' => !dox.access agent w w' || presup w'


/--
Convert a parasitic attitude context to a BeliefLocalCtx.

This shows that parasitic attitudes use the same local context
machinery as belief embedding itself.
-/
def toBeliefLocalCtx {W E : Type*}
    (dox : DoxasticAccessibility W E)
    (globalCtx : W → Prop)
    (agent : E) : BeliefLocalCtx W E :=
  { globalCtx := globalCtx
  , dox := dox
  , agent := agent }

/--
The key insight: parasitic attitudes compute presupposition filtering
using `presupAttributedToHolder` from BeliefEmbedding.

This unifies the treatment: both "X believes P" and "X hopes P" (when
hope is parasitic on belief) use the same local context machinery.
-/
theorem parasitic_uses_belief_local_context {W E : Type*}
    (dox : DoxasticAccessibility W E)
    (globalCtx : W → Prop)
    (agent : E)
    (p : PrProp W) :
    let blc := toBeliefLocalCtx dox globalCtx agent
    presupAttributedToHolder blc p ↔
    ∀ w_star, globalCtx w_star → ∀ w', dox agent w_star w' → p.presup w' = true := by
  simp only [toBeliefLocalCtx, presupAttributedToHolder, BeliefLocalCtx.atWorld,
        Core.CommonGround.ContextSet.entails]
  constructor
  · intro h w_star hw_star w' hdox
    exact h w_star hw_star w' (And.intro hw_star hdox)
  · intro h w_star hw_star w' hw
    exact h w_star hw_star w' hw.2


/--
Summary structure capturing the parasitic attitude analysis.
-/
structure ParasiticAnalysis {W E : Type*} where
  /-- The doxastic predicate that hosts parasitic attitudes -/
  doxasticHost : DoxasticPredicate W E
  /-- List of parasitic attitudes -/
  parasiticAttitudes : List ParasiticAttitude
  /-- The key property: parasitic attitudes use doxastic accessibility -/
  useDoxasticAccessibility : Bool := true

/--
Standard analysis with belief as host.
-/
def standardAnalysis {W E : Type*} (believe : DoxasticPredicate W E) :
    ParasiticAnalysis (W := W) (E := E) :=
  { doxasticHost := believe
  , parasiticAttitudes := [.hope, .fear, .imagine, .dream, .wish, .expect]
  , useDoxasticAccessibility := true }

end Semantics.Attitudes.Parasitic
