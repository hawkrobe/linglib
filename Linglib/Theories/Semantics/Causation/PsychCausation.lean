/-!
# Psych Verb Causation (Kim 2024 UPH)

@cite{kim-2024}

Types for the Uniform Projection Hypothesis: all Class II (object experiencer)
psych verbs uniformly project Cause + Experiencer. The eventive/stative split
comes from the *causal source*: mind-external percepts (eventive, extensional
subject) vs mind-internal representations (stative, intensional subject).

Subject Matter (T/SM) is a causal adjunct mapping to the onset of the causal
chain; its incompatibility with an overt Cause follows from the Onset Condition.

## Key types

| Type | Purpose |
|------|---------|
| `CausalSource` | External (percept) vs internal (representation) |
| `CausalChainPosition` | Onset vs terminus in a two-link chain |

## Key results

- `subjectIntensional`: internal source → intensional subject position
- `onsetCondition`: causal adjuncts map to onset position
- T/SM restriction: Cause occupies onset, SM wants onset → conflict

## References

- Kim, Y. (2024). On the argument structure of object experiencer verbs.
  PhD thesis, University College London.
-/

namespace Semantics.Causation.PsychCausation

/-- Source of causation for psych causatives (Kim 2024 UPH).

    Class II psych verbs uniformly project Cause + Experiencer.
    The aspectual distinction (eventive vs stative) comes from
    what the Cause picks out:
    - `.external`: mind-external percept/event ("the noise frightened John")
    - `.internal`: mind-internal representation via "stative causation" /
      maintenance relation (Kim 2024, §3.3) — an existing mental
      representation maintains the experiencer's psychological state
      ("the problem concerns John") -/
inductive CausalSource where
  | external  -- percept/event → eventive reading
  | internal  -- mental representation (stative causation/maintenance) → stative reading
  deriving DecidableEq, Repr, BEq

/-- Position in a two-link causal chain (Kim 2024, Ch. 5).

    Class II psych verbs involve a causal chain from cause (onset)
    to experiencer's mental state change (terminus). -/
inductive CausalChainPosition where
  | onset      -- first link: external cause or representation
  | terminus   -- final link: experiencer's mental state change
  deriving DecidableEq, Repr, BEq

/-- The Onset Condition: causal adjuncts (including Subject Matter)
    must map to the onset position of the causal chain.

    This is the key to the T/SM restriction: if Cause already occupies
    onset and SM also requires onset, they conflict. -/
def onsetCondition (pos : CausalChainPosition) : Bool :=
  pos == .onset

/-- Internal causal source implies the subject position is intensional.

    When the cause is a mind-internal representation, the subject's
    referent depends on the experiencer's knowledge state, so
    substitution of co-referential terms can fail (Cicero/Tully). -/
def subjectIntensional (src : CausalSource) : Bool :=
  match src with
  | .internal => true
  | .external => false

/-- Is this a stative Class II reading? Stative ↔ internal source. -/
def CausalSource.isStative : CausalSource → Bool
  | .internal => true
  | .external => false

/-- Is this an eventive Class II reading? Eventive ↔ external source. -/
def CausalSource.isEventive : CausalSource → Bool
  | .external => true
  | .internal => false

end Semantics.Causation.PsychCausation
