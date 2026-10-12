module

public import Linglib.Semantics.Tense.Defs

/-!
# Tense and evidence

An evidential frame locates an assertion by three times: the time of speech, the time of the
event, and the time at which the speaker acquires the evidence for the assertion, the learning
time of Koev's account of the Bulgarian evidential and the acquisition time of Cumming's account
of tense-evidential paradigms. Evidence is downstream of the event when the event precedes or
coincides with its acquisition, so that on linear time the event stands to the acquisition in a
nonfuture position.

## Main definitions

* `Tense.EvidentialFrame`: the speech time, the event time and the acquisition time of an
  assertion.
* `Tense.EvidentialFrame.Downstream`: the event is no later than the acquisition of the
  evidence.

## Implementation notes

* Downstream evidence is read temporally, the event no later than the acquisition, as in
  Koev's and Lee's accounts and Cumming's tables; Cumming's own constraint is causal.

## References

* [cumming-2026]
* [koev-2017]
* [huijsmans-2025]
-/

@[expose] public section

namespace Tense

open Semantics

/-- An evidential frame consists of the time of speech, the time of the event, and the time at
which the speaker acquires the evidence for the assertion. -/
structure EvidentialFrame (T : Type*) where
  /-- The time at which the utterance occurs. -/
  speechTime : T
  /-- The time at which the event occurs. -/
  eventTime : T
  /-- The time at which the speaker acquires the evidence for the assertion. -/
  acquisitionTime : T

namespace EvidentialFrame

variable {T : Type*}

/-- The evidence is downstream of the event when the event precedes or coincides with its
acquisition. -/
def Downstream [LE T] (f : EvidentialFrame T) : Prop := f.eventTime ≤ f.acquisitionTime

instance [LE T] [DecidableLE T] (f : EvidentialFrame T) : Decidable f.Downstream :=
  inferInstanceAs (Decidable (f.eventTime ≤ f.acquisitionTime))

theorem downstream_iff [LinearOrder T] (f : EvidentialFrame T) :
    f.Downstream ↔ compare f.eventTime f.acquisitionTime ∈ ⟦future⟧ᶜ :=
  (compare_mem_compl_future _ _).symm

end EvidentialFrame

end Tense
