import Linglib.Semantics.Tense.Reichenbach

/-!
# Tense and evidence

This file extends Reichenbach's frame with the time at which the speaker acquires the
evidence for the assertion, the learning time of Koev's account of the Bulgarian evidential
and the acquisition time of Cumming's account of tense-evidential paradigms. Evidence is
downstream of the event when the event precedes or coincides with its acquisition, and it is
acquired when its acquisition precedes or coincides with speech. Downstream evidence that has
been acquired is evidence for a nonfuture event, which is why no language restricts a true
future tense to downstream evidence.

## Main definitions

* `EvidentialFrame`: Reichenbach's frame with an acquisition time.
* `EvidentialFrame.Downstream`, `EvidentialFrame.Acquired`: the relations of the acquisition
  time to the event and to speech.

## Implementation notes

* Downstream evidence is read temporally, the event no later than the acquisition, as in
  Koev's and Lee's accounts and Cumming's tables; Cumming's own constraint is causal.

## References

* [S. Cumming, *Tense and evidence* (2026)][cumming-2026]
* [T. Koev, *Evidentiality, learning events and spatiotemporal distance* (2017)][koev-2017]
* [M. Huijsmans, *Timing of evidence and epistemic modal claims* (2025)][huijsmans-2025]
* [H. Reichenbach, *Elements of symbolic logic* (1947)][reichenbach-1947]
-/

namespace Tense.Evidential

open Semantics

variable {T : Type*}

/-- Reichenbach's frame with the time at which the speaker acquires the evidence grounding
the assertion. -/
structure EvidentialFrame (T : Type*) extends ReichenbachFrame T where
  /-- The time at which the speaker acquires the evidence for the assertion. -/
  acquisitionTime : T

namespace EvidentialFrame

/-- The evidence is downstream of the event when the event precedes or coincides with its
acquisition. -/
def Downstream [LE T] (f : EvidentialFrame T) : Prop := f.eventTime ≤ f.acquisitionTime

/-- The evidence is acquired by the time of speech. -/
def Acquired [LE T] (f : EvidentialFrame T) : Prop := f.acquisitionTime ≤ f.speechTime

instance [LE T] [DecidableLE T] (f : EvidentialFrame T) : Decidable f.Downstream :=
  inferInstanceAs (Decidable (f.eventTime ≤ f.acquisitionTime))

instance [LE T] [DecidableLE T] (f : EvidentialFrame T) : Decidable f.Acquired :=
  inferInstanceAs (Decidable (f.acquisitionTime ≤ f.speechTime))

theorem downstream_iff [LinearOrder T] (f : EvidentialFrame T) :
    f.Downstream ↔ compare f.eventTime f.acquisitionTime ∈ ⟦future⟧ᶜ :=
  (compare_mem_compl_future _ _).symm

theorem acquired_iff [LinearOrder T] (f : EvidentialFrame T) :
    f.Acquired ↔ compare f.acquisitionTime f.speechTime ∈ ⟦future⟧ᶜ :=
  (compare_mem_compl_future _ _).symm

/-- Downstream evidence acquired by the time of speech is evidence for a nonfuture event. -/
theorem eventTime_le_speechTime [Preorder T] {f : EvidentialFrame T} (hd : f.Downstream)
    (hA : f.Acquired) : f.eventTime ≤ f.speechTime :=
  le_trans hd hA

end EvidentialFrame

end Tense.Evidential
