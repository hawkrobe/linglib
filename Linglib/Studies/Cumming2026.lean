import Linglib.Fragments.English.Tense
import Linglib.Fragments.Korean.Evidentials
import Linglib.Fragments.Slavic.Bulgarian.Evidentials
import Linglib.Data.Examples.Cumming2026

/-!
# Tense and evidence

Ninan observed that a future-tense sentence can be asserted on prior inferential grounds
while the past-tense sentence about the same event, uttered once the event has passed on the
same grounds, cannot, although the two are true in the same circumstances. In Cumming's
version, *Alma will enjoy the meal* is assertible before the meal and *Alma enjoyed the meal*
is not the next day, yet *Alma will have enjoyed the meal* is, which tells against an
epistemic account of the asymmetry. Cumming's explanation is linguistic and amends
Cariani's: the constraint that the speaker's evidence be causally downstream of the event
described, which Cariani places on every predicate and lets modals obviate, belongs to the
nonfuture tenses of English as non-truth-conditional meaning, and the future forms lack it.
The evidential paradigms of Korean and Bulgarian show the same recruitment of tense. Under
the evidentials *-te*, *-ney* and *-l*, tense fixes the evidential perspective, the relation
of the event to the acquisition of the evidence; *-te* and *-ney* place the acquisition in the
past of speech and at speech, and for *-l* it suffices that evidence is acquired by the time
of speech; and the utterance perspective, the ordinary contribution of tense, is derived:
present evidence that is prospective is evidence for a future event, downstream evidence
acquired by the time of speech is evidence for a nonfuture event, and past evidence that is
prospective leaves the utterance perspective open. The past- and present-directed *will have*
and *will now* carry the prospective constraint with a past or present utterance perspective.
No language should have a true future restricted to downstream evidence, since the speaker
would have to acquire the evidence after speaking. Where Cariani's account offers the
downstream constraint or its obviation, Korean under *-te* and the English *will* forms show a
third option, the positive restriction to prospective evidence. Planned or scheduled events
are exempt from both perspectives, as in the futurate.

We derive the utterance-perspective column of the Korean and Bulgarian paradigms as the
composition of the evidential-perspective column with the cell relating the acquisition of
the evidence to speech, show that the future cells leave the utterance perspective open,
prove that a downstream-restricted future is unsatisfiable and that the prospective cells lie
beyond obviation, and check the paper's felicity judgments against the paradigm cells on the
frames its scenarios fix.

## Implementation notes

* Paradigm cells are the fragments' rows, each an evidential-perspective and an
  utterance-perspective constraint on a frame of speech, acquisition and event times, read
  temporally as in the paper's tables. Cumming's own constraint is causal, and he declines
  the temporal reading of Lee's and Koev's accounts; evidence temporally after but causally
  independent of the event, or before it yet downstream, as the rewatched film of footnote
  9, is not represented.
* The cells relating acquisition to speech, the past for *-te*, the present for *-ney*, and
  the nonfuture for *-l* as for any assertion, are the paper's; the utterance perspective is
  their composition with the evidential perspective by the substrate's cell composition.
* The paper calls the constraint non-truth-conditional and a felicity condition; the
  substrate renders it as a presupposition, and the shared assertion of cells differing in
  tense holds there by construction rather than being derived.
* The felicity data enter each scenario's times as small integers on one line; scenarios
  the paper does not spell out are reconstructed and say so. The futurate exemption is
  recorded as a flag on the planned or scheduled examples rather than derived, since the
  paper leaves the criterion for it open.
* The unmarked pattern of §7, the ranking of evidential sources and the acquaintance
  inference, is prose.

## TODO

* Causal downstreamness, on which the paper's decisive cases turn, needs a relation between
  the evidence-acquiring event and the described event with the temporal constraint as a
  consequence.

## References

* [S. Cumming, *Tense and evidence* (2026)][cumming-2026]
* [D. Ninan, *Assertion, evidence, and the future* (2022)][ninan-2022]
* [F. Cariani, *The modal future* (2021)][cariani-2021]
* [F. Cariani, *Future-past asymmetries, evidential grounding, and projection*
  (2022)][cariani-2022]
* [J. Lee, *Evidentiality and its interaction with tense: evidence from Korean*
  (2011)][lee-2011]
* [J. Lee, *Temporal constraints on the meaning of evidentiality* (2013)][lee-2013]
* [T. Koev, *Evidentiality, learning events and spatiotemporal distance* (2017)][koev-2017]
* [L. Winans, *Inferences of will* (2016)][winans-2016]
* [S. Cumming, L. Winans, *Counterfactuals and abduction* (2021)][cumming-winans-2021]
* [L. Matthewson, *Evidence type, evidence location, evidence strength*
  (2020)][matthewson-2020]
-/

namespace Cumming2026

open Tense Tense.Evidential Korean.Evidentials Bulgarian.Evidentials

/-- A frame with the perspective and reference times at speech. -/
def frame (s a t : ℤ) : EvidentialFrame ℤ :=
  { speechTime := s, perspectiveTime := s, referenceTime := s, eventTime := t,
    acquisitionTime := a }

/-! ### Utterance perspective derived (§3) -/

/-- Under *-te*, past sensory evidence, each cell's utterance perspective is the composition
of its evidential perspective with the past ((18)). -/
theorem te_up_eq_comp : ∀ p ∈ teEntries, p.up.toRelation = comp p.ep.toRelation past := by
  decide

/-- Under *-ney*, present sensory evidence, each cell's utterance perspective is the
composition of its evidential perspective with the present ((19)): present evidence that is
prospective is for a future event. -/
theorem ney_up_eq_comp : ∀ p ∈ neyEntries, p.up.toRelation = comp p.ep.toRelation present := by
  decide

/-- Under *-l*, with the evidence acquired by the time of speech, each cell's utterance
perspective is the composition of its evidential perspective with the nonfuture ((17)):
downstream evidence is for a nonfuture event. -/
theorem l_up_eq_comp :
    ∀ p ∈ Bulgarian.Evidentials.allEntries, p.up.toRelation = comp p.ep.toRelation futureᶜ := by
  decide

/-- Prospective evidence acquired in the past of speech leaves the utterance perspective
open: the future under *-te* is compatible with a past, present or future event. -/
theorem comp_future_past : comp future past = ⊤ := by decide

/-- Prospective evidence acquired by the time of speech leaves the utterance perspective
open: the future under *-l* describes yesterday's forecast rain ((16)). -/
theorem comp_future_compl_future : comp future futureᶜ = ⊤ := by decide

/-! ### Beyond obviation, and the unmarked pattern (§5, §7) -/

/-- Korean under *-te* restricts the evidence to the prospective, an option that neither the
downstream constraint nor its obviation provides. -/
theorem exists_te_prospective : ∃ p ∈ teEntries, p.ep = .prospective := by decide

/-- The English *will* forms restrict the evidence to the prospective. -/
theorem exists_will_prospective : ∃ p ∈ English.Tense.allEntries, p.ep = .prospective := by
  decide

/-- No true future restricted to downstream evidence: evidence acquired by the time of speech
and downstream of the event places the event no later than speech. -/
theorem not_speechTime_lt_eventTime {f : EvidentialFrame ℤ} (hd : f.Downstream)
    (hA : f.Acquired) : ¬ f.speechTime < f.eventTime :=
  not_lt.2 (f.eventTime_le_speechTime hd hA)

/-! ### The felicity judgments -/

/-- The paradigm cells of the three languages. -/
def allParadigms : List TAMEEntry :=
  English.Tense.allEntries ++ Korean.Evidentials.allEntries ++ Bulgarian.Evidentials.allEntries

/-- A felicity judgment of the paper: the paradigm cell, the frame the scenario fixes, whether
the event is planned or scheduled, and the judgment. -/
structure Datum where
  cell : TAMEEntry
  frame : EvidentialFrame ℤ
  scheduled : Bool
  judgment : Features.Judgment

/-- An example's judgment together with its cell and the scenario's times. -/
def datum (e : Data.Examples.LinguisticExample) : Option Datum := do
  let cell ← allParadigms.find? (·.label == (← e.feature? "form"))
  let s ← e.nat? "speechTime"
  let a ← e.nat? "acquisitionTime"
  let t ← e.nat? "eventTime"
  pure { cell, frame := frame s a t,
         scheduled := decide (e.feature? "scheduled" = some "true"), judgment := e.judgment }

/-- Every example names a cell and a scenario. -/
theorem datum_isSome : ∀ e ∈ Examples.all, (datum e).isSome := by decide

/-- The paper's felicity judgments. -/
def data : List Datum := Examples.all.filterMap datum

/-- An assertion is felicitous exactly when its cell's two constraints hold on the scenario's
frame, planned or scheduled events exempt (§6). -/
theorem judgment_iff : ∀ d ∈ data, d.judgment = .acceptable ↔
    d.scheduled ∨ (d.cell.ep.toConstraint d.frame ∧ d.cell.up.toConstraint d.frame) := by
  decide

end Cumming2026
