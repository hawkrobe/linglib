import Linglib.Fragments.English.Tense
import Linglib.Fragments.Korean.Evidentials
import Linglib.Fragments.Slavic.Bulgarian.Evidentials
import Linglib.Data.Examples.Cumming2026

/-!
# Tense and evidence

Ninan's puzzle is that a future-tense sentence can be asserted on prior inferential grounds
while the past-tense sentence about the same event, on the same grounds, cannot, though
*will have* is assertible again. Cumming's answer, amending Cariani, is that the nonfuture
tenses carry, as non-truth-conditional meaning, the constraint that the speaker's evidence be
causally downstream of the event, and the future forms do not. Under the Korean evidentials
*-te* and *-ney* and the Bulgarian *-l*, tense fixes the evidential perspective, the
evidential the relation of the acquisition of evidence to speech, and the utterance
perspective is derived from the two; the English *will have* and *will now* restrict evidence
to the prospective; no true future can be restricted to downstream evidence; and planned
events are exempt, as in the futurate.

We derive the utterance-perspective column of the Korean and Bulgarian paradigms as the
composition of the evidential-perspective column with the evidential's cell, prove that a
downstream-restricted future is unsatisfiable and that the prospective cells lie beyond
Cariani's obviation, and check the paper's felicity judgments against the cells on the
frames its scenarios fix.

## Implementation notes

* The constraints are read temporally, as in the paper's tables; Cumming's own constraint is
  causal, and cases turning on the difference, as the rewatched film of footnote 9, are not
  represented.

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
