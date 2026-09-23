module

public import Linglib.Semantics.Tense.Evidential
public import Linglib.Semantics.Presupposition.Basic
public import Linglib.Data.Examples.Cumming2026

/-!
# Cumming (2026): Tense and evidence

This file formalizes [cumming-2026]'s answer to Ninan's puzzle, that a future-tense sentence
can be asserted on prior inferential grounds while the past-tense sentence about the same
event cannot. Cumming, amending Cariani, assigns the nonfuture tenses the non-truth-conditional
constraint that the speaker's evidence be downstream of the event, and the future forms no
such constraint. A cell of a tense-evidential paradigm constrains three relations of the
frame, the evidential perspective, of the event to the acquisition of the evidence, the
relation of the acquisition to speech, and the utterance perspective, of the event to speech,
each a cell of the tense partition. Under the Korean evidentials *-te* and *-ney* of Lee and
the Bulgarian *-l* of Koev, the evidential fixes the relation of the acquisition to speech and
the tense the evidential perspective, and the utterance perspective is the composition of the
two; the English nonfuture tenses fix the utterance perspective and carry the downstream
constraint, and the past- and present-directed *will* forms of Winans restrict the evidence
to the prospective.

We derive the utterance-perspective columns of the paper's tables by composing cells, show
that the nonfuture cells of all three languages require downstream evidence, that no true
future can, and that the prospective cells lie beyond Cariani's obviation, and check the
paper's felicity judgments against the cells on the frames its scenarios fix, with planned
events exempt.

## Implementation notes

* The constraints are read temporally, as in the paper's tables; Cumming's own constraint is
  causal, and cases turning on the difference, as the rewatched film of footnote 9, are not
  represented.
* Koev distinguishes a null past and a null present tense under *-l*; Cumming's nonfuture cell
  is their join, and a frame satisfies it exactly when it satisfies one of Koev's two.
* The printed table (22) gives *will have* the utterance perspective T > S; the text and the
  example of the Fed's meeting require a past event, recorded here.

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

@[expose] public section

namespace Cumming2026

open Semantics

open Tense Tense.Evidential Presupposition Data.Examples

variable {T : Type*} [LinearOrder T]

/-! ### Paradigm cells -/

/-- A cell of a tense-evidential paradigm constrains the evidential perspective, the relation
of the event to the acquisition of the evidence, the relation of the acquisition to speech,
and the utterance perspective, the relation of the event to speech, each by a cell of the
tense partition, `⊤` where the paradigm leaves the relation open. -/
structure Cell where
  /-- The constraint on the evidential perspective. -/
  ep : Finset Ordering := ⊤
  /-- The constraint on the relation of the acquisition of the evidence to speech. -/
  acquisition : Finset Ordering := ⊤
  /-- The constraint on the utterance perspective. -/
  up : Finset Ordering := ⊤
  deriving DecidableEq

namespace Cell

/-- A cell holds at a frame when its three constraints do. -/
def Holds (c : Cell) (f : EvidentialFrame T) : Prop :=
  compare f.eventTime f.acquisitionTime ∈ c.ep ∧
    compare f.acquisitionTime f.speechTime ∈ c.acquisition ∧
    compare f.eventTime f.speechTime ∈ c.up

instance (c : Cell) (f : EvidentialFrame T) : Decidable (c.Holds f) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The utterance perspective that a cell's evidential perspective and its relation of the
acquisition to speech compose to (§3). -/
def derivedUp (c : Cell) : Finset Ordering := comp c.ep c.acquisition

/-- At a frame where a cell holds, the event stands to speech in the composition of the
cell's evidential perspective with its relation of the acquisition to speech. -/
theorem compare_mem_derivedUp {c : Cell} {f : EvidentialFrame T} (h : c.Holds f) :
    compare f.eventTime f.speechTime ∈ c.derivedUp :=
  compare_mem_comp h.1 h.2.1

/-- A cell whose evidential perspective lies within the nonfuture requires downstream
evidence, the constraint (10). -/
theorem downstream_of_holds {c : Cell} (hc : c.ep ≤ ⟦future⟧ᶜ) {f : EvidentialFrame T}
    (h : c.Holds f) : f.Downstream :=
  f.downstream_iff.2 (hc h.1)

/-- The meaning of a cell at a frame, with the constraints presupposed and the content
asserted: the constraint is not part of what is asserted. -/
@[simps] def meaning {W : Type*} (c : Cell) (f : EvidentialFrame T) (φ : W → Prop) :
    PartialProp W where
  presup _ := c.Holds f
  assertion := φ

end Cell

/-- An evidential fixes the relation of the acquisition of the evidence to speech and turns
the tense it combines with into a constraint on the evidential perspective (§3). -/
def evidential (acquisition tense : Finset Ordering) : Cell := { ep := tense, acquisition }

/-- A tense that is the join of two tenses holds under an evidential exactly when one of
them does. -/
theorem holds_evidential_sup {a t t' : Finset Ordering} {f : EvidentialFrame T} :
    (evidential a (t ⊔ t')).Holds f ↔ (evidential a t).Holds f ∨ (evidential a t').Holds f := by
  simp only [Cell.Holds, evidential, Finset.sup_eq_union, Finset.mem_union, Finset.top_eq_univ,
    Finset.mem_univ, and_true, or_and_right]

/-! ### The paradigms (§2 to §4) -/

/-- Korean *-te*, sensory evidence acquired in the past of speech ((13), (18)). -/
def te : Finset Ordering → Cell := evidential ⟦past⟧

/-- Korean *-ney*, sensory evidence acquired at speech ((14), (19)). -/
def ney : Finset Ordering → Cell := evidential ⟦present⟧

/-- Bulgarian *-l*, indirect evidence acquired by the time of speech ((15) to (17)). -/
def l : Finset Ordering → Cell := evidential ⟦future⟧ᶜ

/-- The English simple past requires downstream evidence for a past event ((20)). -/
def simplePast : Cell := { ep := ⟦future⟧ᶜ, up := ⟦past⟧ }

/-- The English present progressive requires downstream evidence for a present event ((20)). -/
def presentProgressive : Cell := { ep := ⟦future⟧ᶜ, up := ⟦present⟧ }

/-- The English future *will* places no evidential constraint on a future event ((20)). -/
def will : Cell := { up := ⟦future⟧ }

/-- The past-directed *will have* requires prospective evidence for a past event ((22)). -/
def willHave : Cell := { ep := ⟦future⟧, up := ⟦past⟧ }

/-- The present-directed *will now* requires prospective evidence for a present event ((22)). -/
def willNow : Cell := { ep := ⟦future⟧, up := ⟦present⟧ }

/-! ### The utterance perspective derived (§3)

Under *-te* and *-ney* the tense fixes the evidential perspective and the evidential the
relation of the acquisition to speech, and the utterance-perspective columns of tables (18)
and (19) are compositions; under *-l* the same holds of table (17), whose nonfuture cell is
the join of Koev's null past and null present. -/

theorem te_past_derivedUp : (te ⟦past⟧).derivedUp = ⟦past⟧ := comp_past_past

theorem te_present_derivedUp : (te ⟦present⟧).derivedUp = ⟦past⟧ := comp_present_left _

/-- Prospective evidence acquired in the past of speech leaves the utterance perspective
open: the future under *-te* is compatible with a past, present or future event. -/
theorem te_future_derivedUp : (te ⟦future⟧).derivedUp = ⊤ := comp_future_past

theorem ney_past_derivedUp : (ney ⟦past⟧).derivedUp = ⟦past⟧ := comp_present_right _

theorem ney_present_derivedUp : (ney ⟦present⟧).derivedUp = ⟦present⟧ := comp_present_right _

/-- Present evidence that is prospective is for a future event, since S = A and A < T give
S < T. -/
theorem ney_future_derivedUp : (ney ⟦future⟧).derivedUp = ⟦future⟧ := comp_present_right _

/-- Downstream evidence acquired by the time of speech is for a nonfuture event ((17)). -/
theorem l_nonfuture_derivedUp : (l ⟦future⟧ᶜ).derivedUp = ⟦future⟧ᶜ := by
  show comp ⟦future⟧ᶜ ⟦future⟧ᶜ = ⟦future⟧ᶜ
  rw [← past_sup_present, comp_sup_left, comp_sup_right, comp_sup_right]
  simp

/-- Prospective evidence acquired by the time of speech leaves the utterance perspective
open: the future under *-l* describes yesterday's forecast rain ((16)). -/
theorem l_future_derivedUp : (l ⟦future⟧).derivedUp = ⊤ := by
  show comp ⟦future⟧ ⟦future⟧ᶜ = ⊤
  rw [← past_sup_present, comp_sup_right]
  simp

/-- Cumming's nonfuture cell under *-l* holds exactly when Koev's null past or null present
does (footnote 7). -/
theorem holds_l_nonfuture_iff {f : EvidentialFrame T} :
    (l ⟦future⟧ᶜ).Holds f ↔ (l ⟦past⟧).Holds f ∨ (l ⟦present⟧).Holds f := by
  rw [← past_sup_present]
  exact holds_evidential_sup

/-! ### Downstream evidence, obviation and the true future (§5, §7) -/

/-- Across the three languages, the nonfuture tenses restrict the evidence to the
non-prospective. -/
theorem nonfuture_ep_le :
    ∀ c ∈ [simplePast, presentProgressive, te ⟦past⟧, te ⟦present⟧, ney ⟦past⟧, ney ⟦present⟧,
      l ⟦future⟧ᶜ], c.ep ≤ ⟦future⟧ᶜ := by
  decide

/-- The prospective cells of Korean, Bulgarian and the English *will* forms are neither
restricted to downstream evidence nor unrestricted, the two options Cariani's obviation
provides (§5). -/
theorem prospective_beyond_obviation :
    ∀ c ∈ [te ⟦future⟧, ney ⟦future⟧, l ⟦future⟧, willHave, willNow],
      c.ep ≠ ⟦future⟧ᶜ ∧ c.ep ≠ ⊤ := by
  decide

/-- No true future is restricted to downstream evidence, since at a frame where such a cell
held the speaker would speak before acquiring the evidence (§7). -/
theorem speechTime_lt_acquisitionTime {f : EvidentialFrame T}
    (h : (⟨⟦future⟧ᶜ, ⊤, ⟦future⟧⟩ : Cell).Holds f) : f.speechTime < f.acquisitionTime :=
  lt_of_lt_of_le ((compare_mem_future _ _).1 h.2.2) ((compare_mem_compl_future _ _).1 h.1)

/-- The past-directed *will have* and the simple past assert the same proposition and differ
in what they presuppose, so *will have* is no necessity modal ((23)). -/
theorem willHave_meaning_assertion {W : Type*} (f : EvidentialFrame T) (φ : W → Prop) :
    (willHave.meaning f φ).assertion = (simplePast.meaning f φ).assertion :=
  rfl

/-! ### The felicity judgments -/

/-- The cell a row's `form` feature names. -/
def cell? (e : LinguisticExample) : Option Cell :=
  e.parse? "form"
    [("simple past", simplePast), ("present progressive", presentProgressive),
      ("future (will)", will), ("will have V-ed", willHave), ("will now be V-ing", willNow),
      ("-te PAST", te ⟦past⟧), ("-te PRES", te ⟦present⟧), ("-te FUT", te ⟦future⟧),
      ("-ney PAST", ney ⟦past⟧), ("-ney PRES", ney ⟦present⟧), ("-ney FUT", ney ⟦future⟧),
      ("NFUT + -l", l ⟦future⟧ᶜ), ("FUT + -l", l ⟦future⟧)]

/-- The frame a row's scenario fixes, with the perspective and reference times at speech. -/
def frame? (e : LinguisticExample) : Option (EvidentialFrame ℤ) := do
  let s ← e.nat? "speechTime"
  let a ← e.nat? "acquisitionTime"
  let t ← e.nat? "eventTime"
  pure { speechTime := s, perspectiveTime := s, referenceTime := s, eventTime := t,
         acquisitionTime := a }

/-- The row describes a planned or scheduled event (§6). -/
def Scheduled (e : LinguisticExample) : Prop := e.feature? "scheduled" = some "true"

instance : DecidablePred Scheduled := fun _ ↦ inferInstanceAs (Decidable (_ = _))

/-- Every example names a cell and a scenario. -/
theorem cell?_frame?_isSome : ∀ e ∈ Examples.all, (cell? e).isSome ∧ (frame? e).isSome := by
  decide

/-- An assertion is felicitous exactly when its cell holds on the scenario's frame, planned
or scheduled events exempt (§6). -/
theorem judgment_iff : ∀ e ∈ Examples.all, ∀ c ∈ cell? e, ∀ f ∈ frame? e,
    (e.judgment = .acceptable ↔ Scheduled e ∨ c.Holds f) := by
  decide

end Cumming2026
