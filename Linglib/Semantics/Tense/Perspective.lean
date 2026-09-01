import Linglib.Semantics.Tense.Reichenbach
import Linglib.Semantics.Tense.Embedding

/-!
# Perspectival tense: presuppositions anchored to π

[tsilia-zhao-2026] and [zhao-2025] interpret tenses as temporal pronouns with
presuppositions anchored to a perspective parameter π
(`ReichenbachFrame.perspectiveTime`): PRES presupposes overlap of its
reference with π, PAST precedence, and temporal ⌈then⌉ disjointness
(`thenPresup`). The operator OP_π (`opPi`), modelled on the context-shifting
monsters of [anand-nevins-2004] and [deal-2020], rebinds π for a whole
clause, so clausemate PRES and ⌈then⌉ always read the same π and their
presuppositions clash (`then_present_clash`) — the ⌈then⌉-present puzzle.
Deleted (SOT) tense carries no perspectival presupposition, so ⌈then⌉
remains satisfiable (`thenPresup_satisfiable`).

In the point approximation used throughout, overlap is equality: the PRES
presupposition *is* `ReichenbachFrame.isPresent` (R = π) and the PAST
presupposition *is* `ReichenbachFrame.isPast` (R < π), so theorems here are
stated directly with the frame predicates. Tenses and ⌈then⌉ are temporal
pronouns in one architecture ([partee-1973], `TensePronoun`): each
presupposes a comparison category (`Finset Ordering`) of its reference
against π — PAST `Tense.past`, PRES `Tense.present`, and ⌈then⌉
`Tense.presentᶜ`, the complement of `Tense.present`, so the
⌈then⌉-present clash is disjointness of comparison categories.
-/

open Time

namespace Tense.Perspective

open Tense

/-! ### The ⌈then⌉ presupposition -/

/-- Temporal ⌈then⌉ presupposes that its reference is disjoint from the
    perspective π: the cell `Tense.presentᶜ`, the complement of PRES's
    `Tense.present` ([tsilia-zhao-2026]). This is ⌈then⌉'s own
    presupposition, separate from the presuppositions of any co-clausal
    tense; the clash with PRES arises because the temporal assertion
    ("during then") forces the PRES reference inside the ⌈then⌉
    reference. -/
def thenPresup {T : Type*} [LinearOrder T] (thenRef perspective : T) : Prop :=
  compare thenRef perspective ∈ Tense.presentᶜ

@[simp] theorem thenPresup_def {T : Type*} [LinearOrder T]
    (thenRef perspective : T) :
    thenPresup thenRef perspective ↔ thenRef ≠ perspective := by
  simp [thenPresup]

/-- A ⌈then⌉-type temporal adverb: a lexical item denoting a temporal pronoun
    that carries the `thenPresup` disjointness presupposition (English *then*,
    Greek *tóte*, Japanese *tōji*, ... — [zhao-2025]). Entries live in
    `Fragments/{Language}/TemporalDeictic.lean`. -/
structure ThenAdverb where
  /-- Surface form -/
  form : String
  /-- English gloss -/
  gloss : String
  deriving Repr, DecidableEq

/-! ### OP_π: the perspective-shifting operator -/

/-- OP_π shifts the perspective time to a new value.
    ⟦OP_π φ⟧^{c,π,g} = λi_κ. ⟦φ⟧^{c,i_t,g}(i) -/
def opPi {T : Type*} (f : ReichenbachFrame T) (newPi : T) :
    ReichenbachFrame T :=
  { f with perspectiveTime := newPi }

/-- OP_π corresponds to `embeddedFrame` when shifting to the matrix event time. -/
theorem opPi_eq_embeddedFrame {T : Type*}
    (matrixFrame : ReichenbachFrame T) (embeddedR embeddedE : T) :
    opPi { speechTime := matrixFrame.speechTime
           perspectiveTime := matrixFrame.speechTime
           referenceTime := embeddedR
           eventTime := embeddedE }
         matrixFrame.eventTime =
    embeddedFrame matrixFrame embeddedR embeddedE := by
  simp only [opPi, embeddedFrame]

/-! ### Clash and satisfiability -/

/-- The ⌈then⌉-present clash. Three ingredients produce the contradiction:
    PRES presupposes R = π (`isPresent`), the temporal assertion requires the
    ⌈then⌉ reference to contain — in the point approximation, equal — R
    ("during then"), and ⌈then⌉ presupposes its reference disjoint from π. -/
theorem then_present_clash {T : Type*} [LinearOrder T]
    (f : ReichenbachFrame T)
    {thenRef : T} (hPres : f.isPresent) (hDuring : f.referenceTime = thenRef)
    (hThen : thenPresup thenRef f.perspectiveTime) : False :=
  (thenPresup_def _ _).mp hThen (hDuring.symm.trans hPres)

/-- ⌈then⌉'s presupposition is satisfiable on any timeline with two points.
    This is why ⌈then⌉ is compatible with *deleted* (SOT) tense
    ([tsilia-zhao-2026]): a deleted tense contributes no perspectival
    presupposition, leaving only `thenPresup`, which any reference off the
    perspective witnesses. -/
theorem thenPresup_satisfiable {T : Type*} [LinearOrder T] [Nontrivial T]
    (perspective : T) : ∃ thenRef, thenPresup thenRef perspective := by
  simpa using exists_ne perspective

end Tense.Perspective
