import Linglib.Semantics.Tense.Reichenbach
import Linglib.Semantics.Tense.Basic

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
stated directly with the frame predicates.
-/

open Time

namespace Tense.Perspective

open Tense

/-! ### The ⌈then⌉ presupposition -/

/-- Temporal ⌈then⌉ presupposes that its reference is disjoint from the
    perspective π — in the point approximation, `thenRef ≠ perspective`
    ([tsilia-zhao-2026]). This is ⌈then⌉'s own presupposition, separate from
    the presuppositions of any co-clausal tense; the clash with PRES arises
    because the temporal assertion ("during then") forces the PRES reference
    inside the ⌈then⌉ reference. -/
def thenPresup {Time : Type*} (thenRef perspective : Time) : Prop :=
  thenRef ≠ perspective

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
def opPi {Time : Type*} (f : ReichenbachFrame Time) (newPi : Time) :
    ReichenbachFrame Time :=
  { f with perspectiveTime := newPi }

/-- OP_π corresponds to `embeddedFrame` when shifting to the matrix event time. -/
theorem opPi_eq_embeddedFrame {Time : Type*}
    (matrixFrame : ReichenbachFrame Time) (embeddedR embeddedE : Time) :
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
theorem then_present_clash {Time : Type*} (f : ReichenbachFrame Time)
    {thenRef : Time} (hPres : f.isPresent) (hDuring : f.referenceTime = thenRef)
    (hThen : thenPresup thenRef f.perspectiveTime) : False :=
  hThen (hDuring.symm.trans hPres)

/-- ⌈then⌉'s presupposition is satisfiable on any timeline with two points.
    This is why ⌈then⌉ is compatible with *deleted* (SOT) tense
    ([tsilia-zhao-2026]): a deleted tense contributes no perspectival
    presupposition, leaving only `thenPresup`, which any reference off the
    perspective witnesses. -/
theorem thenPresup_satisfiable {Time : Type*} [Nontrivial Time]
    (perspective : Time) : ∃ thenRef, thenPresup thenRef perspective :=
  exists_ne perspective

end Tense.Perspective
