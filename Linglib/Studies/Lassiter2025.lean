import Linglib.Data.Examples.Lassiter2025
import Linglib.Fragments.English.PolarityItems
import Linglib.Fragments.Japanese.Conditionals
import Linglib.Fragments.German.Conditionals

/-!
# Lassiter (2025): Sorting Out Left-Nested Conditionals

This file formalizes [lassiter-2025]'s account of left-nested conditionals, conditionals with
another conditional in their antecedent, such as [gibbard-1981]'s *If Kripke was there if
Strawson was, then Anscomb was there*. A conditional is construed as hypothetical or as a
premise conditional ([iatridou-1991]); a left-nested conditional whose embedded conditional
is bare admits only the premise reading, while an embedded modal, adverb of quantification,
or generic operator restores the hypothetical one (`readings`). A sentence is acceptable
when some reading open to it meets what its context or diagnostic demands (`Acceptable`), so
for a bare left-nested conditional every diagnostic reduces to the premise reading
(`acceptable_bare_iff`). A premise reading needs a discourse antecedent, so bare left-nested
conditionals are odd out of the blue and improve once the embedded conditional has been
asserted; the premise reading admits positive but not negative polarity items in the embedded
consequent and excludes *only*-inversion. Overt markers make the prediction visible: Japanese
*-ra* and German *falls*, restricted to hypothetical conditionals, cannot head a bare
left-nested conditional, whereas *nara* and *wenn* can (`heads_bare_iff`); `marker_rows` and
`anchoring_rows` check the paper's examples against the fragments' markers.

## Implementation notes

Readings are the substrate's `Conditional.Reading`, and the polarity diagnostic reads its
`Reading.AdmitsInAntecedent`, on which a premise antecedent hosts positive polarity items and
licenses no negative ones. The paper's rows carry their features as strings, so `shape` and
`markerOf` are adapters from `paperFeatures` into the typed model and the fragments' marker
entries.

## References

* [lassiter-2025]
* [gibbard-1981]
* [iatridou-1991]
-/

namespace Lassiter2025

open Conditional Data.Examples

/-- The content of an embedded conditional. -/
inductive Content
  | bare
  | modal
  | quantAdv
  | generic
  deriving DecidableEq, Repr

/-- A conditional's antecedent: simple, or itself a conditional with the given content. -/
inductive Shape
  | simple
  | nested (content : Content)
  deriving DecidableEq, Repr

/-- The readings open to a conditional: a bare embedded conditional leaves only the
premise reading. -/
def readings : Shape → Finset Reading
  | .nested .bare => {.premise}
  | _ => {.hypothetical, .premise}

/-- A conditional is acceptable under a demand on its reading iff some reading open to
it meets the demand. -/
def Acceptable (s : Shape) (ok : Reading → Prop) : Prop := ∃ ct ∈ readings s, ok ct

instance (s : Shape) (ok : Reading → Prop) [DecidablePred ok] :
    Decidable (Acceptable s ok) := by
  unfold Acceptable; infer_instance

/-- A bare left-nested conditional meets a demand iff the premise reading does. -/
theorem acceptable_bare_iff (ok : Reading → Prop) :
    Acceptable (.nested .bare) ok ↔ ok .premise := by
  simp [Acceptable, readings]

/-- What the discourse demands: an antecedent asserted in prior discourse takes the premise
reading, an unanchored one the hypothetical reading. -/
def anchoring (anchored : Prop) (ct : Reading) : Prop :=
  (anchored ∧ ct = .premise) ∨ (¬ anchored ∧ ct = .hypothetical)

instance (anchored : Prop) [Decidable anchored] : DecidablePred (anchoring anchored) :=
  λ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- Gibbard's puzzle: a bare left-nested conditional has no reading out of the blue, none
under *only*-inversion, and none coordinated with a hypothetical antecedent. -/
theorem bare_not_hypothetical : ¬ Acceptable (.nested .bare) (· = .hypothetical) := by
  simp [acceptable_bare_iff]

/-- A bare left-nested conditional is a premise conditional once its embedded conditional has
been asserted. -/
theorem bare_premise : Acceptable (.nested .bare) (· = .premise) :=
  (acceptable_bare_iff _).2 rfl

/-- The exception: a modal, quantificational, or generic embedded conditional admits the
hypothetical reading. -/
theorem hypothetical_of_ne_bare (c : Content) (h : c ≠ .bare) :
    Acceptable (.nested c) (· = .hypothetical) := by
  cases c
  · exact absurd rfl h
  all_goals decide

/-- In the embedded consequent, a bare left-nested conditional admits exactly the positive
polarity items. -/
theorem bare_polarity (e : Polarity.Item) :
    Acceptable (.nested .bare) (·.AdmitsInAntecedent e) ↔ e.isPPI :=
  acceptable_bare_iff _

/-- (29) against (30): *rather pleased* survives in a bare left-nested conditional, *lifted a
finger* and *anybody* do not, though *any* is fine in a simple conditional (32a). -/
theorem rather_not_any :
    Acceptable (.nested .bare) (·.AdmitsInAntecedent English.PolarityItems.rather) ∧
      ¬ Acceptable (.nested .bare) (·.AdmitsInAntecedent English.PolarityItems.any) ∧
      Acceptable .simple (·.AdmitsInAntecedent English.PolarityItems.any) := by
  decide

/-- A marker heads a bare left-nested conditional iff it can mark a premise conditional. -/
theorem heads_bare_iff (m : Marker) :
    Acceptable (.nested .bare) (· ∈ m.readings) ↔ .premise ∈ m.readings :=
  acceptable_bare_iff _

/-! ### The paper's examples -/

/-- The row's shape, read from its `is_lnc` and `content` features. -/
def shape (row : LinguisticExample) : Shape :=
  if row.feature? "is_lnc" = some "true" then
    .nested <|
      match row.feature? "content" with
      | some "modal" => .modal
      | some "quantAdv" => .quantAdv
      | some "generic" => .generic
      | _ => .bare
  else .simple

/-- The fragment entry for the row's main conditional marker. -/
def markerOf (row : LinguisticExample) : Option Marker :=
  match row.feature? "marker" with
  | some "nara"  => some Japanese.Conditionals.nara
  | some "ra"    => some Japanese.Conditionals.ra
  | some "wenn"  => some German.Conditionals.wenn
  | some "falls" => some German.Conditionals.falls
  | _ => none

/-- Every marker row is acceptable iff the fragment's marker can mark a reading open to the
row's shape: *nara* and *wenn* head the bare left-nested conditionals of (18) and (23), *-ra*
and *falls* of (19) and (24) do not. -/
theorem marker_rows :
    ∀ row ∈ Examples.all, ∀ m ∈ markerOf row,
      (row.judgment = .acceptable ↔ Acceptable (shape row) (· ∈ m.readings)) := by
  decide

/-- Every discourse-anchoring row is acceptable iff its shape has the reading the context
demands: Gibbard's (4) fails out of the blue, (11)–(13) succeed after the embedded
conditional has been asserted. -/
theorem anchoring_rows :
    ∀ row ∈ Examples.all, row.feature? "diagnostic" = some "discourse_anchoring" →
      (row.judgment = .acceptable ↔
        Acceptable (shape row) (anchoring (row.feature? "has_context" = some "true"))) := by
  decide

/-- Every content-exception row, (40)–(43), is acceptable on the hypothetical reading. -/
theorem exception_rows :
    ∀ row ∈ Examples.all, row.feature? "diagnostic" = some "content_exception" →
      Acceptable (shape row) (· = .hypothetical) := by
  decide

end Lassiter2025
