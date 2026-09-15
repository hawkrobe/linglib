import Linglib.Semantics.Reference.Givenness
import Linglib.Semantics.Focus.Marking

/-!
# Information-structural extraction clash

`extractionISClash`: a focused filler extracted from a given/backgrounded
domain clashes — the filler addresses the QUD while the domain is
QUD-invisible ([erteschik-shir-1973], [abeille-et-al-2020]). Predicate
over the marking axes `(Mark, BinaryGivenness)`.
-/

namespace Focus.ExtractionClash

open Reference (BinaryGivenness)

/-- **Information-structural extraction clash** ([erteschik-shir-1973],
    [abeille-et-al-2020]): a focused filler extracted from a
    given/backgrounded domain creates an incompatibility between the
    filler's discourse function (addressing the QUD) and the domain's
    discourse status (QUD-invisible).

    The two parameters are independent Krifka axes — filler focus
    marking (`Mark`, the binary focus axis) and domain givenness
    (`BinaryGivenness`, the Prince hearer-status axis).

    Use sites:
    - MoS islands: `extractionISClash .focused domainGivenness` (filler
      always focused; only the domain varies)
    - Subject islands: `extractionISClash (fillerFocus c) (subjectGivenness c)`
      (filler focus and domain givenness both vary by construction)
    - General FBC: same shape, varying both arguments. -/
def extractionISClash (filler : Mark) (domain : BinaryGivenness) :
    Prop :=
  filler = .focused ∧ domain = .given

instance (f : Mark) (d : BinaryGivenness) :
    Decidable (extractionISClash f d) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Extraction of a focused filler from a given/backgrounded domain clashes. -/
theorem extractionISClash_focused_given :
    extractionISClash .focused .given := ⟨rfl, rfl⟩

/-- Extraction from a non-given (new) domain does not clash, even when
    the filler is focused. -/
theorem extractionISClash_focused_new :
    ¬ extractionISClash .focused .new := by decide

/-- Non-focused extraction (e.g., relative clause heads, topics) does
    not clash, even when the domain is given. -/
theorem extractionISClash_nonFocused_given :
    ¬ extractionISClash .nonFocused .given := by decide

end Focus.ExtractionClash
