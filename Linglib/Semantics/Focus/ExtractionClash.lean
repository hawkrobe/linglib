import Linglib.Features.Givenness
import Linglib.Semantics.Focus.Marking

/-!
# Information-structural extraction clash

`extractionISClash`: a focused filler extracted from a given/backgrounded
domain clashes — the filler addresses the QUD while the domain is
QUD-invisible ([erteschik-shir-1973], [abeille-et-al-2020]). Predicate
over the marking axes `(Mark, BinaryGivenness)`.
-/

namespace Focus.ExtractionClash

open Features (BinaryGivenness)

/-- Two propositions are semantically independent iff neither entails the other.
    [umbach-2004] §2.2: required for alternatives in focus, coordination,
    and discourse relations. Violation explains the oddness of
    *#John had a drink and Mary had a martini*. -/
def semanticallyIndependent {W : Type*} (a b : Set W) : Prop :=
  ¬ a ⊆ b ∧ ¬ b ⊆ a

/-- A common integrator subsumes all alternatives.
    [umbach-2004] §2.2, following [lang-1984]: coordinated elements
    and focus alternatives must share a common superordinate concept.
    For example, in "beer and martini", "drink" is the common integrator. -/
def commonIntegrator {W : Type*} (alts : List (Set W)) (integ : Set W) : Prop :=
  ∀ a ∈ alts, a ⊆ integ

/-- A well-formed alternative set satisfies both constraints.
    [umbach-2004] §2.2: alternatives must be comparable, i.e.,
    similar (common integrator) and dissimilar (pairwise independent). -/
def wellFormedAlts {W : Type*} (alts : List (Set W)) (integ : Set W) : Prop :=
  commonIntegrator alts integ ∧
  ∀ a ∈ alts, ∀ b ∈ alts, a ≠ b → semanticallyIndependent a b


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
