import Linglib.Features.Givenness
import Linglib.Features.InformationStructure

/-!
# Theories.Semantics.Focus.Comparability

@cite{umbach-2004} @cite{erteschik-shir-1973} @cite{abeille-et-al-2020}

Theory predicates over the substance taxonomies in `Features/`:
- @cite{umbach-2004} alternative-set well-formedness (similarity +
  dissimilarity).
- @cite{erteschik-shir-1973} / @cite{abeille-et-al-2020} extraction-IS
  clash constraint, parameterized over the **two** Krifka axes the
  paper conflates: filler focus marking
  (`Features.InformationStructure.FocusMark`) and domain givenness
  (`Features.BinaryGivenness`).

The `extractionISClash` signature is `(filler : FocusMark, domain :
BinaryGivenness) → Prop`, making the two-axis structure of the FBC
explicit. (`ExclusionVariety` and `PolaritySwitchContext` were
collapsed into `Core.Discourse.Coherence.CoherenceRelation` in the
0.230.488 cleanup.)
-/

namespace Semantics.Focus.Comparability

open Features (BinaryGivenness)
open Features.InformationStructure (FocusMark)

/-! ## Alternative-Set Well-Formedness (@cite{umbach-2004} §2.2)

@cite{umbach-2004} identifies two constraints that jointly determine when
elements can serve as alternatives (in focus, coordination, or discourse):

1. **Semantic independence**: neither alternative entails the other
   (dissimilarity). Explains why *#John had a drink and Mary had a martini*
   is odd — "drink" subsumes "martini".

2. **Common integrator**: a concept subsuming all alternatives (similarity).
   Explains why alternatives must be of a comparable type.

Together these define *comparability* = similarity + dissimilarity, which
is the prerequisite for any type of contrast. -/

/-- Two propositions are semantically independent iff neither entails the other.
    @cite{umbach-2004} §2.2: required for alternatives in focus, coordination,
    and discourse relations. Violation explains the oddness of
    *#John had a drink and Mary had a martini*. -/
def semanticallyIndependent {W : Type} (a b : Set W) : Prop :=
  ¬ a ⊆ b ∧ ¬ b ⊆ a

/-- A common integrator subsumes all alternatives.
    @cite{umbach-2004} §2.2, following @cite{lang-1984}: coordinated elements
    and focus alternatives must share a common superordinate concept.
    For example, in "beer and martini", "drink" is the common integrator. -/
def commonIntegrator {W : Type} (alts : List (Set W)) (integ : Set W) : Prop :=
  ∀ a ∈ alts, a ⊆ integ

/-- A well-formed alternative set satisfies both constraints.
    @cite{umbach-2004} §2.2: alternatives must be comparable, i.e.,
    similar (common integrator) and dissimilar (pairwise independent). -/
def wellFormedAlts {W : Type} (alts : List (Set W)) (integ : Set W) : Prop :=
  commonIntegrator alts integ ∧
  ∀ a ∈ alts, ∀ b ∈ alts, a ≠ b → semanticallyIndependent a b

/-! ## Extraction and Information-Structural Clash
@cite{erteschik-shir-1973} @cite{abeille-et-al-2020}

Wh-extraction foregrounds ([FoC]) the moved element. Extracting from a
backgrounded ([G]) domain creates an information-structural clash: the
element is supposed to address the QUD (as [FoC]) but belongs to a
dimension the QUD ignores (as [G]).

This is the constraint underlying both @cite{erteschik-shir-1973}'s
Dominance Condition on Extraction and @cite{abeille-et-al-2020}'s Focus
Background Constraint (FBC): "a focused element should not be part of
a backgrounded constituent." -/

/-- **Information-structural extraction clash** (@cite{erteschik-shir-1973},
    @cite{abeille-et-al-2020}): a focused filler extracted from a
    given/backgrounded domain creates an incompatibility between the
    filler's discourse function (addressing the QUD) and the domain's
    discourse status (QUD-invisible).

    The two parameters are independent Krifka axes — filler focus
    marking (`FocusMark`, the binary focus axis) and domain givenness
    (`BinaryGivenness`, the Prince hearer-status axis).

    Use sites:
    - MoS islands: `extractionISClash .focused domainGivenness` (filler
      always focused; only the domain varies)
    - Subject islands: `extractionISClash (fillerFocus c) (subjectGivenness c)`
      (filler focus and domain givenness both vary by construction)
    - General FBC: same shape, varying both arguments. -/
def extractionISClash (filler : FocusMark) (domain : BinaryGivenness) :
    Prop :=
  filler = .focused ∧ domain = .given

instance (f : FocusMark) (d : BinaryGivenness) :
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

end Semantics.Focus.Comparability
