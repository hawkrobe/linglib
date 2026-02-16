import Linglib.Theories.Syntax.Minimalism.Core.Labeling
import Linglib.Core.Interfaces.CombinationSchema

/-!
# Classification of Merge into Three Combination Schemata

Explicit classification of Minimalist Merge operations into Müller's (2013)
three universal combination schemata: Head-Complement, Head-Specifier, Head-Filler.

The existing `MergeUnification.lean` proves that Internal and External Merge
are the same operation. This file further classifies Merge by *combination kind*:

| Merge type | Precondition | Schema |
|-----------|-------------|--------|
| External (selection holds) | `selectsB a b` | Head-Complement |
| External (specifier) | neither selects, arg is maximal | Head-Specifier |
| Internal | `contains target mover` | Head-Filler |

## Connection to Müller (2013)

- §2.1: External Merge with selection ≈ Head-Complement
- §2.2: External Merge without selection ≈ Head-Specifier
- §2.3: Internal Merge ≈ Head-Filler

## References

- Chomsky, N. (1995, 2004, 2013). The Minimalist Program.
- Müller, S. (2013). Unifying Everything. Language 89(4):920–950.
-/

namespace Minimalism

open Core.Interfaces

/-! ## Classification of Merge -/

/-- Classify an External Merge (known to have no containment). -/
def classifyExternalMerge (a b : SyntacticObject) : CombinationKind :=
  if selectsB a b || selectsB b a then
    .headComplement
  else
    .headSpecifier

/-- Classify an Internal Merge (known to have containment). -/
def classifyInternalMerge : CombinationKind := .headFiller

/-! ## Which daughter is the head? -/

/-- Determine which daughter is the head of a Merge.

The head is the daughter whose label matches the result's label.
In Minimalism, this is determined by which element projects. -/
def mergeHead (a b result : SyntacticObject) : Option SyntacticObject :=
  if labelCat result == labelCat a then some a
  else if labelCat result == labelCat b then some b
  else none

/-! ## Key theorems -/

/-- External Merge with selection is Head-Complement.

When one SO selects the other (first merge consuming a selectional feature),
this is the Head-Complement schema: the selector is the head, the selectee
is the complement. -/
theorem selection_implies_headComplement (a b : SyntacticObject)
    (h : selectsB a b = true) :
    classifyExternalMerge a b = .headComplement := by
  simp [classifyExternalMerge, h]

/-- External Merge without selection is Head-Specifier.

When neither SO selects the other (e.g., subject merging with TP),
this is the Head-Specifier schema. -/
theorem no_selection_implies_headSpecifier (a b : SyntacticObject)
    (ha : selectsB a b = false) (hb : selectsB b a = false) :
    classifyExternalMerge a b = .headSpecifier := by
  simp [classifyExternalMerge, ha, hb]

/-- Internal Merge is always Head-Filler.

Movement (re-merge of a contained element) is always the Head-Filler schema,
regardless of what the mover or target looks like. -/
theorem internal_merge_is_headFiller :
    classifyInternalMerge = .headFiller := rfl

/-- The classification is exhaustive: every External Merge is either
Head-Complement or Head-Specifier. -/
theorem classify_external_exhaustive (a b : SyntacticObject) :
    classifyExternalMerge a b = .headComplement ∨
    classifyExternalMerge a b = .headSpecifier := by
  unfold classifyExternalMerge
  cases h : (selectsB a b || selectsB b a) <;> simp

/-- Label = Head Feature Principle: when α selects β, the label of {α, β} = label α.

This is the Minimalist analogue of the Head Feature Principle:
the selector projects, so the result's label equals the selector's label. -/
theorem label_from_head (a b : SyntacticObject) (h : selects a b) :
    label (merge a b) = label a := by
  simp only [merge, label, selects] at *
  simp [h]

/-- Concrete example: D selects N, so D→N merge is Head-Complement. -/
example : classifyExternalMerge (.leaf detThe) (.leaf nounPizza) = .headComplement := by
  native_decide

/-- Concrete example: V selects D, so V→DP merge is Head-Complement. -/
example : classifyExternalMerge (.leaf verbEat) theDP = .headComplement := by
  native_decide

/-- Concrete example: label of {D, N} = D (head feature principle). -/
example : labelCat (.node (.leaf detThe) (.leaf nounPizza)) = some .D := by
  native_decide

end Minimalism
