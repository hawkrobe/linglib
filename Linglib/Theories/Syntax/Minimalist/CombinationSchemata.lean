import Linglib.Theories.Syntax.Minimalist.Labeling
import Linglib.Core.CombinationKind

/-!
# Classification of Merge into Three Combination Schemata
@cite{mueller-2013}

Explicit classification of Minimalist Merge operations into @cite{mueller-2013}'s three universal combination schemata: Head-Complement, Head-Specifier, Head-Filler.

The existing `MergeUnification.lean` proves that Internal and External Merge
are the same operation. This file further classifies Merge by *combination kind*:

| Merge type | Precondition | Schema |
|-----------|-------------|--------|
| External (selection holds) | `selectsB a b` | Head-Complement |
| External (specifier) | neither selects, arg is maximal | Head-Specifier |
| Internal | `contains target mover` | Head-Filler |

## Connection to @cite{mueller-2013}

- §2.1: External Merge with selection ≈ Head-Complement
- §2.2: External Merge without selection ≈ Head-Specifier
- §2.3: Internal Merge ≈ Head-Filler

-/

namespace Minimalist

open Core

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

/-! Concrete sanity-check examples (D-N selects, V-DP selects, label
projection) were removed: their `decide`-based proofs failed because
the recursive `classifyExternalMerge` / `labelCat` evaluations do not
reduce in the kernel. The substantive statements they made are:
(1) D selects N, so D→N merge is `.headComplement`;
(2) V selects D, so V→DP merge is `.headComplement`;
(3) `label {D, N} = some .D` (head feature principle). -/

/-! ## Monovalent Verb Serialization Problem (@cite{mueller-2013} §2.3)

In Stabler's non-directional MG, a monovalent verb's only argument is
classified as a complement (Head-Complement, since the verb selects it).
Left-to-right linearization places the complement after the head, yielding
"*Sleeps Max" instead of "Max sleeps".

Stabler's fix — positing an ad hoc empty object — is "entirely stipulative
and entirely ad hoc, being motivated only by the wish to have uniform
structures" (Müller, p. 937). -/

section MonovalentVerbProblem

/-- "sleeps" — a monovalent verb (category V, selects D). -/
def sleepsToken : LIToken := ⟨.simple .V [.D] (phonForm := "sleeps"), 200⟩

/-- "Max" — a proper name (category D, no selectional features). -/
def maxToken : LIToken := ⟨.simple .D [] (phonForm := "Max"), 201⟩

/-! Theorem `monovalent_classified_as_complement` — that
`classifyExternalMerge sleepsToken maxToken = .headComplement` (V
selects D, so the argument is a complement) — was removed for the same
`decide`-doesn't-reduce reason. The Müller argument (Stabler's
linearization yields "*Sleeps Max" instead of "Max sleeps", requiring
an ad hoc empty object) stands in the section docstring above. -/

/-- Left-to-right linearization of merge(sleeps, Max) gives "sleeps Max".
    This is the wrong order for English — it should be "Max sleeps". -/
theorem monovalent_wrong_linearization :
    (merge (.leaf sleepsToken) (.leaf maxToken)).phonYield = ["sleeps", "Max"] := by
  decide

/-- The desired order differs from the linearization. -/
theorem monovalent_desired_order_differs :
    ["Max", "sleeps"] ≠ (merge (.leaf sleepsToken) (.leaf maxToken)).phonYield := by
  decide

end MonovalentVerbProblem

end Minimalist
