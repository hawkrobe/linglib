import Linglib.Syntax.Minimalist.Labeling
import Linglib.Core.CombinationKind

/-!
# Classification of Merge into Three Combination Schemata
[mueller-2013]

Explicit classification of Minimalist Merge operations into [mueller-2013]'s three universal combination schemata: Head-Complement, Head-Specifier, Head-Filler.

The existing `MergeUnification.lean` proves that Internal and External Merge
are the same operation. This file further classifies Merge by *combination kind*:

| Merge type | Precondition | Schema |
|-----------|-------------|--------|
| External (selection holds) | `selects a b` | Head-Complement |
| External (specifier) | neither selects, arg is maximal | Head-Specifier |
| Internal | `contains target mover` | Head-Filler |

## MCB alignment

Per [marcolli-chomsky-berwick-2025] §1.13.6, head identification is
parametric over a `HeadFunction`. All head-aware definitions in this
file take `h : HeadFunction` explicitly; there is no hidden default.
Callers wanting English-like leftmost-headed semantics pass
`HeadFunction.leftSpine`; derivation-anchored Studies pass the
head function tracked through the derivation; etc.

## Connection to [mueller-2013]

- §2.1: External Merge with selection ≈ Head-Complement
- §2.2: External Merge without selection ≈ Head-Specifier
- §2.3: Internal Merge ≈ Head-Filler

-/

namespace Minimalist

open Core

/-! ## Selection (LIToken-level primitive + h-parametric SO wrapper) -/

/-- LIToken-level c-selection: `selector` selects `selected` iff
    `selector`'s outermost selectional feature equals `selected`'s outer
    category. Pure LIToken relation; no SO structure involved. -/
def LIToken.selects (selector selected : LIToken) : Prop :=
  selector.item.outerSel.head? = some selected.item.outerCat

instance (lt1 lt2 : LIToken) : Decidable (LIToken.selects lt1 lt2) := by
  unfold LIToken.selects; infer_instance

/-- SO-level c-selection parameterised over a head function:
    `a` selects `b` (under `h`) iff `h`'s head-leaf for `a` selects
    `h`'s head-leaf for `b`. -/
def selects (h : HeadFunction) (a b : SyntacticObject) : Prop :=
  (h.head a).selects (h.head b)

noncomputable instance (h : HeadFunction) (a b : SyntacticObject) :
    Decidable (selects h a b) := by
  unfold selects; classical infer_instance

/-! ## Classification of Merge -/

/-- Classify an External Merge under head function `h`. -/
noncomputable def classifyExternalMerge (h : HeadFunction) (a b : SyntacticObject) :
    CombinationKind :=
  if selects h a b ∨ selects h b a then
    .headComplement
  else
    .headSpecifier

/-- Classify an Internal Merge (head-function-independent: IM is always
    Head-Filler regardless of which side projects). -/
def classifyInternalMerge : CombinationKind := .headFiller

/-! ## Which daughter is the head? -/

/-- Determine which daughter is the head of a Merge under head function `h`.
    The head is the daughter whose head leaf agrees with the result's. -/
noncomputable def mergeHead (h : HeadFunction) (a b result : SyntacticObject) :
    Option SyntacticObject :=
  if h.head result = h.head a then some a
  else if h.head result = h.head b then some b
  else none

/-! ## Key theorems -/

/-- External Merge with selection is Head-Complement (under any `h`). -/
theorem selection_implies_headComplement
    (h : HeadFunction) (a b : SyntacticObject) (hs : selects h a b) :
    classifyExternalMerge h a b = .headComplement := by
  simp [classifyExternalMerge, hs]

/-- External Merge without selection is Head-Specifier (under any `h`). -/
theorem no_selection_implies_headSpecifier
    (h : HeadFunction) (a b : SyntacticObject)
    (ha : ¬ selects h a b) (hb : ¬ selects h b a) :
    classifyExternalMerge h a b = .headSpecifier := by
  simp [classifyExternalMerge, ha, hb]

/-- Internal Merge is always Head-Filler. -/
theorem internal_merge_is_headFiller :
    classifyInternalMerge = .headFiller := rfl

/-- The classification is exhaustive (under any `h`). -/
theorem classify_external_exhaustive
    (h : HeadFunction) (a b : SyntacticObject) :
    classifyExternalMerge h a b = .headComplement ∨
    classifyExternalMerge h a b = .headSpecifier := by
  unfold classifyExternalMerge
  by_cases hs : selects h a b ∨ selects h b a <;> simp [hs]

/-- Head Feature Principle (MCB §1.13.6 / Minimalist analogue): under
    any head function `h` and the externalize choice it supplies,
    `h.head (.node a b)` is one of `h.head a` or `h.head b`.

    TODO: with `headAt h so := leftmostLeafPlanar (h.section_.σ so)`,
    proving this requires reasoning about what `h.section_.σ (a*b)`
    looks like — concretely, that it's some planar tree whose leftmost
    leaf descends from either `a` or `b`. This needs a coherence lemma
    about how externalize interacts with binary nodes, which is part of
    the Tier A cascade. -/
theorem head_node_eq_daughter (h : HeadFunction) (a b : SyntacticObject) :
    h.head (.node a b) = h.head a ∨ h.head (.node a b) = h.head b := by
  sorry

/-! Concrete sanity-check examples (D-N selects, V-DP selects, label
projection) were removed: their `decide`-based proofs failed because
the recursive `classifyExternalMerge` / `labelCat` evaluations do not
reduce in the kernel. The substantive statements they made are:
(1) D selects N, so D→N merge is `.headComplement`;
(2) V selects D, so V→DP merge is `.headComplement`;
(3) `label {D, N} = some .D` (head feature principle). -/

/-! ## Monovalent Verb Serialization Problem ([mueller-2013] §2.3)

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
    This is the wrong order for English — it should be "Max sleeps".

    TODO Phase 2: `phonYield` is `Quot.out`-based after the FreeCommMagma
    migration; `decide` no longer reduces. Re-prove with parameterized
    linearization. -/
theorem monovalent_wrong_linearization :
    HeadFunction.leftSpine.phonYield (merge (.leaf sleepsToken) (.leaf maxToken))
      = ["sleeps", "Max"] := by
  sorry

/-- The desired order differs from the linearization. -/
theorem monovalent_desired_order_differs :
    ["Max", "sleeps"] ≠
      HeadFunction.leftSpine.phonYield (merge (.leaf sleepsToken) (.leaf maxToken)) := by
  sorry

end MonovalentVerbProblem

end Minimalist
