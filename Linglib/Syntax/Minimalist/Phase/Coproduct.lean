import Linglib.Syntax.Minimalist.Merge.External
import Linglib.Syntax.Minimalist.Phase.Basic
import Linglib.Syntax.Minimalist.Phase

/-!
# Algebraic Phase Coproduct Δ^c_Φ
[marcolli-chomsky-berwick-2025] §1.14, Definition 1.14.5

Implements the **phase-restricted coproduct** Δ^c_Φ of MCB §1.14, eq (1.14.6):

    Δ^c_Φ(T) = Σ_{v ∈ Φ_{h_T} ∖ Y_{h_T}}  F_v ⊗ T/^c F_v

restricting the cut sum to vertices `v` that are **phase-accessible** — not in
the inaccessibility set `Y_ℓ` of any lower phase. This is the algebraic
implementation of the Phase Impenetrability Condition: cuts that would extract
material from a closed lower phase are dropped from the coproduct.

Per MCB Lemma 1.14.6 (book p. 138), Δ^c_Φ is well-defined and coassociative.

## Phase-accessibility check: forward, not inverse

The phase substrate (`Merge/Phase.lean`) names the inaccessibility set `Y_ℓ` as a
`Multiset SyntacticObject`; the carrier is `ConnesKreimer ℤ (Nonplanar (LIToken ⊕
Unit))`. To ask whether an admissible cut extracts an inaccessible subtree we
compare on the **carrier** side: map `Y_ℓ` forward through the total embedding
`SyntacticObject.toNonplanar` and test crown membership there. This avoids any partial
`Nonplanar → SyntacticObject` recovery (which is ill-defined past binary trees,
since `SyntacticObject = FreeCommMagma _` is commutative but non-associative);
`toNonplanar` is total and clean.

## Implementation

`comulPhaseC` routes through the substrate primitive `comulTreeNFiltered`
(`Core/Algebra/RootedTree/Coproduct/PruningNonplanar.lean`), the filtered Δ^ρ
that also yields `comulTreeN` in the `pred = always-true` limit. The phase case
filters `cutSummandsN T.toNonplanar` by `cutPhaseCompatible`.

## Coassociativity (MCB Lemma 1.14.6) — deferred

The headline `(Δ^c_Φ ⊗ id) ∘ Δ^c_Φ = (id ⊗ Δ^c_Φ) ∘ Δ^c_Φ` is **not stated**
here: it needs a `LinearMap`-shaped Δ^c_Φ to express the iterated composition,
and the per-tree phase context `(h, T, ℓ)` does not propagate canonically to
extracted sub-trees. MCB prove it (book p. 138) by bijection with `comul`
(coassociative, Lemma 1.2.10) on the phase-head cut tree; discharging that
bijection in Lean is the substantive remaining work.

## PICStrength dispatch

`comulPICStrength` selects the variant per `Phase.lean`'s `PICStrength`:
`.weak` → the default `Y_ℓ` (eq 1.14.5, heads in the edge — `comulPhaseC`);
`.strong` → lower-phase heads also frozen per [marcolli-chomsky-berwick-2025]
Remark 1.14.4 (`comulPhaseC_strong`); `.linearizationBound` → unrestricted Δ^c
(`comulC_unrestricted`), with the linearization gate enforced separately at
externalization.
-/

namespace Minimalist.Phase

open RootedTree RootedTree.ConnesKreimer
open scoped TensorProduct
open Minimalist (HeadFunction ComplementedHeadFunction SyntacticObject LIToken PICStrength)

/-! ### Phase-compatibility predicate on cut summands -/

/-- A Δ^ρ cut summand `p` of `T.toNonplanar` is **phase-compatible** with phase `Φ_ℓ`
    on `T` iff none of its crown components `p.1` is the `toNonplanar`-image of an
    inaccessible term (a vertex in `Y_ℓ`).

    This is the predicate that filters `cutSummandsN T.toNonplanar` to obtain Δ^c_Φ
    ([marcolli-chomsky-berwick-2025] Definition 1.14.5 eq 1.14.6). -/
noncomputable def cutPhaseCompatible (h : HeadFunction) (T : SyntacticObject)
    (ℓ : LIToken) (p : Forest (Nonplanar (LIToken ⊕ Unit)) × Nonplanar (LIToken ⊕ Unit)) :
    Prop :=
  ∀ sub ∈ p.1, sub ∉ (inaccessibleTerms h T ℓ).map SyntacticObject.toNonplanar

/-- `inaccessibleTerms` is noncomputable, so phase-compatibility is decided
    classically (the phase coproduct is noncomputable regardless). -/
noncomputable instance (h : HeadFunction) (T : SyntacticObject) (ℓ : LIToken) :
    DecidablePred (cutPhaseCompatible h T ℓ) := Classical.decPred _

/-! ### Tree-level Δ^c_Φ (MCB Def 1.14.5 eq 1.14.6) -/

/-- The **tree-level phase coproduct** Δ^c_Φ
    ([marcolli-chomsky-berwick-2025] Definition 1.14.5 eq 1.14.6), as the
    `comulTreeNFiltered` of `T.toNonplanar` filtered by `cutPhaseCompatible`. Sums the
    `T ⊗ 1` primitive plus the phase-compatible cut summands; cuts extracting an
    inaccessible (`Y_ℓ`) subtree are dropped. -/
noncomputable def comulPhaseC (h : HeadFunction) (T : SyntacticObject) (ℓ : LIToken) :
    ConnesKreimer ℤ (Nonplanar (LIToken ⊕ Unit)) ⊗[ℤ]
      ConnesKreimer ℤ (Nonplanar (LIToken ⊕ Unit)) :=
  comulTreeNFiltered T.toNonplanar (cutPhaseCompatible h T ℓ)

/-- **Unrestricted-limit recovery**: when every cut is phase-compatible, Δ^c_Φ
    recovers the full Δ^ρ `comulTreeN`. Δ^c_Φ is a *restriction* of the
    coproduct, not a parallel definition. -/
theorem comulPhaseC_eq_comulTreeN_of_no_filter
    (h : HeadFunction) (T : SyntacticObject) (ℓ : LIToken)
    (hAll : ∀ p ∈ cutSummandsN T.toNonplanar, cutPhaseCompatible h T ℓ p) :
    comulPhaseC h T ℓ = comulTreeN T.toNonplanar :=
  comulTreeNFiltered_eq_comulTreeN T.toNonplanar (cutPhaseCompatible h T ℓ) hAll

/-- Unrestricted Δ^ρ on `T`'s embedding, in the same shape as `comulPhaseC`.
    The `.linearizationBound` PIC mode and the comparison baseline. -/
noncomputable def comulC_unrestricted (T : SyntacticObject) :
    ConnesKreimer ℤ (Nonplanar (LIToken ⊕ Unit)) ⊗[ℤ]
      ConnesKreimer ℤ (Nonplanar (LIToken ⊕ Unit)) :=
  comulTreeN T.toNonplanar

/-! ### PICStrength dispatch (strong PIC, Remark 1.14.4)

The default `comulPhaseC` already uses the MCB default `Y_ℓ` (eq 1.14.5) where the
*interior is the complement* (`Phase/Basic.lean`), so lower-phase **heads are in the
edge and stay accessible** — this is the WEAK PIC. The STRONG variant additionally
freezes those heads ([marcolli-chomsky-berwick-2025] Remark 1.14.4) via the
substrate's `inaccessibleTerms_strong`. -/

/-- STRONG-PIC analogue of `cutPhaseCompatible` ([marcolli-chomsky-berwick-2025]
    Remark 1.14.4): the *more restrictive* condition that also freezes the head
    leaves of the lower phases (`inaccessibleTerms_strong`), banning head movement
    out of a closed phase. -/
noncomputable def cutPhaseCompatible_strong (h : HeadFunction) (T : SyntacticObject)
    (ℓ : LIToken) (p : Forest (Nonplanar (LIToken ⊕ Unit)) × Nonplanar (LIToken ⊕ Unit)) :
    Prop :=
  ∀ sub ∈ p.1, sub ∉ (inaccessibleTerms_strong h T ℓ).map SyntacticObject.toNonplanar

noncomputable instance (h : HeadFunction) (T : SyntacticObject) (ℓ : LIToken) :
    DecidablePred (cutPhaseCompatible_strong h T ℓ) := Classical.decPred _

/-- The **STRONG** tree-level phase coproduct Δ^c_Φ: a further restriction of
    `comulPhaseC` that also drops cuts extracting a lower-phase head (Remark 1.14.4). -/
noncomputable def comulPhaseC_strong (h : HeadFunction) (T : SyntacticObject) (ℓ : LIToken) :
    ConnesKreimer ℤ (Nonplanar (LIToken ⊕ Unit)) ⊗[ℤ]
      ConnesKreimer ℤ (Nonplanar (LIToken ⊕ Unit)) :=
  comulTreeNFiltered T.toNonplanar (cutPhaseCompatible_strong h T ℓ)

/-- The phase-coproduct under `PICStrength` dispatch ([marcolli-chomsky-berwick-2025]
    Remark 1.14.4).

    - `.strong`: lower-phase heads also frozen (`comulPhaseC_strong`,
      `inaccessibleTerms_strong`).
    - `.weak`: the default `Y_ℓ` (eq 1.14.5) — heads in the edge, accessible
      (`comulPhaseC`).
    - `.linearizationBound`: unrestricted Δ^c (`comulC_unrestricted`); the
      linearization gate is enforced separately at externalization. -/
noncomputable def comulPICStrength (mode : PICStrength)
    (h : HeadFunction) (T : SyntacticObject) (ℓ : LIToken) :
    ConnesKreimer ℤ (Nonplanar (LIToken ⊕ Unit)) ⊗[ℤ]
      ConnesKreimer ℤ (Nonplanar (LIToken ⊕ Unit)) :=
  match mode with
  | .strong              => comulPhaseC_strong h T ℓ
  | .weak                => comulPhaseC h T ℓ
  | .linearizationBound  => comulC_unrestricted T

end Minimalist.Phase
