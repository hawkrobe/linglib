import Linglib.Semantics.Supervaluation
import Linglib.Core.Data.Trivalent
import Linglib.Logic.Consequence
import Linglib.Logic.Trivalent.Propositional
import Linglib.Logic.Modal.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Cobreros, Egré, Ripley & van Rooij 2012: 4-Element Sorites Model

[cobreros-etal-2012]

The paper's TCS apparatus together with its worked 4-element example
(described in the body text on p. 354, immediately above footnote 4).

## The model

Four individuals `a, b, c, d` arranged in a similarity chain
`a ~ b ~ c ~ d` (with reflexivity and symmetry, no other pairs).
The classical extension of `tall` is `{a, b}`. The paper uses this
model to illustrate:

- The **extension hierarchy**: `{a} ⊆ {a,b} ⊆ {a,b,c}` (strict ⊆ classical ⊆ tolerant)
- **Borderline cases**: `b` and `c` are tolerantly tall AND tolerantly not-tall
- **Two-step tolerance limit**: `d` is NOT tolerantly tall (three steps from `a` exceeds Fact 3)
- **Sorites resolution**: each one-step inference `Pa, aIb ⊨ˢᵗ Pb` is
  valid; each two-step `Pa, aIb, bIc ⊨ˢᵗ Pc` is valid; but the
  three-step `Pa, aIb, bIc, cId ⊨ˢᵗ Pd` is **invalid**.

  Attribution: paper §3.4.1 (p. 372) demonstrates non-transitivity for
  `⊨ᶜᵗ` (the chain `Pa_1, a_1I_Pa_2, a_2I_Pa_3 ⊭ᶜᵗ Pa_3`); the `⊨ˢᵗ`
  version of the sorites is stated in §3.6 (Version 1, p. 376). The
  structural pattern — each step valid, chain fails — is §3.4.1's
  contribution; the `st`-instantiation here applies that pattern to
  the relation the paper ultimately advocates (paper p. 373).

## Cross-framework note

`tcs_supervaluation_disagree_concrete` instantiates the existence
theorem `tcs_vs_supervaluation_borderline_contradiction` at
`(soritesModel, .tall, .b)`. Comparator caveat: the paper's headline
borderline-contradiction contrast (p. 356) is actually with **Hyde 1997
subvaluationism**, not with Fine 1975 supervaluation. Subvaluationism
*agrees* with TCS that `P ∧ ¬P` holds at borderline cases — they
disagree on framework foundations. The Lean theorem here formalises the
*formal-validity-side* contrast (p. 359) where TCS at `t` mode says ✓
and supervaluation says ✗. Subvaluationism is not formalised in linglib;
a proper "borderline-verdict comparator" theorem awaits its formalisation.

The asymmetric-engagement reciprocation: `LassiterGoodman2017PMF.lean::lg_literal_borderline_bounded`
proves L&G's literal-meaning rule predicts ≤ 25% acceptance for
borderline `tall ∧ ¬ tall`, well below the [alxatib-pelletier-2011]
empirical 44.7%. That paper's docstring cites TCS as the alternative
that handles the data; this file's `b_tolerant_contradiction` shows the
TCS prediction direction matches the data.

## Architecture

This file is anchored on the Cobreros-Egré-Ripley-van Rooij 2012 paper
itself and contains both the paper's TCS apparatus (the sections
immediately below) and its worked example. General supervaluation
substrate remains in `Semantics/Supervaluation.lean`.
-/

/-!
## The TCS apparatus

[cobreros-etal-2012]

[cobreros-etal-2012] "Tolerant, Classical, Strict",
*Journal of Philosophical Logic* 41:347–385.

A similarity-based three-valued semantics for vague predicates that
derives three notions of truth from a single model:

- **Classical (c)**: standard satisfaction `M ⊨ᶜ P(a) iff a ∈ I(P)` (Def 9)
- **Tolerant (t)**: `M ⊨ᵗ P(a) iff ∃d ~_P a, d ∈ I(P)` (Def 9)
- **Strict (s)**: `M ⊨ˢ P(a) iff ∀d ~_P a, d ∈ I(P)` (Def 9)

The indifference relation `~_P` is reflexive and symmetric — but, crucially,
not necessarily transitive — capturing "looks the same for predicate P."

## Paper-anchored mathematical foundation

The paper formulates TCS in terms of indifference relations derived from
**semi-orders** (paper p. 350 fn 1, citing Luce 1956). The same atom-level
operators are equivalently described as the **lower / upper approximation
operators** of a tolerance approximation space in the rough-set tradition.
The paper flags this analogy in **footnote 5 (p. 355)**, citing
[pawlak-1982] (paper's reference [19]) for the equivalence-relation
case; borderline cases are exactly the boundary `upper \ lower`.

## Re-reading TCS through a modal-logic lens (formaliser's framing)

The paper itself does NOT use modal-logic vocabulary. The framing in this
section is the formaliser's lens, used to integrate with the existing
`Semantics/Intensional/RestrictedModality.lean` substrate; it is not
paper-anchored.

Structurally, TCS is a propositional modal logic in which each predicate
`P` carries its own reflexive-symmetric (KTB) Kripke accessibility
relation `~_P`. The strict and tolerant satisfaction operators are
exactly the modal `□` and `◇` over `~_P`, applied to the classical
extension of `P`:

- `strict P at a` ≡ `box (~_P) I(P) a` (Definition 9)
- `tolerant P at a` ≡ `diamond (~_P) I(P) a` (Definition 9)

The s ⊆ c ⊆ t hierarchy is the **T axiom** instantiated at `box`
(`ModalLogic.box_T`); the t/s duality is the standard
modal de Morgan `box R ¬p ↔ ¬diamond R p`. T-models satisfy
`frameConditions ModalLogic.KTB` by construction (Definition 4 of
[cobreros-etal-2012]); see `TModel.satisfies_KTB` for the explicit
witness. The Brouwersche axiom B / symmetric-frame correspondence is
a standard Sahlqvist result; for systematic treatment see
[blackburn-derijke-venema-2001] §3.5–3.6 and the model-theoretic
overview [goranko-otto-2007]. The non-equivalence-relation
generalisation of Pawlak's rough sets to tolerance approximation spaces
(which the paper implicitly uses in footnote 5) is due to
[skowron-stepaniuk-1996]; this attribution is supplied by the
formaliser, not the paper.

## Key Results (paper-section-tagged)

- **Definition 9** (p. 353): t/s atomic clauses + their compositional lift
- **Lemma 1** (p. 357): extension hierarchy s ⊆ c ⊆ t
- **Facts 2-3** (p. 354): one-step + two-step tolerance principle
- **Definition 10** (p. 355): borderline = `upper \ lower`
- **Lemma 2** (p. 357): identity-model collapse of all three modes
- **Definition 17** (p. 366): nine mixed consequence relations ⊨ᵐⁿ
- **Lemma 7** (p. 368): strength ordering ⊨ᵗᵐ ⊆ ⊨ᶜᵐ ⊆ ⊨ˢᵐ
- **Lemma 8** (p. 369): collapse cc = sc = ct = st on restricted vocabulary
- **Remark 1** (p. 353), **Lemma 10** (p. 371): t/s duality + self-duality
  of st and cc → deduction theorem
- **Lemma 4** (p. 361) + **Theorem 3** (p. 362): formula-level then
  consequence-level correspondence with LP and K3. Note: paper Lemma 4 is
  stated only for the restricted vocabulary (no `I_P`); the formalisation
  in §15 extends it to handle similarity atoms by treating them as
  classical Bool-valued (always in `{0, 1} ⊂ {0, 1/2, 1}`), which is a
  faithful extension of the paper's construction.

## Cross-framework comparators (paper p. 356, p. 359)

The paper draws TWO distinct contrasts on the borderline-contradictions
question, with two different opponents:

- **Borderline-verdict contrast (p. 356)** — TCS vs **subvaluationism**
  (Hyde 1997). Both make `P ∧ ¬P` true at borderline cases; the contrast
  is over the underlying framework foundations (TCS via similarity-based
  modal semantics; subvaluationism via dual super-truth). Subvaluationism
  is not formalised in linglib; this is the closer comparator on the
  *verdict* but cannot be checked at the Lean level here.
- **Formal-validity contrast (p. 359)** — TCS vs **supervaluationism**
  (Fine 1975). Supervaluationism makes `P ∧ ¬P` super-FALSE even at
  borderline cases (penumbral connection); this is the comparator
  formalised here, and it is realised as the §17 cross-framework theorem
  `tcs_vs_supervaluation_borderline_contradiction`. The Lean theorem
  combines the TCS half (`IsBorderline` definition unfolding through
  `SatMode.dual`) with the supervaluation half (`nonContradiction_superFalse`
  from `Supervaluation/Basic.lean`).

Strict truth for an atomic predicate at individual `a` IS supervaluation
over the tolerance neighborhood of `a`: `superTrue I(P) {d | d ~_P a}`.
Tolerant truth is its existential dual. This makes TCS a **localized**
supervaluation — each individual gets its own specification space
determined by its similarity neighborhood.

## Architecture

This file provides the **propositional restricted-vocabulary** fragment
of TCS — atoms cover both predicate atoms `P(a)` and similarity atoms
`a I_P b` (paper Definition 8), but no quantifiers. All §2 (restricted
vocabulary) results apply; phenomena requiring first-order quantifiers
(paper §2.3) are out of scope.

The 4-element worked example from p. 354 of the paper (in the body text
immediately above footnote 4) lives in the study sections below. The
asymmetric reciprocation point with
`LassiterGoodman2017PMF.lean::lg_literal_borderline_bounded`
is addressed in §8–§9 below.
-/

namespace Semantics.Supervaluation.TCS

open ModalLogic
  (IsKTBFrame IsSerial box diamond box_T)
open ModalLogic (KTB frameConditions)
open Consequence (MixedConsequence SatImplies IsSelfDual
  premise_monotone conclusion_monotone mixed_monotone)
open Semantics.Supervaluation (SpecSpace superTrue
  superTrue_true_iff superTrue_false_iff superTrue_indet_iff
  nonContradiction_superFalse)

-- ════════════════════════════════════════════════════
-- § 1. T-Models (Definition 4, p. 351)
-- ════════════════════════════════════════════════════

/-- A T-model: a classical model equipped with per-predicate tolerance
    relations. Each `~_P` is reflexive and symmetric — but possibly
    non-transitive — capturing "looks the same for predicate P."

    Definition 4 of [cobreros-etal-2012]. The non-transitivity of
    `~_P` is what makes vagueness possible: a can look like b and b can
    look like c, but a need not look like c.

    Following the modal-logic tradition, the similarity relation is
    `Prop`-valued so that it integrates directly with `box`/`diamond`.
    Decidability is added per-model where computation is needed. -/
structure TModel (D Pred : Type*) where
  /-- Classical interpretation `I : Pred → D → Prop`. -/
  interp : Pred → D → Prop
  /-- Decidability of the interpretation (per predicate, per individual).
      Bundled so each `TModel` instance carries its own decision procedure. -/
  decInterp : ∀ P d, Decidable (interp P d)
  /-- Tolerance (indifference) relation `~_P` per predicate. -/
  sim : Pred → D → D → Prop
  /-- Each `~_P` is reflexive + symmetric (KTB frame). -/
  sim_ktb : ∀ P, IsKTBFrame (sim P)

/-- Per-`TModel` decidability instance for the classical interpretation,
    extracted from the bundled `decInterp` field. -/
instance TModel.instDecidablePredInterp {D Pred : Type*}
    (M : TModel D Pred) (P : Pred) : DecidablePred (M.interp P) :=
  M.decInterp P

namespace TModel

variable {D Pred : Type*}

/-- The similarity relation as a Kripke accessibility relation — the frame
    associated with each predicate. By construction this frame is
    reflexive + symmetric, i.e., a **KTB frame** (`ModalLogic.KTB`). -/
@[reducible] def simAccess (M : TModel D Pred) (P : Pred) : D → D → Prop := M.sim P

/-- Per-`(M, P)` KTB-frame instance: lets typeclass search reach
    `Std.Refl` and `Std.Symm` on `M.sim P` from any call site. -/
instance (M : TModel D Pred) (P : Pred) : IsKTBFrame (M.sim P) := M.sim_ktb P

/-- **T-models are KTB frames by construction**: every per-predicate
    similarity relation `~_P` satisfies the frame conditions for the
    normal modal logic `KTB = K + T + B` (reflexive + symmetric Kripke
    frame), via the `IsKTBFrame` instance and the syntactic-semantic
    bridge `frameConditions_KTB_iff`. -/
theorem satisfies_KTB (M : TModel D Pred) (P : Pred) :
    frameConditions KTB (M.simAccess P) :=
  (ModalLogic.frameConditions_KTB_iff _).mpr inferInstance

end TModel

-- ════════════════════════════════════════════════════
-- § 2. Atoms and Formulas
-- ════════════════════════════════════════════════════

/-- Atoms of the propositional restricted vocabulary of TCS. Two
    constructors per Definitions 8-9 of [cobreros-etal-2012]:

    - `pred P a` ≡ `P(a)` — predicate application; t/c/s satisfaction
      clauses depend on the mode (Definition 9).
    - `sim P a b` ≡ `a I_P b` — similarity predicate; **classically
      interpreted in all modes** (Definition 8, p. 353 + Remark 2,
      p. 354 reiterating the assumption for s/t modes). -/
inductive TCSAtom (Pred D : Type*) where
  | pred : Pred → D → TCSAtom Pred D
  | sim : Pred → D → D → TCSAtom Pred D

/-- TCS formulas: propositional combinations (¬, ∧) of TCS atoms.
    Reuses the canonical `Trivalent.Formula` rather than introducing a duplicate
    inductive — `Trivalent.Formula.eval` and the `Trivalent.Formula.Realize` lemmas apply directly. -/
abbrev TCSFormula (Pred D : Type*) := Trivalent.Formula (TCSAtom Pred D)

-- ════════════════════════════════════════════════════
-- § 3. Atomic Satisfaction (Definition 9 atomic clauses, p. 353)
-- ════════════════════════════════════════════════════

variable {D Pred : Type*}

/-- **Strict** atomic satisfaction: `P` holds at every `~_P`-neighbour
    of `a`. Definition 9, atomic clause for `⊨ˢ`. Modal-logic-wise,
    this is `box (M.simAccess P)` over the classical extension. -/
def StrictAt (M : TModel D Pred) (P : Pred) (a : D) : Prop :=
  ∀ d, M.sim P a d → M.interp P d

/-- **Tolerant** atomic satisfaction: `P` holds at some `~_P`-neighbour
    of `a`. Definition 9, atomic clause for `⊨ᵗ`. Modal-logic-wise,
    this is `diamond (M.simAccess P)` over the classical extension. -/
def TolerantAt (M : TModel D Pred) (P : Pred) (a : D) : Prop :=
  ∃ d, M.sim P a d ∧ M.interp P d

/-- **Strict atom = `box` over the similarity frame.** This is
    definitionally true; the lemma exists to expose the modal-logic
    framing and to let downstream proofs invoke `box_T`/`box_B`
    directly. -/
theorem strictAt_eq_box (M : TModel D Pred) (P : Pred) (a : D) :
    StrictAt M P a = box (M.simAccess P) (λ d => M.interp P d) a := rfl

/-- **Tolerant atom = `diamond` over the similarity frame.** Definitional. -/
theorem tolerantAt_eq_diamond (M : TModel D Pred) (P : Pred) (a : D) :
    TolerantAt M P a = diamond (M.simAccess P) (λ d => M.interp P d) a := rfl

-- ════════════════════════════════════════════════════
-- § 4. Lemma 1 atomic (extension hierarchy, p. 357)
-- ════════════════════════════════════════════════════

/-- **Strict ⟹ classical** at the atomic level: if `P` holds for every
    `~_P`-neighbour of `a`, it holds for `a` itself by reflexivity of
    `~_P`. This is the **T axiom** instantiated. -/
theorem StrictAt.imp_classical (M : TModel D Pred) (P : Pred) (a : D)
    (hs : StrictAt M P a) : M.interp P a :=
  box_T (M.simAccess P) _ a hs

/-- **Classical ⟹ tolerant** at the atomic level: `a` itself
    witnesses the existential by reflexivity of `~_P`. -/
theorem TolerantAt.of_classical (M : TModel D Pred) (P : Pred) (a : D)
    (hc : M.interp P a) : TolerantAt M P a :=
  ⟨a, Std.Refl.refl (r := M.sim P) a, hc⟩

/-- **Strict ⟹ tolerant** (transitive from above). -/
theorem StrictAt.imp_tolerant (M : TModel D Pred) (P : Pred) (a : D)
    (hs : StrictAt M P a) : TolerantAt M P a :=
  TolerantAt.of_classical M P a (StrictAt.imp_classical M P a hs)

-- ════════════════════════════════════════════════════
-- § 5. Tolerance Principle (Facts 2-3, p. 354)
-- ════════════════════════════════════════════════════

/-- **One-step tolerance** (Fact 2 of [cobreros-etal-2012], p. 354):
    if `a` is strictly `P` and `a ~_P b`, then `b` is tolerantly `P`.
    The tolerance principle `∀x∀y(P(x) ∧ x~_Py → P(y))` is t-valid.

    Proof structure: strict-at-a + sim(a,b) gives classical-at-b
    (via the strict clause); classical implies tolerant. -/
theorem tolerance_one_step (M : TModel D Pred) (P : Pred) (a b : D)
    (hs : StrictAt M P a) (hsim : M.sim P a b) :
    TolerantAt M P b :=
  TolerantAt.of_classical M P b (hs b hsim)

/-- **Two-step tolerance** (Fact 3 of [cobreros-etal-2012], p. 354):
    tolerance propagates across two similarity steps. The third step
    can fail because `~_P` is non-transitive — paper footnote 4
    illustrates this on the 4-element model with `Pa, a~b, b~c, c~d`
    where `Pd` is NOT tolerantly true.

    Proof: strict(a) + sim(a,b) gives classical(b); then b witnesses
    tolerant(c) via sim(c,b) (by symmetry). -/
theorem tolerance_two_step (M : TModel D Pred) (P : Pred) (a b c : D)
    (hs : StrictAt M P a) (hab : M.sim P a b) (hbc : M.sim P b c) :
    TolerantAt M P c :=
  ⟨b, Std.Symm.symm (r := M.sim P) b c hbc, hs b hab⟩

-- ════════════════════════════════════════════════════
-- § 6. Borderline (Definition 10, p. 355)
-- ════════════════════════════════════════════════════

/-- **Borderline**: in the tolerant extension but not the strict.

    Definition 10 (p. 355): `b(P)^M := ⟦P⟧ᵗ \ ⟦P⟧ˢ`. We adopt this
    set-difference form as canonical; the equivalent paraconsistent
    characterisation `tolerant P ∧ tolerant ¬P` follows from Definition
    9's negation clause (`tolerant ¬P ↔ ¬strict P`) and is recorded as
    `IsBorderline.iff_tolerant_pair` below. -/
def IsBorderline (M : TModel D Pred) (P : Pred) (a : D) : Prop :=
  TolerantAt M P a ∧ ¬ StrictAt M P a

/-- **Borderline iff witnesses on both sides** of the classical extension
    in the similarity neighbourhood. This is the structural reading
    underlying paper p. 355's discussion of borderline-as-disagreement. -/
theorem IsBorderline.iff_both_witnesses (M : TModel D Pred) (P : Pred) (a : D) :
    IsBorderline M P a ↔
      (∃ d, M.sim P a d ∧ M.interp P d) ∧
      (∃ d, M.sim P a d ∧ ¬ M.interp P d) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨d, hsd, hpd⟩, hns⟩
    refine ⟨⟨d, hsd, hpd⟩, ?_⟩
    by_contra hc
    apply hns
    intro e hse
    by_contra hne
    exact hc ⟨e, hse, hne⟩
  · rintro ⟨⟨d, hsd, hpd⟩, ⟨e, hse, hne⟩⟩
    refine ⟨⟨d, hsd, hpd⟩, ?_⟩
    intro hs
    exact hne (hs e hse)

-- ════════════════════════════════════════════════════
-- § 7. Bridge: TCS atoms ↔ Supervaluation (paper p. 355 footnote 5)
-- ════════════════════════════════════════════════════

section Bridge

variable [Fintype D]

/-- The tolerance neighborhood of `a` under `P` as a `SpecSpace`.
    Reflexivity of `~_P` ensures `a` is in its own neighbourhood, so the
    admissible Finset is non-empty.

    This makes TCS a **localized supervaluation**: each individual gets
    its own specification space (the rough-set / tolerance-approximation
    "granule" around it). -/
def toleranceSpace (M : TModel D Pred) (P : Pred) (a : D)
    [DecidablePred (M.sim P a)] : SpecSpace D where
  admissible := Finset.univ.filter (M.sim P a)
  nonempty := ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a,
    Std.Refl.refl (r := M.sim P) a⟩⟩

/-- **Strict truth = super-truth** over the tolerance neighborhood.
    `P` is strict at `a` iff `P` is super-true (true at every spec point)
    over `a`'s tolerance space. The central architectural connection to
    `Supervaluation/Basic.lean`. -/
theorem StrictAt.iff_superTrue (M : TModel D Pred) (P : Pred) (a : D)
    [DecidablePred (M.sim P a)] :
    StrictAt M P a ↔
      superTrue (M.interp P) (toleranceSpace M P a) = Trivalent.true := by
  rw [superTrue_true_iff]
  refine ⟨λ h d hd => h d (Finset.mem_filter.mp hd).2,
          λ h d hd => h d (Finset.mem_filter.mpr ⟨Finset.mem_univ d, hd⟩)⟩

/-- **¬Tolerant = super-false** over the tolerance neighborhood. -/
theorem TolerantAt.not_iff_superFalse (M : TModel D Pred) (P : Pred) (a : D)
    [DecidablePred (M.sim P a)] :
    ¬ TolerantAt M P a ↔
      superTrue (M.interp P) (toleranceSpace M P a) = Trivalent.false := by
  rw [superTrue_false_iff]
  refine ⟨?_, ?_⟩
  · intro h d hd hpd
    have hsim := (Finset.mem_filter.mp hd).2
    exact h ⟨d, hsim, hpd⟩
  · rintro h ⟨d, hsim, hpd⟩
    have hd : d ∈ Finset.univ.filter (M.sim P a) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ d, hsim⟩
    exact h d hd hpd

/-- **Borderline = supervaluationally indeterminate** over the tolerance
    neighborhood. Connects TCS to [fine-1975]: borderline cases are
    exactly where the tolerance neighborhood disagrees on `P`. -/
theorem IsBorderline.iff_superTrue_indet (M : TModel D Pred) (P : Pred) (a : D)
    [DecidablePred (M.sim P a)] :
    IsBorderline M P a ↔
      superTrue (M.interp P) (toleranceSpace M P a) = Trivalent.indet := by
  rw [IsBorderline.iff_both_witnesses, superTrue_indet_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨d, hsd, hpd⟩, ⟨e, hse, hne⟩⟩
    exact ⟨⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ d, hsd⟩, hpd⟩,
           ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ e, hse⟩, hne⟩⟩
  · rintro ⟨⟨d, hd, hpd⟩, ⟨e, he, hne⟩⟩
    exact ⟨⟨d, (Finset.mem_filter.mp hd).2, hpd⟩,
           ⟨e, (Finset.mem_filter.mp he).2, hne⟩⟩

end Bridge

-- ════════════════════════════════════════════════════
-- § 8. SatMode and Compositional Satisfaction (Definition 9 full)
-- ════════════════════════════════════════════════════

/-- The three satisfaction modes of [cobreros-etal-2012]. -/
inductive SatMode | tolerant | classical | strict
  deriving DecidableEq, Repr, Inhabited

namespace SatMode

/-- The dual operation on modes: tolerant ↔ strict, classical fixed.
    Encodes the mutual recursion of Definition 9: `M ⊨ᵗ ¬φ iff M ⊭ˢ φ`. -/
def dual : SatMode → SatMode
  | .tolerant => .strict
  | .strict => .tolerant
  | .classical => .classical

/-- `dual` is an involution. Packaged as `Function.Involutive` so
    downstream consumers can use mathlib's involution machinery. -/
theorem dual_involutive : Function.Involutive dual := λ m => by cases m <;> rfl

@[simp] theorem dual_dual (m : SatMode) : m.dual.dual = m := dual_involutive m

end SatMode

/-- **Three-valued satisfaction (Definition 9 full).** The propositional
    fragment of Definition 9, dispatching on mode at atoms and threading
    `SatMode.dual` through negation. Similarity atoms `a I_P b` are
    classically interpreted regardless of mode (Definition 8 +
    standing assumption above Definition 9). -/
def Sat (M : TModel D Pred) : SatMode → TCSFormula Pred D → Prop
  | _, .atom (.sim P a b) => M.sim P a b
  | .classical, .atom (.pred P a) => M.interp P a
  | .tolerant, .atom (.pred P a) => TolerantAt M P a
  | .strict, .atom (.pred P a) => StrictAt M P a
  | m, .neg φ => ¬ Sat M m.dual φ
  | m, .conj φ ψ => Sat M m φ ∧ Sat M m ψ

@[simp] theorem Sat.atom_classical_pred (M : TModel D Pred) (P : Pred) (a : D) :
    Sat M .classical (.atom (.pred P a)) = (M.interp P a) := rfl

@[simp] theorem Sat.atom_tolerant_pred (M : TModel D Pred) (P : Pred) (a : D) :
    Sat M .tolerant (.atom (.pred P a)) = TolerantAt M P a := rfl

@[simp] theorem Sat.atom_strict_pred (M : TModel D Pred) (P : Pred) (a : D) :
    Sat M .strict (.atom (.pred P a)) = StrictAt M P a := rfl

@[simp] theorem Sat.atom_sim (M : TModel D Pred) (m : SatMode)
    (P : Pred) (a b : D) :
    Sat M m (.atom (.sim P a b)) = M.sim P a b := by
  cases m <;> rfl

@[simp] theorem Sat.neg_eq (M : TModel D Pred) (m : SatMode) (φ : TCSFormula Pred D) :
    Sat M m (.neg φ) = ¬ Sat M m.dual φ := rfl

@[simp] theorem Sat.conj_eq (M : TModel D Pred) (m : SatMode) (φ ψ : TCSFormula Pred D) :
    Sat M m (.conj φ ψ) = (Sat M m φ ∧ Sat M m ψ) := rfl

-- ════════════════════════════════════════════════════
-- § 9. Lemma 1 full (formula-level hierarchy, p. 357)
-- ════════════════════════════════════════════════════

/-- **Lemma 1** (paper p. 357, formula level): for any TCS formula φ,
    strict satisfaction implies classical, and classical implies
    tolerant. Both directions must be proved together because the
    negation case for one direction needs the contrapositive of the
    other.

    For predicate atoms this is the atomic Lemma 1 (`StrictAt.imp_classical`,
    `TolerantAt.of_classical`). For similarity atoms all three modes
    agree (similarity predicates are uniformly classical). The negation
    case turns into a `dual`-swap; conjunction is pointwise. -/
theorem Sat.hierarchy (M : TModel D Pred) (φ : TCSFormula Pred D) :
    (Sat M .strict φ → Sat M .classical φ) ∧
    (Sat M .classical φ → Sat M .tolerant φ) := by
  induction φ with
  | atom α =>
    cases α with
    | pred P a =>
      exact ⟨StrictAt.imp_classical M P a, TolerantAt.of_classical M P a⟩
    | sim P a b => exact ⟨id, id⟩
  | neg ψ ih =>
    -- The neg case reduces both directions to contrapositives of `ih`.
    -- `Sat M .strict (.neg ψ) = ¬ Sat M .tolerant ψ` and
    -- `Sat M .classical (.neg ψ) = ¬ Sat M .classical ψ` definitionally,
    -- so each direction is `(¬ q) → (¬ p)` which is `mt p_imp_q`.
    exact ⟨λ h hc => h (ih.2 hc), λ h hs => h (ih.1 hs)⟩
  | conj ψ χ ihψ ihχ =>
    exact ⟨λ ⟨h1, h2⟩ => ⟨ihψ.1 h1, ihχ.1 h2⟩,
           λ ⟨h1, h2⟩ => ⟨ihψ.2 h1, ihχ.2 h2⟩⟩

theorem Sat.strict_imp_classical (M : TModel D Pred) (φ : TCSFormula Pred D) :
    Sat M .strict φ → Sat M .classical φ := (Sat.hierarchy M φ).1

theorem Sat.classical_imp_tolerant (M : TModel D Pred) (φ : TCSFormula Pred D) :
    Sat M .classical φ → Sat M .tolerant φ := (Sat.hierarchy M φ).2

theorem Sat.strict_imp_tolerant (M : TModel D Pred) (φ : TCSFormula Pred D) :
    Sat M .strict φ → Sat M .tolerant φ :=
  λ h => Sat.classical_imp_tolerant M φ (Sat.strict_imp_classical M φ h)

-- ════════════════════════════════════════════════════
-- § 10. Identity Models and Lemma 2 (p. 357)
-- ════════════════════════════════════════════════════

/-- An **identity T-model**: similarity is propositional equality.
    Paper Lemma 2 (p. 357): every C-model can be expanded to a T-model
    where t/c/s satisfaction coincide.

    The construction is parameterised by an `interp` and produces the
    T-model whose similarity relation is `(· = ·)`. -/
def identityModel (interp : Pred → D → Prop) [∀ P d, Decidable (interp P d)] :
    TModel D Pred where
  interp := interp
  decInterp := inferInstance
  sim _ d₁ d₂ := d₁ = d₂
  sim_ktb _ := { refl := fun _ => rfl, symm := fun _ _ h => h.symm }

/-- In an identity model, tolerant atomic = classical. -/
theorem identityModel.tolerantAt_iff (interp : Pred → D → Prop)
    [∀ P d, Decidable (interp P d)] (P : Pred) (a : D) :
    TolerantAt (identityModel interp) P a ↔ interp P a :=
  ⟨λ ⟨_, hsim, hp⟩ => by cases hsim; exact hp,
   λ h => ⟨a, rfl, h⟩⟩

/-- In an identity model, strict atomic = classical. -/
theorem identityModel.strictAt_iff (interp : Pred → D → Prop)
    [∀ P d, Decidable (interp P d)] (P : Pred) (a : D) :
    StrictAt (identityModel interp) P a ↔ interp P a :=
  ⟨λ h => h a rfl, λ h _ hsim => by cases hsim; exact h⟩

/-- **Lemma 2** (formula level): all three modes agree in an identity
    model, for every formula. -/
theorem identityModel.modes_agree (interp : Pred → D → Prop)
    [∀ P d, Decidable (interp P d)]
    (mode : SatMode) (φ : TCSFormula Pred D) :
    Sat (identityModel interp) mode φ ↔ Sat (identityModel interp) .classical φ := by
  induction φ generalizing mode with
  | atom α =>
    cases α with
    | pred P a =>
      cases mode with
      | classical => exact Iff.rfl
      | tolerant =>
        simp only [Sat.atom_tolerant_pred, Sat.atom_classical_pred]
        exact identityModel.tolerantAt_iff interp P a
      | strict =>
        simp only [Sat.atom_strict_pred, Sat.atom_classical_pred]
        exact identityModel.strictAt_iff interp P a
    | sim P a b => simp only [Sat.atom_sim]
  | neg ψ ih =>
    simp only [Sat.neg_eq]
    exact not_congr (ih mode.dual)
  | conj ψ χ ihψ ihχ =>
    simp only [Sat.conj_eq]
    exact and_congr (ihψ mode) (ihχ mode)

-- ════════════════════════════════════════════════════
-- § 11. Mixed Consequence (Definition 17, p. 366)
-- ════════════════════════════════════════════════════

/-- **Mixed TCS-consequence** (Definition 17 of [cobreros-etal-2012]):
    `Γ ⊨ᵐⁿ φ` iff every T-model that m-satisfies all premises also
    n-satisfies the conclusion. The nine combinations (m, n ∈ {t, c, s})
    yield the nine consequence relations.

    Specialisation of `Consequence.MixedConsequence`. As an
    `abbrev` so the substrate API surface (`mixed_monotone`, etc.) is
    reachable without `unfold`. -/
abbrev tcsConsequence
    (m n : SatMode) (Γ : List (TCSFormula Pred D)) (φ : TCSFormula Pred D) : Prop :=
  MixedConsequence (Sat (D := D) (Pred := Pred)) m n Γ φ

-- ════════════════════════════════════════════════════
-- § 12. Lemma 7 strength ordering (consequence level, p. 368)
-- ════════════════════════════════════════════════════

/-- The atomic-level **`Sat`Implies** witnesses for the three pairwise
    implications among satisfaction modes. These lift the formula-level
    Lemma 1 (`Sat.strict_imp_classical` etc.) into the abstract
    `SatImplies` shape that `MixedConsequence`'s monotonicity API
    consumes. -/
theorem satImplies_strict_classical :
    SatImplies (Sat (D := D) (Pred := Pred)) .strict .classical :=
  λ M φ h => Sat.strict_imp_classical M φ h

theorem satImplies_classical_tolerant :
    SatImplies (Sat (D := D) (Pred := Pred)) .classical .tolerant :=
  λ M φ h => Sat.classical_imp_tolerant M φ h

theorem satImplies_strict_tolerant :
    SatImplies (Sat (D := D) (Pred := Pred)) .strict .tolerant :=
  SatImplies.trans satImplies_strict_classical satImplies_classical_tolerant

/-- **Lemma 7, premise-mode clause** (p. 368): premise-mode strengthening
    coarsens consequence: `⊨ᵗᵐ ⊆ ⊨ᶜᵐ ⊆ ⊨ˢᵐ` for any conclusion mode `m`.
    The "first/second part" decomposition is the formaliser's exposition;
    the paper states both clauses as a single result. -/
theorem tcsConsequence.from_tolerant_premise
    {m : SatMode} {Γ : List (TCSFormula Pred D)} {φ : TCSFormula Pred D}
    (h : tcsConsequence .tolerant m Γ φ) :
    tcsConsequence .classical m Γ φ :=
  premise_monotone satImplies_classical_tolerant h

theorem tcsConsequence.from_classical_premise
    {m : SatMode} {Γ : List (TCSFormula Pred D)} {φ : TCSFormula Pred D}
    (h : tcsConsequence .classical m Γ φ) :
    tcsConsequence .strict m Γ φ :=
  premise_monotone satImplies_strict_classical h

/-- **Lemma 7, conclusion-mode clause** (p. 368): conclusion-mode weakening
    coarsens consequence: `⊨ᵐˢ ⊆ ⊨ᵐᶜ ⊆ ⊨ᵐᵗ` for any premise mode `m`. -/
theorem tcsConsequence.to_classical_conclusion
    {m : SatMode} {Γ : List (TCSFormula Pred D)} {φ : TCSFormula Pred D}
    (h : tcsConsequence m .strict Γ φ) :
    tcsConsequence m .classical Γ φ :=
  conclusion_monotone satImplies_strict_classical h

theorem tcsConsequence.to_tolerant_conclusion
    {m : SatMode} {Γ : List (TCSFormula Pred D)} {φ : TCSFormula Pred D}
    (h : tcsConsequence m .classical Γ φ) :
    tcsConsequence m .tolerant Γ φ :=
  conclusion_monotone satImplies_classical_tolerant h

-- ════════════════════════════════════════════════════
-- § 13. Lemma 8 collapse cc = sc = ct = st (p. 369, restricted vocabulary)
-- ════════════════════════════════════════════════════

/-- A TCS formula is **restricted** if it uses only predicate atoms.
    Paper §2 (p. 356) defines the restricted vocabulary as formulas
    free of BOTH `I_P` (similarity) atoms AND `=` (identity) atoms;
    this Lean substrate has no `=` constructor on `TCSAtom`, so this
    predicate captures only the no-`I_P` half of the paper's restriction.
    For the propositional fragment under consideration here, the two
    coincide.

    On this fragment the **Lemma 8** collapse holds (paper §3.3.1, p. 369,
    states `⊨ˢᵗ ⇒ ⊨ᶜᶜ`, and combined with Lemma 7 monotonicity gives
    cc = sc = ct = st). With similarity (or identity) atoms in the
    language, ALL NINE consequence relations of Definition 17 become
    genuinely distinct (paper §3.4 full-vocabulary diagram, p. 371);
    the four strongest (cc, sc, ct, st) are demonstrated distinct in
    paper §3.4 via the one-step tolerance inference `{Pa, aI_Pb} ⊨ Pb`. -/
def IsRestricted : TCSFormula Pred D → Prop
  | .atom (.pred _ _) => True
  | .atom (.sim _ _ _) => False
  | .neg φ => IsRestricted φ
  | .conj φ ψ => IsRestricted φ ∧ IsRestricted ψ

/-- **Identity-model construction for Lemma 8.** On the restricted
    vocabulary (no sim atoms), the identity model built from `M`'s
    classical interpretation classically satisfies the same formulas
    as `M`. Combined with `identityModel.modes_agree` (where t = c = s
    in the identity model), this drives the cc=st collapse. -/
private theorem identityModel.classical_eq (M : TModel D Pred)
    (φ : TCSFormula Pred D) (hr : IsRestricted φ) :
    Sat (identityModel M.interp) .classical φ ↔ Sat M .classical φ := by
  induction φ with
  | atom α =>
    cases α with
    | pred P a => exact Iff.rfl
    | sim P a b => exact hr.elim
  | neg ψ ih =>
    simp only [Sat.neg_eq, SatMode.dual]
    exact not_congr (ih hr)
  | conj ψ χ ihψ ihχ =>
    simp only [Sat.conj_eq]
    exact and_congr (ihψ hr.1) (ihχ hr.2)

/-- **Lemma 8, st ⟹ cc** on restricted formulas (paper p. 369): the
    heart of the collapse. An st-counterexample to a cc-claim survives
    in the identity model where all modes agree.

    The restriction to `IsRestricted` formulas is essential — paper §3.4
    (p. 371) shows all nine consequence relations are distinct in the
    full vocabulary. -/
theorem tcsConsequence.st_imp_cc_restricted
    {Γ : List (TCSFormula Pred D)} {φ : TCSFormula Pred D}
    (hΓ : ∀ ψ ∈ Γ, IsRestricted ψ) (hφ : IsRestricted φ)
    (hst : tcsConsequence (D := D) (Pred := Pred) .strict .tolerant Γ φ) :
    tcsConsequence .classical .classical Γ φ := by
  intro M hprem
  let M' := identityModel (D := D) (Pred := Pred) M.interp
  have hprem' : ∀ γ ∈ Γ, Sat M' .strict γ := by
    intro γ hγ
    rw [identityModel.modes_agree, identityModel.classical_eq _ _ (hΓ γ hγ)]
    exact hprem γ hγ
  have hconc' := hst M' hprem'
  rw [identityModel.modes_agree, identityModel.classical_eq _ _ hφ] at hconc'
  exact hconc'

/-- **cc ⟹ st** by monotonicity (Lemma 7, twice). Holds unrestricted. -/
theorem tcsConsequence.cc_imp_st
    {Γ : List (TCSFormula Pred D)} {φ : TCSFormula Pred D}
    (hcc : tcsConsequence (D := D) (Pred := Pred) .classical .classical Γ φ) :
    tcsConsequence .strict .tolerant Γ φ :=
  mixed_monotone satImplies_strict_classical satImplies_classical_tolerant hcc

/-- **Lemma 8 cc ↔ st** on restricted formulas: classical consequence
    collapses with strict-to-tolerant. -/
theorem tcsConsequence.cc_iff_st_restricted
    {Γ : List (TCSFormula Pred D)} {φ : TCSFormula Pred D}
    (hΓ : ∀ ψ ∈ Γ, IsRestricted ψ) (hφ : IsRestricted φ) :
    tcsConsequence (D := D) (Pred := Pred) .classical .classical Γ φ ↔
      tcsConsequence .strict .tolerant Γ φ :=
  ⟨tcsConsequence.cc_imp_st, tcsConsequence.st_imp_cc_restricted hΓ hφ⟩

/-- **Lemma 8 cc ↔ sc** on restricted formulas: sandwiching via Lemma 7. -/
theorem tcsConsequence.cc_iff_sc_restricted
    {Γ : List (TCSFormula Pred D)} {φ : TCSFormula Pred D}
    (hΓ : ∀ ψ ∈ Γ, IsRestricted ψ) (hφ : IsRestricted φ) :
    tcsConsequence (D := D) (Pred := Pred) .classical .classical Γ φ ↔
      tcsConsequence .strict .classical Γ φ := by
  refine ⟨premise_monotone satImplies_strict_classical, ?_⟩
  intro h
  apply tcsConsequence.st_imp_cc_restricted hΓ hφ
  exact conclusion_monotone satImplies_classical_tolerant h

/-- **Lemma 8 cc ↔ ct** on restricted formulas: the dual sandwich. -/
theorem tcsConsequence.cc_iff_ct_restricted
    {Γ : List (TCSFormula Pred D)} {φ : TCSFormula Pred D}
    (hΓ : ∀ ψ ∈ Γ, IsRestricted ψ) (hφ : IsRestricted φ) :
    tcsConsequence (D := D) (Pred := Pred) .classical .classical Γ φ ↔
      tcsConsequence .classical .tolerant Γ φ := by
  refine ⟨conclusion_monotone satImplies_classical_tolerant, ?_⟩
  intro h
  apply tcsConsequence.st_imp_cc_restricted hΓ hφ
  exact premise_monotone satImplies_strict_classical h

-- ════════════════════════════════════════════════════
-- § 14. Duality (Remark 1 + Lemma 10, pp. 353+371)
-- ════════════════════════════════════════════════════

/-- **Remark 1** (p. 353): satisfaction-level duality. Negation swaps
    the satisfaction mode via `dual`: `M ⊨ᵐ ¬φ ↔ ¬ M ⊨^{dual m} φ`.
    Definitionally true from `Sat.neg_eq`.

    Note: the abstract `Bilateral.SatDuality` structure
    requires `neg` to be a syntactic involution (`¬¬φ = φ`). TCSFormula
    negation is NOT syntactically involutive (we have `.neg (.neg φ)`,
    not `φ`), so the abstract structure does not literally apply. The
    semantic-level swap is what's needed downstream and is proved here
    directly. -/
theorem Sat.neg_swap (M : TModel D Pred) (m : SatMode) (φ : TCSFormula Pred D) :
    Sat M m (.neg φ) ↔ ¬ Sat M m.dual φ := Iff.rfl

/-- **Lemma 10** self-dual witnesses: the consequence relations satisfying
    `m = dual n` (equivalently `n = dual m`) are exactly the self-dual ones,
    and these are exactly the ones for which the deduction theorem holds.
    For TCS this gives `st`, `ts`, and `cc`. -/
theorem st_self_dual : IsSelfDual SatMode.dual .strict .tolerant := rfl

theorem ts_self_dual : IsSelfDual SatMode.dual .tolerant .strict := rfl

theorem cc_self_dual : IsSelfDual SatMode.dual .classical .classical := rfl

-- ════════════════════════════════════════════════════
-- § 15. Lemma 4 + Theorem 3 (LP/K3 correspondence, pp. 361-362)
-- ════════════════════════════════════════════════════

section LpK3

attribute [local instance] Classical.propDecidable

/-- The MV-model construction of Lemma 4 (p. 361). Each TCS atom is
    classified into Strong Kleene's `{true, false, indet}`:

    - `pred P a` → `.true` if `StrictAt M P a`, `.false` if `¬TolerantAt M P a`,
      `.indet` otherwise (borderline).
    - `sim P a b` → classical: `.true` if similar, `.false` otherwise.

    Definition is `noncomputable` because strictness/tolerance are not
    decidable in general (only when `D` is finite and `sim` is decidable).
    The local `Classical.propDecidable` instance makes the `if-then-else`
    well-typed; every theorem about `toMV` remains constructive. -/
noncomputable def toMV (M : TModel D Pred) : Trivalent.Model (TCSAtom Pred D) := λ α =>
  match α with
  | .pred P a =>
    if StrictAt M P a then Trivalent.true
    else if TolerantAt M P a then Trivalent.indet
    else Trivalent.false
  | .sim P a b => if M.sim P a b then Trivalent.true else Trivalent.false

theorem toMV_pred_true_iff (M : TModel D Pred) (P : Pred) (a : D) :
    toMV M (.pred P a) = Trivalent.true ↔ StrictAt M P a := by
  unfold toMV
  by_cases hs : StrictAt M P a
  · simp [hs]
  · simp only [if_neg hs]
    refine ⟨λ h => absurd ?_ hs, λ h => absurd h hs⟩
    by_cases ht : TolerantAt M P a
    · rw [if_pos ht] at h; exact Trivalent.noConfusion h
    · rw [if_neg ht] at h; exact Trivalent.noConfusion h

theorem toMV_pred_false_iff (M : TModel D Pred) (P : Pred) (a : D) :
    toMV M (.pred P a) = Trivalent.false ↔ ¬ TolerantAt M P a := by
  unfold toMV
  by_cases hs : StrictAt M P a
  · simp only [if_pos hs]
    exact ⟨λ h => Trivalent.noConfusion h,
           λ h => absurd (StrictAt.imp_tolerant M P a hs) h⟩
  · simp only [if_neg hs]
    by_cases ht : TolerantAt M P a
    · simp only [if_pos ht]
      exact ⟨λ h => Trivalent.noConfusion h, λ h => absurd ht h⟩
    · simp only [if_neg ht]
      refine Iff.intro (λ _ => ht) (λ _ => ?_)
      trivial

theorem toMV_sim_true_iff (M : TModel D Pred) (P : Pred) (a b : D) :
    toMV M (.sim P a b) = Trivalent.true ↔ M.sim P a b := by
  unfold toMV
  by_cases h : M.sim P a b
  · simp [h]
  · simp only [if_neg h]
    exact ⟨λ heq => Trivalent.noConfusion heq, λ hh => absurd hh h⟩

theorem toMV_sim_false_iff (M : TModel D Pred) (P : Pred) (a b : D) :
    toMV M (.sim P a b) = Trivalent.false ↔ ¬ M.sim P a b := by
  unfold toMV
  by_cases h : M.sim P a b
  · simp only [if_pos h]
    exact ⟨λ heq => Trivalent.noConfusion heq, λ hn => absurd h hn⟩
  · simp [h]

/-- **Lemma 4** (p. 361, formula-level): for every T-model `M` and TCS
    formula `φ`,

    - `M ⊨ᵗ φ ↔ Trivalent.Formula.eval (toMV M) φ` is LP-designated (non-false)
    - `M ⊨ˢ φ ↔ Trivalent.Formula.eval (toMV M) φ` is K3-designated (= true)

    The two halves are proved by mutual induction. The negation case
    uses `lpSat_neg_iff`/`k3Sat_neg_iff` from the substrate; the
    conjunction case uses `lpSat_conj`/`k3Sat_conj`. -/
theorem tcs_lp_k3_correspondence (M : TModel D Pred) (φ : TCSFormula Pred D) :
    (Sat M .tolerant φ ↔ Trivalent.Formula.Realize (toMV M) .lp φ) ∧
    (Sat M .strict φ ↔ Trivalent.Formula.Realize (toMV M) .k3 φ) := by
  induction φ with
  | atom α =>
    cases α with
    | pred P a =>
      refine ⟨?_, ?_⟩
      · -- tolerant ↔ LP-designated
        simp only [Sat.atom_tolerant_pred, Trivalent.Formula.Realize, Trivalent.designated_lp_iff, Trivalent.Formula.eval]
        constructor
        · intro h heq
          have := (toMV_pred_false_iff M P a).mp heq
          exact this h
        · intro h
          by_contra hnot
          exact h ((toMV_pred_false_iff M P a).mpr hnot)
      · -- strict ↔ K3-designated
        simp only [Sat.atom_strict_pred, Trivalent.Formula.Realize, Trivalent.designated_k3_iff, Trivalent.Formula.eval]
        exact (toMV_pred_true_iff M P a).symm
    | sim P a b =>
      refine ⟨?_, ?_⟩
      · -- For sim atoms: Sat M m (sim) = M.sim P a b regardless of m.
        -- LP-sat: Trivalent.Formula.eval = sim ? .true : .false; LP-designated iff true iff sim.
        simp only [Sat.atom_sim, Trivalent.Formula.Realize, Trivalent.designated_lp_iff, Trivalent.Formula.eval, toMV]
        by_cases hsim : M.sim P a b
        · simp only [if_pos hsim]
          exact ⟨λ _ h => Trivalent.noConfusion h, λ _ => hsim⟩
        · simp only [if_neg hsim]
          exact ⟨λ h => absurd h hsim, λ h => absurd rfl h⟩
      · simp only [Sat.atom_sim, Trivalent.Formula.Realize, Trivalent.designated_k3_iff, Trivalent.Formula.eval, toMV]
        by_cases hsim : M.sim P a b
        · simp only [if_pos hsim]
          refine Iff.intro (λ _ => ?_) (λ _ => hsim)
          trivial
        · simp only [if_neg hsim]
          exact ⟨λ h => absurd h hsim, λ h => Trivalent.noConfusion h⟩
  | neg ψ ih =>
    obtain ⟨iht, ihs⟩ := ih
    refine ⟨?_, ?_⟩
    · -- tolerant (¬ψ) ↔ LP-designated of neg
      simp only [Sat.neg_eq, SatMode.dual, Trivalent.Formula.realize_neg, Trivalent.Designation.dual_lp, Trivalent.Designation.dual_k3]
      exact not_congr ihs
    · simp only [Sat.neg_eq, SatMode.dual, Trivalent.Formula.realize_neg, Trivalent.Designation.dual_lp, Trivalent.Designation.dual_k3]
      exact not_congr iht
  | conj ψ χ ihψ ihχ =>
    obtain ⟨ihtψ, ihsψ⟩ := ihψ
    obtain ⟨ihtχ, ihsχ⟩ := ihχ
    refine ⟨?_, ?_⟩
    · simp only [Sat.conj_eq, Trivalent.Formula.realize_conj]
      exact and_congr ihtψ ihtχ
    · simp only [Sat.conj_eq, Trivalent.Formula.realize_conj]
      exact and_congr ihsψ ihsχ

/-- **Lemma 4, t-direction**: tolerant satisfaction = LP-satisfaction
    via `toMV`. -/
theorem tolerant_iff_lp (M : TModel D Pred) (φ : TCSFormula Pred D) :
    Sat M .tolerant φ ↔ Trivalent.Formula.Realize (toMV M) .lp φ :=
  (tcs_lp_k3_correspondence M φ).1

/-- **Lemma 4, s-direction**: strict satisfaction = K3-satisfaction
    via `toMV`. -/
theorem strict_iff_k3 (M : TModel D Pred) (φ : TCSFormula Pred D) :
    Sat M .strict φ ↔ Trivalent.Formula.Realize (toMV M) .k3 φ :=
  (tcs_lp_k3_correspondence M φ).2

/-- **Theorem 3** (paper p. 362, consequence-level): on the restricted
    propositional vocabulary, t-consequence equals LP-consequence and
    s-consequence equals K3-consequence (modulo the `toMV` translation
    on premise/conclusion). The forward direction lifts Lemma 4
    pointwise; the reverse direction uses the same `toMV`. -/
theorem tcs_lp_consequence_correspondence
    (Γ : List (TCSFormula Pred D)) (φ : TCSFormula Pred D) :
    tcsConsequence .tolerant .tolerant Γ φ ↔
      ∀ M : TModel D Pred,
        (∀ γ ∈ Γ, Trivalent.Formula.Realize (toMV M) .lp γ) → Trivalent.Formula.Realize (toMV M) .lp φ := by
  refine ⟨?_, ?_⟩
  · intro h M hprem
    rw [← tolerant_iff_lp]
    exact h M (λ γ hγ => (tolerant_iff_lp M γ).mpr (hprem γ hγ))
  · intro h M hprem
    rw [tolerant_iff_lp]
    exact h M (λ γ hγ => (tolerant_iff_lp M γ).mp (hprem γ hγ))

theorem tcs_k3_consequence_correspondence
    (Γ : List (TCSFormula Pred D)) (φ : TCSFormula Pred D) :
    tcsConsequence .strict .strict Γ φ ↔
      ∀ M : TModel D Pred,
        (∀ γ ∈ Γ, Trivalent.Formula.Realize (toMV M) .k3 γ) → Trivalent.Formula.Realize (toMV M) .k3 φ := by
  refine ⟨?_, ?_⟩
  · intro h M hprem
    rw [← strict_iff_k3]
    exact h M (λ γ hγ => (strict_iff_k3 M γ).mpr (hprem γ hγ))
  · intro h M hprem
    rw [strict_iff_k3]
    exact h M (λ γ hγ => (strict_iff_k3 M γ).mp (hprem γ hγ))

end LpK3

-- ════════════════════════════════════════════════════
-- § 16. Non-transitivity schema via similarity atoms
-- ════════════════════════════════════════════════════

/-! Schema theorems for the non-transitivity demonstration. With
    similarity atoms in the formula language, we can now state and prove
    the structural pattern of paper §3.4.1: each one-step / two-step
    sorites inference is individually valid in mixed consequence, but
    chaining past Fact 3's two-step limit fails.

    Attribution caveat: the paper's §3.4.1 demonstration of
    non-transitivity is for `⊨ᶜᵗ` (the corresponding chain `Pa, aI_Pb,
    bI_Pc ⊭ᶜᵗ Pc`). The `⊨ˢᵗ` version of the sorites is stated separately
    in paper §3.6 (Version 1 of the sorites, p. 376). The structural
    pattern — each step valid in isolation, chain fails — is what §3.4.1
    contributes; the `st`-instantiation here applies the same pattern to
    the relation the paper ultimately advocates (paper p. 373: "st" is
    the best-motivated choice).

    Each one-step inference `[Pa, a I_P b] ⊨ˢᵗ Pb` is st-valid (Fact 2 of
    the paper, p. 354). Two such inferences chain to give
    `[Pa, a I_P b, b I_P c] ⊨ˢᵗ Pc` via Fact 3 (two-step tolerance,
    p. 354). But three steps cannot be chained: on a model where `~_P`
    exhausts at two steps, `[Pa, a I_P b, b I_P c, c I_P d] ⊭ˢᵗ Pd`. The
    Studies file instantiates this on the 4-element model from p. 354. -/

/-- Convenience: `Pa, a I_P b ⊨ˢᵗ Pb` is st-valid for every T-model
    (one-step tolerance, schema form). Consumes paper Fact 2. -/
theorem st_one_step_valid (P : Pred) (a b : D) :
    tcsConsequence (D := D) (Pred := Pred) .strict .tolerant
      [.atom (.pred P a), .atom (.sim P a b)]
      (.atom (.pred P b)) := by
  intro M hprem
  have hPa : StrictAt M P a := hprem (.atom (.pred P a)) (by simp)
  have hsim : M.sim P a b := hprem (.atom (.sim P a b)) (by simp)
  exact tolerance_one_step M P a b hPa hsim

/-- Two-step tolerance is st-valid in schema form. Consumes paper Fact 3. -/
theorem st_two_step_valid (P : Pred) (a b c : D) :
    tcsConsequence (D := D) (Pred := Pred) .strict .tolerant
      [.atom (.pred P a), .atom (.sim P a b), .atom (.sim P b c)]
      (.atom (.pred P c)) := by
  intro M hprem
  have hPa : StrictAt M P a := hprem (.atom (.pred P a)) (by simp)
  have hab : M.sim P a b := hprem (.atom (.sim P a b)) (by simp)
  have hbc : M.sim P b c := hprem (.atom (.sim P b c)) (by simp)
  exact tolerance_two_step M P a b c hPa hab hbc

-- ════════════════════════════════════════════════════
-- § 17. Cross-framework divergence: TCS vs Supervaluation
-- ════════════════════════════════════════════════════

/-! Cross-framework divergence between TCS and Fine 1975 supervaluationism
    on borderline contradictions: TCS makes `P ∧ ¬P` tolerantly true while
    supervaluation makes it super-FALSE on the same neighbourhood. Both
    ingredients exist in the substrate (`TolerantAt`,
    `nonContradiction_superFalse`); this section combines them into a
    Lean-checkable existential divergence claim.

    Comparator caveat: the paper's headline borderline-contradiction
    contrast (p. 356) is actually with **Hyde 1997 subvaluationism**, NOT
    with Fine 1975 supervaluationism. Subvaluation and TCS *agree* that
    `P ∧ ¬P` holds at borderline cases; they disagree on the underlying
    framework. The contrast formalised here — TCS vs supervaluation —
    is the *formal-validity-side* contrast (paper p. 359, where TCS's
    *t*/*s*-validity diverge from supervaluationist validity in the
    quantifier-pattern sense). Subvaluationism is not formalised in
    linglib; if it were, a NEW divergence theorem on the
    framework-foundations axis would be the right comparator on the
    *verdict* question.

    A concrete instantiation on the paper's 4-element model is provided
    in `Studies/CobrerosEtAl2012.lean`. -/

/-- **TCS-vs-Supervaluation borderline-contradiction divergence (schema
    form)**: for any T-model `M`, predicate `P`, and individual `a` that
    is borderline-`P`, the conjunction `P(a) ∧ ¬P(a)` is **tolerantly**
    true at `a` in TCS while the supervaluation of the same conjunction
    over the tolerance neighborhood is **super-FALSE**.

    The two frameworks DISAGREE on the formal-validity-side verdict of
    borderline contradictions: TCS at `t` mode says ✓, supervaluation
    says ✗ everywhere. (Note: on the *verdict* question, the paper's
    headline contrast is with subvaluationism; see the section docstring.) -/
theorem tcs_vs_supervaluation_borderline_contradiction
    [Fintype D] [DecidableEq D]
    (M : TModel D Pred) (P : Pred) (a : D) [DecidablePred (M.sim P a)]
    (hb : IsBorderline M P a) :
    Sat M .tolerant (.conj (.atom (.pred P a)) (.neg (.atom (.pred P a)))) ∧
    superTrue (fun d => M.interp P d ∧ ¬ M.interp P d) (toleranceSpace M P a)
      = Trivalent.false := by
  refine ⟨?_, nonContradiction_superFalse _ _⟩
  -- TCS side: tolerant(P) ∧ tolerant(¬P)
  -- tolerant(¬P) = ¬strict(P), which holds because borderline.
  refine ⟨hb.1, ?_⟩
  -- Sat M .tolerant (.neg (.atom (.pred P a))) = ¬ Sat M .strict (.atom (.pred P a)) = ¬ StrictAt M P a
  simp only [Sat.neg_eq, SatMode.dual, Sat.atom_strict_pred]
  exact hb.2

/-- **Paracomplete dual** (schema form): on the same borderline cases,
    `¬(P ∧ ¬P)` (i.e., excluded middle in dual form) fails strictly.

    Note that strict satisfaction is the **paracomplete** dual of
    tolerant: in TCS, borderline cases satisfy `P ∧ ¬P` tolerantly
    AND fail to satisfy classical principles strictly. -/
theorem tcs_borderline_excluded_middle_strict_fails
    (M : TModel D Pred) (P : Pred) (a : D) (hb : IsBorderline M P a) :
    ¬ Sat M .strict (.neg (.conj (.atom (.pred P a)) (.neg (.atom (.pred P a))))) := by
  -- Sat M .strict (.neg φ) = ¬ Sat M .tolerant φ. The conjunction is
  -- tolerantly true at borderline cases (`tcs_vs_supervaluation_borderline_contradiction`),
  -- so its strict negation fails. simp collapses ¬¬ to give the IsBorderline
  -- shape directly.
  simp only [Sat.neg_eq, SatMode.dual, Sat.conj_eq, Sat.atom_tolerant_pred,
    Sat.atom_strict_pred, not_not]
  exact hb

end Semantics.Supervaluation.TCS

namespace CobrerosEtAl2012

open Semantics.Supervaluation.TCS
open Semantics.Supervaluation (SpecSpace superTrue)

-- ════════════════════════════════════════════════════
-- § 1. The 4-element domain (paper footnote 4, p. 354)
-- ════════════════════════════════════════════════════

/-- Four individuals — the elements of the paper's chain. -/
inductive Elt | a | b | c | d
  deriving Repr, DecidableEq

instance : Fintype Elt where
  elems := {.a, .b, .c, .d}
  complete x := by cases x <;> decide

/-- One vague predicate — "tall". -/
inductive VPred | tall
  deriving Repr, DecidableEq

instance : Fintype VPred where
  elems := {.tall}
  complete x := by cases x; decide

-- ════════════════════════════════════════════════════
-- § 2. Similarity relation (paper footnote 4, p. 354)
-- ════════════════════════════════════════════════════

/-- The similarity chain `a ~ b ~ c ~ d` with reflexivity + symmetry,
    nothing else. Implemented via a Bool-valued helper so the `Decidable`
    instance reduces through Bool equality, keeping the model fully
    computable for `decide`-based extension proofs. -/
def soritesSimBool : Elt → Elt → Bool
  | .a, .a => true | .a, .b => true
  | .b, .a => true | .b, .b => true | .b, .c => true
  | .c, .b => true | .c, .c => true | .c, .d => true
  | .d, .c => true | .d, .d => true
  | _, _ => false

/-- The similarity relation as a `Prop`, for direct integration with
    the modal-logic substrate's `box`/`diamond`. -/
def soritesSim (x y : Elt) : Prop := soritesSimBool x y = true

instance : DecidableRel soritesSim := λ x y =>
  inferInstanceAs (Decidable (soritesSimBool x y = true))

-- ════════════════════════════════════════════════════
-- § 3. The T-model itself (paper footnote 4, p. 354)
-- ════════════════════════════════════════════════════

/-- The paper's running 4-element model: `I(tall) = {a, b}`, similarity
    chain `a ~ b ~ c ~ d`. -/
def soritesModel : TModel Elt VPred where
  interp
    | .tall, .a => True
    | .tall, .b => True
    | .tall, .c => False
    | .tall, .d => False
  decInterp P x := by cases P; cases x <;> simp only [] <;> infer_instance
  sim _ := soritesSim
  sim_ktb _ := { refl := fun x => by cases x <;> decide
                 symm := fun x y h => by cases x <;> cases y <;> first | decide | exact h }

/-- Per-pair decidability of the model's sim relation. Needed for
    `decide`-style proofs of the extension theorems below. Since
    `soritesModel.sim P` ignores `P` (definitionally `soritesSim`),
    the instance reduces to `soritesSim`'s `DecidableRel`. The
    `DecidablePred (soritesModel.sim P x)` shape needed by `toleranceSpace`
    is auto-derived from this per-pair instance. -/
instance soritesModel_sim_dec (P : VPred) (x y : Elt) :
    Decidable (soritesModel.sim P x y) :=
  inferInstanceAs (Decidable (soritesSim x y))

-- ════════════════════════════════════════════════════
-- § 4. Atomic-level decidability (so `decide` works)
-- ════════════════════════════════════════════════════

/-- `StrictAt` is decidable on the sorites model: it's a finite
    universal over the 4 elements. -/
instance soritesModel_strict_dec (P : VPred) (x : Elt) :
    Decidable (StrictAt soritesModel P x) :=
  Fintype.decidableForallFintype

/-- `TolerantAt` is decidable on the sorites model: it's a finite
    existential. -/
instance soritesModel_tolerant_dec (P : VPred) (x : Elt) :
    Decidable (TolerantAt soritesModel P x) :=
  Fintype.decidableExistsFintype

instance soritesModel_borderline_dec (P : VPred) (x : Elt) :
    Decidable (IsBorderline soritesModel P x) :=
  inferInstanceAs (Decidable (TolerantAt soritesModel P x ∧ _))

-- ════════════════════════════════════════════════════
-- § 5. Extension verification
-- ════════════════════════════════════════════════════

/-- **Strict extension** of `tall`: `{a}` only. Other elements have
    similar individuals that aren't classically tall. -/
theorem strict_extension :
    StrictAt soritesModel .tall .a ∧
    ¬ StrictAt soritesModel .tall .b ∧
    ¬ StrictAt soritesModel .tall .c ∧
    ¬ StrictAt soritesModel .tall .d := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- **Classical extension** of `tall`: `{a, b}` directly from `I(tall)`. -/
theorem classical_extension :
    soritesModel.interp .tall .a ∧
    soritesModel.interp .tall .b ∧
    ¬ soritesModel.interp .tall .c ∧
    ¬ soritesModel.interp .tall .d := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [soritesModel]

/-- **Tolerant extension** of `tall`: `{a, b, c}`. `d` is too far from
    the classical extension to count as tolerantly tall (three steps
    from `a`, exceeding Fact 3's two-step limit). -/
theorem tolerant_extension :
    TolerantAt soritesModel .tall .a ∧
    TolerantAt soritesModel .tall .b ∧
    TolerantAt soritesModel .tall .c ∧
    ¬ TolerantAt soritesModel .tall .d := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

-- ════════════════════════════════════════════════════
-- § 6. Borderline classification
-- ════════════════════════════════════════════════════

/-- `b` is borderline-tall: tolerantly tall (witness: `a`), but not
    strictly tall (counter-witness: `c`, which is similar to `b` but
    not classically tall). -/
theorem b_is_borderline : IsBorderline soritesModel .tall .b := by decide

/-- `c` is borderline-tall: tolerantly tall (witness: `b`), but not
    strictly tall (counter-witness: `d`). -/
theorem c_is_borderline : IsBorderline soritesModel .tall .c := by decide

/-- `a` is NOT borderline: strictly tall, hence not in `tolerant \ strict`. -/
theorem a_not_borderline : ¬ IsBorderline soritesModel .tall .a := by decide

/-- `d` is NOT borderline: not even tolerantly tall, hence not in `tolerant \ strict`. -/
theorem d_not_borderline : ¬ IsBorderline soritesModel .tall .d := by decide

-- ════════════════════════════════════════════════════
-- § 7. Tolerant contradictions at borderline cases (paraconsistent half)
-- ════════════════════════════════════════════════════

/-- At the borderline individual `b`, `tall ∧ ¬ tall` is **tolerantly true**
    in TCS — the paraconsistent feature. Compare with the same conjunction
    being super-FALSE in supervaluation: see §8 below. -/
theorem b_tolerant_contradiction :
    Sat soritesModel .tolerant
      (.conj (.atom (.pred .tall .b)) (.neg (.atom (.pred .tall .b)))) := by
  exact (tcs_vs_supervaluation_borderline_contradiction
    soritesModel .tall .b b_is_borderline).1

/-- Same for `c`. -/
theorem c_tolerant_contradiction :
    Sat soritesModel .tolerant
      (.conj (.atom (.pred .tall .c)) (.neg (.atom (.pred .tall .c)))) :=
  (tcs_vs_supervaluation_borderline_contradiction
    soritesModel .tall .c c_is_borderline).1

/-- At the **non-borderline** individual `a` (strictly tall), the
    contradiction `tall ∧ ¬ tall` is NOT tolerantly true. -/
theorem a_no_tolerant_contradiction :
    ¬ Sat soritesModel .tolerant
      (.conj (.atom (.pred .tall .a)) (.neg (.atom (.pred .tall .a)))) := by
  rintro ⟨_, hneg⟩
  -- hneg : ¬ Sat soritesModel .strict (.atom (.pred .tall .a))
  -- But a IS strictly tall — contradiction.
  exact hneg strict_extension.1

/-- Dually for `d` (not even tolerantly tall). -/
theorem d_no_tolerant_contradiction :
    ¬ Sat soritesModel .tolerant
      (.conj (.atom (.pred .tall .d)) (.neg (.atom (.pred .tall .d)))) := by
  rintro ⟨htol, _⟩
  exact tolerant_extension.2.2.2 htol

-- ════════════════════════════════════════════════════
-- § 8. Cross-framework divergence (TCS vs Fine 1975 supervaluation)
-- ════════════════════════════════════════════════════

/-- **Cross-framework divergence theorem**, instantiated at
    `(soritesModel, .tall, .b)`.

    On the same tolerance neighborhood `{d | b ~ d}`:
    - **TCS** says `tall(b) ∧ ¬ tall(b)` is **tolerantly true**
    - **Fine 1975 supervaluation** says it is **super-FALSE** (= `Trivalent.false`)

    The frameworks disagree on the *formal-validity-side* verdict.
    Caveat (per the file docstring): the paper's headline contrast on
    borderline contradictions (p. 356) is with **Hyde 1997
    subvaluationism**, which agrees with TCS on the verdict. Fine 1975
    supervaluation is the comparator we can formalise here because it's
    the only one of the two with a substrate in linglib. -/
theorem tcs_supervaluation_disagree_concrete :
    Sat soritesModel .tolerant
      (.conj (.atom (.pred .tall .b)) (.neg (.atom (.pred .tall .b)))) ∧
    superTrue (λ e => soritesModel.interp .tall e && !soritesModel.interp .tall e)
      (toleranceSpace soritesModel .tall .b)
      = Trivalent.false :=
  tcs_vs_supervaluation_borderline_contradiction
    soritesModel .tall .b b_is_borderline

-- ════════════════════════════════════════════════════
-- § 9. Genuine non-transitivity demonstration via similarity atoms
-- ════════════════════════════════════════════════════

/-- Named atoms used in the non-transitivity demonstration. Extracting
    them as private definitions avoids dotted-identifier elaboration
    issues in conjunctions and lists where the expected element type
    isn't propagated through the syntactic constructors. -/
private abbrev fmlPa : TCSFormula VPred Elt := .atom (.pred .tall .a)
private abbrev fmlPb : TCSFormula VPred Elt := .atom (.pred .tall .b)
private abbrev fmlPc : TCSFormula VPred Elt := .atom (.pred .tall .c)
private abbrev fmlPd : TCSFormula VPred Elt := .atom (.pred .tall .d)
private abbrev fmlIab : TCSFormula VPred Elt := .atom (.sim .tall .a .b)
private abbrev fmlIbc : TCSFormula VPred Elt := .atom (.sim .tall .b .c)
private abbrev fmlIcd : TCSFormula VPred Elt := .atom (.sim .tall .c .d)

/-! Non-transitivity in the full vocabulary with similarity predicates
    `Iₚ`. Each one-step `Pa, aIb ⊨ˢᵗ Pb` is valid (Fact 2, p. 354); each
    two-step `Pa, aIb, bIc ⊨ˢᵗ Pc` is valid (Fact 3, p. 354); but
    three-step `Pa, aIb, bIc, cId ⊨ˢᵗ Pd` is **invalid** because `d`
    requires three similarity steps from the classical extension `{a, b}`,
    exceeding Fact 3's two-step limit.

    Attribution: paper §3.4.1 (p. 372) demonstrates non-transitivity for
    `⊨ᶜᵗ` (the chain `Pa_1, a_1I_Pa_2, a_2I_Pa_3 ⊭ᶜᵗ Pa_3`), and
    footnote 14 formalises the simple-transitivity statement. The `⊨ˢᵗ`
    sorites version is in §3.6 (Version 1, p. 376). The structural
    pattern (each step valid, chain fails) is §3.4.1's contribution; the
    `st`-instantiation here transfers it to the relation the paper
    advocates. -/

/-- **One-step st-validity**, instantiated to the model: `tall(a), aIb ⊨ˢᵗ tall(b)`.
    The schema theorem `Semantics.Supervaluation.TCS.st_one_step_valid` instantiates here. -/
theorem st_one_step_a_to_b :
    tcsConsequence (D := Elt) (Pred := VPred) .strict .tolerant
      [fmlPa, fmlIab] fmlPb :=
  st_one_step_valid (P := VPred.tall) (a := Elt.a) (b := Elt.b)

/-- **Two-step st-validity**: `tall(a), aIb, bIc ⊨ˢᵗ tall(c)`. -/
theorem st_two_step_a_to_c :
    tcsConsequence (D := Elt) (Pred := VPred) .strict .tolerant
      [fmlPa, fmlIab, fmlIbc] fmlPc :=
  st_two_step_valid (P := VPred.tall) (a := Elt.a) (b := Elt.b) (c := Elt.c)

/-- **Three-step st-INVALIDITY**: `tall(a), aIb, bIc, cId ⊭ˢᵗ tall(d)`.

    Each step is individually st-valid (above), but the chain of three
    exhausts the two-step tolerance limit (Fact 3, p. 354), so the
    conclusion fails to hold even tolerantly at `d`. Structural pattern
    of paper §3.4.1; paper itself states the `⊨ᶜᵗ` version there and
    the `⊨ˢᵗ` sorites Version 1 in §3.6 (p. 376). -/
theorem st_three_step_invalid :
    ¬ tcsConsequence (D := Elt) (Pred := VPred) .strict .tolerant
      [fmlPa, fmlIab, fmlIbc, fmlIcd] fmlPd := by
  intro h
  have hprem : ∀ γ ∈ [fmlPa, fmlIab, fmlIbc, fmlIcd],
      Sat soritesModel .strict γ := by
    intro γ hγ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hγ
    rcases hγ with rfl | rfl | rfl | rfl
    · exact strict_extension.1
    all_goals (simp only [Sat.atom_sim]; decide)
  exact tolerant_extension.2.2.2 (h soritesModel hprem)

/-- Convenience packaging: the chain of one-step + two-step st-valid
    inferences cannot be extended to three steps, even though each
    constituent step is valid. -/
theorem st_chain_breaks_at_step_three :
    tcsConsequence (D := Elt) (Pred := VPred) .strict .tolerant
        [fmlPa, fmlIab] fmlPb ∧
    tcsConsequence (D := Elt) (Pred := VPred) .strict .tolerant
        [fmlPa, fmlIab, fmlIbc] fmlPc ∧
    ¬ tcsConsequence (D := Elt) (Pred := VPred) .strict .tolerant
        [fmlPa, fmlIab, fmlIbc, fmlIcd] fmlPd :=
  ⟨st_one_step_a_to_b, st_two_step_a_to_c, st_three_step_invalid⟩

-- ════════════════════════════════════════════════════
-- § 10. Cross-framework reciprocations (Lean-checkable)
-- ════════════════════════════════════════════════════

/-! Two Lean-checkable cross-framework theorems that close gaps flagged
    by the cross-framework reconciler:

    1. **TCS-vs-product-rule expressivity gap**: TCS predicts borderline
       contradictions *categorically* (the conjunction is true, not
       fractional); any framework that predicts them as a product of
       complementary probabilities is *fractionally bounded* by 1/4
       (AM-GM). The architectural divergence between TCS and L&G's
       literal rule is structural, not parametric.
    2. **Klein-delineation tension**: in `soritesModel`, two adjacent
       individuals are tolerantly similar AND both borderline, yet
       classically separated — exactly the configuration where any
       sound Klein delineation would over-impose a scalar relation. -/

/-- **TCS predicts borderline contradictions categorically.** Helper:
    for any T-model `M`, predicate `P`, and individual `a` that is
    borderline-`P`, the conjunction `P(a) ∧ ¬P(a)` is tolerantly true.
    Extracted from the TCS half of
    `tcs_vs_supervaluation_borderline_contradiction`. -/
theorem tcs_borderline_contradiction_categorical
    {D' Pred' : Type*} (M : TModel D' Pred') (P : Pred') (a : D')
    (hb : IsBorderline M P a) :
    Sat M .tolerant (.conj (.atom (.pred P a)) (.neg (.atom (.pred P a)))) := by
  refine ⟨hb.1, ?_⟩
  simp only [Sat.neg_eq, SatMode.dual, Sat.atom_strict_pred]
  exact hb.2

/-- **TCS-vs-product-rule framework expressivity gap.** A framework-level
    contrast theorem with two simultaneous halves, witnessing that TCS
    and any "literal rule = product of complementary probabilities"
    framework (paradigmatically L&G:
    `Studies/LassiterGoodman2017PMF.lean::lg_literal_borderline_bounded`)
    diverge structurally on borderline contradictions:

    - **TCS half**: the conjunction `P(a) ∧ ¬P(a)` is tolerantly TRUE
      (not fractional) at every borderline `a`. This is a categorical
      framework prediction — independent of any parameter.
    - **Product-rule half**: any product `q · (1 - q)` for `q ∈ [0, 1]`
      is bounded above by `1/4` (AM-GM). This is the framework-level
      ceiling on any literal-meaning rule that multiplies a probability
      by its complement. L&G's `lg_literal_borderline_bounded` is the
      `PMF`-typed instance of this generic bound.

    The empirical Alxatib-Pelletier 2011 acceptance rate (44.7% — see
    the [alxatib-pelletier-2011] contrast section of
    `Studies/LassiterGoodman2017PMF.lean`)
    exceeds the product-rule's 25% ceiling, refuting the literal-rule
    framework empirically. TCS's categorical prediction is consistent
    with the empirical direction without committing to any specific
    fractional value. The structural divergence is what's interesting:
    L&G's framework architecture *cannot represent* the empirical
    direction (any literal-rule PMF is bounded ≤ 25%); TCS's framework
    architecture predicts it categorically. -/
theorem tcs_categorical_vs_product_bounded
    {D' Pred' : Type*} (M : TModel D' Pred') (P : Pred') (a : D')
    (hb : IsBorderline M P a) (q : ℝ) :
    Sat M .tolerant (.conj (.atom (.pred P a)) (.neg (.atom (.pred P a)))) ∧
    q * (1 - q) ≤ (1 / 4 : ℝ) := by
  refine ⟨tcs_borderline_contradiction_categorical M P a hb, ?_⟩
  -- (q - 1/2)² ≥ 0 expands to q² - q + 1/4 ≥ 0 ⟹ q(1-q) ≤ 1/4 for ALL real q
  -- (no [0, 1] constraint needed — the bound is universal).
  nlinarith [sq_nonneg (q - 1/2)]

/-- **Klein-delineation tension witness**: in `soritesModel`, the
    individuals `b` and `c` are both borderline-tall AND tolerantly
    similar (`b ~_tall c`), yet classically separated (b is classically
    tall, c is classically not-tall). Any Klein-style sound delineation
    derived from `M.interp .tall` would impose a scalar relation
    `R b c` on this pair (per
    `Semantics/Degree/Delineation.lean::IsSoundDelineation`),
    over-generating where TCS says `b` and `c` are *both equally
    borderline* and the scalar relation should be unwarranted.

    This is the Lean-checkable witness for the prose tension flagged at
    `Comparison/Delineation.lean` lines 566-571. -/
theorem klein_delineation_tension_concrete :
    -- Both are borderline:
    IsBorderline soritesModel .tall .b ∧
    IsBorderline soritesModel .tall .c ∧
    -- They are tolerantly similar:
    soritesModel.sim .tall .b .c ∧
    -- Yet classically separated:
    soritesModel.interp .tall .b ∧
    ¬ soritesModel.interp .tall .c :=
  ⟨b_is_borderline, c_is_borderline, by decide, by simp [soritesModel], by simp [soritesModel]⟩

-- ════════════════════════════════════════════════════
-- § 11. Single-premise sorites unsoundness
-- ════════════════════════════════════════════════════

/-- Single-premise sorites unsoundness (the previous formalization's
    `sorites_chain_invalid`). Subsumed by `st_three_step_invalid` above
    but kept under the historical name. -/
theorem sorites_chain_invalid :
    ¬ tcsConsequence (D := Elt) (Pred := VPred) .strict .tolerant
      [.atom (.pred .tall .a)] (.atom (.pred .tall .d)) := by
  intro h
  have hprem : ∀ γ ∈ [(.atom (.pred .tall .a) : TCSFormula VPred Elt)],
      Sat soritesModel .strict γ := by
    intro γ hγ
    simp at hγ
    subst hγ
    exact strict_extension.1
  have hconc := h soritesModel hprem
  exact tolerant_extension.2.2.2 hconc

end CobrerosEtAl2012
