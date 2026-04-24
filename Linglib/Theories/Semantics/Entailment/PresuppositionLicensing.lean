import Mathlib.Order.Monotone.Defs
import Linglib.Core.Semantics.Presupposition
import Linglib.Theories.Semantics.Exhaustification.Operators.Basic

/-!
# Presupposition-aware NPI licensing — Karttunen-Peters Conditions
@cite{karttunen-peters-1979} @cite{gajewski-2011}

This file formalizes the Karttunen-Peters two-dimensional ⟨truth, presup⟩
framework as it bears on NPI licensing, following @cite{gajewski-2011} §4.4
(eqs. 92-94, p. 134). The substrate concept is a **K&P operator**: a
function from arguments to presuppositional propositions, recording both
truth-conditional and presuppositional content separately.

## Conditions 3 and 4

Per @cite{gajewski-2011} eqs. 93-94: NPI licensing conditions assess
DE-ness on different conjunctions of the K&P content:

- **Condition 3** (weak NPIs): the assertion alone is DE in the argument
  position.
- **Condition 4** (strong NPIs): the assertion *together with the
  operator's presupposition* is DE.

The asymmetry is empirically substantive: an operator that satisfies
Condition 3 but not Condition 4 — i.e., one whose presupposition is
*not* DE in the argument — licenses weak NPIs but blocks strong NPIs.
@cite{gajewski-2011}'s canonical case is `only`: its assertion (`no
y ≠ x has scope`) is classically DE in scope, but its presupposition
(`some y has x and scope`) is upward entailing in scope, so the
conjunction is not DE.

This makes precise the intuition that "presupposition can destroy
DE-ness in the licensee position" — and that strong NPIs are sensitive
to this destruction while weak NPIs are not.
-/

namespace Semantics.Entailment.PresuppositionLicensing

/-- A **Karttunen-Peters operator**: a function from an argument set to
    a presuppositional proposition (truth + presup). The presupposition
    may depend on the argument (per K&P 1979's heritage function). -/
abbrev KPOperator (W : Type*) : Type _ := Set W → Core.Presupposition.PrProp W

/-- The truth-conditional projection of a K&P operator. -/
def KPOperator.truth {W : Type*} (op : KPOperator W) : Set W → Set W :=
  fun arg w => (op arg).assertion w

/-- The presuppositional projection of a K&P operator (parameterized by
    the argument). -/
def KPOperator.opPresup {W : Type*} (op : KPOperator W) : Set W → W → Prop :=
  fun arg w => (op arg).presup w

/-- The full meaning of a K&P operator: assertion *and* presupposition.
    What's checked for Condition 4 (strong NPI licensing). -/
def KPOperator.full {W : Type*} (op : KPOperator W) : Set W → Set W :=
  fun arg w => (op arg).assertion w ∧ (op arg).presup w

/-- @cite{gajewski-2011} eq. 93: **Condition 3** (weak NPI licensing).

    A K&P operator licenses weak NPIs in its argument position iff its
    truth-conditional projection is DE (Antitone) in the argument. The
    operator's own presupposition does NOT enter the licensing check —
    weak NPIs ignore the licenser's presupposition. -/
def Condition3 {W : Type*} (op : KPOperator W) : Prop :=
  Antitone op.truth

/-- @cite{gajewski-2011} eq. 94: **Condition 4** (strong NPI licensing).

    A K&P operator licenses strong NPIs in its argument position iff
    `assertion ∧ operator-presupposition` is DE in the argument. The
    operator's presupposition CAN destroy DE-ness; if it does, the
    operator licenses weak but not strong NPIs. -/
def Condition4 {W : Type*} (op : KPOperator W) : Prop :=
  Antitone op.full

/-- Trivially: an operator with no presupposition (always-`True`) makes
    Condition 3 and Condition 4 equivalent. -/
theorem condition3_iff_condition4_of_trivial_presup {W : Type*}
    (op : KPOperator W) (h : ∀ (arg : Set W) (w : W), (op arg).presup w) :
    Condition3 op ↔ Condition4 op := by
  constructor
  · intro h3 p q hpq w hfull
    exact ⟨h3 hpq hfull.1, h p w⟩
  · intro h4 p q hpq w hassert
    exact (h4 hpq ⟨hassert, h q w⟩).1

/- Note on Condition 4 vs Condition 3 implication:

   Adding more conjuncts to a meaning can destroy DE-ness in the
   licensee position — that is precisely the Gajewski point. So
   Condition 4 does not imply Condition 3 in general, nor vice versa.
   They are *independent* DE checks on different conjunctions of the
   K&P content. -/

-- ============================================================================
-- §2 Conditions 1, 2 — implicature-based licensing (Chierchia line)
-- ============================================================================

/-!
## Conditions 1, 2 — the implicature-based licensing line

Whereas Conditions 3, 4 (above) handle presuppositions via the K&P
framework, Conditions 1, 2 (Gajewski eqs. 59, 66) handle scalar
implicatures via @cite{chierchia-2004}'s O-operator and
alternative-set machinery. The two frameworks make parallel
predictions for `only`: weak NPIs licensed (Condition 1 / Condition 3)
but strong NPIs blocked (Condition 2 / Condition 4) — once the
implicatures (Cond 1/2) or presuppositions (Cond 3/4) of the licenser
are factored in, DE-ness is destroyed.

The substrate's O-operator is `Exhaustification.exhMW` (Spector 2016,
based on minimal worlds) or its equivalent `exhIE` (innocent-exclusion
based, agree under closure under conjunction; see Spector Theorem 9).
We use `exhMW` because its trivial-ALT case is `exhMW ∅ φ = φ` cleanly,
which simplifies the empty-implicature reduction.

Gajewski's ALT vs ALT-1 distinction (eqs. 54, 55) is encoded as
two parameters to Condition 2: the standard alternative set ALT and
the restricted ALT-1 (Chierchia's "highest-scopal-item only").
-/

/-- @cite{gajewski-2011} eq. 59: **Condition 1** (weak NPI licensing).

    Operator `op` licenses weak NPIs in its argument position iff
    `O(op(γ), op(ALT(γ)))` is DE in γ, where `alts γ` generates the
    alternative set against which `op(γ)` is exhaustified.

    `Exhaustification.exhMW` plays the role of Gajewski's `O(F, G)`. -/
def Condition1 {W : Type*} (op : Set W → Set W)
    (alts : Set W → Set (Set W)) : Prop :=
  Antitone (fun γ => Exhaustification.exhMW (alts γ) (op γ))

/-- @cite{gajewski-2011} eq. 66: **Condition 2** (strong NPI licensing).

    Adds a parallel DE check against ALT-1 — the restricted alternative
    set (Chierchia's "highest-scopal-item only", eq. 55). Strong NPIs
    are licensed iff *both* DE checks pass: `O(op(γ), op(ALT(γ)))` AND
    `O(op(γ), op(ALT-1(γ)))`. -/
def Condition2 {W : Type*} (op : Set W → Set W)
    (alts altsOne : Set W → Set (Set W)) : Prop :=
  Condition1 op alts ∧
  Antitone (fun γ => Exhaustification.exhMW (altsOne γ) (op γ))

/-- Trivial-ALT lemma: with no alternatives, `exhMW` collapses to the
    prejacent. Spector 2016's minimality reduces to `True` when there
    are no alternatives to be minimal-with-respect-to. -/
theorem exhMW_empty_eq {W : Type*} (φ : Set W) :
    Exhaustification.exhMW (∅ : Set (Set W)) φ = φ := by
  ext u
  unfold Exhaustification.exhMW Exhaustification.ltALT Exhaustification.leALT
  simp

/-- **Trivial-ALT bridge for Cond 1**: Condition 1 with no alternatives
    reduces to classical DE. -/
theorem condition1_with_no_alts_iff_de {W : Type*} (op : Set W → Set W) :
    Condition1 op (fun _ => ∅) ↔ Antitone op := by
  unfold Condition1
  have h : (fun γ => Exhaustification.exhMW (∅ : Set (Set W)) (op γ)) = op := by
    funext γ
    exact exhMW_empty_eq (op γ)
  rw [h]

/-- **Trivial-ALT bridge for Cond 2**: with no alternatives in either
    ALT or ALT-1, Condition 2 reduces to classical DE. The empirical
    discriminative power of Cond 2 vs Cond 1 only emerges with
    non-trivial ALT-1 (Chierchia's "highest-scopal-item only"). -/
theorem condition2_with_no_alts_iff_de {W : Type*} (op : Set W → Set W) :
    Condition2 op (fun _ => ∅) (fun _ => ∅) ↔ Antitone op := by
  unfold Condition2
  rw [condition1_with_no_alts_iff_de]
  constructor
  · exact fun ⟨h, _⟩ => h
  · intro h
    refine ⟨h, ?_⟩
    have heq : (fun γ => Exhaustification.exhMW (∅ : Set (Set W)) (op γ)) = op := by
      funext γ; exact exhMW_empty_eq (op γ)
    rw [heq]; exact h

/-- **Bridge to Conditions 3, 4**: when `op`'s K&P-form has no
    presupposition (so the operator is presupposition-free), Conditions
    3 and 4 collapse, AND Condition 1 with no alternatives reduces to
    classical DE. Hence presuppositionless + alternative-free ⇒ all
    four Gajewski conditions reduce to classical DE.

    This is the structural reason Gajewski's framework matters: both
    presuppositions (the K&P side) AND implicatures (the Chierchia
    side) can destroy DE-ness in the licensee position; the four
    conditions track which side does what. -/
theorem all_conditions_reduce_to_DE_when_trivial {W : Type*}
    (op : KPOperator W)
    (hPresup : ∀ arg w, (op arg).presup w)
    (hOpFnDE : Antitone op.truth) :
    Condition1 op.truth (fun _ => ∅) ∧
    Condition3 op ∧
    Condition4 op := by
  refine ⟨?_, hOpFnDE, ?_⟩
  · exact (condition1_with_no_alts_iff_de op.truth).mpr hOpFnDE
  · -- Cond 4: assert ∧ presup is DE; presup is trivial, so equals assertion
    intro p q hpq w hfull
    exact ⟨hOpFnDE hpq hfull.1, hPresup p w⟩

end Semantics.Entailment.PresuppositionLicensing
