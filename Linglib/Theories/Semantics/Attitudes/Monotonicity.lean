import Linglib.Core.NaturalLogic
import Linglib.Theories.Semantics.Truthmaker.Basic
import Linglib.Theories.Semantics.Attitudes.NegRaising

/-! # Attitude Verb Monotonicity (Bondarenko & Elliott 2026)

Classifies attitude verb complement positions using `EntailmentSig` from
`Core/NaturalLogic.lean` — the same 9-element lattice used for quantifier
determiners. This makes the parallel between quantifier monotonicity and
attitude monotonicity explicit: both are instances of the same algebraic
classification.

## Key contributions

1. **Conjunction distribution derived from EntailmentSig**: An attitude verb
   distributes over conjunction iff its complement signature refines `.mono`.
   This is not stipulated — it follows from the definition of upward
   monotonicity.

2. **Neg-raising from monotonicity + EMP**: Bondarenko & Elliott derive
   neg-raising from upward monotonicity plus an excluded-middle
   presupposition (EMP), NOT from veridicality (as in `NegRaising.lean`).
   Both derivations agree on believe/think/know.

3. **Mereological grounding**: The conjunction distribution theorem
   (`mono_att_distrib_and` in `Truthmaker.Basic`) proves that the
   distribution follows from the `SemilatticeSup` structure of states.

## References

- Bondarenko, T. & Elliott, P.D. (2026). Monotonicity via mereology.
  @cite{bondarenko-elliott-2026}
- Icard, T. (2012). Inclusion and Exclusion in Natural Language.
-/

namespace Semantics.Attitudes.Monotonicity

open Core.NaturalLogic (EntailmentSig)
open Semantics.Attitudes.NegRaising (negRaisingAvailable)
open Semantics.Attitudes.Doxastic (Veridicality)

-- ════════════════════════════════════════════════════
-- § 1. Attitude Complement Signatures
-- ════════════════════════════════════════════════════

/-- Believe: upward monotone in its complement.
    "believe (p and q)" ↔ "believe p and believe q". -/
def believeSig : EntailmentSig := .mono

/-- Know: upward monotone in its complement.
    Factive, but still monotone: "know (p and q)" ↔ "know p and know q". -/
def knowSig : EntailmentSig := .mono

/-- Think: upward monotone in its complement. -/
def thinkSig : EntailmentSig := .mono

/-- Hope: upward monotone in its complement. -/
def hopeSig : EntailmentSig := .mono

/-- Be surprised: multiplicative but not additive.
    Distributes over ∧ but not ∨: "surprised that p and q" ↔
    "surprised that p and surprised that q", but
    "surprised that p or q" does NOT distribute. -/
def surpriseSig : EntailmentSig := .mult

-- ════════════════════════════════════════════════════
-- § 2. Conjunction Distribution from Signature
-- ════════════════════════════════════════════════════

/-- An attitude distributes over conjunction iff its complement signature
    refines `.mono` (upward monotone). This includes: `.all`, `.addMult`,
    `.additive`, `.mult`, and `.mono` itself.

    Note: `.mult` (multiplicative) distributes over ∧ by definition —
    f(A ∧ B) = f(A) ∧ f(B). The `.mono` refinement captures this. -/
def distribOverConj (sig : EntailmentSig) : Bool :=
  sig.refines .mono

-- Verification: monotone attitudes distribute
#guard distribOverConj believeSig   -- believe distributes
#guard distribOverConj knowSig      -- know distributes
#guard distribOverConj thinkSig     -- think distributes
#guard distribOverConj hopeSig      -- hope distributes
#guard distribOverConj surpriseSig  -- surprise distributes (multiplicative!)

-- Non-monotone attitudes would not distribute:
#guard !distribOverConj .anti       -- antitone does not
#guard !distribOverConj .antiAdd    -- anti-additive does not

-- ════════════════════════════════════════════════════
-- § 3. Neg-Raising: Monotonicity + EMP Account
-- ════════════════════════════════════════════════════

/-- Excluded-Middle Presupposition (EMP).
    An attitude verb has EMP if it presupposes that the agent either
    holds the attitude toward p or toward ¬p.
    EMP(V, x, p) := V(x, p) ∨ V(x, ¬p)

    Under EMP, ¬V(p) → V(¬p) is immediate (disjunctive syllogism).
    This is neg-raising.

    The Bondarenko & Elliott insight: EMP is motivated by monotonicity.
    Upward-monotone verbs have a "gapless" information state — the
    state either contains a verifier for p or for ¬p (no undecided gap).
    This is a presupposition, not a semantic entailment. -/
def hasEMP (sig : EntailmentSig) : Bool :=
  sig.refines .mono

/-- Neg-raising available via monotonicity + EMP.
    This is an alternative to `NegRaising.negRaisingAvailable`, which
    derives neg-raising from veridicality. Both are correct derivations
    that agree on all standard verbs but have different theoretical
    underpinnings.

    Bondarenko & Elliott: monotonicity + EMP → neg-raising
    Horn (2001): non-veridicality → neg-raising -/
def negRaisingFromMono (sig : EntailmentSig) (v : Veridicality) : Bool :=
  hasEMP sig && v == .nonVeridical

-- ════════════════════════════════════════════════════
-- § 4. Bridge Theorems: Two Routes to Neg-Raising
-- ════════════════════════════════════════════════════

/-- For believe: both accounts predict neg-raising.
    Veridicality account: nonVeridical → negRaising ✓
    Monotonicity account: mono + EMP + nonVeridical → negRaising ✓ -/
theorem believe_negRaising_both_accounts :
    negRaisingAvailable .nonVeridical = true ∧
    negRaisingFromMono believeSig .nonVeridical = true :=
  ⟨rfl, rfl⟩

/-- For think: both accounts predict neg-raising. -/
theorem think_negRaising_both_accounts :
    negRaisingAvailable .nonVeridical = true ∧
    negRaisingFromMono thinkSig .nonVeridical = true :=
  ⟨rfl, rfl⟩

/-- For know: both accounts predict NO neg-raising.
    Veridicality account: veridical → no negRaising ✓
    Monotonicity account: mono + EMP, but veridical → no negRaising ✓
    (Know has EMP but is veridical, so the pragmatic inference is
    blocked by the factivity presupposition.) -/
theorem know_no_negRaising_both_accounts :
    negRaisingAvailable .veridical = false ∧
    negRaisingFromMono knowSig .veridical = false :=
  ⟨rfl, rfl⟩

/-- The veridicality and monotonicity accounts agree on all standard
    doxastic verbs: both predict neg-raising for non-veridical monotone
    verbs and no neg-raising for veridical ones.

    They could diverge for hypothetical verbs that are:
    - Monotone but veridical (know-like) → both block neg-raising
    - Non-monotone but non-veridical → veridicality allows, monotonicity blocks

    Currently both routes agree because all non-veridical doxastic verbs
    in the lexicon are also monotone. -/
theorem negRaising_accounts_agree_doxastic (v : Veridicality) :
    negRaisingFromMono .mono v = negRaisingAvailable v := by
  cases v <;> rfl

-- ════════════════════════════════════════════════════
-- § 5. Connection to Mereological Foundation
-- ════════════════════════════════════════════════════

/-- The truthmaker conjunction distribution theorem
    (`Truthmaker.mono_att_distrib_and`) provides the semantic *why* for
    the monotonicity classification.

    This re-export makes the connection explicit: the EntailmentSig
    classification of attitude verbs is *grounded* in the SemilatticeSup
    structure of propositional content via truthmaker semantics. -/
theorem conjunction_distribution_grounded :
    ∀ (S E : Type*) [SemilatticeSup S] (σ : E → S)
      (p q : Semantics.Truthmaker.TMProp S) (x : E),
    Semantics.Truthmaker.attHolds σ (Semantics.Truthmaker.tmAnd p q) x ↔
    Semantics.Truthmaker.attHolds σ p x ∧ Semantics.Truthmaker.attHolds σ q x :=
  λ _ _ _ σ p q x => Semantics.Truthmaker.mono_att_distrib_and_iff σ p q x

end Semantics.Attitudes.Monotonicity
