import Linglib.Core.NaturalLogic
import Linglib.Theories.Semantics.Truthmaker.Basic
import Linglib.Theories.Semantics.Attitudes.NegRaising

/-! # Attitude Verb Monotonicity (Bondarenko & Elliott 2026)

Classifies attitude verb complement positions using `EntailmentSig` from
`Core/NaturalLogic.lean` — the same 9-element lattice used for quantifier
determiners. This makes the parallel between quantifier monotonicity and
attitude monotonicity explicit: both are instances of the same algebraic
classification.

Per-verb monotonicity data lives on `VerbCore.complementSig` in the
fragment lexicon (`Fragments/English/Predicates/Verbal.lean`), not here.
This file provides only the derivation logic: given an `EntailmentSig`,
what follows about conjunction distribution and neg-raising?

## Key contributions

1. **Conjunction distribution derived from EntailmentSig**: An attitude verb
   distributes over conjunction iff its complement signature refines `.mono`.

2. **Neg-raising from monotonicity + EMP**: Bondarenko & Elliott derive
   neg-raising from upward monotonicity plus an excluded-middle
   presupposition (EMP), NOT from veridicality (as in `NegRaising.lean`).
   Both derivations agree on standard doxastic verbs.

3. **Mereological grounding**: The conjunction distribution theorem
   (`mono_att_distrib_and_iff` in `Truthmaker.Basic`) proves that the
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
-- § 1. Conjunction Distribution from Signature
-- ════════════════════════════════════════════════════

/-- An attitude distributes over conjunction iff its complement signature
    refines `.mono` (upward monotone). This includes: `.all`, `.addMult`,
    `.additive`, `.mult`, and `.mono` itself.

    Note: `.mult` (multiplicative) distributes over ∧ by definition —
    f(A ∧ B) = f(A) ∧ f(B). The `.mono` refinement captures this. -/
def distribOverConj (sig : EntailmentSig) : Bool :=
  sig.refines .mono

-- Verification: signatures that distribute over conjunction
#guard distribOverConj .mono       -- upward monotone
#guard distribOverConj .mult       -- multiplicative (∧-distributing but not ∨)
#guard distribOverConj .additive   -- additive
#guard distribOverConj .addMult    -- both additive and multiplicative
#guard distribOverConj .all        -- top of lattice

-- Signatures that do NOT distribute
#guard !distribOverConj .anti      -- antitone
#guard !distribOverConj .antiAdd   -- anti-additive
#guard !distribOverConj .antiMult     -- anti-multiplicative
#guard !distribOverConj .antiAddMult  -- anti-additive + anti-multiplicative

-- ════════════════════════════════════════════════════
-- § 2. Neg-Raising: Monotonicity + EMP Account
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
-- § 3. Bridge: Two Routes to Neg-Raising Agree
-- ════════════════════════════════════════════════════

/-- The veridicality and monotonicity accounts agree on all standard
    doxastic verbs: both predict neg-raising for non-veridical monotone
    verbs and no neg-raising for veridical ones.

    They could diverge for hypothetical verbs that are:
    - Non-monotone but non-veridical → veridicality allows, monotonicity blocks

    Currently both routes agree because all non-veridical doxastic verbs
    in the lexicon are also monotone. -/
theorem negRaising_accounts_agree (v : Veridicality) :
    negRaisingFromMono .mono v = negRaisingAvailable v := by
  cases v <;> rfl

-- ════════════════════════════════════════════════════
-- § 4. Mereological Grounding
-- ════════════════════════════════════════════════════

/-- The truthmaker conjunction distribution theorem
    (`Truthmaker.mono_att_distrib_and_iff`) provides the semantic *why*
    for the monotonicity classification.

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
