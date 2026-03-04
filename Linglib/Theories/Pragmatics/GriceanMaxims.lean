/-!
# Gricean Maxims of Conversation

@cite{grice-1975}

Logic and Conversation. In P. Cole & J.L. Morgan (eds.), *Syntax and
Semantics 3: Speech Acts*, 41–58. Academic Press.

## Design

The Cooperative Principle and four maxims are formalized as types, not
as behavioral predictions. Behavioral predictions (e.g., "speakers
maximize informativity") belong in the implementing frameworks — RSA
formalizes Quantity via `s1Score`, NeoGricean via the Standard Recipe,
Dale & Reiter via incremental attribute selection. Study files that
test the maxims directly (e.g., @cite{engelhardt-etal-2006}) import
this module.

Linking theorems connecting maxims to specific frameworks belong in
`Comparisons/`.

## The Quantity Maxim

Grice's Quantity maxim has two sub-maxims:

1. **Q1**: "Make your contribution as informative as is required
   (for the current purposes of the exchange)."
2. **Q2**: "Do not make your contribution more informative than is
   required."

@cite{engelhardt-etal-2006} showed these behave asymmetrically:
Q1 violations (under-description) are penalized in both production
and explicit judgment; Q2 violations (over-description) are produced
frequently, tolerated explicitly, but detected implicitly via
processing costs.
-/

namespace Theories.Pragmatics.GriceanMaxims

-- ============================================================================
-- § The Cooperative Principle and Maxims
-- ============================================================================

/-- The four Gricean maxims of conversation. -/
inductive Maxim where
  /-- Make your contribution as informative as is required;
      do not make it more informative than is required. -/
  | quantity
  /-- Do not say what you believe to be false;
      do not say that for which you lack adequate evidence. -/
  | quality
  /-- Be relevant. -/
  | relation
  /-- Avoid obscurity of expression; avoid ambiguity;
      be brief; be orderly. -/
  | manner
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- § Quantity Sub-Maxims
-- ============================================================================

/-- The Quantity maxim decomposes into two independent sub-maxims.
    Grice (1975) states both; @cite{engelhardt-etal-2006} showed
    empirically that they are independently violable. -/
inductive QuantitySubmaxim where
  /-- "Make your contribution as informative as is required
      (for the current purposes of the exchange)." -/
  | Q1
  /-- "Do not make your contribution more informative than is
      required." -/
  | Q2
  deriving DecidableEq, BEq, Repr

/-- Direction of a Quantity violation. -/
inductive QuantityViolation where
  /-- Too little information (violates Q1). E.g., "the apple" when
      two apples are present. -/
  | underInformative
  /-- Too much information (violates Q2). E.g., "the red apple" when
      only one apple is present. -/
  | overInformative
  deriving DecidableEq, BEq, Repr

/-- Which sub-maxim a violation direction targets. -/
def QuantityViolation.submaxim : QuantityViolation → QuantitySubmaxim
  | .underInformative => .Q1
  | .overInformative  => .Q2

/-- The two violation directions target different sub-maxims. -/
theorem violations_independent :
    QuantityViolation.underInformative.submaxim ≠
    QuantityViolation.overInformative.submaxim := by decide

end Theories.Pragmatics.GriceanMaxims
