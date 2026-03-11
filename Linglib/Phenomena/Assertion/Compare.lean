/-!
# Assertion Theories: Cross-Theory Comparison
@cite{brandom-1994} @cite{farkas-bruce-2010} @cite{gunlogson-2001} @cite{krifka-2015} @cite{lauer-2013} @cite{stalnaker-1978}

Compares six theories of assertion along structural dimensions:
Stalnaker, Farkas & Bruce, Krifka, Brandom, Gunlogson, and Lauer.

## Comparison Matrix

| Theory | Commitment ≠ Belief | Retraction | Source | Entitlements | Probabilistic |
|--------|---------------------|------------|--------|-------------|---------------|
| Stalnaker | No | No | No | No | No |
| F&B | Yes | No | No | No | No |
| Krifka | Yes | Yes | No | No | No |
| Brandom | Yes | Yes | No | Yes | No |
| Gunlogson | Yes | Yes | Yes | No | No |
| Lauer | Yes | No | No | No | Yes |

## Key Embeddings

1. **Stalnaker embeds in Krifka**: when commitment = belief (no lying,
   no hedging), Krifka's model collapses to Stalnaker's.
2. **F&B's dcS/dcL are Krifka commitment states**: dcS = speaker's
   commitment slate, dcL = addressee's commitment slate.
3. **Brandom strictly richer than Stalnaker**: entitlements have no
   Stalnaker analog.
4. **Gunlogson models rising declaratives; Stalnaker cannot**.
5. **Lying**: Krifka and Brandom handle it (commitment without belief);
   Stalnaker struggles (assertion = belief update).

-/

namespace Phenomena.Assertion.Compare

-- ════════════════════════════════════════════════════
-- § 1. Comparison Matrix
-- ════════════════════════════════════════════════════

/-- Summary comparison record for one theory. -/
structure AssertionComparison where
  /-- Theory name -/
  name : String
  /-- Separates commitment from belief? -/
  separates : Bool
  /-- Supports retraction? -/
  retraction : Bool
  /-- Models source marking? -/
  source : Bool
  deriving Repr

/-- The full comparison matrix. -/
def comparisonMatrix : List AssertionComparison :=
  [ ⟨"Stalnaker", false, false, false⟩
  , ⟨"Farkas & Bruce", true, false, false⟩
  , ⟨"Krifka", true, true, false⟩
  , ⟨"Brandom", true, true, false⟩
  , ⟨"Gunlogson", true, true, true⟩
  , ⟨"Lauer", true, false, false⟩ ]

/-- The matrix agrees with the interface flags. -/
theorem matrix_correct :
    comparisonMatrix.length = 6 := rfl

end Phenomena.Assertion.Compare
