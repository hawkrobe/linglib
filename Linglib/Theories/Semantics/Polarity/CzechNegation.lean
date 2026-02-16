/-!
# Czech Three-Way Negation: Core Types

Pure type definitions for the three-way negation distinction in Czech polar
questions (Staňková 2026). Extracted from `Phenomena.Negation.CzechThreeWayNeg`
so that Fragment files can reference these types without importing empirical data.

## References

- Staňková, V. (2026). A three-way distinction of negation interpretation in Czech.
- Zeijlstra, H. (2004). Sentential Negation and Negative Concord. LOT.
-/

namespace Semantics.Polarity.CzechNegation

/-- The three LF positions for negation in Czech PQs (Staňková 2026 §3, ex. 16).

  [CP ... [PolP ne-    [ModP ne-     [TP ne-    ]]]]
              OUTER          MEDIAL       INNER
-/
inductive NegPosition where
  /-- Inner negation: in TP, propositional ¬p. Narrow scope.
      Licenses NCIs by Agree, licenses NPIs. Standard sentential negation. -/
  | inner
  /-- Medial negation: in ModP, scopes over □_ev. Wide scope but syntactically low.
      Non-propositional: part of evidential bias presupposition. -/
  | medial
  /-- Outer negation: in PolP, FALSUM operator. Widest scope.
      Maps to high negation (VSO word order). Obligatorily focused. -/
  | outer
  deriving DecidableEq, BEq, Repr

/-- Diagnostics that distinguish the three negation readings (Table 1). -/
inductive Diagnostic where
  /-- ne- outscopes a PPI like *nějaký* 'some.DET.PPI' -/
  | ppiOutscoping
  /-- Negative concord item like *žádný* 'no.DET.NCI' is licensed -/
  | nciLicensed
  /-- Particle *náhodou* 'by chance' is compatible -/
  | nahodou
  /-- Particle *ještě* 'yet/still' is compatible (with telic predicates + neg) -/
  | jeste
  /-- Particle *fakt* 'really' is compatible -/
  | fakt
  deriving DecidableEq, BEq, Repr

/-- Table 1 from Staňková (2026 §3): compatibility of each negation reading
with polarity items and particles.

This is the core empirical fingerprint: each negation position has a unique
Boolean signature across the five diagnostics. -/
def licenses : NegPosition → Diagnostic → Bool
  | .outer,  .ppiOutscoping => true
  | .outer,  .nciLicensed   => false
  | .outer,  .nahodou       => true
  | .outer,  .jeste         => false
  | .outer,  .fakt          => false
  | .medial, .ppiOutscoping => true
  | .medial, .nciLicensed   => false
  | .medial, .nahodou       => false
  | .medial, .jeste         => false
  | .medial, .fakt          => true
  | .inner,  .ppiOutscoping => false
  | .inner,  .nciLicensed   => true
  | .inner,  .nahodou       => false
  | .inner,  .jeste         => true
  | .inner,  .fakt          => true

end Semantics.Polarity.CzechNegation
