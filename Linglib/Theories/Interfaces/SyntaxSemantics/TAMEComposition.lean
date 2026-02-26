import Linglib.Theories.Syntax.Minimalism.Core.ClauseSpine
import Linglib.Theories.Semantics.Tense.Evidential

/-!
# Compositional TAME Bridge

Compositional bridge connecting `ClauseSpine` (syntax) → morphological realization →
`TAMEEntry` (semantics). The key operation is `composeTAME`, which walks a clause
spine bottom-up and collects EP/UP constraints contributed by each projected head.

## Design

Each functional head optionally contributes an `EPCondition` and/or `UPCondition`.
The composition rule is **highest wins**: the highest head in the spine that
contributes a constraint determines the value for that dimension. This models
cartographic scoping — higher heads override lower ones.

## Application

Stojković (2026) shows that the South Slavic L-participle serves different
grammatical functions (past tense vs. evidential) across SC and Bulgarian,
depending on its syntactic position. The `composeTAME` functor derives the
TAME interpretation from the spine structure, making the cross-linguistic
difference fall out from which head the L-form realizes.

## References

- Stojković, S. (2026). L-participle variation in South Slavic.
- Cinque, G. (1999). Adverbs and Functional Heads. OUP.
- Cumming, S. (2026). Tense and evidence. *L&P* 49:153–175.
-/

namespace Theories.Interfaces.SyntaxSemantics.TAMEComposition

open Minimalism
open Semantics.Tense.Evidential

-- ════════════════════════════════════════════════════
-- § 1. Per-Head Semantic Contribution
-- ════════════════════════════════════════════════════

/-- Semantic contribution of a single functional head to the TAME system.
    Each head optionally contributes an evidential perspective (EP) constraint
    and/or an utterance perspective (UP) constraint. -/
structure HeadSemantics where
  /-- Evidential perspective contribution (T vs A) -/
  ep : Option EPCondition := none
  /-- Utterance perspective contribution (T vs S) -/
  up : Option UPCondition := none
  deriving DecidableEq, Repr, BEq

/-- Head semantics with no contribution. -/
def HeadSemantics.silent : HeadSemantics := ⟨none, none⟩

-- ════════════════════════════════════════════════════
-- § 2. Morphological Exponents
-- ════════════════════════════════════════════════════

/-- Morphological exponent function: maps each Cat to the surface form
    (if any) that realizes it in a given language/construction. -/
def Exponents := Cat → Option String

-- ════════════════════════════════════════════════════
-- § 3. TAME Result
-- ════════════════════════════════════════════════════

/-- The composed TAME result after walking a clause spine. -/
structure TAMEResult where
  /-- Composed evidential perspective constraint -/
  ep : Option EPCondition := none
  /-- Composed utterance perspective constraint -/
  up : Option UPCondition := none
  deriving DecidableEq, Repr, BEq

-- ════════════════════════════════════════════════════
-- § 4. Composition
-- ════════════════════════════════════════════════════

/-- Merge a head's contribution into the running result.
    **Last-write-wins**: if the head contributes a constraint, it overrides
    whatever was accumulated so far. This models cartographic scoping —
    higher heads in the spine override lower ones. -/
def mergeHead (acc : TAMEResult) (hs : HeadSemantics) : TAMEResult where
  ep := hs.ep.orElse (fun _ => acc.ep)
  up := hs.up.orElse (fun _ => acc.up)

/-- Compose TAME semantics across a clause spine (bottom-up).
    Walks the projected heads from lowest to highest, accumulating
    EP/UP constraints. The highest contributing head wins per dimension. -/
def composeTAME (spine : ClauseSpine) (headSem : Cat → HeadSemantics) : TAMEResult :=
  spine.projectedHeads.foldl (fun acc c => mergeHead acc (headSem c)) ⟨none, none⟩

-- ════════════════════════════════════════════════════
-- § 5. Bridge to TAMEEntry
-- ════════════════════════════════════════════════════

/-- Convert a composed result to a `TAMEEntry`, defaulting unconstrained
    dimensions to `.unconstrained`. -/
def TAMEResult.toTAMEEntry (r : TAMEResult) (label : String) : TAMEEntry where
  label := label
  ep := r.ep.getD .unconstrained
  up := r.up.getD .unconstrained

-- ════════════════════════════════════════════════════
-- § 6. Surface Forms
-- ════════════════════════════════════════════════════

/-- Collect non-none exponents from a spine — the observable morpheme sequence. -/
def surfaceForms (spine : ClauseSpine) (exps : Exponents) : List String :=
  spine.projectedHeads.filterMap exps

-- ════════════════════════════════════════════════════
-- § 7. TAME Derivation (bundled record)
-- ════════════════════════════════════════════════════

/-- A complete TAME derivation: spine + per-head semantics + exponents. -/
structure TAMEDerivation where
  /-- The clause spine -/
  spine : ClauseSpine
  /-- Per-head semantic contribution -/
  headSem : Cat → HeadSemantics
  /-- Per-head morphological realization -/
  exponents : Exponents

/-- Compose the derivation's TAME result. -/
def TAMEDerivation.compose (d : TAMEDerivation) : TAMEResult :=
  composeTAME d.spine d.headSem

/-- Get the surface forms of a derivation. -/
def TAMEDerivation.forms (d : TAMEDerivation) : List String :=
  surfaceForms d.spine d.exponents

end Theories.Interfaces.SyntaxSemantics.TAMEComposition
