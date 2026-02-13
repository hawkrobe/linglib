/-
How monotonicity affects scalar implicatures: in UE contexts scales are
preserved; in DE contexts scales reverse, blocking "some -> not all".
Reference: van Benthem (1986), Ladusaw (1980), Barwise & Cooper (1981).
-/

import Linglib.Theories.TruthConditional.Sentence.Entailment.Basic
import Linglib.Core.HornScale

namespace TruthConditional.Sentence.Entailment.ScaleInteraction

open TruthConditional.Sentence.Entailment
open Core.Scale

/-- Scale reversal: UE alternatives of "some" are [most, all]; DE alternatives are [none]. -/
theorem scale_alternatives_reverse :
    scalarAlternativesInContext Quantifiers.quantScale .some_ .upward = [.most, .all] ∧
    scalarAlternativesInContext Quantifiers.quantScale .some_ .downward = [.none_] := by
  native_decide

/-- DE blocks "some -> not all" because "all" is not a stronger alternative in DE. -/
theorem de_blocks_scalar_implicature :
    -- In UE, alternatives include "all"
    scalarAlternativesInContext Quantifiers.quantScale .some_ .upward = [.most, .all] ∧
    -- In DE, alternatives do NOT include "all"
    scalarAlternativesInContext Quantifiers.quantScale .some_ .downward = [.none_] := by
  native_decide


end TruthConditional.Sentence.Entailment.ScaleInteraction
