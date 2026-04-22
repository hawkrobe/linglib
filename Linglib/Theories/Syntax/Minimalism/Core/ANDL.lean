import Linglib.Theories.Syntax.Minimalism.Core.Features
import Linglib.Core.Lexical.ExpressiveModifier

/-!
# Minimalist Analysis of ANDL Wh-Modifiers

@cite{chou-2012} @cite{huang-ochi-2004} @cite{merchant-2002}
@cite{chan-shen-2026}

The Minimalist (POV-feature) analysis of aggressively non-D-linked
(ANDL) wh-modifiers. The theory-neutral lexical entry lives in
`Core/Lexical/ExpressiveModifier.lean`; this file adds the
framework-specific syntactic apparatus: an unvalued POV feature [*ud*]
on the modifier, a valued [+d] POV operator merged in matrix C, and
Spec-head Agree as the licensing relation.

## The analysis (@cite{chou-2012}, adapted by @cite{chan-shen-2026})

1. ANDL modifier (e.g., *the-hell*) carries an **unvalued** POV feature
   [*ud*]: a probe needing valuation.
2. Matrix C carries a **valued** POV operator [+d]: a goal.
3. Feature checking happens in Spec-head configuration in matrix CP.
4. Therefore the modifier must reach matrix Spec-CP. For parasitic
   modifiers (English/Singlish *the-hell*), this requires the wh-host
   to reach matrix Spec-CP. For independent modifiers (Mandarin *daodi*),
   the modifier moves on its own.
-/

namespace Minimalism.ANDL

open Core.Lexical.ExpressiveModifier (ExpressiveWhModifier ANDLMovementType
  ANDLHostPosition Licensed)

-- ============================================================================
-- §1. POV feature inventory
-- ============================================================================

/-- The unvalued POV feature [*ud*] borne by ANDL modifiers
    (@cite{chou-2012}). A probe seeking a [+d] goal in a Spec-head
    relation. -/
def povUnvaluedFeature : GramFeature := .unvalued (.pov true)

/-- The valued POV feature [+d] on the matrix-C POV operator. The goal
    that values [*ud*]. -/
def povOperatorFeature : GramFeature := .valued (.pov true)

/-- The probe-goal pair matches under `featuresMatch`: same feature
    type, opposite valuation status — the prerequisite for Agree. -/
theorem pov_probe_goal_match :
    featuresMatch povUnvaluedFeature povOperatorFeature = true := rfl

/-- The ANDL modifier's POV feature is unvalued (a probe). -/
theorem andl_pov_unvalued :
    povUnvaluedFeature.isUnvalued = true := rfl

/-- The matrix-C POV operator carries a valued feature (a goal). -/
theorem pov_operator_valued :
    povOperatorFeature.isValued = true := rfl

-- ============================================================================
-- §2. Minimalist licensing predicate
-- ============================================================================

/-- Minimalist licensing: an ANDL modifier is licensed iff a configuration
    obtains in which `povUnvaluedFeature` checks against `povOperatorFeature`
    in matrix Spec-CP. Operationally:

    - For a **parasitic** modifier, the wh-host must reach matrix Spec-CP
      (so that the adjoined modifier reaches Spec-CP with it).
    - For an **independent** modifier, the modifier moves to matrix Spec-CP
      on its own — host reachability is irrelevant.

    This is the Minimalist instantiation of the theory-neutral
    `Core.Lexical.ExpressiveModifier.Licensed`. The Minimalist version
    doesn't add a separate condition — it identifies "modifier reaches
    Spec-CP" as the structural realization of "scope position reached". -/
abbrev LicensedMinimalist (m : ExpressiveWhModifier)
    (whHostReachesMatrixSpecCP : Prop) : Prop :=
  Licensed m whHostReachesMatrixSpecCP

end Minimalism.ANDL
