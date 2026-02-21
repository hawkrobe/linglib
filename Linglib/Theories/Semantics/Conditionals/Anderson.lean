import Linglib.Theories.Semantics.Conditionals.Iatridou
import Linglib.Theories.Semantics.Reference.Kaplan

/-!
# Anderson Conditionals: Crosslinguistic Marking Strategies
@cite{mizuno-2024}

Formalizes the crosslinguistic typology of Anderson conditionals from
Mizuno (2024) "Strategies for Anderson Conditionals", *Semantics and
Pragmatics* 17(8): 1–14.

## Anderson Conditionals

Anderson conditionals (Anderson 1951) are counterfactuals where the speaker
believes the antecedent is actually true:

> "If Jones had taken arsenic, he would have shown exactly the symptoms
>  he is *actually* showing."

The speaker believes Jones *did* take arsenic, and uses the conditional
to argue from the observed symptoms to that conclusion. The challenge:
how does the consequent describe the actual world when the conditional
morphology shifts evaluation to counterfactual alternatives?

## Two Marking Strategies

Mizuno identifies two crosslinguistic strategies:

- **X-marking** (English): Counterfactual morphology (fake past) in the
  antecedent shifts the evaluation world away from the actual world,
  producing modal ExclF (Iatridou 2000). "Actually" in the consequent
  recovers the actual world via Kaplanian origin access.

- **O-marking** (Japanese): Non-Past / Historical Present in the consequent.
  No counterfactual morphology, so no ExclF — the evaluation world remains
  the actual world. The consequent directly describes actuality.

## Connection to Existing Infrastructure

- **X-marking**: `subjShift_produces_modal_exclF` (Iatridou) produces the
  world shift; `opActually_shift_invariant` (Kaplan) recovers the origin.
- **O-marking**: `root_no_modal_exclF` (Iatridou) — no shift means no ExclF,
  so the actual world is directly accessible.

## FLV Correlation

The availability of X-marking for Anderson conditionals correlates with its
availability for Future Less Vivid conditionals (Iatridou 2000, §4.2):
- English: X-marking available for both Anderson and FLV
- Japanese: X-marking available for neither (Ogihara 2014)
- Mandarin: X-marking available for neither

## References

- Mizuno, T. (2024). Strategies for Anderson conditionals.
  *Semantics and Pragmatics* 17(8): 1–14.
- Anderson, A. R. (1951). A note on subjunctive and counterfactual
  conditionals. *Analysis* 12(2): 35–38.
-/

namespace Semantics.Conditionals.Anderson

open Core.Context (KContext ContextTower ContextShift)
open Semantics.Conditionals.Iatridou (ExclF)
open Semantics.Reference.Kaplan (opActually_access opActually_shift_invariant)
open Semantics.Mood (subjShift)

-- ════════════════════════════════════════════════════════════════
-- § Marking Strategy Typology
-- ════════════════════════════════════════════════════════════════

/-- The two crosslinguistic marking strategies for Anderson conditionals.

Mizuno (2024): languages differ in whether they use X-marking (counterfactual
morphology) or O-marking (indicative/non-past) to express Anderson conditionals.
English requires X-marking; Japanese requires O-marking. -/
inductive MarkingStrategy where
  /-- X-marking: CF morphology in antecedent + "actually" recovers actual world.
      English: "If Jones *had taken* arsenic, he *would have shown* exactly
      the symptoms he is *actually* showing." -/
  | xMarking
  /-- O-marking: Non-Past/Historical Present — no CF morphology, actual world
      directly accessible.
      Japanese: "Jones-ga ... nom-*eba*, ... mise-*ru* (hazuda)." -/
  | oMarking
  deriving DecidableEq, Repr, BEq

-- ════════════════════════════════════════════════════════════════
-- § Strategy Properties
-- ════════════════════════════════════════════════════════════════

/-- X-marking strategy uses counterfactual morphology; O-marking does not.

    This is the single primitive property of marking strategies. All other
    properties (ExclF production, "actually" requirement, FLV availability)
    are derived from it — they are `abbrev`s equal to `hasXMarking`, with
    docstrings explaining *why* the correlation holds.

    Both strategies access the actual world in the consequent — X-marking
    via Kaplanian "actually" (origin access through shifted tower), O-marking
    directly (no world shift). This is universal, not a distinguishing
    property. -/
def MarkingStrategy.hasXMarking : MarkingStrategy → Bool
  | .xMarking => true
  | .oMarking => false

/-- X-marking produces ExclF; O-marking does not.

    X-marking is counterfactual morphology: `subjShift` changes the evaluation
    world, creating modal ExclF (origin.world ≠ innermost.world). O-marking
    leaves the tower at the root, so no ExclF arises.

    Definitionally equal to `hasXMarking` — the correlation holds because
    ExclF is the *mechanism* of X-marking. -/
abbrev MarkingStrategy.producesExclF (s : MarkingStrategy) : Bool := s.hasXMarking

/-- X-marking requires "actually" to recover the actual world; O-marking
    does not.

    When X-marking produces ExclF, the actual world is excluded from the
    shifted evaluation. "Actually" (Kaplanian origin access) is needed to
    reach back through the shift. With O-marking, the evaluation world IS
    the actual world, so no recovery operator is needed.

    Definitionally equal to `hasXMarking` — the "actually" requirement is
    a direct consequence of ExclF. -/
abbrev MarkingStrategy.requiresActuallyOperator (s : MarkingStrategy) : Bool := s.hasXMarking

-- ════════════════════════════════════════════════════════════════
-- § Tower-Level Theorems
-- ════════════════════════════════════════════════════════════════

variable {W : Type*} {E : Type*} {P : Type*} {T : Type*}

/-- X-marking produces modal ExclF: subjunctive shift changes the world,
    creating world exclusion (origin.world ≠ innermost.world).

    This is why English Anderson conditionals use CF morphology:
    the X-marking shifts the evaluation world away from the actual world,
    setting up the need for "actually" to recover it.

    Wraps `Iatridou.subjShift_produces_modal_exclF`. -/
theorem xMarking_produces_exclF (c : KContext W E P T) (w' : W) (t' : T)
    (h : w' ≠ c.world) :
    ExclF .modal ((ContextTower.root c).push (subjShift w' t')) :=
  Iatridou.subjShift_produces_modal_exclF c w' t' h

/-- "Actually" recovers the origin world even after X-marking shift.

    In an Anderson conditional with X-marking, the CF morphology pushes
    the tower (shifting the evaluation world). But "actually" — being a
    Kaplanian indexical with `depth = .origin` — resolves to the speech-act
    world regardless. This is what makes Anderson conditionals felicitous
    despite the counterfactual morphology: "actually" reaches through the
    CF layer to access the actual world.

    Wraps `Kaplan.opActually_shift_invariant`. -/
theorem actually_recovers_origin_after_shift
    (t : ContextTower (KContext W E P T)) (σ : ContextShift (KContext W E P T)) :
    opActually_access.resolve (t.push σ) = opActually_access.resolve t :=
  opActually_shift_invariant t σ

/-- O-marking has no modal ExclF: without CF morphology, the tower stays
    at the root, and origin.world = innermost.world.

    This is why Japanese Anderson conditionals use O-marking: no world shift
    means the actual world is directly accessible without "actually".

    Wraps `Iatridou.root_no_modal_exclF`. -/
theorem oMarking_no_exclF (c : KContext W E P T) :
    ¬ ExclF .modal (ContextTower.root c) :=
  Iatridou.root_no_modal_exclF c

/-- X-marking is available for FLV where it's available for Anderson.

    Mizuno (2024, §4.2): "the availability of X-marking for Anderson
    conditionals and the availability of X-marking for Future Less Vivid
    conditionals seem to stand or fall together."

    English (X-marking for Anderson) → X-marking available for FLV.
    Japanese (O-marking for Anderson) → X-marking NOT available for FLV.

    Definitionally equal to `hasXMarking` — an empirical generalization
    over English, Japanese, and Mandarin, not a logical necessity. -/
abbrev MarkingStrategy.flvXMarkingAvailable (s : MarkingStrategy) : Bool := s.hasXMarking

end Semantics.Conditionals.Anderson
