import Linglib.Theories.Semantics.Dynamic.Bilateral.FreeChoice

/-!
# Elliott & Sudo (2025): Free Choice with Anaphora
@cite{elliott-sudo-2025}

Bilateral Update Semantics (BUS) applied to bathroom disjunctions.

This study file derives the concrete FC-with-anaphora inference
from the general modal disjunction operator defined in
`Theories/Semantics/Dynamic/Bilateral/FreeChoice.lean`.

## Key results

The paper's general `disjPos1`/`disjPos2` (eq. 92) simplify for the
bathroom case (eqs. 93-94):
- `disjPos1` ⊆ `s[∃ₓB(x)]⁻` (eq. 93)
- `disjPos2` ⊆ `s[∃ₓB(x)]⁺[F(x)]⁺` (eq. 94)

Under these simplification conditions, the general FC preconditions
(both disjPos nonempty) yield the bathroom inference:
1. It's possible there's no bathroom
2. It's possible there's a bathroom in a funny place

-/

namespace ElliottSudo2025

open Semantics.Dynamic.Core
open Semantics.Dynamic.BUS.FreeChoice
open Classical

variable {W E : Type*}

-- ============================================================================
-- Section 1: Bathroom configuration
-- ============================================================================

/--
The bathroom disjunction configuration.

"Either there's no bathroom or it's in a funny place"
-/
structure BathroomConfig (W E : Type*) where
  /-- The existential: ∃x.bathroom(x) -/
  bathroom : BilateralDen W E
  /-- The predicate on x: funny-place(x) -/
  funnyPlace : BilateralDen W E
  /-- The variable bound by the existential -/
  x : Nat

/--
The bathroom disjunction sentence: ¬∃x.bathroom(x) ∨ᶠᶜ funny-place(x)
-/
def bathroomSentence (cfg : BathroomConfig W E) : BilateralDen W E :=
  (BilateralDen.neg cfg.bathroom) ∨ᶠᶜ cfg.funnyPlace

-- ============================================================================
-- Section 2: FC with anaphora (general form)
-- ============================================================================

/--
DNE as structural equality: ¬¬φ = φ.
-/
theorem anaphora_via_dne (cfg : BathroomConfig W E) :
    BilateralDen.neg (BilateralDen.neg cfg.bathroom) = cfg.bathroom := by
  simp only [BilateralDen.neg_neg]

/--
FC with anaphora: the bathroom disjunction inference.

The paper's eqs. 93-94 show that for bathroom disjunctions, the general
`disjPos1`/`disjPos2` (eq. 92) simplify so that:
- `disjPos1` reduces to `bath.negative s` (possible there's no bathroom)
- `disjPos2` reduces to `funnyPlace.positive (bath.positive s)` (possible
  there's a bathroom in a funny place)

The hypotheses `h_dp1` and `h_dp2` encode these simplifications: the
general forms are contained in the simplified forms, so nonemptiness
of the general forms transfers to the simplified forms.

These hold when `funnyPlace` is eliminative (output ⊆ input), as is the
case for atomic predicates (`pred1`).
-/
theorem fc_with_anaphora (cfg : BathroomConfig W E) (s : InfoState W E)
    (h_poss : possible (bathroomSentence cfg) s)
    (h_dp1 : disjPos1 (BilateralDen.neg cfg.bathroom) cfg.funnyPlace s ⊆
             cfg.bathroom.negative s)
    (h_dp2 : disjPos2 (BilateralDen.neg cfg.bathroom) cfg.funnyPlace s ⊆
             cfg.funnyPlace.positive (cfg.bathroom.positive s)) :
    (cfg.bathroom.negative s).Nonempty ∧
    (cfg.funnyPlace.positive (cfg.bathroom.positive s)).Nonempty := by
  obtain ⟨⟨p1, hp1⟩, ⟨p2, hp2⟩⟩ := fc_preconditions _ _ s h_poss
  exact ⟨⟨p1, h_dp1 hp1⟩, ⟨p2, h_dp2 hp2⟩⟩

-- ============================================================================
-- Section 3: Concrete example
-- ============================================================================

inductive BathroomWorld where
  | noBathroom
  | bathroomNormal
  | bathroomFunny
  deriving DecidableEq, Repr

inductive BathroomEntity where
  | theBathroom
  deriving DecidableEq, Repr

def isBathroom : BathroomEntity → BathroomWorld → Bool
  | .theBathroom, .noBathroom => false
  | .theBathroom, _ => true

def inFunnyPlace : BathroomEntity → BathroomWorld → Bool
  | .theBathroom, .bathroomFunny => true
  | _, _ => false

def exampleBathroomConfig : BathroomConfig BathroomWorld BathroomEntity :=
  { bathroom := BilateralDen.exists_ 0 Set.univ (BilateralDen.pred1 isBathroom 0)
  , funnyPlace := BilateralDen.pred1 inFunnyPlace 0
  , x := 0 }

end ElliottSudo2025
