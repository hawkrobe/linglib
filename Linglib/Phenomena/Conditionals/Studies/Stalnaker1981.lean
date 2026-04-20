import Mathlib.Data.Finset.Card
import Linglib.Theories.Semantics.Conditionals.Counterfactual

/-!
# Stalnaker 1981 @cite{stalnaker-1981}

A Defense of Conditional Excluded Middle. In Harper, Stalnaker & Pearce
(eds.), *Ifs*, 87--104. Springer.

## Core Contributions

1. **CEM is valid** under selection-function semantics + supervaluation
2. **Uniqueness as vagueness**: ties in similarity are semantic
   indeterminacy, handled by supervaluation rather than by abandoning
   uniqueness
3. **`Might` counterfactuals**: CEM + Lewis's definition of `might` as
   ¬(would ¬B) collapses might into would. Stalnaker treats `might` as
   genuine epistemic possibility, restoring the distinction via
   supervaluation over ties.
4. **Distribution principle**: (A □→ (B∨C)) ⊃ ((A □→ B) ∨ (A □→ C))
   holds for selection semantics with uniqueness, fails for universal

## Integration

- CEM: `cem_selectional` (Counterfactual.lean)
- Supervaluation bridge: `selectional_as_supervaluation` (Counterfactual.lean)
- Might collapse: `lewis_might_eq_would_cem`, `lewis_might_eq_would_singleton`
- Distribution: `distribution_selectional`, `distribution_fails_universal`
- This file: concrete worked examples (Bizet--Verdi, might/would, scope)
-/

namespace Stalnaker1981

open Semantics.Conditionals (SimilarityOrdering)
open Semantics.Conditionals.Counterfactual
open Core.Duality (Truth3)

-- ════════════════════════════════════════════════════
-- § 1. The Bizet–Verdi Example: Indeterminacy from Ties
-- ════════════════════════════════════════════════════

/-!
## The Bizet--Verdi Example

The example originates with @cite{quine-1950}.

"If Bizet and Verdi had been compatriots, Bizet would have been Italian."
"If Bizet and Verdi had been compatriots, Verdi would have been French."

On Lewis's analysis, both are false (each individual CF fails because
not all closest worlds satisfy the consequent). On Stalnaker's, both are
*indeterminate* — the selection function faces a genuine tie between the
both-Italian and both-French worlds.

CEM still holds: for each conditional, the disjunction φ ∨ ¬φ is not
false (it is gap ∨ gap under supervaluation). But under universal
semantics CEM *fails*: both φ and ¬φ are false.
-/

section BizetVerdi

/-- Three possible worlds for the Bizet--Verdi scenario. -/
inductive BVWorld where
  | actual       -- Neither compatriots
  | bothItalian  -- Bizet becomes Italian
  | bothFrench   -- Verdi becomes French
  deriving Repr, DecidableEq

instance : Fintype BVWorld where
  elems := {.actual, .bothItalian, .bothFrench}
  complete x := by cases x <;> simp

/-- Similarity ordering for Bizet--Verdi: actual is strictly closest to
    itself (centering), and bothItalian and bothFrench are equally close
    (mutual ≤). This models the tie that Stalnaker's supervaluation
    handles. -/
def bvSim : SimilarityOrdering BVWorld := .ofBool
  (fun | .actual, .actual, _ => true
       | .actual, .bothItalian, .bothFrench => true
       | .actual, .bothFrench, .bothItalian => true
       | _, w₁, w₂ => w₁ == w₂)
  (by decide) (by decide)

/-- The antecedent: Bizet and Verdi are compatriots. -/
def compatriots : BVWorld → Prop
  | .bothItalian | .bothFrench => True
  | .actual => False

instance : DecidablePred compatriots := fun w => by cases w <;> unfold compatriots <;> infer_instance

/-- The consequent: Bizet is Italian. -/
def bizetItalian : BVWorld → Prop
  | .bothItalian => True
  | _ => False

instance : DecidablePred bizetItalian := fun w => by cases w <;> unfold bizetItalian <;> infer_instance

/-- The consequent: Verdi is French. -/
def verdiFrench : BVWorld → Prop
  | .bothFrench => True
  | _ => False

instance : DecidablePred verdiFrench := fun w => by cases w <;> unfold verdiFrench <;> infer_instance

/-- "If B&V had been compatriots, Bizet would have been Italian" is
    indeterminate: some closest compatriot-worlds make it true (.bothItalian),
    others false (.bothFrench). -/
theorem bizet_italian_indeterminate :
    selectionalCounterfactual bvSim compatriots bizetItalian .actual
    = .gap := by decide

/-- "If B&V had been compatriots, Verdi would have been French" is also
    indeterminate, for the same reason. -/
theorem verdi_french_indeterminate :
    selectionalCounterfactual bvSim compatriots verdiFrench .actual
    = .gap := by decide

/-- **CEM holds for Bizet--Verdi under selectional semantics.** Derived
    from the generic `cem_selectional` — concrete examples inherit from
    the theory rather than being independently verified. -/
theorem bizet_verdi_cem :
    let φ := selectionalCounterfactual bvSim compatriots bizetItalian .actual
    let ψ := selectionalCounterfactual bvSim compatriots (¬ bizetItalian ·) .actual
    Truth3.join φ ψ ≠ .false :=
  cem_selectional bvSim compatriots bizetItalian .actual

/-- **CEM fails under universal semantics.** Lewis's theory makes both
    "would B" and "would ¬B" false — so their disjunction is false.
    This is the central empirical divergence. -/
theorem bizet_cem_fails_universal :
    ¬ universalCounterfactual bvSim compatriots bizetItalian .actual ∧
    ¬ universalCounterfactual bvSim compatriots (¬ bizetItalian ·) .actual :=
  ⟨by decide, by decide⟩

end BizetVerdi

-- ════════════════════════════════════════════════════
-- § 2. Might Counterfactuals: The Collapse Problem
-- ════════════════════════════════════════════════════

/-!
## Might Counterfactuals

Lewis defines "if A, might B" as ¬(A □→ ¬B). Combined with CEM, this
collapses `might` into `would`:

1. CEM: (A □→ B) ∨ (A □→ ¬B)
2. If (A □→ ¬B), then ¬(A ◇→ B) by Lewis's def, so (A ◇→ B) → (A □→ B)
3. If (A □→ B), then (A ◇→ B) since would implies might
4. Therefore: (A ◇→ B) ↔ (A □→ B)

The general collapse is proved as `lewis_might_eq_would_cem` in
Counterfactual.lean, with `lewis_might_eq_would_singleton` as the
special case for unique closest worlds. Here we show concrete
consequences:

- In Bizet--Verdi (ties), selectional `might` is true while `would` is
  gap — the distinction is preserved by supervaluation
- Lewis's `might` is also true here (no collapse because Lewis
  rejects CEM), but for the wrong reason: it conflates epistemic
  possibility with the absence of universal counterfactual negation
-/

section MightCollapse

/-- In the Bizet--Verdi scenario, the selectional `might` is true —
    correctly predicting that "Bizet MIGHT have been Italian" is
    acceptable. -/
theorem selectional_might_bizet_true :
    selectionalMight bvSim compatriots bizetItalian .actual := by decide

/-- Selectional `might` is also true for the French direction. -/
theorem selectional_might_verdi_true :
    selectionalMight bvSim compatriots verdiFrench .actual := by decide

/-- **The might/would asymmetry under supervaluation**: both `might`
    conditionals are true even though neither `would` conditional is
    determinate (both are gap). This is the correct pattern: "Bizet
    might have been Italian" is acceptable, "Bizet would have been
    Italian" is neither true nor false. -/
theorem might_would_asymmetry :
    selectionalMight bvSim compatriots bizetItalian .actual ∧
    selectionalMight bvSim compatriots verdiFrench .actual ∧
    selectionalCounterfactual bvSim compatriots bizetItalian .actual = .gap ∧
    selectionalCounterfactual bvSim compatriots verdiFrench .actual = .gap :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- **Singleton collapse**: with a single closest world, Lewis's `might`
    and `would` give identical results. This is the concrete instance of
    `lewis_might_eq_would_singleton`. -/

inductive SWorld where | actual | closest deriving Repr, DecidableEq

instance : Fintype SWorld where
  elems := {.actual, .closest}
  complete x := by cases x <;> simp

/-- Singleton similarity: actual is strictly closest to itself
    (centering), and closest is the unique closest non-actual world. -/
def sSim : SimilarityOrdering SWorld := .ofBool
  (fun | .actual, .actual, _ => true
       | _, w₁, w₂ => w₁ == w₂)
  (by decide) (by decide)
def sAnte : SWorld → Prop | .closest => True | _ => False
instance : DecidablePred sAnte := fun w => by cases w <;> unfold sAnte <;> infer_instance
def sCons : SWorld → Prop | .closest => True | _ => False
instance : DecidablePred sCons := fun w => by cases w <;> unfold sCons <;> infer_instance

/-- With a unique closest world, Lewis's `might` = `would`. -/
theorem singleton_collapse :
    lewisMight sSim sAnte sCons .actual ↔
    universalCounterfactual sSim sAnte sCons .actual :=
  lewis_might_eq_would_singleton sSim sAnte sCons .actual (by decide)

end MightCollapse

-- ════════════════════════════════════════════════════
-- § 3. Distribution Principle: Worked Example
-- ════════════════════════════════════════════════════

/-!
## Distribution Principle

On Lewis's account, conditionals act like necessity operators on their
consequents. The distribution principle

    (A □→ (B ∨ C)) ⊃ ((A □→ B) ∨ (A □→ C))

holds for selection semantics with uniqueness (one world, B∨C ⊃ B or C)
but fails for universal semantics (∀ distributes over ∧, not ∨).
-/

section DistributionWorked

/-- Under universal semantics: compatriots □→ (Italian ∨ French) is true
    (every compatriot-world satisfies one or the other), but NEITHER
    compatriots □→ Italian NOR compatriots □→ French is true.
    Distribution fails. -/
theorem distribution_fails_bizetverdi :
    universalCounterfactual bvSim compatriots
      (λ w => bizetItalian w ∨ verdiFrench w) .actual ∧
    ¬ universalCounterfactual bvSim compatriots bizetItalian .actual ∧
    ¬ universalCounterfactual bvSim compatriots verdiFrench .actual :=
  ⟨by decide, by decide, by decide⟩

/-- Under selectional semantics with ties, the compound conditional
    (B∨C) is true (all closest worlds agree on B∨C), but the individual
    conditionals are indeterminate. The uniqueness premise of
    `distribution_selectional` is not met here (two closest worlds). -/
theorem distribution_needs_uniqueness :
    selectionalCounterfactual bvSim compatriots
      (λ w => bizetItalian w ∨ verdiFrench w) .actual = .true ∧
    selectionalCounterfactual bvSim compatriots bizetItalian .actual = .gap ∧
    selectionalCounterfactual bvSim compatriots verdiFrench .actual = .gap :=
  ⟨by decide, by decide, by decide⟩

end DistributionWorked

-- ════════════════════════════════════════════════════
-- § 4. Scope Ambiguity: Conditionals and Quantifiers
-- ════════════════════════════════════════════════════

/-!
## Conditionals and Quantifier Scope

On Lewis's analysis, conditional antecedents determine a set of possible
worlds, so conditionals interact with quantifiers exactly like necessity
operators. The scope distinction between (A > (∃x)Fx) and (∃x)(A > Fx)
is semantically significant.

The Supreme Court dialogue:
- "He has to appoint some woman" (narrow scope: ∃ under □)
- "He doesn't have to appoint any particular woman" (no wide scope)

The same pattern arises in counterfactuals when there are ties: the
selection function will pick a world where *someone* is appointed, but
no particular woman is the one who *would* be appointed.
-/

section QuantifierScope

inductive CourtWorld where | actual | w1 | w2
  deriving Repr, DecidableEq

/-- w1 and w2 are equally close to actual (mutual ≤): the president's
    choice is underdetermined. -/
instance : Fintype CourtWorld where
  elems := {.actual, .w1, .w2}
  complete x := by cases x <;> simp

def courtSim : SimilarityOrdering CourtWorld := .ofBool
  (fun | .actual, .actual, _ => true
       | .actual, .w1, .w2 => true
       | .actual, .w2, .w1 => true
       | _, w₁, w₂ => w₁ == w₂)
  (by decide) (by decide)

/-- The antecedent: a vacancy occurs. -/
def vacancy : CourtWorld → Prop
  | .actual => False | _ => True

instance : DecidablePred vacancy := fun w => by cases w <;> unfold vacancy <;> infer_instance

/-- Woman A is appointed in w1. -/
def appointA : CourtWorld → Prop
  | .w1 => True | _ => False

instance : DecidablePred appointA := fun w => by cases w <;> unfold appointA <;> infer_instance

/-- Woman B is appointed in w2. -/
def appointB : CourtWorld → Prop
  | .w2 => True | _ => False

instance : DecidablePred appointB := fun w => by cases w <;> unfold appointB <;> infer_instance

/-- Someone is appointed (narrow scope ∃). -/
def someoneAppointed : CourtWorld → Prop
  | .w1 | .w2 => True | .actual => False

instance : DecidablePred someoneAppointed :=
  fun w => by cases w <;> unfold someoneAppointed <;> infer_instance

/-- Narrow scope: "he would appoint some woman" — all closest worlds have
    someone appointed, so this is true even under universal semantics. -/
theorem narrow_scope_true :
    universalCounterfactual courtSim vacancy someoneAppointed .actual := by decide

/-- Wide scope fails for each particular woman: "he would appoint woman A"
    is indeterminate (gap) under selectional semantics. -/
theorem wide_scope_A_gap :
    selectionalCounterfactual courtSim vacancy appointA .actual
    = .gap := by decide

theorem wide_scope_B_gap :
    selectionalCounterfactual courtSim vacancy appointB .actual
    = .gap := by decide

/-- The scope contrast: narrow scope (someone appointed) is true, but
    wide scope for each individual is indeterminate. This illustrates
    Stalnaker's point that counterfactual antecedents purport to pick
    a unique world even when the choice is underdetermined — scope
    interacts with the selection function. -/
theorem scope_contrast :
    selectionalCounterfactual courtSim vacancy someoneAppointed .actual = .true ∧
    selectionalCounterfactual courtSim vacancy appointA .actual = .gap ∧
    selectionalCounterfactual courtSim vacancy appointB .actual = .gap :=
  ⟨by decide, by decide, by decide⟩

end QuantifierScope

end Stalnaker1981
