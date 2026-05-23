import Linglib.Dialogue.LayeredAssertion
import Linglib.Phenomena.Assertion.Basic

/-!
# Layered Assertive Clauses: JP/ComP modifiers
@cite{krifka-2020} @cite{speas-2004} @cite{wiltschko-2014}

Worked examples for @cite{krifka-2020}'s four-layer clause structure
(TP > JP > ComP > ActP). The JP layer originates with @cite{speas-2004}
and is developed crosslinguistically by @cite{wiltschko-2014};
@cite{krifka-2020} synthesises them with the commitment-space framework
of @cite{krifka-2015} (see sibling
`Studies/Krifka2015.lean`).

## Coverage

- §1 — Hedges as JP modifiers ("I think p" → epistemicStatus := weak)
- §2 — Oaths as ComP modifiers ("I swear p" → commitmentStrength := strong)
- §3 — JP/ComP independence (commute, layer non-interaction)
- §4 — Data bridges to `Phenomena/Assertion/Basic.lean` empirical data

## Out of scope

- The actual commitment-space dynamics — see Krifka2015.lean.
- Proxy assertions ("Mary says p") — flagged in @cite{krifka-2015}
  conclusion, not exercised here.
- Conjunct/disjunct systems (Newari etc.) — typological extension noted
  in @cite{krifka-2015} conclusion but separate study.
-/

namespace Krifka2020

open Dialogue.Krifka
open Phenomena.Assertion (hedgeExamples oathExamples
  all_hedges_reduce all_oaths_increase)

-- ════════════════════════════════════════════════════
-- § 1. Hedges as JP Modifiers
-- ════════════════════════════════════════════════════

/-- A hedge modifies the JP layer (epistemic status) to `weak`.

    "I think p" = assertion with `epistemicStatus := .weak`.
    The TP content (p) is unchanged; only the JP layer is modified. -/
def hedgeAsJP {W : Type*} (la : LayeredAssertion W) : LayeredAssertion W :=
  { la with epistemicStatus := .weak }

/-- Hedging preserves content (TP is untouched by JP modification). -/
theorem hedgeAsJP_content_eq {W : Type*} (la : LayeredAssertion W) :
    (hedgeAsJP la).content = la.content := rfl

/-- Hedging sets epistemic status to weak. -/
theorem hedgeAsJP_epistemicStatus_eq_weak {W : Type*} (la : LayeredAssertion W) :
    (hedgeAsJP la).epistemicStatus = .weak := rfl

/-- Hedging does not affect commitment strength. -/
theorem hedgeAsJP_commitmentStrength_eq {W : Type*} (la : LayeredAssertion W) :
    (hedgeAsJP la).commitmentStrength = la.commitmentStrength := rfl

-- ════════════════════════════════════════════════════
-- § 2. Oaths as ComP Modifiers
-- ════════════════════════════════════════════════════

/-- An oath modifies the ComP layer (commitment strength) to `strong`.

    "I swear p" = assertion with `commitmentStrength := .strong`.
    The TP content (p) is unchanged; only the ComP layer is modified. -/
def oathAsComP {W : Type*} (la : LayeredAssertion W) : LayeredAssertion W :=
  { la with commitmentStrength := .strong }

/-- Oaths preserve content. -/
theorem oathAsComP_content_eq {W : Type*} (la : LayeredAssertion W) :
    (oathAsComP la).content = la.content := rfl

/-- Oaths set commitment strength to strong. -/
theorem oathAsComP_commitmentStrength_eq_strong {W : Type*}
    (la : LayeredAssertion W) :
    (oathAsComP la).commitmentStrength = .strong := rfl

/-- Oaths do not affect epistemic status. -/
theorem oathAsComP_epistemicStatus_eq {W : Type*} (la : LayeredAssertion W) :
    (oathAsComP la).epistemicStatus = la.epistemicStatus := rfl

-- ════════════════════════════════════════════════════
-- § 3. JP/ComP Independence
-- ════════════════════════════════════════════════════

/-- JP and ComP can co-occur: hedging + oath on the same assertion.

    "I think I swear p": epistemicStatus = weak, commitmentStrength = strong.
    "I swear I think p": same result (layers are independent). -/
def hedgedOath {W : Type*} (la : LayeredAssertion W) : LayeredAssertion W :=
  { la with epistemicStatus := .weak, commitmentStrength := .strong }

/-- Order doesn't matter: hedge(oath(la)) = oath(hedge(la)). -/
theorem hedgeAsJP_oathAsComP_comm {W : Type*} (la : LayeredAssertion W) :
    hedgeAsJP (oathAsComP la) = oathAsComP (hedgeAsJP la) := rfl

/-- Hedged oath has weak epistemic + strong commitment. -/
theorem hedgedOath_profile {W : Type*} (la : LayeredAssertion W) :
    (hedgedOath la).epistemicStatus = .weak ∧
    (hedgedOath la).commitmentStrength = .strong :=
  ⟨rfl, rfl⟩

/-- Both layered modifications preserve TP content. -/
theorem hedgedOath_content_eq {W : Type*} (la : LayeredAssertion W) :
    (hedgedOath la).content = la.content := rfl

-- ════════════════════════════════════════════════════
-- § 4. Empirical-Data Bridges
-- ════════════════════════════════════════════════════

/-- All hedges reduce commitment, AND the JP-modifier mechanism produces
    a strictly lower-rank epistemic status than `.standard`. The data
    side is `all_hedges_reduce` from `Phenomena/Assertion/Basic.lean`;
    the mechanism side is the JP-modifier rank ordering. -/
theorem hedge_data_bridge :
    hedgeExamples.all (·.reducesCommitment) = true ∧
    CommitmentStrength.weak.rank < CommitmentStrength.standard.rank :=
  ⟨all_hedges_reduce, by decide⟩

/-- All oaths increase commitment, AND the ComP-modifier mechanism
    produces a strictly higher-rank commitment strength than `.standard`.
    The data side is `all_oaths_increase` from `Basic.lean`; the
    mechanism side is the ComP-modifier rank ordering. -/
theorem oath_data_bridge :
    oathExamples.all (·.increasesCommitment) = true ∧
    CommitmentStrength.strong.rank > CommitmentStrength.standard.rank :=
  ⟨all_oaths_increase, by decide⟩

end Krifka2020
