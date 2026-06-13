import Linglib.Discourse.LayeredAssertion

/-!
# Layered Assertive Clauses: JP/ComP modifiers
[krifka-2020] [speas-2004] [wiltschko-2014]

Worked examples for [krifka-2020]'s four-layer clause structure
(TP > JP > ComP > ActP). The JP layer originates with [speas-2004]
and is developed crosslinguistically by [wiltschko-2014];
[krifka-2020] synthesises them with the commitment-space framework
of [krifka-2015] (see sibling
`Studies/Krifka2015.lean`).

## Coverage

- §1 — Hedges as JP modifiers ("I think p" → epistemicStatus := weak)
- §2 — Oaths as ComP modifiers ("I swear p" → commitmentStrength := strong)
- §3 — JP/ComP independence (commute, layer non-interaction)
- §4 — Rank orderings: hedges weaken, oaths strengthen, relative to the
  `.standard` default

## Out of scope

- The actual commitment-space dynamics — see Krifka2015.lean.
- Proxy assertions ("Mary says p") — flagged in [krifka-2015]
  conclusion, not exercised here.
- Conjunct/disjunct systems (Newari etc.) — typological extension noted
  in [krifka-2015] conclusion but separate study.
-/

namespace Krifka2020

open Discourse.Krifka

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
-- § 4. Rank Orderings
-- ════════════════════════════════════════════════════

/-- Hedging produces a strictly lower-rank epistemic status than the
    `.standard` default: "I think p" weakens the assertion. -/
theorem hedgeAsJP_rank_lt_standard {W : Type*} (la : LayeredAssertion W) :
    (hedgeAsJP la).epistemicStatus.rank < CommitmentStrength.standard.rank :=
  show CommitmentStrength.weak.rank < CommitmentStrength.standard.rank by decide

/-- Oaths produce a strictly higher-rank commitment strength than the
    `.standard` default: "I swear p" strengthens the assertion. -/
theorem oathAsComP_rank_gt_standard {W : Type*} (la : LayeredAssertion W) :
    (oathAsComP la).commitmentStrength.rank > CommitmentStrength.standard.rank :=
  show CommitmentStrength.strong.rank > CommitmentStrength.standard.rank by decide

end Krifka2020
