import Linglib.Core.Semantics.Presupposition

/-!
# Rooth-Partee Conditionals: Empirical Data

@cite{sharvit-2025} @cite{rooth-partee-1982}Theory-neutral data for @cite{sharvit-2025} "Rooth-Partee Conditionals."

## The puzzle

(85) "If Mia is penniless or proud of her money, Sue shouldn't lend her any."

Two readings:

- **(86a) if-over-∃**: If [penniless ∨ proud-of-money], shouldn't-lend.
  Single conditional with disjunctive antecedent.

- **(86b) ∀-over-if**: For each P ∈ {penniless, proud-of-money}: if P(m),
  shouldn't-lend. Conjunction of two conditionals.

"Proud of her money" presupposes "Mia has money." Empirically the readings
are Strawson-equivalent — speakers cannot distinguish them. Under K/P
(material conditional filtering) they are NOT Strawson-equivalent because
`or^{K/P}(penniless, proud)` is undefined at penniless-worlds, causing those
worlds to drop from the ∃-reading's quantification domain.

-/

namespace Phenomena.Presupposition.Studies.Sharvit2025

open Core.Presupposition
open Core.Proposition

-- ════════════════════════════════════════════════════════════════
-- § World type (Sharvit's Mia/Sue scenario)
-- ════════════════════════════════════════════════════════════════

/-- Worlds for sentence (85). Cross-product of Mia's financial status
(penniless vs has-money-and-proud) with whether Sue lends. -/
inductive W where
  | pennyNotLend    -- Mia penniless, Sue doesn't lend
  | pennyLend       -- Mia penniless, Sue lends
  | proudNotLend    -- Mia has money & proud, Sue doesn't lend
  | proudLend       -- Mia has money & proud, Sue lends
  deriving DecidableEq, Repr, Inhabited

/-- All worlds in the model. -/
def allWorlds : List W := [.pennyNotLend, .pennyLend, .proudNotLend, .proudLend]

theorem allWorlds_complete : ∀ w : W, w ∈ allWorlds := by
  intro w; cases w <;> simp [allWorlds]

-- ════════════════════════════════════════════════════════════════
-- § Lexical properties
-- ════════════════════════════════════════════════════════════════

/-- "Mia has money" — the presupposition of "proud of her money." -/
def hasMoney : BProp W
  | .proudNotLend | .proudLend => true
  | _ => false

/-- "Mia is penniless" — presuppositionless. -/
def penniless : BProp W
  | .pennyNotLend | .pennyLend => true
  | _ => false

/-- "Mia is proud of her money" — presupposes hasMoney. -/
def proudOfMoney : PrProp W where
  presup := hasMoney
  assertion := fun
    | .proudNotLend | .proudLend => true
    | _ => false

/-- "Sue shouldn't lend Mia any money" — presuppositionless. -/
def shouldntLend : PrProp W where
  presup := fun _ => true
  assertion := fun
    | .pennyNotLend | .proudNotLend => true
    | _ => false

/-- Presuppositionless version of penniless as PrProp. -/
def pennilessPr : PrProp W := PrProp.ofBProp penniless

-- ════════════════════════════════════════════════════════════════
-- § Structural properties
-- ════════════════════════════════════════════════════════════════

/-- Penniless entails ¬hasMoney: the presuppositions conflict. -/
theorem penniless_entails_no_money : ∀ w, penniless w = true → hasMoney w = false := by
  intro w; cases w <;> simp [penniless, hasMoney]

/-- The disjunction "penniless or proud" under `orFilter` is UNDEFINED
at penniless-worlds. This is the root cause of K/P's failure: `orFilter`'s
filtering condition requires "proud of money" to be defined when
"penniless" is true, but penniless entails ¬hasMoney. -/
theorem orFilter_undefined_at_penny :
    (PrProp.orFilter pennilessPr proudOfMoney).presup W.pennyNotLend = false := by rfl

/-- The disjunction IS defined at proud-worlds. -/
theorem orFilter_defined_at_proud :
    (PrProp.orFilter pennilessPr proudOfMoney).presup W.proudNotLend = true := by rfl

end Phenomena.Presupposition.Studies.Sharvit2025
