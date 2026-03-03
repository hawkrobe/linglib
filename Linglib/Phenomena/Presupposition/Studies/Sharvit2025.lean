import Linglib.Core.Semantics.Presupposition
import Linglib.Theories.Semantics.Conditionals.Presuppositional

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

-- ============================================================================
-- Part II: K/P and K/P* Analysis
-- ============================================================================

open Semantics.Conditionals.Presuppositional

-- § K/P fails: ∃-reading drops penniless-worlds

/-- Under K/P, the ∃-reading uses `orFilter` for the antecedent disjunction. -/
def existReading_KP : PrProp W :=
  ifKP allWorlds (PrProp.orFilter pennilessPr proudOfMoney) shouldntLend

/-- Under K/P, the ∀-reading is the conjunction of two K/P conditionals. -/
def forallReading_KP : PrProp W :=
  PrProp.and (ifKP allWorlds pennilessPr shouldntLend)
             (ifKP allWorlds proudOfMoney shouldntLend)

/-- K/P ∃-reading is UNDEFINED at penniless-worlds. -/
theorem kp_exist_undefined_at_penny :
    existReading_KP.presup W.pennyNotLend = false ∧
    existReading_KP.presup W.pennyLend = false := by
  constructor <;> native_decide

/-- K/P ∃-reading IS defined at proud-worlds. -/
theorem kp_exist_defined_at_proud :
    existReading_KP.presup W.proudNotLend = true ∧
    existReading_KP.presup W.proudLend = true := by
  constructor <;> native_decide

/-- K/P ∀-reading: the first conditional (if penniless, shouldntLend) is always defined. -/
theorem kp_forall_first_cond_always_defined :
    ∀ w, (ifKP allWorlds pennilessPr shouldntLend).presup w = true := by
  intro w; cases w <;> native_decide

/-- K/P ∀-reading presup = hasMoney (from the second conditional). -/
theorem kp_forall_presup_eq_hasMoney :
    ∀ w, forallReading_KP.presup w = hasMoney w := by
  intro w; cases w <;> native_decide

/-- K/P ∃-reading assertion excludes penny-worlds from quantification. -/
theorem kp_exist_assertion_excludes_penny :
    existReading_KP.presup W.proudNotLend = true ∧
    (ifKP allWorlds pennilessPr shouldntLend).presup W.proudNotLend = true := by
  constructor <;> native_decide

-- § K/P* conditionals: CLOS-based filtering

/-- K/P* conditional: if penniless, shouldntLend. -/
def cond_penniless : PrProp W :=
  ifPresup trivialCloser allWorlds pennilessPr shouldntLend

/-- K/P* conditional: if proud-of-money, shouldntLend. -/
def cond_proud : PrProp W :=
  ifPresup trivialCloser allWorlds proudOfMoney shouldntLend

/-- K/P* conditional with penniless: always defined. -/
theorem kpstar_penniless_always_defined :
    ∀ w, cond_penniless.presup w = true := by
  intro w; cases w <;> native_decide

/-- K/P* conditional with proud-of-money: defined iff hasMoney. -/
theorem kpstar_proud_presup_eq_hasMoney :
    ∀ w, cond_proud.presup w = hasMoney w := by
  intro w; cases w <;> native_decide

-- § K/P* full readings

/-- K/P* ∃-reading. -/
def existReading_KPstar : PrProp W :=
  ifPresup trivialCloser allWorlds
    (orPresup trivialCloser allWorlds pennilessPr proudOfMoney)
    shouldntLend

/-- K/P* ∀-reading. -/
def forallReading_KPstar : PrProp W :=
  andPresup trivialCloser allWorlds cond_penniless cond_proud

/-- Both K/P* readings have presupposition = hasMoney. -/
theorem kpstar_exist_presup_eq :
    ∀ w, existReading_KPstar.presup w = hasMoney w := by
  intro w; cases w <;> native_decide

theorem kpstar_forall_presup_eq :
    ∀ w, forallReading_KPstar.presup w = hasMoney w := by
  intro w; cases w <;> native_decide

/-- Both K/P* readings have identical assertions. -/
theorem kpstar_assertions_agree :
    ∀ w, existReading_KPstar.assertion w = forallReading_KPstar.assertion w := by
  intro w; cases w <;> native_decide

/-- Strawson equivalence of ∃ and ∀ readings under K/P*. -/
theorem kpstar_strawson_equiv :
    PrProp.strawsonEquiv existReading_KPstar forallReading_KPstar := by
  constructor <;> intro w hp ha
  · exact ⟨by rw [kpstar_forall_presup_eq, ← kpstar_exist_presup_eq]; exact hp,
           fun _ => by rw [← kpstar_assertions_agree]; exact ha⟩
  · exact ⟨by rw [kpstar_exist_presup_eq, ← kpstar_forall_presup_eq]; exact hp,
           fun _ => by rw [kpstar_assertions_agree]; exact ha⟩

-- § K/P also yields Strawson equivalence in this 4-world model

theorem kp_exist_presup_eq :
    ∀ w, existReading_KP.presup w = hasMoney w := by
  intro w; cases w <;> native_decide

theorem kp_orFilter_undefined_at_penny :
    (PrProp.orFilter pennilessPr proudOfMoney).presup W.pennyNotLend = false := rfl

end Phenomena.Presupposition.Studies.Sharvit2025
