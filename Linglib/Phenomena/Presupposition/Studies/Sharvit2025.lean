import Linglib.Core.Semantics.Presupposition
import Linglib.Theories.Semantics.Conditionals.Presupposition

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

namespace Sharvit2025

open Core.Presupposition

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
def hasMoney : (W → Bool)
  | .proudNotLend | .proudLend => true
  | _ => false

/-- "Mia is penniless" — presuppositionless. -/
def penniless : (W → Bool)
  | .pennyNotLend | .pennyLend => true
  | _ => false

/-- "Mia is proud of her money" — presupposes hasMoney.
    Uses `PrProp.ofBool` to keep fields decidable. -/
def proudOfMoney : PrProp W := PrProp.ofBool hasMoney (fun
  | .proudNotLend | .proudLend => true
  | _ => false)

instance proudOfMoney_decAssertion : DecidablePred proudOfMoney.assertion := by
  intro w; simp only [proudOfMoney, PrProp.ofBool]; exact inferInstance

/-- "Sue shouldn't lend Mia any money" — presuppositionless.
    Uses `PrProp.ofBool` for decidability. -/
def shouldntLend : PrProp W := PrProp.ofBool (fun _ => true) (fun
  | .pennyNotLend | .proudNotLend => true
  | _ => false)

instance shouldntLend_decAssertion : DecidablePred shouldntLend.assertion := by
  intro w; simp only [shouldntLend, PrProp.ofBool]; exact inferInstance

/-- Presuppositionless version of penniless as PrProp. -/
def pennilessPr : PrProp W := PrProp.ofBProp penniless

instance pennilessPr_decAssertion : DecidablePred pennilessPr.assertion := by
  intro w; simp only [pennilessPr, PrProp.ofBProp]; exact inferInstance

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
    ¬(PrProp.orFilter pennilessPr proudOfMoney).presup W.pennyNotLend := by
  simp [PrProp.orFilter, pennilessPr, PrProp.ofBProp, penniless, proudOfMoney, PrProp.ofBool, hasMoney]

/-- The disjunction IS defined at proud-worlds. -/
theorem orFilter_defined_at_proud :
    (PrProp.orFilter pennilessPr proudOfMoney).presup W.proudNotLend := by
  simp [PrProp.orFilter, pennilessPr, PrProp.ofBProp, penniless, proudOfMoney, PrProp.ofBool, hasMoney]

-- ============================================================================
-- Part II: K/P and K/P* Analysis
-- ============================================================================

open Semantics.Conditionals.Presupposition

-- Decidable instances for compound PrProp assertions

instance orFilter_decAssertion : DecidablePred (PrProp.orFilter pennilessPr proudOfMoney).assertion := by
  intro w; simp only [PrProp.orFilter, pennilessPr, PrProp.ofBProp, proudOfMoney, PrProp.ofBool]
  exact inferInstance

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
    ¬existReading_KP.presup W.pennyNotLend ∧
    ¬existReading_KP.presup W.pennyLend := by
  constructor <;> intro h <;> simp [existReading_KP, ifKP, PrProp.orFilter,
    pennilessPr, PrProp.ofBProp, penniless, proudOfMoney, PrProp.ofBool, hasMoney] at h

/-- K/P ∃-reading IS defined at proud-worlds. -/
theorem kp_exist_defined_at_proud :
    existReading_KP.presup W.proudNotLend ∧
    existReading_KP.presup W.proudLend := by
  constructor <;> {
    simp [existReading_KP, ifKP, PrProp.orFilter, pennilessPr, PrProp.ofBProp,
      penniless, proudOfMoney, PrProp.ofBool, hasMoney, shouldntLend, allWorlds]
  }

/-- K/P ∀-reading: the first conditional (if penniless, shouldntLend) is always defined. -/
theorem kp_forall_first_cond_always_defined :
    ∀ w, (ifKP allWorlds pennilessPr shouldntLend).presup w := by
  intro w; simp [ifKP, pennilessPr, PrProp.ofBProp, shouldntLend, PrProp.ofBool]

/-- K/P ∀-reading presup = hasMoney (from the second conditional). -/
theorem kp_forall_presup_eq_hasMoney :
    ∀ w, forallReading_KP.presup w ↔ hasMoney w = true := by
  intro w; cases w <;>
    simp [forallReading_KP, PrProp.and, ifKP, pennilessPr, PrProp.ofBProp,
          penniless, proudOfMoney, PrProp.ofBool, hasMoney, shouldntLend, allWorlds]

/-- K/P ∃-reading assertion excludes penny-worlds from quantification. -/
theorem kp_exist_assertion_excludes_penny :
    existReading_KP.presup W.proudNotLend ∧
    (ifKP allWorlds pennilessPr shouldntLend).presup W.proudNotLend := by
  exact ⟨(kp_exist_defined_at_proud).1, kp_forall_first_cond_always_defined _⟩

-- § K/P* conditionals: CLOS-based filtering

instance : DecidablePred (definedFalse pennilessPr) := by
  intro w; simp only [definedFalse, pennilessPr, PrProp.ofBProp, penniless]; exact inferInstance

instance : DecidablePred (definedFalse proudOfMoney) := by
  intro w; simp only [definedFalse, proudOfMoney, PrProp.ofBool, hasMoney]; exact inferInstance

/-- K/P* conditional: if penniless, shouldntLend. -/
def cond_penniless : PrProp W :=
  ifPresup trivialCloser allWorlds pennilessPr shouldntLend

/-- K/P* conditional: if proud-of-money, shouldntLend. -/
def cond_proud : PrProp W :=
  ifPresup trivialCloser allWorlds proudOfMoney shouldntLend

/-- K/P* conditional with penniless: always defined. -/
theorem kpstar_penniless_always_defined :
    ∀ w, cond_penniless.presup w := by
  intro w; simp [cond_penniless, ifPresup, pennilessPr, PrProp.ofBProp, penniless,
                 shouldntLend, PrProp.ofBool, closB, trivialCloser, allWorlds]

/-- K/P* conditional with proud-of-money: defined iff hasMoney. -/
theorem kpstar_proud_presup_eq_hasMoney :
    ∀ w, cond_proud.presup w ↔ hasMoney w = true := by
  intro w; cases w <;>
    simp [cond_proud, ifPresup, proudOfMoney, PrProp.ofBool, hasMoney, shouldntLend,
          closB, trivialCloser, allWorlds, penniless]

-- § K/P* full readings

-- Decidable instances for compound assertions needed by orPresup/andPresup/ifPresup

instance cond_penniless_decAssertion : DecidablePred cond_penniless.assertion := by
  intro w; simp only [cond_penniless, ifPresup, closB, trivialCloser, allWorlds,
    pennilessPr, PrProp.ofBProp, penniless, shouldntLend, PrProp.ofBool]; exact inferInstance

instance orPresup_decAssertion : DecidablePred
    (orPresup trivialCloser allWorlds pennilessPr proudOfMoney).assertion := by
  intro w; simp only [orPresup, pennilessPr, PrProp.ofBProp, proudOfMoney, PrProp.ofBool,
    penniless]; exact inferInstance

instance orPresup_defFalse_dec : DecidablePred
    (definedFalse (orPresup trivialCloser allWorlds pennilessPr proudOfMoney)) := by
  intro w; simp only [definedFalse, orPresup, pennilessPr, PrProp.ofBProp, proudOfMoney,
    PrProp.ofBool, penniless, hasMoney, closB, trivialCloser, allWorlds]; exact inferInstance

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
    ∀ w, existReading_KPstar.presup w ↔ hasMoney w = true := by
  intro w; cases w <;>
    simp [existReading_KPstar, ifPresup, orPresup, pennilessPr, PrProp.ofBProp,
          penniless, proudOfMoney, PrProp.ofBool, hasMoney, shouldntLend, closB,
          trivialCloser, allWorlds, definedFalse]

theorem kpstar_forall_presup_eq :
    ∀ w, forallReading_KPstar.presup w ↔ hasMoney w = true := by
  intro w; cases w <;>
    simp [forallReading_KPstar, andPresup, cond_penniless, cond_proud,
          ifPresup, pennilessPr, PrProp.ofBProp, penniless, proudOfMoney,
          PrProp.ofBool, hasMoney, shouldntLend, closB, trivialCloser, allWorlds]

/-- Both K/P* readings have identical assertions. -/
theorem kpstar_assertions_agree :
    ∀ w, existReading_KPstar.assertion w ↔ forallReading_KPstar.assertion w := by
  intro w; cases w <;>
    simp [existReading_KPstar, forallReading_KPstar, ifPresup, andPresup,
          orPresup, pennilessPr, PrProp.ofBProp, penniless, proudOfMoney,
          PrProp.ofBool, hasMoney, shouldntLend, closB, trivialCloser, allWorlds,
          cond_penniless, cond_proud, definedFalse]

/-- Strawson equivalence of ∃ and ∀ readings under K/P*. -/
theorem kpstar_strawson_equiv :
    PrProp.strawsonEquiv existReading_KPstar forallReading_KPstar := by
  constructor <;> intro w hp ha
  · exact ⟨(kpstar_forall_presup_eq w).mpr ((kpstar_exist_presup_eq w).mp hp),
           fun _ => (kpstar_assertions_agree w).mp ha⟩
  · exact ⟨(kpstar_exist_presup_eq w).mpr ((kpstar_forall_presup_eq w).mp hp),
           fun _ => (kpstar_assertions_agree w).mpr ha⟩

-- § K/P also yields Strawson equivalence in this 4-world model

theorem kp_exist_presup_eq :
    ∀ w, existReading_KP.presup w ↔ hasMoney w = true := by
  intro w; cases w <;>
    simp [existReading_KP, ifKP, PrProp.orFilter, pennilessPr, PrProp.ofBProp,
          penniless, proudOfMoney, PrProp.ofBool, hasMoney, shouldntLend, allWorlds]

theorem kp_orFilter_undefined_at_penny :
    ¬(PrProp.orFilter pennilessPr proudOfMoney).presup W.pennyNotLend := by
  exact orFilter_undefined_at_penny

end Sharvit2025
