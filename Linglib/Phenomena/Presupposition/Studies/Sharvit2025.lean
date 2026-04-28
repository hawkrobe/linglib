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
def hasMoney : W → Prop
  | .proudNotLend | .proudLend => True
  | _ => False

instance : DecidablePred hasMoney
  | .proudNotLend | .proudLend => isTrue trivial
  | .pennyNotLend | .pennyLend => isFalse id

/-- "Mia is penniless" — presuppositionless. -/
def penniless : W → Prop
  | .pennyNotLend | .pennyLend => True
  | _ => False

instance : DecidablePred penniless
  | .pennyNotLend | .pennyLend => isTrue trivial
  | .proudNotLend | .proudLend => isFalse id

/-- "Mia is proud of her money" — presupposes hasMoney. -/
def proudOfMoney : PrProp W where
  presup := hasMoney
  assertion w := w = .proudNotLend ∨ w = .proudLend

instance proudOfMoney_decAssertion : DecidablePred proudOfMoney.assertion := by
  unfold proudOfMoney; intro w; infer_instance

/-- "Sue shouldn't lend Mia any money" — presuppositionless. -/
def shouldntLend : PrProp W where
  presup _ := True
  assertion w := w = .pennyNotLend ∨ w = .proudNotLend

instance shouldntLend_decAssertion : DecidablePred shouldntLend.assertion := by
  unfold shouldntLend; intro w; infer_instance

/-- Presuppositionless version of penniless as PrProp. -/
def pennilessPr : PrProp W := PrProp.ofProp' penniless

instance pennilessPr_decAssertion : DecidablePred pennilessPr.assertion := by
  unfold pennilessPr PrProp.ofProp'; intro w; infer_instance

-- ════════════════════════════════════════════════════════════════
-- § Structural properties
-- ════════════════════════════════════════════════════════════════

/-- Penniless entails ¬hasMoney: the presuppositions conflict. -/
theorem penniless_entails_no_money : ∀ w, penniless w → ¬hasMoney w := by
  intro w; cases w <;> simp [penniless, hasMoney]

/-- The disjunction "penniless or proud" under `orFilter` is UNDEFINED
at penniless-worlds. This is the root cause of K/P's failure: `orFilter`'s
filtering condition requires "proud of money" to be defined when
"penniless" is true, but penniless entails ¬hasMoney. -/
theorem orFilter_undefined_at_penny :
    ¬(PrProp.orFilter pennilessPr proudOfMoney).presup W.pennyNotLend := by
  rintro ⟨h1, _, _⟩
  -- h1 : pennilessPr.assertion → proudOfMoney.presup
  -- pennilessPr.assertion W.pennyNotLend = penniless W.pennyNotLend = True
  -- proudOfMoney.presup W.pennyNotLend = hasMoney W.pennyNotLend = False
  exact (h1 trivial : hasMoney W.pennyNotLend)

/-- The disjunction IS defined at proud-worlds. -/
theorem orFilter_defined_at_proud :
    (PrProp.orFilter pennilessPr proudOfMoney).presup W.proudNotLend :=
  ⟨fun h => absurd h (by simp [pennilessPr, PrProp.ofProp', penniless]),
   fun _ => trivial,
   Or.inr trivial⟩

-- ============================================================================
-- Part II: K/P and K/P* Analysis
-- ============================================================================

open Semantics.Conditionals.Presupposition

-- Decidable instances for compound PrProp assertions

instance orFilter_decAssertion : DecidablePred (PrProp.orFilter pennilessPr proudOfMoney).assertion := by
  intro w; unfold PrProp.orFilter pennilessPr PrProp.ofProp' proudOfMoney
  infer_instance

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
  refine ⟨?_, ?_⟩ <;>
    (intro h; simp [existReading_KP, ifKP, PrProp.orFilter,
      pennilessPr, PrProp.ofProp', penniless, proudOfMoney, hasMoney] at h)

/-- K/P ∃-reading IS defined at proud-worlds. -/
theorem kp_exist_defined_at_proud :
    existReading_KP.presup W.proudNotLend ∧
    existReading_KP.presup W.proudLend := by
  refine ⟨?_, ?_⟩ <;>
    (simp [existReading_KP, ifKP, PrProp.orFilter, pennilessPr, PrProp.ofProp',
      penniless, proudOfMoney, hasMoney, shouldntLend, allWorlds])

/-- K/P ∀-reading: the first conditional (if penniless, shouldntLend) is always defined. -/
theorem kp_forall_first_cond_always_defined :
    ∀ w, (ifKP allWorlds pennilessPr shouldntLend).presup w := by
  intro w; simp [ifKP, pennilessPr, PrProp.ofProp', shouldntLend]

/-- K/P ∀-reading presup = hasMoney (from the second conditional). -/
theorem kp_forall_presup_eq_hasMoney :
    ∀ w, forallReading_KP.presup w ↔ hasMoney w := by
  intro w; cases w <;>
    simp [forallReading_KP, PrProp.and, ifKP, pennilessPr, PrProp.ofProp',
          penniless, proudOfMoney, hasMoney, shouldntLend, allWorlds]

/-- K/P ∃-reading assertion excludes penny-worlds from quantification. -/
theorem kp_exist_assertion_excludes_penny :
    existReading_KP.presup W.proudNotLend ∧
    (ifKP allWorlds pennilessPr shouldntLend).presup W.proudNotLend := by
  exact ⟨(kp_exist_defined_at_proud).1, kp_forall_first_cond_always_defined _⟩

-- § K/P* conditionals: CLOS-based filtering

instance : DecidablePred (definedFalse pennilessPr) := by
  intro w; unfold definedFalse pennilessPr PrProp.ofProp'; infer_instance

instance : DecidablePred (definedFalse proudOfMoney) := by
  intro w; unfold definedFalse proudOfMoney; infer_instance

/-- K/P* conditional: if penniless, shouldntLend. -/
def cond_penniless : PrProp W :=
  ifPresup trivialCloser allWorlds pennilessPr shouldntLend

/-- K/P* conditional: if proud-of-money, shouldntLend. -/
def cond_proud : PrProp W :=
  ifPresup trivialCloser allWorlds proudOfMoney shouldntLend

/-- K/P* conditional with penniless: always defined. -/
theorem kpstar_penniless_always_defined :
    ∀ w, cond_penniless.presup w := by
  intro w; simp [cond_penniless, ifPresup, pennilessPr, PrProp.ofProp', penniless,
                 shouldntLend, closB, trivialCloser, allWorlds]

/-- K/P* conditional with proud-of-money: defined iff hasMoney. -/
theorem kpstar_proud_presup_eq_hasMoney :
    ∀ w, cond_proud.presup w ↔ hasMoney w := by
  intro w; cases w <;>
    simp [cond_proud, ifPresup, proudOfMoney, hasMoney, shouldntLend,
          closB, trivialCloser, allWorlds, penniless]

-- § K/P* full readings

-- Decidable instances for compound assertions needed by orPresup/andPresup/ifPresup

instance cond_penniless_decAssertion : DecidablePred cond_penniless.assertion := by
  intro w; unfold cond_penniless ifPresup
  infer_instance

instance orPresup_decAssertion : DecidablePred
    (orPresup trivialCloser allWorlds pennilessPr proudOfMoney).assertion := by
  intro w; unfold orPresup pennilessPr PrProp.ofProp' proudOfMoney
  infer_instance

instance orPresup_defFalse_dec : DecidablePred
    (definedFalse (orPresup trivialCloser allWorlds pennilessPr proudOfMoney)) := by
  intro w; unfold definedFalse orPresup pennilessPr PrProp.ofProp' proudOfMoney
  infer_instance

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
    ∀ w, existReading_KPstar.presup w ↔ hasMoney w := by
  intro w; cases w <;>
    simp [existReading_KPstar, ifPresup, orPresup, pennilessPr, PrProp.ofProp',
          penniless, proudOfMoney, hasMoney, shouldntLend, closB,
          trivialCloser, allWorlds, definedFalse]

theorem kpstar_forall_presup_eq :
    ∀ w, forallReading_KPstar.presup w ↔ hasMoney w := by
  intro w; cases w <;>
    simp [forallReading_KPstar, andPresup, cond_penniless, cond_proud,
          ifPresup, pennilessPr, PrProp.ofProp', penniless, proudOfMoney,
          hasMoney, shouldntLend, closB, trivialCloser, allWorlds]

/-- Both K/P* readings have identical assertions. -/
theorem kpstar_assertions_agree :
    ∀ w, existReading_KPstar.assertion w ↔ forallReading_KPstar.assertion w := by
  intro w; cases w <;>
    simp [existReading_KPstar, forallReading_KPstar, ifPresup, andPresup,
          orPresup, pennilessPr, PrProp.ofProp', penniless, proudOfMoney,
          hasMoney, shouldntLend, closB, trivialCloser, allWorlds,
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
    ∀ w, existReading_KP.presup w ↔ hasMoney w := by
  intro w; cases w <;>
    simp [existReading_KP, ifKP, PrProp.orFilter, pennilessPr, PrProp.ofProp',
          penniless, proudOfMoney, hasMoney, shouldntLend, allWorlds]

theorem kp_orFilter_undefined_at_penny :
    ¬(PrProp.orFilter pennilessPr proudOfMoney).presup W.pennyNotLend :=
  orFilter_undefined_at_penny

end Sharvit2025
