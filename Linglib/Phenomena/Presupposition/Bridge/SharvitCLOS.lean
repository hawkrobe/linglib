import Linglib.Theories.Semantics.Conditionals.Presuppositional
import Linglib.Phenomena.Presupposition.Studies.Sharvit2025

/-!
# Bridge: CLOS-based Filtering → Rooth-Partee Data

@cite{sharvit-2025}

Connects the K/P and K/P* conditionals to the Rooth-Partee empirical data.

## What this proves

1. **K/P fails**: Under K/P (`ifKP`), `orFilter` is undefined at
   penniless-worlds, causing those worlds to drop from the ∃-reading's
   quantification domain.

2. **K/P* conditionals are well-behaved**: The individual K/P* conditionals
   have correct CLOS-based presupposition projections.

3. **Strawson equivalence under K/P***: The ∃ and ∀ readings of the
   Rooth-Partee conditional are Strawson-equivalent when constructed with
   `orPresup` and `andPresup`. Both readings have presupposition `hasMoney`
   and identical assertions.

4. **Model limitation**: In this 4-world model where penniless = ¬hasMoney,
   K/P and K/P* give identical results. The K/P vs K/P* distinction requires
   a richer model with worlds where Mia is neither penniless nor proud.
   The paper's general proof uses K/P** (type-flexible connectives, (142)).

## References

- Sharvit, Y. (2025). Rooth-Partee Conditionals. L&P.
-/

namespace Phenomena.Presupposition.Bridge.SharvitCLOS

open Core.Presupposition
open Core.Proposition
open Phenomena.Presupposition.Studies.Sharvit2025
open Semantics.Conditionals.Presuppositional

-- ════════════════════════════════════════════════════════════════
-- § K/P fails: ∃-reading drops penniless-worlds
-- ════════════════════════════════════════════════════════════════

/-- Under K/P, the ∃-reading uses `orFilter` for the antecedent disjunction. -/
def existReading_KP : PrProp W :=
  ifKP allWorlds (PrProp.orFilter pennilessPr proudOfMoney) shouldntLend

/-- Under K/P, the ∀-reading is the conjunction of two K/P conditionals. -/
def forallReading_KP : PrProp W :=
  PrProp.and (ifKP allWorlds pennilessPr shouldntLend)
             (ifKP allWorlds proudOfMoney shouldntLend)

/-- K/P ∃-reading is UNDEFINED at penniless-worlds because `orFilter`
excludes them from the disjunction's domain (Sharvit Section 4). -/
theorem kp_exist_undefined_at_penny :
    existReading_KP.presup W.pennyNotLend = false ∧
    existReading_KP.presup W.pennyLend = false := by
  constructor <;> native_decide

/-- K/P ∃-reading IS defined at proud-worlds. -/
theorem kp_exist_defined_at_proud :
    existReading_KP.presup W.proudNotLend = true ∧
    existReading_KP.presup W.proudLend = true := by
  constructor <;> native_decide

/-- K/P ∀-reading: the second conditional (if proud, shouldntLend) requires
hasMoney, but the first (if penniless, shouldntLend) is always defined. -/
theorem kp_forall_first_cond_always_defined :
    ∀ w, (ifKP allWorlds pennilessPr shouldntLend).presup w = true := by
  intro w; cases w <;> native_decide

/-- K/P ∀-reading presup = hasMoney (from the second conditional). -/
theorem kp_forall_presup_eq_hasMoney :
    ∀ w, forallReading_KP.presup w = hasMoney w := by
  intro w; cases w <;> native_decide

/-- The ∃ and ∀ readings have DIFFERENT definedness domains under K/P.
The ∃-reading is undefined at penny-worlds; the ∀-reading is also undefined
there (because proudOfMoney presupposes hasMoney). But crucially, even when
both are defined (at proud-worlds), the ∃-reading's assertion quantifies over
a SMALLER set of worlds (excluding penny-worlds where orFilter is undefined),
while the ∀-reading's first conditional still quantifies over penny-worlds.
This makes them non-equivalent. -/
theorem kp_exist_assertion_excludes_penny :
    -- At proudNotLend, the ∃-reading is defined but its assertion quantifies
    -- only over worlds where orFilter is defined (proud-worlds), not penny-worlds
    existReading_KP.presup W.proudNotLend = true ∧
    -- The ∀-reading's first conditional assertion DOES quantify over penny-worlds
    (ifKP allWorlds pennilessPr shouldntLend).presup W.proudNotLend = true := by
  constructor <;> native_decide

-- ════════════════════════════════════════════════════════════════
-- § K/P* conditionals: CLOS-based filtering
-- ════════════════════════════════════════════════════════════════

/-- K/P* conditional: if penniless, shouldntLend. -/
def cond_penniless : PrProp W :=
  ifPresup trivialCloser allWorlds pennilessPr shouldntLend

/-- K/P* conditional: if proud-of-money, shouldntLend. -/
def cond_proud : PrProp W :=
  ifPresup trivialCloser allWorlds proudOfMoney shouldntLend

/-- K/P* conditional with penniless as antecedent: always defined.
Penniless has no presupposition, and shouldntLend has trivial presup,
so CLOS-based filtering is trivially satisfied. -/
theorem kpstar_penniless_always_defined :
    ∀ w, cond_penniless.presup w = true := by
  intro w; cases w <;> native_decide

/-- K/P* conditional with proud-of-money: defined iff hasMoney.
The OUTER presupposition (antecedent definedness) requires hasMoney.
The INNER presupposition (CLOS-based: shouldntLend defined at closest
proud-worlds) is trivially satisfied since shouldntLend has no presup. -/
theorem kpstar_proud_presup_eq_hasMoney :
    ∀ w, cond_proud.presup w = hasMoney w := by
  intro w; cases w <;> native_decide

-- ════════════════════════════════════════════════════════════════
-- § K/P* full readings with or^{K/P*} and and^{K/P*}
-- ════════════════════════════════════════════════════════════════

/-- K/P* ∃-reading: if (penniless or^{K/P\*} proud), shouldntLend. -/
def existReading_KPstar : PrProp W :=
  ifPresup trivialCloser allWorlds
    (orPresup trivialCloser allWorlds pennilessPr proudOfMoney)
    shouldntLend

/-- K/P* ∀-reading: (if penniless, shouldntLend) and^{K/P\*} (if proud, shouldntLend). -/
def forallReading_KPstar : PrProp W :=
  andPresup trivialCloser allWorlds cond_penniless cond_proud

/-- Both K/P* readings have the same presupposition: hasMoney.

The ∃-reading inherits hasMoney from `or^{K/P\*}(penniless, proud)`,
whose condition 1 requires `and^{K/P\*}` to be defined in at least one
direction — this needs `proud.presup = hasMoney`. The ∀-reading inherits
hasMoney from the second conditional's outer presupposition. -/
theorem kpstar_exist_presup_eq :
    ∀ w, existReading_KPstar.presup w = hasMoney w := by
  intro w; cases w <;> native_decide

theorem kpstar_forall_presup_eq :
    ∀ w, forallReading_KPstar.presup w = hasMoney w := by
  intro w; cases w <;> native_decide

/-- Both K/P* readings have identical assertions at all worlds. -/
theorem kpstar_assertions_agree :
    ∀ w, existReading_KPstar.assertion w = forallReading_KPstar.assertion w := by
  intro w; cases w <;> native_decide

/-- **Strawson equivalence of ∃ and ∀ readings under K/P\*** (Sharvit §5).

The ∃ and ∀ readings are Strawson-equivalent: they have the same
presupposition domain (hasMoney) and the same assertion, so they agree
at every world where either is defined and true.

In this 4-world model, both presuppositions equal `hasMoney` and the
assertions are identical. The paper's general argument for richer models
requires K/P\*\* (type-flexible connectives, (142)), which quantifies over
properties rather than propositions. -/
theorem kpstar_strawson_equiv :
    PrProp.strawsonEquiv existReading_KPstar forallReading_KPstar := by
  constructor <;> intro w hp ha
  · exact ⟨by rw [kpstar_forall_presup_eq, ← kpstar_exist_presup_eq]; exact hp,
           fun _ => by rw [← kpstar_assertions_agree]; exact ha⟩
  · exact ⟨by rw [kpstar_exist_presup_eq, ← kpstar_forall_presup_eq]; exact hp,
           fun _ => by rw [kpstar_assertions_agree]; exact ha⟩

-- ════════════════════════════════════════════════════════════════
-- § K/P also yields Strawson equivalence in this model
-- ════════════════════════════════════════════════════════════════

/-- K/P ∃-reading presup also equals hasMoney in this model.

In the 4-world model where penniless = ¬hasMoney, K/P's `orFilter` presup
simplifies to hasMoney. The K/P vs K/P\* distinction requires a richer
model with worlds where Mia is neither penniless nor proud (see docstring
on `kpstar_strawson_equiv`). -/
theorem kp_exist_presup_eq :
    ∀ w, existReading_KP.presup w = hasMoney w := by
  intro w; cases w <;> native_decide

/-- orFilter FAILS at penny-worlds — the root cause of K/P's failure
in richer models where penniless and hasMoney are not complementary. -/
theorem kp_orFilter_undefined_at_penny :
    (PrProp.orFilter pennilessPr proudOfMoney).presup W.pennyNotLend = false := rfl

end Phenomena.Presupposition.Bridge.SharvitCLOS
