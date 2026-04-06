import Linglib.Theories.Semantics.Attitudes.Doxastic
import Linglib.Theories.Semantics.Attitudes.NegRaising
import Linglib.Core.Semantics.Presupposition
import Linglib.Core.Semantics.CommonGround
import Linglib.Core.Semantics.Postsupposition
import Linglib.Theories.Semantics.Lexical.Verb.VerbEntry
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Fragments.Mandarin.Predicates

/-!
# Glass (2025): Attested versus unattested contrafactive belief verbs
@cite{glass-2025} @cite{glass-2023} @cite{roberts-ozyildiz-2025}

Semantics and Pragmatics 18, Article 8: 1-17.

## Key Claims

1. **Two ways to negate the factive presupposition**: A contrafactive could
   *require* ¬p (all CG worlds are ¬p worlds) or require *compatibility*
   with ¬p (some CG world is a ¬p world).

2. **Strong contrafactives are unattested**: No verb presupposes ¬p (requiring
   CG ⊨ ¬p). This follows from the Predicate Lexicalization Constraint
   (@cite{roberts-ozyildiz-2025}): ¬p cannot causally support B(x)(p).

3. **Weak contrafactives exist**: Mandarin yǐwéi (@cite{glass-2023}) has a
   postsupposition ◇¬p — after utterance, the CG must be compatible with ¬p.
   This is a definedness condition on the *output* context, not a presupposition
   on the input context.

4. **Revised question**: "Why are there belief verbs like *know* (CG ⊨ p)
   and yǐwéi (CG ◇ ¬p), but none like *contra* (CG ⊨ ¬p)?"

## Formalization Strategy

Belief verb denotations are `PrProp W` values produced by
`DoxasticPredicate.toPrProp`. The presup field captures the factive
presupposition (or lack thereof). yǐwéi's postsupposition is a separate
`Core.Postsupposition` value. The `PresupClass` classification and PLC
validation from `Doxastic.lean` derive the contrafactive gap.
-/

namespace Phenomena.Presupposition.Studies.Glass2025

open Semantics.Attitudes.Doxastic
open Core.Presupposition
open Core.Postsupposition
open Core.Verbs
open Fragments.English.Predicates.Verbal
open Fragments.Mandarin.Predicates

-- ============================================================================
-- §1. MiniWorld Model
-- ============================================================================

/-!
Minimal 2-world model for exercising Table 1.
- `w0`: p is true
- `w1`: p is false
-/

private inductive MiniWorld | w0 | w1
  deriving DecidableEq, Repr, Inhabited

/-- The complement proposition: true at w0, false at w1. -/
private def prop : MiniWorld → Bool
  | .w0 => true
  | .w1 => false

/-- Factive context: all worlds satisfy p (CG ⊨ p). -/
private def factiveCtx : List MiniWorld := [.w0]

/-- Neutral context: p is open (CG ◇ p ∧ CG ◇ ¬p). -/
private def neutralCtx : List MiniWorld := [.w0, .w1]

/-- Contrafactive context: no world satisfies p (CG ⊨ ¬p). -/
private def contrafactiveCtx : List MiniWorld := [.w1]

-- ============================================================================
-- §2. Belief Verb PrProps
-- ============================================================================

/-!
Construct presuppositional denotations for four verb types directly
from veridicality, matching @cite{glass-2025} Table 1.

We define the presup fields directly (rather than instantiating full
`DoxasticPredicate`s) to keep the model minimal. The connection to
`DoxasticPredicate.toPrProp` is established by the classification
theorems in §4.
-/

/-- *know*: presupposes p (factive). -/
private def knowPresup : PrProp MiniWorld :=
  { presup := prop         -- p must hold
  , assertion := λ _ => true }  -- (at-issue suppressed for CG tests)

/-- *think*: no presupposition (nonfactive). -/
private def thinkPresup : PrProp MiniWorld :=
  { presup := λ _ => true   -- no constraint
  , assertion := λ _ => true }

/-- Hypothetical *contra*: presupposes ¬p (strong contrafactive). -/
private def contraPresup : PrProp MiniWorld :=
  { presup := λ w => !prop w   -- ¬p must hold
  , assertion := λ _ => true }

/-- yǐwéi: nonfactive PrProp + postsupposition ◇¬p. -/
private def yiweiPresup : PrProp MiniWorld :=
  { presup := λ _ => true      -- no input-context presupposition
  , assertion := λ _ => true }

/-- yǐwéi's postsupposition: CG must be compatible with ¬p. -/
private def yiweiPostsup : Postsupposition MiniWorld :=
  Postsupposition.weakContrafactive

-- ============================================================================
-- §3. Table 1: Context-Set Satisfaction (@cite{glass-2025})
-- ============================================================================

/-!
Table 1 from @cite{glass-2025}: possible states of the Common Ground
*after* updating with each utterance.

|  Utterance   | Projective content | p   | ◇p ∧ ◇¬p | not-p |
|--------------|-------------------|-----|-----------|-------|
| x knows p    | requires p        | ✓   | ✗         | ✗     |
| x thinks p   | (none)            | ✓   | ✓         | ✓     |
| x yǐwéi p   | requires ◇(¬p)    | ✗   | ✓         | ✓     |
| x contra p   | requires ¬p       | ✗   | ✗         | ✓     |

We verify this by checking the presup field against each context type.
-/

-- know: presup satisfied only in factive context

theorem know_satisfied_factive :
    factiveCtx.all knowPresup.presup = true := rfl

theorem know_fails_neutral :
    neutralCtx.all knowPresup.presup = false := rfl

theorem know_fails_contrafactive :
    contrafactiveCtx.all knowPresup.presup = false := rfl

-- think: presup satisfied in all contexts (no constraint)

theorem think_satisfied_factive :
    factiveCtx.all thinkPresup.presup = true := rfl

theorem think_satisfied_neutral :
    neutralCtx.all thinkPresup.presup = true := rfl

theorem think_satisfied_contrafactive :
    contrafactiveCtx.all thinkPresup.presup = true := rfl

-- yǐwéi: presup (input) satisfied everywhere; postsup fails in factive ctx

theorem yiwei_presup_satisfied_factive :
    factiveCtx.all yiweiPresup.presup = true := rfl

theorem yiwei_presup_satisfied_neutral :
    neutralCtx.all yiweiPresup.presup = true := rfl

theorem yiwei_postsup_fails_factive :
    yiweiPostsup.satisfied factiveCtx prop = false := rfl

theorem yiwei_postsup_satisfied_neutral :
    yiweiPostsup.satisfied neutralCtx prop = true := rfl

theorem yiwei_postsup_satisfied_contrafactive :
    yiweiPostsup.satisfied contrafactiveCtx prop = true := rfl

-- contra: presup satisfied only in contrafactive context

theorem contra_fails_factive :
    factiveCtx.all contraPresup.presup = false := rfl

theorem contra_fails_neutral :
    neutralCtx.all contraPresup.presup = false := rfl

theorem contra_satisfied_contrafactive :
    contrafactiveCtx.all contraPresup.presup = true := rfl

-- ============================================================================
-- §4. Per-Verb Verification: Fragment Entries → PresupClass
-- ============================================================================

/-!
Each English/Mandarin attitude verb's `PresupClass` is DERIVED from its
veridicality in the Fragment entry. These theorems will BREAK if:
1. A verb's `attitudeBuilder` changes
2. The `classifyVeridicality` function changes
3. The `veridicality` derivation from `AttitudeBuilder` changes
-/

-- Factive verbs → .factive

theorem know_is_factive :
    know.toVerbCore.veridicality.map classifyVeridicality = some .factive := by
  native_decide

theorem realize_is_factive :
    realize.toVerbCore.veridicality.map classifyVeridicality = some .factive := by
  native_decide

theorem discover_is_factive :
    discover.toVerbCore.veridicality.map classifyVeridicality = some .factive := by
  native_decide

theorem notice_is_factive :
    notice.toVerbCore.veridicality.map classifyVeridicality = some .factive := by
  native_decide

-- Non-factive verbs → .nonfactive

theorem believe_is_nonfactive :
    believe.toVerbCore.veridicality.map classifyVeridicality = some .nonfactive := by
  native_decide

theorem think_is_nonfactive :
    think.toVerbCore.veridicality.map classifyVeridicality = some .nonfactive := by
  native_decide

theorem hope_is_nonfactive :
    hope.toVerbCore.veridicality.map classifyVeridicality = some .nonfactive := by
  native_decide

theorem fear_is_nonfactive :
    fear.toVerbCore.veridicality.map classifyVeridicality = some .nonfactive := by
  native_decide

-- yǐwéi: classified as nonfactive by veridicality alone

theorem yiwei_veridicality_nonfactive :
    yiwei.toVerbCore.veridicality.map classifyVeridicality = some .nonfactive := by
  native_decide

-- ============================================================================
-- §5. yǐwéi Exception: Postsupposition Not Derivable from Veridicality
-- ============================================================================

/-!
yǐwéi is classified as nonfactive by veridicality (§4), but it has an
additional postsupposition ◇¬p that is NOT derivable from veridicality.
This postsupposition is flagged in the Fragment layer and interpreted here.
-/

/-- yǐwéi carries a weak contrafactive postsupposition structurally. -/
theorem yiwei_has_postsupposition :
    yiwei.toVerbCore.postsupType = some .weakContrafactive := by native_decide

/-- yǐwéi's veridicality gives nonfactive — no presupposition. -/
theorem yiwei_derived_nonfactive :
    yiwei.toVerbCore.veridicality = some .nonVeridical := by native_decide

/-- The postsupposition IS necessary: veridicality alone gives .nonfactive
    (no presupposition), but yǐwéi actually has a weak contrafactive
    postsupposition. Without `postsupType`, this would be invisible. -/
theorem yiwei_postsup_not_from_veridicality :
    yiwei.toVerbCore.veridicality.map classifyVeridicality = some .nonfactive ∧
    yiwei.toVerbCore.postsupType = some .weakContrafactive :=
  ⟨by native_decide, by native_decide⟩

-- ============================================================================
-- §6. The Contrafactive Gap
-- ============================================================================

/-!
The contrafactive gap DERIVED from the Predicate Lexicalization Constraint:

- Factive (know): presup = p → PLC satisfied (p → indic(p) → B(a)(p)) ✓
- Nonfactive (think): no presupposition → PLC not applicable ✓
- Contrafactive (contra): presup = ¬p → PLC violated (¬p ↛ B(a)(p)) ✗

This is not a stipulation — it follows from the causal structure of
belief formation (@cite{roberts-ozyildiz-2025}).
-/

/-- The contrafactive gap: factive and nonfactive are valid;
    contrafactive is invalid. -/
theorem contrafactive_gap :
    presupClassIsValid .factive = true ∧
    presupClassIsValid .nonfactive = true ∧
    presupClassIsValid .contrafactive = false :=
  ⟨factive_presup_valid, nonfactive_presup_valid, contrafactive_presup_invalid⟩

/-- All English attitude verbs have valid presuppositional profiles. -/
theorem all_english_attitude_verbs_valid :
    [know, realize, discover, notice, believe, think, want, hope,
     expect, wish, fear, dread, worry].all (fun v =>
      v.toVerbCore.veridicality.map classifyVeridicality |>.map
        presupClassIsValid |>.getD true) = true := by
  native_decide

-- ============================================================================
-- §7. End-to-End Derivation
-- ============================================================================

/-!
The full derivation chain:
  Fragment entry → attitudeBuilder → veridicality → PresupClass
    → presupClassIsValid → PLC check

This section exercises the complete pipeline for representative verbs.
-/

/-- End-to-end: "know" is factive, and factive presuppositions are valid. -/
theorem know_endtoend_valid :
    (know.toVerbCore.veridicality.map classifyVeridicality).map
      presupClassIsValid = some true := by native_decide

/-- End-to-end: "believe" is nonfactive, and nonfactive is valid. -/
theorem believe_endtoend_valid :
    (believe.toVerbCore.veridicality.map classifyVeridicality).map
      presupClassIsValid = some true := by native_decide

/-- End-to-end: know's presupposition is satisfied in a factive context. -/
theorem know_presup_satisfied_endtoend :
    factiveCtx.all prop = true := rfl

/-- End-to-end: know's presupposition fails in a neutral context. -/
theorem know_presup_fails_endtoend :
    neutralCtx.all prop = false := rfl

/-- End-to-end: yǐwéi's postsupposition is satisfied in a neutral context
    (where veridicality-based presupposition is vacuously OK). -/
theorem yiwei_endtoend :
    neutralCtx.all yiweiPresup.presup = true ∧
    yiweiPostsup.satisfied neutralCtx prop = true :=
  ⟨rfl, rfl⟩

-- ============================================================================
-- §8. Connection to Neg-Raising (@cite{glass-2025} §4.2)
-- ============================================================================

/-!
@cite{glass-2025} §4.2 notes that yǐwéi supports neg-raising, like other
nonfactive verbs. This follows from `Veridicality`: neg-raising is available
for non-veridical predicates (@cite{gajewski-2007}, `NegRaising.lean`).

Since `PresupClass.nonfactive` verbs are exactly the non-veridical ones,
the neg-raising gap aligns with the contrafactive gap.
-/

open Semantics.Attitudes.NegRaising (negRaisingAvailable)

/-- Nonfactive verbs (including yǐwéi) support neg-raising. -/
theorem nonfactive_supports_negRaising :
    negRaisingAvailable .nonVeridical = true := rfl

/-- Factive verbs do NOT support neg-raising. -/
theorem factive_blocks_negRaising :
    negRaisingAvailable .veridical = false := rfl

/-- The contrafactive gap and the neg-raising gap trace to the same
    source: veridicality. Factives satisfy PLC but block neg-raising;
    nonfactives escape PLC (no presupposition) and support neg-raising. -/
theorem veridicality_determines_both :
    -- Factive: satisfies PLC, blocks neg-raising
    presupClassIsValid .factive = true ∧
    negRaisingAvailable .veridical = false ∧
    -- Nonfactive: PLC not applicable, supports neg-raising
    presupClassIsValid .nonfactive = true ∧
    negRaisingAvailable .nonVeridical = true :=
  ⟨factive_presup_valid, rfl, nonfactive_presup_valid, rfl⟩

end Phenomena.Presupposition.Studies.Glass2025
