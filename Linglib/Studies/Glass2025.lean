import Linglib.Semantics.Attitudes.Doxastic
import Linglib.Semantics.Attitudes.NegRaising
import Linglib.Semantics.Presupposition.Context
import Linglib.Semantics.Verb.Basic
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Fragments.Mandarin.Predicates

/-!
# Glass (2025): Attested versus unattested contrafactive belief verbs
[glass-2025] [glass-2023] [roberts-ozyildiz-2025]

Semantics and Pragmatics 18, Article 8: 1-17.

## Key Claims

1. **Two ways to negate the factive presupposition**: A contrafactive could
   *require* ¬p (all CommonGround worlds are ¬p worlds) or require *compatibility*
   with ¬p (some CommonGround world is a ¬p world).

2. **Strong contrafactives are unattested**: No verb presupposes ¬p (requiring
   CommonGround ⊨ ¬p). This follows from the Predicate Lexicalization Constraint
   ([roberts-ozyildiz-2025]): ¬p cannot causally support B(x)(p).

3. **Weak contrafactives exist**: Mandarin yǐwéi ([glass-2023]) has a
   postsupposition ◇¬p — after utterance, the CommonGround must be compatible with ¬p.
   This is a definedness condition on the *output* context, not a presupposition
   on the input context.

4. **Revised question**: "Why are there belief verbs like *know* (CommonGround ⊨ p)
   and yǐwéi (CommonGround ◇ ¬p), but none like *contra* (CommonGround ⊨ ¬p)?"

## Formalization Strategy

Belief verb denotations are `PartialProp W` values produced by
`DoxasticPredicate.toPartialProp`. The presup field captures the factive
presupposition (or lack thereof). yǐwéi's postsupposition is a
`Postsupposition` value (§2 below). The `PresupClass` classification and PLC
validation from `Doxastic.lean` derive the contrafactive gap.
-/

namespace Glass2025

open Semantics.Attitudes.Doxastic
open Semantics.Presupposition
open ArgumentStructure
open English.Predicates.Verbal
open Mandarin.Predicates

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

/-- Factive context: all worlds satisfy p (CommonGround ⊨ p). -/
private def factiveCtx : List MiniWorld := [.w0]

/-- Neutral context: p is open (CommonGround ◇ p ∧ CommonGround ◇ ¬p). -/
private def neutralCtx : List MiniWorld := [.w0, .w1]

/-- Contrafactive context: no world satisfies p (CommonGround ⊨ ¬p). -/
private def contrafactiveCtx : List MiniWorld := [.w1]

-- ============================================================================
-- §2. Postsuppositions
-- ============================================================================

/-!
Output-context constraints ([brasoveanu-2013]): conditions on the Common
Ground *after* an utterance updates it, as opposed to presuppositions,
which constrain the *input* context. [glass-2025] argues Mandarin yǐwéi
carries the postsupposition ◇¬p: after accepting "x yǐwéi p", the
CommonGround must be compatible with ¬p — a condition not derivable from
veridicality alone.
-/

/-- A postsupposition: a constraint on the output context after a discourse
    update, taking the context set (as `List W`) and the embedded
    proposition. -/
structure Postsupposition (W : Type*) where
  condition : List W → (W → Prop) → Prop

namespace Postsupposition

variable {W : Type*}

/-- No postsupposition (trivially satisfied). -/
protected def none : Postsupposition W := ⟨fun _ _ => True⟩

/-- Weak contrafactive: the output context is *compatible* with ¬p — some
    world in the output context falsifies p. This is yǐwéi's ◇¬p
    ([glass-2025], [glass-2023]). -/
def weakContrafactive : Postsupposition W :=
  ⟨fun cs p => ∃ w ∈ cs, ¬ p w⟩

/-- Strong contrafactive: the output context *entails* ¬p — every world in
    the output context falsifies p. The hypothetical *contra* verb's
    requirement — UNATTESTED. -/
def strongContrafactive : Postsupposition W :=
  ⟨fun cs p => ∀ w ∈ cs, ¬ p w⟩

/-- The trivial postsupposition is always satisfied. -/
theorem none_condition (cs : List W) (p : W → Prop) :
    Postsupposition.none.condition cs p := trivial

/-- Strong contrafactivity entails weak (nonempty contexts): CommonGround ⊨ ¬p
    forces CommonGround ◇ ¬p — [glass-2025]'s observation that yǐwéi's
    requirement is strictly weaker than *contra*'s. -/
theorem strong_entails_weak {cs : List W} {p : W → Prop} (hne : cs ≠ [])
    (h : strongContrafactive.condition cs p) :
    weakContrafactive.condition cs p :=
  match cs, hne with
  | w :: _, _ => ⟨w, by simp, h w (by simp)⟩

/-- Weak contrafactivity does not entail strong: a context can be compatible
    with ¬p without entailing ¬p. -/
theorem weak_not_entails_strong :
    ∃ (cs : List Bool) (p : Bool → Prop),
      weakContrafactive.condition cs p ∧ ¬ strongContrafactive.condition cs p :=
  ⟨[true, false], (· = true), ⟨false, by simp, by simp⟩,
    fun h => h true (by simp) rfl⟩

end Postsupposition

-- ============================================================================
-- §3. Belief Verb PartialProps
-- ============================================================================

/-!
Construct presuppositional denotations for four verb types directly
from veridicality, matching [glass-2025] Table 1.

We define the presup fields directly (rather than instantiating full
`DoxasticPredicate`s) to keep the model minimal. The connection to
`DoxasticPredicate.toPartialProp` is established by the classification
theorems in §4.
-/

/-- *know*: presupposes p (factive). -/
private def knowPresup : PartialProp MiniWorld where
  presup := λ w => prop w = true
  assertion := λ _ => True

/-- *think*: no presupposition (nonfactive). -/
private def thinkPresup : PartialProp MiniWorld where
  presup := λ _ => True
  assertion := λ _ => True

/-- Hypothetical *contra*: presupposes ¬p (strong contrafactive). -/
private def contraPresup : PartialProp MiniWorld where
  presup := λ w => prop w = false
  assertion := λ _ => True

/-- yǐwéi: nonfactive PartialProp + postsupposition ◇¬p. -/
private def yiweiPresup : PartialProp MiniWorld where
  presup := λ _ => True
  assertion := λ _ => True

/-- yǐwéi's postsupposition: CommonGround must be compatible with ¬p. -/
private def yiweiPostsup : Postsupposition MiniWorld :=
  Postsupposition.weakContrafactive

-- ============================================================================
-- §4. Table 1: Context-Set Satisfaction ([glass-2025])
-- ============================================================================

/-!
Table 1 from [glass-2025]: possible states of the Common Ground
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
    ∀ w ∈ factiveCtx, knowPresup.presup w := by
  intro w hw; simp only [factiveCtx, List.mem_cons, List.mem_nil_iff, or_false] at hw
  subst hw; rfl

theorem know_fails_neutral :
    ¬∀ w ∈ neutralCtx, knowPresup.presup w := by
  intro h; have := h .w1 (List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inl rfl))))
  simp [knowPresup, prop] at this

theorem know_fails_contrafactive :
    ¬∀ w ∈ contrafactiveCtx, knowPresup.presup w := by
  intro h; have := h .w1 (List.mem_cons.mpr (.inl rfl))
  simp [knowPresup, prop] at this

-- think: presup satisfied in all contexts (no constraint)

theorem think_satisfied_factive :
    ∀ w ∈ factiveCtx, thinkPresup.presup w := by
  intro _ _; trivial

theorem think_satisfied_neutral :
    ∀ w ∈ neutralCtx, thinkPresup.presup w := by
  intro _ _; trivial

theorem think_satisfied_contrafactive :
    ∀ w ∈ contrafactiveCtx, thinkPresup.presup w := by
  intro _ _; trivial

-- yǐwéi: presup (input) satisfied everywhere; postsup fails in factive ctx

theorem yiwei_presup_satisfied_factive :
    ∀ w ∈ factiveCtx, yiweiPresup.presup w := by
  intro _ _; trivial

theorem yiwei_presup_satisfied_neutral :
    ∀ w ∈ neutralCtx, yiweiPresup.presup w := by
  intro _ _; trivial

theorem yiwei_postsup_fails_factive :
    ¬ yiweiPostsup.condition factiveCtx (prop · = true) := by
  simp [yiweiPostsup, Postsupposition.weakContrafactive, factiveCtx, prop]

theorem yiwei_postsup_satisfied_neutral :
    yiweiPostsup.condition neutralCtx (prop · = true) :=
  ⟨.w1, by simp [neutralCtx], by simp [prop]⟩

theorem yiwei_postsup_satisfied_contrafactive :
    yiweiPostsup.condition contrafactiveCtx (prop · = true) :=
  ⟨.w1, by simp [contrafactiveCtx], by simp [prop]⟩

-- contra: presup satisfied only in contrafactive context

theorem contra_fails_factive :
    ¬∀ w ∈ factiveCtx, contraPresup.presup w := by
  intro h; have := h .w0 (List.mem_cons.mpr (.inl rfl))
  simp [contraPresup, prop] at this

theorem contra_fails_neutral :
    ¬∀ w ∈ neutralCtx, contraPresup.presup w := by
  intro h; have := h .w0 (List.mem_cons.mpr (.inl rfl))
  simp [contraPresup, prop] at this

theorem contra_satisfied_contrafactive :
    ∀ w ∈ contrafactiveCtx, contraPresup.presup w := by
  intro w hw; simp only [contrafactiveCtx, List.mem_cons, List.mem_nil_iff, or_false] at hw
  subst hw; rfl

-- ============================================================================
-- §5. Per-Verb Verification: Fragment Entries → PresupClass
-- ============================================================================

/-!
Each English/Mandarin attitude verb's `PresupClass` is DERIVED from its
veridicality in the Fragment entry. These theorems will BREAK if:
1. A verb's `attitude` changes
2. The `classifyVeridicality` function changes
3. The `veridicality` derivation from `Attitude` changes
-/

-- Factive verbs → .factive

theorem know_is_factive :
    know.toVerb.veridicality.map classifyVeridicality = some .factive := by
  native_decide

theorem realize_is_factive :
    realize.toVerb.veridicality.map classifyVeridicality = some .factive := by
  native_decide

theorem discover_is_factive :
    discover.toVerb.veridicality.map classifyVeridicality = some .factive := by
  native_decide

theorem notice_is_factive :
    notice.toVerb.veridicality.map classifyVeridicality = some .factive := by
  native_decide

-- Non-factive verbs → .nonfactive

theorem believe_is_nonfactive :
    believe.toVerb.veridicality.map classifyVeridicality = some .nonfactive := by
  native_decide

theorem think_is_nonfactive :
    think.toVerb.veridicality.map classifyVeridicality = some .nonfactive := by
  native_decide

theorem hope_is_nonfactive :
    hope.toVerb.veridicality.map classifyVeridicality = some .nonfactive := by
  native_decide

theorem fear_is_nonfactive :
    fear.toVerb.veridicality.map classifyVeridicality = some .nonfactive := by
  native_decide

-- yǐwéi: classified as nonfactive by veridicality alone

theorem yiwei_veridicality_nonfactive :
    yiwei.toVerb.veridicality.map classifyVeridicality = some .nonfactive := by
  native_decide

-- ============================================================================
-- §6. yǐwéi Exception: Postsupposition Not Derivable from Veridicality
-- ============================================================================

/-!
yǐwéi is classified as nonfactive by veridicality (§5), but it has an
additional postsupposition ◇¬p that is NOT derivable from veridicality.
Veridicality is a derivable property of the canonical Mandarin entry; the
postsupposition is [glass-2025]'s paper-specific overlay, recorded here
in the study rather than as a field on the Fragment entry.
-/

/-- Postsupposition type: output-context constraint distinct from
    presuppositions ([glass-2025]). The world-type-independent tag; the
    concrete construct is `Postsupposition` (§2). -/
inductive PostsupType where
  /-- Output context must be compatible with ¬p: ◇¬p ([glass-2025]). -/
  | weakContrafactive
  /-- Output context must entail ¬p: ⊨¬p (hypothetical, UNATTESTED). -/
  | strongContrafactive
  deriving DecidableEq, Repr

/-- [glass-2025] classifies yǐwéi as carrying a weak contrafactive
    postsupposition. This is the paper's analytical claim about the canonical
    Mandarin `yiwei` entry — not a field on that entry. -/
def yiweiPostsupType : PostsupType := .weakContrafactive

/-- yǐwéi's veridicality gives nonfactive — no presupposition. -/
theorem yiwei_derived_nonfactive :
    yiwei.toVerb.veridicality = some .nonVeridical := by native_decide

/-- The postsupposition IS necessary: veridicality alone gives .nonfactive
    (no presupposition), but yǐwéi actually has a weak contrafactive
    postsupposition. Pairing the canonical entry's derivable veridicality with
    Glass's postsupposition classification shows the two diverge — veridicality
    is blind to the postsupposition. -/
theorem yiwei_postsup_not_from_veridicality :
    yiwei.toVerb.veridicality.map classifyVeridicality = some .nonfactive ∧
    yiweiPostsupType = .weakContrafactive :=
  ⟨by native_decide, rfl⟩

-- ============================================================================
-- §7. The Contrafactive Gap
-- ============================================================================

/-!
The contrafactive gap DERIVED from the Predicate Lexicalization Constraint:

- Factive (know): presup = p → PLC satisfied (p → indic(p) → B(a)(p)) ✓
- Nonfactive (think): no presupposition → PLC not applicable ✓
- Contrafactive (contra): presup = ¬p → PLC violated (¬p ↛ B(a)(p)) ✗

This is not a stipulation — it follows from the causal structure of
belief formation ([roberts-ozyildiz-2025]).
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
      v.toVerb.veridicality.map classifyVeridicality |>.map
        presupClassIsValid |>.getD true) = true := by
  native_decide

-- ============================================================================
-- §8. End-to-End Derivation
-- ============================================================================

/-!
The full derivation chain:
  Fragment entry → attitude → veridicality → PresupClass
    → presupClassIsValid → PLC check

This section exercises the complete pipeline for representative verbs.
-/

/-- End-to-end: "know" is factive, and factive presuppositions are valid. -/
theorem know_endtoend_valid :
    (know.toVerb.veridicality.map classifyVeridicality).map
      presupClassIsValid = some true := by native_decide

/-- End-to-end: "believe" is nonfactive, and nonfactive is valid. -/
theorem believe_endtoend_valid :
    (believe.toVerb.veridicality.map classifyVeridicality).map
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
    (∀ w ∈ neutralCtx, yiweiPresup.presup w) ∧
    yiweiPostsup.condition neutralCtx (prop · = true) :=
  ⟨fun _ _ => trivial, ⟨.w1, by simp [neutralCtx], by simp [prop]⟩⟩

-- ============================================================================
-- §9. Connection to Neg-Raising ([glass-2025] §4.2)
-- ============================================================================

/-!
[glass-2025] §4.2 notes that yǐwéi supports neg-raising, like other
nonfactive verbs. This follows from `Veridicality`: neg-raising is available
for non-veridical predicates ([gajewski-2007], `NegRaising.lean`).

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

end Glass2025
