/-
# The Contrafactive Gap: Bridge Infrastructure

This module connects:
1. The causal model theory (Doxastic.lean) → explains WHY the gap exists
2. The Glass typology (CGRequirement) → describes WHAT the gap looks like
3. The lexical data (Fragments) → which verbs have which properties

## Architecture

```
Fragments (theory-neutral)          Theory (interprets data)
──────────────────────              ──────────────────────
VerbEntry                           Doxastic.lean
├── attitudeBuilder                 ├── CausalModel, PLC
│   (.doxastic .veridical, etc)     ├── CGRequirement typology
│                                   │
│                                   ContrafactiveGap.lean (this file)
│                                   ├── deriveCGReq : VerbEntry → Option CGReq
│                                   ├── Per-verb verification theorems
└───────────────────────────────────┴── yǐwéi exception handled HERE
```

## Key Principle

Fragments contain NO theoretical commitments (no CGRequirement field).
CG requirements are DERIVED in this Bridge layer from `attitudeBuilder`.

Exceptional cases (yǐwéi's postsupposition) are handled HERE, not in Fragments.

## References

- Glass (2025). Attested versus unattested contrafactive belief verbs.
- Roberts & Özyıldız (2025). A causal explanation for the contrafactive gap.
-/

import Linglib.Theories.Semantics.Attitudes.Doxastic
import Linglib.Theories.Semantics.Lexical.Verb.VerbEntry
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Fragments.Mandarin.Predicates

namespace Semantics.Attitudes.ContrafactiveGap

open Semantics.Attitudes.Doxastic
open Core.Verbs
open Fragments.English.Predicates.Verbal

-- ============================================================================
-- Deriving CG Requirements from Fragment Data (Bridge Logic)
-- ============================================================================

/--
Derive CG requirement from a VerbEntry's veridicality.

This is the BRIDGE function that interprets Fragment data theoretically.
The derivation lives HERE (Theory layer), not in Fragments.
-/
def deriveCGReqFromVerb (v : VerbCore) : Option CGRequirement :=
  v.veridicality.bind deriveCGRequirement

/--
Get effective CG requirement for a verb, handling exceptions.

For most verbs: derived from veridicality
For yǐwéi: exceptional postsupposition ◇¬p (weak contrafactive)
-/
def effectiveCGReq (verbForm : String) (v : VerbCore) : Option CGRequirement :=
  if Fragments.Mandarin.Predicates.hasExceptionalPostsupposition verbForm then
    -- yǐwéi has exceptional postsupposition ◇¬p (weak contrafactive)
    some CGRequirement.weakContrafactive
  else
    -- Standard derivation from veridicality
    deriveCGReqFromVerb v

-- ============================================================================
-- yǐwéi: Exceptional Case Handling
-- ============================================================================

/--
**Theorem**: yǐwéi is flagged as having exceptional postsupposition.

This theorem would BREAK if:
1. yǐwéi is removed from the exception list
2. The flag function changes behavior

Breakage signals: re-evaluate whether yǐwéi still needs special handling.
-/
theorem yiwei_is_exceptional :
    Fragments.Mandarin.Predicates.hasExceptionalPostsupposition "yiwei" = true := rfl

/--
**Theorem**: yǐwéi's effective CG requirement is weak contrafactive.

This captures Glass (2022, 2025): yǐwéi requires CG ◇ ¬p.
-/
theorem yiwei_effective_cg :
    effectiveCGReq "yiwei" Fragments.Mandarin.Predicates.yiwei.toVerbCore =
    some CGRequirement.weakContrafactive := rfl

/--
**Theorem**: yǐwéi's derived CG requirement (from veridicality) is NONE.

This proves the exception IS necessary: veridicality alone gives nothing,
but yǐwéi actually has a weak contrafactive postsupposition.
-/
theorem yiwei_derived_cg_none :
    deriveCGReqFromVerb Fragments.Mandarin.Predicates.yiwei.toVerbCore = none := by
  native_decide

/--
**Theorem**: yǐwéi's exception IS justified.

The exception provides something (weak contrafactive) that derivation doesn't (none).
If this theorem ever becomes FALSE, the exception is no longer needed.
-/
theorem yiwei_exception_justified :
    deriveCGReqFromVerb Fragments.Mandarin.Predicates.yiwei.toVerbCore ≠
    effectiveCGReq "yiwei" Fragments.Mandarin.Predicates.yiwei.toVerbCore := by
  simp [deriveCGReqFromVerb, effectiveCGReq]
  native_decide

-- ============================================================================
-- Connecting CGRequirement to the Causal PLC
-- ============================================================================

/--
Map a CGRequirement to the corresponding causal variables for PLC checking.

- Factive (positive × necessity): presup = p, at-issue = B(a)(p)
- Strong contrafactive (negative × necessity): presup = ¬p, at-issue = B(a)(p)

For weak contrafactives and nonfactives, the PLC doesn't directly apply
because they have postsuppositions or no CG requirement.
-/
def cgReqToCausalVars (req : CGRequirement) : Option (CausalVar × CausalVar) :=
  match req.polarity, req.strength with
  | .positive, .necessity => some (BeliefVars.p, BeliefVars.B_a_p)      -- factive
  | .negative, .necessity => some (BeliefVars.not_p, BeliefVars.B_a_p)  -- strong contrafactive
  | .negative, .possibility => none  -- weak contrafactive (postsupposition, not presup)
  | .positive, .possibility => none  -- compatibility requirement

/--
Check if a CGRequirement satisfies the Predicate Lexicalization Constraint.

Returns `none` if the PLC doesn't apply (postsuppositions, no CG requirement).
Returns `some true` if it satisfies PLC.
Returns `some false` if it violates PLC.
-/
def satisfiesPLCOpt (req : CGRequirement) : Option Bool :=
  match cgReqToCausalVars req with
  | none => none
  | some (presup, atIssue) => some (satisfiesPLC presup atIssue)

-- ============================================================================
-- Verification Theorems: Glass Typology ↔ PLC
-- ============================================================================

/--
**Theorem**: Factive requirements satisfy the PLC.

Factives like "know" have presup=p and at-issue=B(a)(p).
There's a causal chain p → indic(p) → acq(a)(iₚ) → B(a)(p).
-/
theorem factive_satisfies_plc' :
    satisfiesPLCOpt CGRequirement.factive = some true := by
  simp [satisfiesPLCOpt, cgReqToCausalVars, CGRequirement.factive]
  exact factive_satisfies_plc

/--
**Theorem**: Strong contrafactive requirements violate the PLC.

Hypothetical "contra" would have presup=¬p and at-issue=B(a)(p).
There's NO causal chain from ¬p to B(a)(p).
-/
theorem strong_contrafactive_violates_plc' :
    satisfiesPLCOpt CGRequirement.strongContrafactive = some false := by
  simp [satisfiesPLCOpt, cgReqToCausalVars, CGRequirement.strongContrafactive]
  exact strong_contrafactive_violates_plc

/--
**Theorem**: Weak contrafactive requirements are not subject to the PLC.

Glass (2022) argues that yǐwéi's falsity inference is a postsupposition
about the output context, not a presupposition about the input context.
The PLC constrains presupposition-assertion pairs, not postsuppositions.
-/
theorem weak_contrafactive_escapes_plc :
    satisfiesPLCOpt CGRequirement.weakContrafactive = none := by
  simp [satisfiesPLCOpt, cgReqToCausalVars, CGRequirement.weakContrafactive]

-- ============================================================================
-- Per-Verb Verification (connecting Fragments to Theory)
-- ============================================================================

/--
For verbs with a CGRequirement, check if the requirement is theoretically valid.
A requirement is valid if it either:
1. Satisfies the PLC (for presuppositions), or
2. Is not subject to the PLC (for postsuppositions)
-/
def cgRequirementIsValid (req : CGRequirement) : Bool :=
  match satisfiesPLCOpt req with
  | none => true        -- Not subject to PLC (postsuppositions OK)
  | some true => true   -- Satisfies PLC
  | some false => false -- Violates PLC (should not exist)

/--
**Key Result**: Strong contrafactives are invalid.

This is WHY they're unattested: they would require a causal chain from
¬p to B(x)(p), which doesn't exist in normal belief formation.
-/
theorem strong_contrafactive_invalid :
    cgRequirementIsValid CGRequirement.strongContrafactive = false := by
  simp [cgRequirementIsValid, satisfiesPLCOpt, cgReqToCausalVars]
  simp [CGRequirement.strongContrafactive]
  exact strong_contrafactive_violates_plc

theorem factive_valid :
    cgRequirementIsValid CGRequirement.factive = true := by
  simp [cgRequirementIsValid, satisfiesPLCOpt, cgReqToCausalVars]
  simp [CGRequirement.factive]
  exact factive_satisfies_plc

theorem weak_contrafactive_valid :
    cgRequirementIsValid CGRequirement.weakContrafactive = true := by
  simp [cgRequirementIsValid, satisfiesPLCOpt, cgReqToCausalVars]
  simp [CGRequirement.weakContrafactive]

-- ============================================================================
-- The Gap as an Explanatory Result
-- ============================================================================

/--
**The Contrafactive Gap Explained**

The gap between factives and strong contrafactives follows from:
1. A general causal constraint on lexicalization (the PLC)
2. The asymmetric structure of belief formation

This is not a stipulation but a DERIVATION from:
- Facts about how beliefs are formed (via evidence acquisition)
- The requirement that presuppositions causally support at-issue content

The result: {factive, weak_contrafactive} are valid; {strong_contrafactive} is not.
-/
theorem contrafactive_gap_explained :
    cgRequirementIsValid CGRequirement.factive = true ∧
    cgRequirementIsValid CGRequirement.weakContrafactive = true ∧
    cgRequirementIsValid CGRequirement.strongContrafactive = false :=
  ⟨factive_valid, weak_contrafactive_valid, strong_contrafactive_invalid⟩

-- ============================================================================
-- Per-Verb Verification: Dense Web of Theorems
-- ============================================================================

/-!
## Per-Verb Verification

Each verb gets explicit theorems that will BREAK if:
1. Its semantic structure changes incompatibly
2. The derivation rules change

This creates the "dense web" where changes propagate and get caught.
-/

/-- All English attitude verbs for batch verification -/
def englishAttitudeVerbs : List VerbEntry :=
  [believe, think, want, hope, expect, wish, fear, dread, worry]

/-- Verify all English attitude verbs have valid derived CG requirements.

Valid means: either satisfies PLC or is not subject to PLC.
-/
theorem all_english_verbs_valid :
    englishAttitudeVerbs.all (fun v =>
      deriveCGReqFromVerb v.toVerbCore |>.map cgRequirementIsValid |>.getD true) = true := by
  native_decide

-- English verbs: CG requirements are DERIVED from veridicality

theorem believe_cg_none :
    deriveCGReqFromVerb believe.toVerbCore = none := by native_decide

theorem think_cg_none :
    deriveCGReqFromVerb think.toVerbCore = none := by native_decide

theorem hope_cg_none :
    deriveCGReqFromVerb hope.toVerbCore = none := by native_decide

theorem fear_cg_none :
    deriveCGReqFromVerb fear.toVerbCore = none := by native_decide

/-!
## Handling yǐwéi's Exception

yǐwéi's postsupposition (◇¬p) is exceptional because:
1. It's NOT a presupposition (input context) but a postsupposition (output)
2. It cannot be derived from veridicality alone
3. It's specific to certain Mandarin verbs

This exception is handled in the Mandarin bridge module, NOT in Fragments.
The Fragment layer remains theory-neutral.

### What Happens If yǐwéi's Exception Becomes Derivable?

If future analysis shows yǐwéi's ◇¬p requirement IS derivable from
some general principle (e.g., a new veridicality category), then:

1. Add the new derivation rule to `deriveCGRequirement` in Doxastic.lean
2. Update verbs in Fragments/Mandarin to have the appropriate attitudeBuilder
3. Per-verb theorems here verify the derivation produces correct results
4. The Mandarin bridge exception becomes unnecessary

The system enforces: **derive what you can, stipulate only what you must**.
-/

end Semantics.Attitudes.ContrafactiveGap
