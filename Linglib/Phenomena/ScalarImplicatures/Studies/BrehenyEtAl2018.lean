import Linglib.Theories.Semantics.Exhaustification.InnocentExclusion
import Linglib.Theories.Semantics.Alternatives.Symmetric

/-!
# The Symmetry Problem: Current Theories and Prospects
@cite{breheny-et-al-2018}

Breheny, R., Klinedinst, N., Romoli, J. & Sudo, Y. (2018).
The Symmetry Problem: Current Theories and Prospects.
Natural Language Semantics, 26(2), 85–110.

## Overview

Critical survey of three approaches to the **symmetry problem** for
scalar implicature alternatives:

1. **Structural approach** (@cite{katzir-2007}, @cite{fox-katzir-2011}):
   alternatives restricted by structural complexity. Solves the basic
   symmetry problem (some/all) but undergenerates for indirect and
   particularised scalar implicatures.

2. **Atomicity Constraint** (@cite{trinh-haida-2015}): augments the
   structural approach by making extracted subconstituents atomic (opaque
   to further substitution). Solves indirect SIs but wrongly blocks
   the needed antonym alternative for gradable adjectives under negation.

3. **RSA approach** (@cite{bergen-levy-goodman-2016}): replaces structural
   restriction with utterance cost + relative informativity. Handles
   direct SIs and gradable adjectives but fails for indirect SIs of
   equal complexity and for the @cite{swanson-2010} cases.

No single approach handles all cases. The symmetry problem remains open.

## Formalization Strategy

The paper's core arguments are demonstrated computationally using the
`exhB`/`ieIndices` machinery from @cite{fox-2007} (`InnocentExclusion.lean`).
Each section defines a small domain and shows how different alternative
sets yield different (correct/incorrect) predictions. This makes the
paper's claims machine-checkable: the structural approach's failures
and the AC's overcorrection are verified by `native_decide`.

## Key Results

- `indirect_si_blocked`: with symmetric alts, exh fails for indirect SIs
- `indirect_si_correct`: without symmetric alt, exh derives correct SI
- `ac_wrong_for_adjectives`: the AC produces wrong prediction for full/empty
- `adjective_correct_alts`: the correct prediction requires alts the AC blocks
- `particularised_symmetric`: smoked/ran∧¬smoked partition ran
- `swanson_symmetric`: required/optional partition permitted
- `swanson_exh_vacuous`: lexicalized symmetric alts make exh vacuous
-/

namespace Phenomena.ScalarImplicatures.Studies.BrehenyEtAl2018

open Exhaustification.InnocentExclusion
open Alternatives.Symmetric


-- ═══════════════════════════════════════════════════════════════════════
-- §1  Indirect Scalar Implicatures (§2.2, examples 12–15)
-- ═══════════════════════════════════════════════════════════════════════

/-!
## The Problem of Indirect Scalar Implicatures

(12a) John didn't do all of the homework.
(12b) ⤳ John did some of the homework.

This is an **indirect** SI: the inference arises from negating the
stronger alternative ¬any (= "didn't do any") under the scope of
sentential negation. The structural approach (@cite{fox-katzir-2011})
wrongly generates the symmetric alternative "some" (= "did some")
by extracting the VP subconstituent and substituting all→some within
it, blocking the correct inference.

@cite{trinh-haida-2015}'s Atomicity Constraint solves this: after
extracting the VP, it becomes atomic and the internal substitution
all→some is blocked.
-/

section IndirectSI

/-- Three homework worlds: did none, did some but not all, did all. -/
inductive HWWorld where
  | none_ | someNotAll | all_
  deriving Repr, DecidableEq, BEq

private def hwDomain : List HWWorld := [.none_, .someNotAll, .all_]

/-- ¬all = "didn't do all the homework" = {none, someNotAll}. -/
private def notAll : HWWorld → Bool
  | .none_ | .someNotAll => true | .all_ => false

/-- ¬any = "didn't do any" = {none}. Stronger than ¬all. -/
private def notAny : HWWorld → Bool
  | .none_ => true | _ => false

/-- some = "did some" = {someNotAll, all}. Independent of ¬all. -/
private def didSome : HWWorld → Bool
  | .someNotAll | .all_ => true | .none_ => false

/-- With the symmetric alternative "some" present (as the structural
    approach generates), exh is vacuous: neither ¬any nor some is in
    I-E. The correct inference (12b) is not derived.

    F(12a) ⊇ {¬all, ¬any, some} per @cite{fox-katzir-2011}, because
    "some" is derivable by extracting the VP subconstituent and
    substituting all→some within it. -/
theorem indirect_si_blocked :
    ∀ w : HWWorld, exhB hwDomain [notAll, notAny, didSome] notAll w
      = notAll w := by
  intro w; cases w <;> native_decide

/-- Without "some" (the Atomicity Constraint's prediction), exh
    correctly derives the indirect SI: ¬all ∧ ¬(¬any) = {someNotAll}.

    The AC blocks "some" because deriving it requires extracting the
    VP and then substituting within it, violating atomicity. -/
theorem indirect_si_correct :
    ∀ w : HWWorld, exhB hwDomain [notAll, notAny] notAll w
      = (notAll w && didSome w) := by
  intro w; cases w <;> native_decide

/-- I-E includes ¬any when "some" is absent. -/
theorem ac_solves_indirect_si :
    (ieIndices hwDomain notAll [notAll, notAny]).contains 1 = true := by
  native_decide

end IndirectSI


-- ═══════════════════════════════════════════════════════════════════════
-- §2  AC Fails: Gradable Adjectives (§3.2.2, examples 32–40)
-- ═══════════════════════════════════════════════════════════════════════

/-!
## Gradable Adjectives Under Negation

The Atomicity Constraint backfires for gradable adjectives with
contradictory antonyms:

(32) It's not the case that the glass is full.
  a. ⤳ The glass is not empty.        (observed)
  b. ⤴ The glass is empty.            (not observed)

The structural approach generates "not empty" as an alternative to
"not full" by simple lexical substitution of full→empty under negation.
The AC also blocks "empty" (the bare positive form) because deriving
it requires extracting the AP/S subconstituent and substituting within
it (ex. 40).

Without "empty" to serve as a counterweight, exh negates "not empty"
and derives the WRONG inference (32b): the glass IS empty. The AC's
solution for one class of cases (indirect SIs) creates a problem for
another (gradable adjectives).

### Adjective pair asymmetry (ex. 38)

Not all contradictory antonym pairs generate the inference:
- full/empty: "not full" ⤳ not empty      ✓
- required/allowed: "not required" ⤳ allowed ✓
- certain/possible: "not certain" ⤳ possible ✓
- safe/dangerous: "not safe" ⤴ not dangerous  ✗
- tall/short: "not tall" ⤴ not short      ✗
- transparent/opaque: "not transparent" ⤴ not opaque ✗

The paper notes this variation cuts across scale structure: safe has
an upper closed scale, transparent has a fully closed scale, and tall
a fully open scale — yet none generates the inference. The explanation
remains open, though the paper suggests the POS morpheme and its
interaction with degree modifiers (partly, half) may be relevant.
-/

section GradableAdjectives

/-- Three-degree scale for a closed-scale adjective pair (full/empty).
    Represents glass fullness: empty (0), mid (0.5), full (1). -/
inductive GlassWorld where
  | empty_ | mid | full_
  deriving Repr, DecidableEq, BEq

private def glassDomain : List GlassWorld := [.empty_, .mid, .full_]

private def isFull : GlassWorld → Bool
  | .full_ => true | _ => false

private def isEmpty : GlassWorld → Bool
  | .empty_ => true | _ => false

private def notFull : GlassWorld → Bool
  | .empty_ | .mid => true | .full_ => false

private def notEmpty : GlassWorld → Bool
  | .mid | .full_ => true | .empty_ => false

-- ── Full alternative set (no AC) ─────────────────────────────

/-- With all four alternatives {¬full, ¬empty, full, empty}, only
    "full" (index 2) is in I-E — but ¬full already entails ¬full,
    so exh adds nothing. The crucial inference ¬empty is NOT derived.

    This is because ¬empty and empty cannot both be excluded
    (¬empty ∧ empty = ⊥), and they end up in different MCEs. -/
theorem adjective_full_alts_ie :
    ieIndices glassDomain notFull [notFull, notEmpty, isFull, isEmpty]
      = [2] := by native_decide

/-- Consequence: exh(¬full) = ¬full (vacuous for the empty/¬empty
    pair). Neither the correct inference (32a) nor the wrong one (32b)
    is derived. -/
theorem adjective_full_alts_vacuous :
    ∀ w : GlassWorld,
      exhB glassDomain [notFull, notEmpty, isFull, isEmpty] notFull w
        = notFull w := by
  intro w; cases w <;> native_decide

-- ── AC alternative set (empty removed) ───────────────────────

/-- With the AC, "empty" is blocked (requires extraction + substitution,
    ex. 40). Alternatives: {¬full, ¬empty, full}. Now both ¬empty
    (index 1) and full (index 2) are in I-E. -/
theorem ac_adjective_ie :
    ieIndices glassDomain notFull [notFull, notEmpty, isFull]
      = [1, 2] := by native_decide

/-- The AC produces the WRONG prediction: exh(¬full) = ¬full ∧ empty
    = {empty}. This says the glass IS empty — inference (32b).

    The derivation: ¬empty is in I-E, so exh negates it. ¬(¬empty)
    = empty. Combined with ¬full: ¬full ∧ empty = {empty}. -/
theorem ac_wrong_for_adjectives :
    ∀ w : GlassWorld,
      exhB glassDomain [notFull, notEmpty, isFull] notFull w
        = isEmpty w := by
  intro w; cases w <;> native_decide

-- ── Desired alternative set ──────────────────────────────────

/-- To derive the correct inference (32a), the alternatives must
    include "empty" but NOT "¬empty". Then exh(¬full) = ¬full ∧
    ¬empty = {mid} — the glass is neither full nor empty.

    No version of the structural approach (with or without AC)
    produces this alternative set: ¬empty is always derivable by
    leaf substitution of full→empty under negation. -/
theorem adjective_correct_alts :
    ∀ w : GlassWorld,
      exhB glassDomain [notFull, isFull, isEmpty] notFull w
        = (notFull w && notEmpty w) := by
  intro w; cases w <;> native_decide

end GradableAdjectives


-- ═══════════════════════════════════════════════════════════════════════
-- §3  Particularised Scalar Implicatures (§3.2.1, examples 18, 28)
-- ═══════════════════════════════════════════════════════════════════════

/-!
## Particularised SIs and the Role of Conjunction

(18) Bill went for a run and didn't smoke. What did John do?
     John went for a run.
     ⤳ John smoked.

The inference is derived by negating the contextually salient
alternative "ran ∧ ¬smoked" (from Bill's sentence). The AC correctly
handles this case: the conjunctive constituent α = "went for a run
and didn't smoke" is atomic after extraction, blocking generation of
the symmetric counterpart "smoked".

(28) Bill went for a run. He didn't smoke. What did John do?
     John went for a run.
     ⤳ John smoked.

Same inference, but now the conjunction is split across two sentences.
The crucial constituent "ran ∧ ¬smoked" is NOT a subconstituent of
any single sentence, yet the inference persists. Neither the AC nor
the structural approach generates the right alternative here.
-/

section ParticularisedSI

/-- Three activity worlds for John. -/
inductive ActivityWorld where
  | ranOnly | ranAndSmoked | neither
  deriving Repr, DecidableEq, BEq

private def actDomain : List ActivityWorld :=
  [.ranOnly, .ranAndSmoked, .neither]

private def ran : ActivityWorld → Bool
  | .ranOnly | .ranAndSmoked => true | .neither => false

private def smoked : ActivityWorld → Bool
  | .ranAndSmoked => true | _ => false

private def ranAndNotSmoked : ActivityWorld → Bool
  | .ranOnly => true | _ => false

/-- "smoked" and "ran ∧ ¬smoked" are symmetric alternatives of "ran":
    they partition ran's denotation (ex. 19). -/
theorem particularised_symmetric :
    isSymmetric actDomain ran smoked ranAndNotSmoked = true := by
  native_decide

/-- With the symmetric alternative present, exh is vacuous —
    the inference "John smoked" is not derived. -/
theorem particularised_blocked :
    ∀ w : ActivityWorld,
      exhB actDomain [ran, smoked, ranAndNotSmoked] ran w
        = ran w := by
  intro w; cases w <;> native_decide

/-- With only the conjunctive alternative "ran ∧ ¬smoked" (salient
    from context), exh correctly derives: ran ∧ ¬(ran ∧ ¬smoked)
    = ran ∧ smoked = {ranAndSmoked}.

    The structural approach generates this alternative for (18) via
    contextual salience (@cite{fox-katzir-2011} def 37), but NOT
    for (28), where the conjunction spans separate sentences. -/
theorem particularised_correct :
    ∀ w : ActivityWorld,
      exhB actDomain [ran, ranAndNotSmoked] ran w
        = smoked w := by
  intro w; cases w <;> native_decide

end ParticularisedSI


-- ═══════════════════════════════════════════════════════════════════════
-- §4  Too Many Lexical Alternatives (§4.2, @cite{swanson-2010})
-- ═══════════════════════════════════════════════════════════════════════

/-!
## Lexicalized Symmetric Alternatives

@cite{swanson-2010} observes scalar items with lexicalized symmetric
counterparts:

(44) Going to confession is permitted.
  a. ⤳ Going to confession is optional.     (observed)
  b. ⤴ Going to confession is required.     (not observed)

The structural approach cannot exclude "optional" because it is a
single lexical item of equal structural complexity to "permitted" and
"required". Since "required" and "optional" partition "permitted"'s
denotation, they are symmetric, and exh is vacuous.

(45) The heater sometimes squeaks.
  a. ⤳ The heater intermittently squeaks.   (observed)
  b. ⤴ The heater always squeaks.           (not observed)

Same pattern: "intermittently" ≈ sometimes ∧ ¬always.
-/

section SwansonCases

/-- Three deontic worlds. -/
inductive DeonticWorld where
  | forbidden | optional_ | required_
  deriving Repr, DecidableEq, BEq

private def deonticDomain : List DeonticWorld :=
  [.forbidden, .optional_, .required_]

private def isPermitted : DeonticWorld → Bool
  | .optional_ | .required_ => true | .forbidden => false

private def isRequired : DeonticWorld → Bool
  | .required_ => true | _ => false

private def isOptional : DeonticWorld → Bool
  | .optional_ => true | _ => false

/-- "required" and "optional" partition "permitted"'s denotation —
    they are symmetric alternatives (cf. some/all and some-but-not-all
    in `Symmetry.lean`). -/
theorem swanson_symmetric :
    isSymmetric deonticDomain isPermitted isRequired isOptional
      = true := by native_decide

/-- With both lexicalized symmetric alternatives, exh is vacuous.
    The structural approach cannot block "optional" from F because
    it has the same structural complexity as "permitted" — it is a
    single lexical item, not a phrasal combination like "some but
    not all" which requires ConjP/NegP structure. -/
theorem swanson_exh_vacuous :
    ∀ w : DeonticWorld,
      exhB deonticDomain [isPermitted, isRequired, isOptional]
        isPermitted w = isPermitted w := by
  intro w; cases w <;> native_decide

/-- Without the symmetric partner, exh correctly derives the SI:
    permitted ∧ ¬required = optional. -/
theorem swanson_without_symmetric :
    ∀ w : DeonticWorld,
      exhB deonticDomain [isPermitted, isRequired] isPermitted w
        = isOptional w := by
  intro w; cases w <;> native_decide

end SwansonCases


-- ═══════════════════════════════════════════════════════════════════════
-- §5  The RSA Approach (§5, @cite{bergen-levy-goodman-2016})
-- ═══════════════════════════════════════════════════════════════════════

/-!
## The RSA Approach to Symmetry

@cite{bergen-levy-goodman-2016} propose that utterance **cost**
(structural complexity) combined with **relative informativity**
dissolves the symmetry problem without structural restriction of
alternatives.

### Successes
- **Direct SIs**: "some but not all" is costlier than "all", so
  cost breaks the symmetry → SI ¬all is derived.
- **Gradable adjectives** (ex. 50): "not empty" is more complex than
  "empty", so the RSA correctly derives ¬empty for "not full".

### Failures
- **Indirect SIs** (ex. 48): "didn't see all" has symmetric
  alternatives {some, none} of equal complexity. Neither cost nor
  informativity breaks the symmetry.
- **Adjective asymmetry** (ex. 56): RSA predicts the same inference
  for all adjective pairs (safe/dangerous, tall/short), but only
  full/empty actually generates it.
- **@cite{swanson-2010} cases** (ex. 57): "intermittently" is not more
  complex than "always", so cost cannot break the symmetry.

See `Comparisons/RSANeoGricean.lean` for the formal connection between
RSA at α → ∞ and categorical exhaustification.
-/


-- ═══════════════════════════════════════════════════════════════════════
-- §6  Summary
-- ═══════════════════════════════════════════════════════════════════════

/-!
## Summary: Landscape of Predictions

| Phenomenon                    | Structural | +AC | RSA |
|-------------------------------|:---:|:---:|:---:|
| Direct SI (some/all)          | ✓   | ✓   | ✓   |
| Indirect SI (¬all → some)     | ✗   | ✓   | ✗   |
| Gradable adj (¬full → ¬empty) | ✗   | ✗   | ✓   |
| Particularised SI (28)        | ✗   | ✗   | ✗   |
| Swanson (permitted/optional)  | ✗   | ✗   | ✗   |

No single approach handles all cases. The symmetry problem remains
open as of this paper.

## Architectural observations for linglib

This paper reveals several tensions in linglib's organization:

1. **Alternatives straddle semantics/pragmatics**: structural
   alternatives (`Theories/Semantics/Alternatives/`) and RSA
   alternatives (`Theories/Pragmatics/RSA/`) address the same
   problem but with incompatible representations.

2. **Type-level vs value-level alternatives**: RSA models define
   alternatives as `Fintype U` (compile-time); structural alternatives
   are computed as `List (PFTree W)` (runtime). No bridge exists.

3. **Adjective scale structure and alternative generation are
   disconnected**: the full/empty case requires connecting
   `Adjective/Theory.lean` antonym pairs to `Structural.lean`
   substitution — currently four separate modules with no wiring.

4. **No embedded exhaustification**: `exhB` operates at a single
   point, but indirect SIs require exhaustification under negation.
   The `RSA/ScalarImplicatures/Embedded/` directory partially handles
   this for RSA but not for the grammatical approach.
-/


end Phenomena.ScalarImplicatures.Studies.BrehenyEtAl2018
