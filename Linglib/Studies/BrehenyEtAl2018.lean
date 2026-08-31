import Mathlib.Tactic.DeriveFintype
import Linglib.Semantics.Exhaustification.Finite
import Linglib.Semantics.Alternatives.Symmetric

/-!
# Breheny, Klinedinst, Romoli and Sudo 2018: the symmetry problem

[breheny-et-al-2018] (Natural Language Semantics 26) surveys the symmetry
problem for scalar-implicature alternatives: a theory must admit the
alternative A while excluding its symmetric partner S ∧ ¬A. The structural
approach ([katzir-2007], [fox-katzir-2011]) solves the basic some/all case
but undergenerates for indirect (12) and particularised (18) implicatures;
[trinh-haida-2015]'s Atomicity Constraint repairs those two and backfires on
gradable adjectives under negation (32), blocking the needed *empty*
alternative (40); and the RSA account of [bergen-levy-goodman-2016] covers
the direct, indirect, and full/empty cases through cost and relative
informativity, but fails on the many-variant (54), the run-and-smoke
sentences (55), the adjective asymmetry (56), and — short of frequency
costs — [swanson-2010]'s lexicalized partners (44), (57). No account covers
everything; the problem stays open. Each argument runs through
[fox-2007]'s innocent-exclusion engine on a small domain: the wrong
alternative sets make `exh` vacuous or derive the unattested inference, the
right ones derive the observed implicature.

## Main results

* `indirect_si_blocked`, `indirect_si_correct` — (12): with the symmetric
  *some* present, exhaustification is vacuous; under the Atomicity
  Constraint the indirect implicature is derived.
* `adjective_full_alts_vacuous`, `ac_wrong_for_adjectives`,
  `adjective_correct_alts` — (32): without the constraint neither inference
  arrives, with it the unattested "the glass is empty" is derived, and the
  observed inference needs an alternative set no structural variant
  generates.
* `particularised_symmetric`, `particularised_blocked`,
  `particularised_correct` — (18) and (28): the conjunctive alternative
  derives the implicature exactly when the substitution source supplies it.
* `swanson_symmetric`, `swanson_exh_vacuous`, `swanson_without_symmetric` —
  (44): lexicalized symmetric partners of equal complexity leave
  exhaustification vacuous.

## References

* [breheny-et-al-2018] — the paper.
* [katzir-2007], [fox-katzir-2011] — the structural approach.
* [trinh-haida-2015] — the Atomicity Constraint.
* [bergen-levy-goodman-2016], [swanson-2010] — the RSA account and the
  lexicalized-symmetry cases.
* [fox-2007] — innocent exclusion.
-/

namespace BrehenyEtAl2018

open Exhaustification (innocent predToFinset altsFromPreds)
open Alternatives.Symmetric

/-!
## The Problem of Indirect Scalar Implicatures

(12a) John didn't do all of the homework.
(12b) ⤳ John did some of the homework.

This is an **indirect** SI: the inference arises from negating the
stronger alternative ¬any (= "didn't do any") under the scope of
sentential negation. The structural approach ([fox-katzir-2011])
wrongly generates the symmetric alternative "some" (= "did some")
by extracting the VP subconstituent and substituting all→some within
it, blocking the correct inference.

[trinh-haida-2015]'s Atomicity Constraint solves this: after
extracting the VP, it becomes atomic and the internal substitution
all→some is blocked.
-/

section IndirectSI

/-- Three homework worlds: did none, did some but not all, did all. -/
inductive HWWorld where
  | none_ | someNotAll | all_
  deriving Repr, DecidableEq, Fintype

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

    F(12a) ⊇ {¬all, ¬any, some} per [fox-katzir-2011], because
    "some" is derivable by extracting the VP subconstituent and
    substituting all→some within it. -/
theorem indirect_si_blocked :
    innocent.exh (altsFromPreds [notAll, notAny, didSome]) (predToFinset notAll)
      = predToFinset notAll := by decide

/-- Without "some" (the Atomicity Constraint's prediction), exh
    correctly derives the indirect SI: ¬all ∧ ¬(¬any) = {someNotAll}.

    The AC blocks "some" because deriving it requires extracting the
    VP and then substituting within it, violating atomicity. -/
theorem indirect_si_correct :
    innocent.exh (altsFromPreds [notAll, notAny]) (predToFinset notAll)
      = predToFinset (fun w => notAll w && didSome w) := by decide

/-- I-E includes ¬any when "some" is absent. -/
theorem ac_solves_indirect_si :
    predToFinset notAny ∈
      innocent.excluded (altsFromPreds [notAll, notAny]) (predToFinset notAll) := by
  decide

end IndirectSI

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

### Adjective pair asymmetry ((34), (35), (38))

Not all contradictory antonym pairs generate the inference: full/empty,
required/allowed (34), and certain/possible (35) do; the (38) pairs
safe/dangerous, tall/short, and transparent/opaque do not.

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
  deriving Repr, DecidableEq, Fintype

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
    "full" is in I-E — but ¬full already entails ¬full, so exh adds
    nothing. The crucial inference ¬empty is NOT derived.

    This is because ¬empty and empty cannot both be excluded
    (¬empty ∧ empty = ⊥), and they end up in different MCEs. -/
theorem adjective_full_alts_ie :
    innocent.excluded
      (altsFromPreds [notFull, notEmpty, isFull, isEmpty]) (predToFinset notFull)
      = {predToFinset isFull} := by decide

/-- Consequence: exh(¬full) = ¬full (vacuous for the empty/¬empty
    pair). Neither the correct inference (32a) nor the wrong one (32b)
    is derived. -/
theorem adjective_full_alts_vacuous :
    innocent.exh (altsFromPreds [notFull, notEmpty, isFull, isEmpty]) (predToFinset notFull)
      = predToFinset notFull := by decide

-- ── AC alternative set (empty removed) ───────────────────────

/-- With the AC, "empty" is blocked (requires extraction + substitution,
    ex. 40). Alternatives: {¬full, ¬empty, full}. Now both ¬empty and
    "full" are in I-E. -/
theorem ac_adjective_ie :
    innocent.excluded (altsFromPreds [notFull, notEmpty, isFull]) (predToFinset notFull)
      = {predToFinset notEmpty, predToFinset isFull} := by decide

/-- The AC produces the WRONG prediction: exh(¬full) = ¬full ∧ empty
    = {empty}. This says the glass IS empty — inference (32b).

    The derivation: ¬empty is in I-E, so exh negates it. ¬(¬empty)
    = empty. Combined with ¬full: ¬full ∧ empty = {empty}. -/
theorem ac_wrong_for_adjectives :
    innocent.exh (altsFromPreds [notFull, notEmpty, isFull]) (predToFinset notFull)
      = predToFinset isEmpty := by decide

-- ── Desired alternative set ──────────────────────────────────

/-- To derive the correct inference (32a), the alternatives must
    include "empty" but NOT "¬empty". Then exh(¬full) = ¬full ∧
    ¬empty = {mid} — the glass is neither full nor empty.

    No version of the structural approach (with or without AC)
    produces this alternative set: ¬empty is always derivable by
    leaf substitution of full→empty under negation. -/
theorem adjective_correct_alts :
    innocent.exh (altsFromPreds [notFull, isFull, isEmpty]) (predToFinset notFull)
      = predToFinset (fun w => notFull w && notEmpty w) := by decide

end GradableAdjectives

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
  deriving Repr, DecidableEq, Fintype

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
  decide

/-- With the symmetric alternative present, exh is vacuous —
    the inference "John smoked" is not derived. -/
theorem particularised_blocked :
    innocent.exh (altsFromPreds [ran, smoked, ranAndNotSmoked]) (predToFinset ran)
      = predToFinset ran := by decide

/-- With only the conjunctive alternative "ran ∧ ¬smoked" (salient
    from context), exh correctly derives: ran ∧ ¬(ran ∧ ¬smoked)
    = ran ∧ smoked = {ranAndSmoked}.

    The structural approach generates this alternative for (18) because
    the salient conjunctive constituent is in the substitution source, but
    NOT for (28), where the conjunction spans separate sentences. -/
theorem particularised_correct :
    innocent.exh (altsFromPreds [ran, ranAndNotSmoked]) (predToFinset ran)
      = predToFinset smoked := by decide

end ParticularisedSI

/-!
## Lexicalized Symmetric Alternatives

[swanson-2010] observes scalar items with lexicalized symmetric
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
  b. ⤴ The heater constantly squeaks.       (not observed)

Same pattern: "intermittently" ≈ sometimes ∧ ¬always.
-/

section SwansonCases

/-- Three deontic worlds. -/
inductive DeonticWorld where
  | forbidden | optional_ | required_
  deriving Repr, DecidableEq, Fintype

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
      = true := by decide

/-- With both lexicalized symmetric alternatives, exh is vacuous.
    The structural approach cannot block "optional" from F because
    it has the same structural complexity as "permitted" — it is a
    single lexical item, not a phrasal combination like "some but
    not all" which requires ConjP/NegP structure. -/
theorem swanson_exh_vacuous :
    innocent.exh (altsFromPreds [isPermitted, isRequired, isOptional]) (predToFinset isPermitted)
      = predToFinset isPermitted := by decide

/-- Without the symmetric partner, exh correctly derives the SI:
    permitted ∧ ¬required = optional. -/
theorem swanson_without_symmetric :
    innocent.exh (altsFromPreds [isPermitted, isRequired]) (predToFinset isPermitted)
      = predToFinset isOptional := by decide

end SwansonCases

/-!
## The RSA Approach to Symmetry

[bergen-levy-goodman-2016] propose that utterance **cost**
(structural complexity) combined with **relative informativity**
dissolves the symmetry problem without structural restriction of
alternatives.

What it covers: direct SIs — *some but not all* is costlier than *all*,
so cost breaks the symmetry; plain indirect SIs (48) — the alternatives
{some, none} tie in complexity, but *some* is relatively uninformative
against *not all* where *none* is not, so informativity breaks it; and
the full/empty case (50), since *not empty* is costlier than *empty*.

Where it fails: the many-variant (54), where the unwanted *many* matches
the needed *not many* on both dimensions; the run-and-smoke sentences (55),
where the unattested alternative is if anything simpler; the adjective
asymmetry (56), predicting the same inference for safe/dangerous and
tall/short as for full/empty; and (57), where *intermittently* is no more
complex than *always* — unless lexical frequency is priced into cost.
-/

/-!
## Summary

The paper's three problems — indirect and particularised implicatures, too
few lexical alternatives (the Japanese deontic paradigm (41)–(43), where
the needed necessity alternative is not structurally derivable), and too
many (Swanson's lexicalized partners) — leave every account partial: the
structural approach fails the first, the Atomicity Constraint trades the
indirect cases for the gradable-adjective ones, and the RSA account clears
direct, indirect, and full/empty but not (54)–(57). The symmetry problem
remains open as of this paper.
-/

end BrehenyEtAl2018
