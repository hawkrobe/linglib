import Linglib.Fragments.English.Predicates.Verbal

/-! # Bruening 2021 — Implicit Arguments in English Double Object Constructions
@cite{bruening-2021}

Implicit arguments in English double object constructions.
*Natural Language and Linguistic Theory* 39:1023–1085.

## Core Empirical Findings

Bruening examines patterns of argument optionality in English ditransitive
constructions and discovers four systematic asymmetries:

1. **Sluicing asymmetry**: Implicit second objects and PPs license sluicing,
   but implicit first objects never do.
2. **Interpretation asymmetry**: Implicit second objects and PPs can be
   definite or indefinite (depending on the verb), but implicit first
   objects are uniformly definite.
3. **Base transitivity constraint**: A simple transitive that allows an
   implicit object does NOT allow it when used in the DOC
   (*We're baking* ✓ → *\*We're baking them* with implicit second obj).
4. **Frame-dependent licensing**: An implicit direct object is licensed
   only in the DOC for some verbs, and only in the PP frame for others.

## Theoretical Analysis

Bruening adopts the ApplP analysis (@cite{marantz-1993}): in the DOC, the
second object is selected by V while the first object is projected by
Appl(icative) above VP. Implicit arguments of V are licensed by functional
heads ∃ (indefinite) or ι (definite) that adjoin to V. Implicit arguments
of functional heads (Voice, Appl) require a higher functional head
(Pass, ApplPass) to make them implicit.

## Formalization

This file verifies Bruening's empirical generalizations against the
English verb fragment. Each generalization is stated as a theorem over
the set of ditransitive verbs with implicit argument properties.

## Coverage

Table (56) lists ~40 verbs across 10 cells. This formalization covers 31
of them. The remaining verbs (ask, promise, wish, leave, afford, lose,
guarantee, rent, save) are either already in the Fragment with different
complement types (attitude/question-embedding senses) or require new
entries. The three-frame limitation (VerbCore has complementType +
altComplementType, so max two frames) prevents fully encoding verbs like
send/tell/throw that have NP, NP_NP, and NP_PP frames.
-/

namespace Phenomena.ArgumentStructure.Studies.Bruening2021

open Fragments.English.Predicates.Verbal
open Core.Verbs

-- ════════════════════════════════════════════════════
-- § Ditransitive verb data
-- ════════════════════════════════════════════════════

/-- The set of ditransitive verbs from the English fragment that are
    relevant to Bruening's classification (Table (56)). -/
def ditransitiveVerbs : List VerbEntry := [
  -- DOC-only: implicit second obj indef, implicit first obj def
  charge, cost, fine, tip, pay, strike_, deny, permit,
  -- DOC-only: implicit second obj indef, implicit first obj def (psych)
  envy,
  -- DOC-only: implicit second obj def, implicit first obj def
  forgive,
  -- DOC-only: implicit second obj def, no implicit first obj
  spare,
  -- DOC-only: no implicit args
  begrudge, bet,
  -- Alternating: both DOC and PP frames
  give, serve, teach, feed, show_, tell, sell,
  assign, award, forward_, grant, offer, reserve, send,
  pass, throw, write,
  -- Alternating: no implicit args in either frame
  hand, lend
]

-- ════════════════════════════════════════════════════
-- § Per-verb verification theorems
-- ════════════════════════════════════════════════════

/-! Each theorem verifies one verb's implicit argument properties against
    Bruening's classification (Table (56)). Changing a field on the Fragment
    entry breaks exactly one theorem. -/

-- § DOC-only: indefinite second object, definite first object

theorem charge_implicit : charge.implicitObj = some .indef
    ∧ charge.implicitGoal = some .def := ⟨rfl, rfl⟩

theorem cost_implicit : cost.implicitObj = some .indef
    ∧ cost.implicitGoal = some .def := ⟨rfl, rfl⟩

theorem fine_implicit : fine.implicitObj = some .indef
    ∧ fine.implicitGoal = some .def := ⟨rfl, rfl⟩

theorem tip_implicit : tip.implicitObj = some .indef
    ∧ tip.implicitGoal = some .def := ⟨rfl, rfl⟩

theorem pay_implicit : pay.implicitObj = some .indef
    ∧ pay.implicitGoal = some .def := ⟨rfl, rfl⟩

theorem strike_implicit : strike_.implicitObj = some .indef
    ∧ strike_.implicitGoal = some .def := ⟨rfl, rfl⟩

theorem deny_implicit : deny.implicitObj = some .indef
    ∧ deny.implicitGoal = some .def := ⟨rfl, rfl⟩

theorem permit_implicit : permit.implicitObj = some .indef
    ∧ permit.implicitGoal = some .def := ⟨rfl, rfl⟩

theorem envy_implicit : envy.implicitObj = some .indef
    ∧ envy.implicitGoal = some .def := ⟨rfl, rfl⟩

-- § DOC-only: definite second object

theorem forgive_implicit : forgive.implicitObj = some .def
    ∧ forgive.implicitGoal = some .def := ⟨rfl, rfl⟩

theorem spare_implicit : spare.implicitObj = some .def
    ∧ spare.implicitGoal = none := ⟨rfl, rfl⟩

-- § DOC-only: no implicit arguments

theorem begrudge_no_implicit : begrudge.implicitObj = none
    ∧ begrudge.implicitGoal = none := ⟨rfl, rfl⟩

theorem bet_no_implicit : bet.implicitObj = none
    ∧ bet.implicitGoal = none := ⟨rfl, rfl⟩

-- § Alternating verbs

theorem give_implicit : give.implicitObj = some .indef
    ∧ give.implicitGoal = some .def
    ∧ give.altComplementType = some .np_pp := ⟨rfl, rfl, rfl⟩

theorem serve_implicit : serve.implicitObj = some .indef
    ∧ serve.implicitGoal = some .def
    ∧ serve.altComplementType = some .np_pp := ⟨rfl, rfl, rfl⟩

theorem teach_implicit : teach.implicitObj = some .indef
    ∧ teach.implicitGoal = some .indef
    ∧ teach.altComplementType = some .np_pp := ⟨rfl, rfl, rfl⟩

theorem feed_implicit : feed.implicitObj = some .indef
    ∧ feed.implicitGoal = none
    ∧ feed.altComplementType = some .np_pp := ⟨rfl, rfl, rfl⟩

theorem show_implicit : show_.implicitObj = some .def
    ∧ show_.implicitGoal = none
    ∧ show_.altComplementType = some .np_pp := ⟨rfl, rfl, rfl⟩

theorem tell_implicit : tell.implicitObj = some .def
    ∧ tell.implicitGoal = some .indef := ⟨rfl, rfl⟩

theorem sell_implicit : sell.implicitObj = some .def
    ∧ sell.implicitGoal = some .indef := ⟨rfl, rfl⟩

theorem assign_implicit : assign.implicitObj = some .indef
    ∧ assign.implicitGoal = some .def
    ∧ assign.altComplementType = some .np_pp := ⟨rfl, rfl, rfl⟩

theorem award_implicit : award.implicitObj = none
    ∧ award.implicitGoal = some .def
    ∧ award.altComplementType = some .np_pp := ⟨rfl, rfl, rfl⟩

theorem forward_implicit : forward_.implicitObj = none
    ∧ forward_.implicitGoal = some .def
    ∧ forward_.altComplementType = some .np_pp := ⟨rfl, rfl, rfl⟩

theorem grant_implicit : grant.implicitObj = none
    ∧ grant.implicitGoal = some .def
    ∧ grant.altComplementType = some .np_pp := ⟨rfl, rfl, rfl⟩

theorem offer_implicit : offer.implicitObj = none
    ∧ offer.implicitGoal = some .def
    ∧ offer.altComplementType = some .np_pp := ⟨rfl, rfl, rfl⟩

theorem reserve_implicit : reserve.implicitObj = none
    ∧ reserve.implicitGoal = some .def
    ∧ reserve.altComplementType = some .np_pp := ⟨rfl, rfl, rfl⟩

theorem send_implicit : send.implicitObj = none
    ∧ send.implicitGoal = some .def := ⟨rfl, rfl⟩

theorem pass_implicit : pass.implicitObj = some .def
    ∧ pass.implicitGoal = some .indef := ⟨rfl, rfl⟩

theorem throw_implicit : throw.implicitObj = some .def
    ∧ throw.implicitGoal = some .indef := ⟨rfl, rfl⟩

theorem write_implicit : write.implicitObj = some .indef
    ∧ write.implicitGoal = none := ⟨rfl, rfl⟩

-- § Alternating verbs: no implicit arguments

theorem hand_no_implicit : hand.implicitObj = none
    ∧ hand.implicitGoal = none
    ∧ hand.altComplementType = some .np_pp := ⟨rfl, rfl, rfl⟩

theorem lend_no_implicit : lend.implicitObj = none
    ∧ lend.implicitGoal = none
    ∧ lend.altComplementType = some .np_pp := ⟨rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § Generalization 2: DOC-only implicit first objects are always definite
-- ════════════════════════════════════════════════════

/-- DOC-only verbs: those that appear in the double object construction
    but NOT the prepositional dative (Table (56), "First Object" columns).

    This is an explicit list because the two-field complement type model
    cannot always distinguish DOC-only from alternating verbs (verbs like
    envy have complementType = .np with altComplementType = .np_np, which
    makes them alternating in the data model, but DOC-only in Bruening's
    classification). -/
def docOnlyVerbs : List VerbEntry := [
  charge, cost, fine, tip, pay, strike_, deny, permit,
  envy, forgive, spare, begrudge, bet
]

/-- Bruening's Generalization 2 (§2.2):
    Among DOC-only verbs, every implicit first object is definite.
    No DOC-only verb allows an indefinite implicit first object.

    This follows from the ApplP analysis: implicit first objects are
    licensed by ApplPass, which (like Pass for Voice) only produces
    definite implicit arguments. -/
theorem doc_only_implicit_goal_def :
    docOnlyVerbs.all (λ v =>
      match v.implicitGoal with
      | some .indef => false
      | _ => true) = true := by native_decide

-- ════════════════════════════════════════════════════
-- § Generalization 2b: Implicit themes vary in interpretation
-- ════════════════════════════════════════════════════

/-- Implicit themes (second objects) can be either definite or indefinite,
    depending on the verb. Both interpretations are attested. -/
theorem implicit_obj_varies :
    ditransitiveVerbs.any (λ v => v.implicitObj == some .indef) = true
    ∧ ditransitiveVerbs.any (λ v => v.implicitObj == some .def) = true := by
  exact ⟨by native_decide, by native_decide⟩

-- ════════════════════════════════════════════════════
-- § Generalization 3: Base transitivity constraint
-- ════════════════════════════════════════════════════

/-- Bruening's Generalization 3 (§2.3.1):
    Base transitives that allow an implicit object (*bake*, *melt*, *build*)
    do NOT allow it when used in the DOC.

    Formalized as: these verbs have `complementType = .np` (base transitive)
    with `implicitObj = some _`, but their complementType is NOT `.np_np`.

    Bruening's explanation: the implicit ∃/ι heads adjoin to V and close
    off V's selectional feature. When Appl adds the first object above VP,
    V already has a complete argument structure — V's implicit-licensing
    head blocks the DOC from licensing an implicit second object. -/
theorem bake_class_no_doc :
    melt.complementType = .np ∧ melt.implicitObj = some .indef
    ∧ build.complementType = .np ∧ build.implicitObj = some .indef := ⟨rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § Summary statistics
-- ════════════════════════════════════════════════════

/-- Verbs with implicit themes. -/
def verbsWithImplicitObj : List VerbEntry :=
  ditransitiveVerbs.filter (λ v => v.implicitObj.isSome)

/-- Verbs with implicit goals. -/
def verbsWithImplicitGoal : List VerbEntry :=
  ditransitiveVerbs.filter (λ v => v.implicitGoal.isSome)

theorem implicit_obj_count : verbsWithImplicitObj.length = 22 := by native_decide

theorem implicit_goal_count : verbsWithImplicitGoal.length = 24 := by native_decide

-- ════════════════════════════════════════════════════
-- § Connection to Larson (1988)
-- ════════════════════════════════════════════════════

/-- Bruening vs Larson (@cite{larson-1988}): both analyses predict IO > DO
    c-command in DOC, but make different predictions about implicit arguments.

    Larson's analysis (both objects selected by V) wrongly predicts that
    implicit first objects should behave like implicit second objects.
    In fact they differ: among DOC-only verbs, implicit goals are
    *uniformly* definite, while implicit themes vary.

    This asymmetry is Bruening's primary argument against Larson's VP-shell
    analysis and in favor of the ApplP analysis (@cite{marantz-1993}). -/
theorem larson_bruening_divergence :
    -- DOC-only implicit goals are never indefinite
    docOnlyVerbs.all (λ v =>
      match v.implicitGoal with
      | some .indef => false
      | _ => true) = true
    -- But implicit themes include both definite and indefinite
    ∧ docOnlyVerbs.any (λ v => v.implicitObj == some .indef) = true
    ∧ docOnlyVerbs.any (λ v => v.implicitObj == some .def) = true := by
  exact ⟨by native_decide, by native_decide, by native_decide⟩

-- ════════════════════════════════════════════════════
-- § Connection to Pylkkänen (2008) and ApplP
-- ════════════════════════════════════════════════════

/-- The DOC-only verbs in our fragment all have NP_NP complement type
    (the double object frame), confirming that the DOC projects the
    first object structurally (via Appl) rather than lexically.

    @cite{pylkkanen-2008}'s high applicative analysis predicts exactly
    this: the first object position is available independent of the
    lexical verb's complement type. -/
theorem doc_only_all_np_np :
    docOnlyVerbs.all (λ v =>
      v.complementType == .np_np || v.altComplementType == some .np_np) = true := by
  native_decide

-- ════════════════════════════════════════════════════
-- § Connection to DativeAlternation
-- ════════════════════════════════════════════════════

/-- Bruening refines the general claim in DativeAlternation that ditransitives
    require both arguments. While give is standardly cited as requiring both
    a theme and a recipient, Bruening shows the goal CAN be implicit (definite):
    "She gave $5" (contextually determined recipient).

    This is not a contradiction: DativeAlternation captures the GENERAL
    pattern, while Bruening's implicit argument data captures the EXCEPTIONS
    that specific verbs allow under specific pragmatic conditions. -/
theorem give_has_implicit_goal :
    give.implicitGoal = some .def
    ∧ give.implicitObj = some .indef := ⟨rfl, rfl⟩

end Phenomena.ArgumentStructure.Studies.Bruening2021
