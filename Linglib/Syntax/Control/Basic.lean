/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/

/-!
# Control Theory: Tiers, Predicate Classes, Clause Classes

The Two-Tiered Theory of Control ([landau-2015]): obligatory control in
complement clauses divides into **predicative** control (nonattitude
complements, syntactic predication) and **logophoric** control (attitude
complements, predication + variable binding of a perspectival
coordinate). The [landau-2004] finiteness scale classifies complement
clauses, and the Feature Transmission asymmetry derives the OC-NC
generalization — `[+Agr]` blocks logophoric but not predicative control.

Originates with [landau-2015]; graduated to the theory layer as substrate
for the paper-anchored control studies (`Studies/Landau2015.lean`,
`Studies/Ostrove2026.lean`, `Studies/Chierchia1984.lean`,
`Studies/Allotey2021.lean`).

## Main definitions

- `Control.Tier`: predicative vs. logophoric control
- `Control.PredicateClass`: the eight predicate classes, mapped to tiers
- `Control.ClauseClass`: the finiteness scale (C-subjunctive,
  F-subjunctive, finite) with the Agr-sensitive `hasOCWithAgr`
- `Control.agrBlocksControl`: the OC-NC generalization, from the
  Feature Transmission asymmetry
-/

namespace Control

/-! ### The two tiers -/

/-- The two tiers of obligatory control ([landau-2015]).

    Predicative control (EC complements): selected by nonattitude
    predicates; PRO moves to Spec,Fin and control is syntactic
    predication; forces exhaustive control.

    Logophoric control (PC complements): selected by attitude
    predicates; C^OC projects a perspectival coordinate and control is
    predication + variable binding; allows partial control and forces
    *de se* interpretation. -/
inductive Tier where
  /-- Predicative control: nonattitude, predication only -/
  | predicative
  /-- Logophoric control: attitude, predication + variable binding -/
  | logophoric
  deriving DecidableEq, Repr

/-- Logophoric control corresponds to attitude complements. -/
def Tier.isAttitude : Tier → Bool
  | .predicative => false
  | .logophoric  => true

/-- Condition on syntactic predication ([landau-2015] (90)): the argument
    predicated of must be syntactically represented. Predicative control
    therefore requires a syntactically present controller; the logophoric
    AUTHOR/ADDRESSEE coordinate is discourse-anchored and does not. -/
def Tier.requiresSyntacticController : Tier → Bool
  | .predicative => true
  | .logophoric  => false

/-- [−human] PRO is compatible with predicative control only
    ([landau-2015] (81)): the logophoric binder is mapped to the
    AUTHOR/ADDRESSEE function, which is defined only for humans. -/
def Tier.allowsNonhumanPRO : Tier → Bool
  | .predicative => true
  | .logophoric  => false

/-! Partial control, obligatory *de se*, control shift, implicit control,
    and split control are all available under logophoric control and
    blocked under predicative control — one underlying mechanism
    (variable binding of a perspectival coordinate), so each is derived
    as `isAttitude` rather than restipulated. -/

/-- Partial control is available only under logophoric control;
    predicative control forces exhaustive control. -/
def Tier.allowsPartialControl := Tier.isAttitude

/-- Obligatory *de se* arises only under logophoric control. -/
def Tier.obligatoryDeSe := Tier.isAttitude

/-- Control shift is available only under logophoric control:
    predicative control enters a biunique predication relation. -/
def Tier.allowsControlShift := Tier.isAttitude

/-- Implicit control is the complement of requiring a syntactic
    controller (condition (90)). -/
def Tier.allowsImplicitControl := Tier.isAttitude

/-- Split control is available only under logophoric control. -/
def Tier.allowsSplitControl := Tier.isAttitude

/-- Implicit control derives from the condition on syntactic predication:
    `allowsImplicitControl` is the negation of
    `requiresSyntacticController`. -/
theorem implicit_control_from_predication_condition (tier : Tier) :
    tier.allowsImplicitControl = !tier.requiresSyntacticController := by
  cases tier <;> rfl

/-- [−human] PRO derives from the logophoric mechanism:
    `allowsNonhumanPRO` is the negation of `isAttitude`. -/
theorem nonhuman_pro_from_attitude (tier : Tier) :
    tier.allowsNonhumanPRO = !tier.isAttitude := by
  cases tier <;> rfl

/-! ### Predicate classification -/

/-- [landau-2015]'s predicate classification by complement type:
    classes (4a–d) select untensed complements (nonattitude →
    predicative control); classes (5a–d) select tensed complements
    (attitude → logophoric control). -/
inductive PredicateClass where
  /-- avoid, dare, manage, remember, … (nonattitude) -/
  | implicative
  /-- begin, continue, finish, start, stop (nonattitude) -/
  | aspectual
  /-- have, is able, may, must, need, should (nonattitude) -/
  | modal
  /-- bold, crazy, kind, rude, silly, smart (nonattitude; adjectives) -/
  | evaluative
  /-- dislike, glad, hate, regret, sorry, … (attitude) -/
  | factive
  /-- affirm, believe, claim, declare, say, think (attitude) -/
  | propositional
  /-- agree, choose, decide, hope, intend, want, … (attitude) -/
  | desiderative
  /-- ask, guess, inquire, know, wonder (attitude) -/
  | interrogative
  deriving DecidableEq, Repr

/-- Map predicate class to control tier. -/
def PredicateClass.tier : PredicateClass → Tier
  | .implicative | .aspectual | .modal | .evaluative => .predicative
  | .factive | .propositional | .desiderative | .interrogative => .logophoric

/-! ### The OC-NC generalization -/

/-- The OC-NC generalization ([landau-2015] (70)): `[+Agr]` blocks
    logophoric but not predicative control, by the Feature Transmission
    asymmetry ((60): predication is not contingent on feature matching —
    Icelandic quirky constructions — while variable binding is,
    [heim-2008], [kratzer-2009]). -/
def agrBlocksControl : Tier → Bool
  | .predicative => false
  | .logophoric  => true

/-! ### Clause classes -/

/-- [landau-2004]'s finiteness scale, as recast in [landau-2015]: the
    [±T] distinction is subsumed by attitude/nonattitude. C-subjunctives
    (untensed) take predicative control; F-subjunctives (tensed,
    `[−Agr]`) take logophoric control, blocked by `[+Agr]` per the OC-NC
    generalization; fully finite clauses take no control. -/
inductive ClauseClass where
  /-- Untensed nonfinite; predicative control -/
  | cSubjunctive
  /-- Tensed nonfinite; logophoric control -/
  | fSubjunctive
  /-- Fully finite; no control -/
  | finite
  deriving DecidableEq, Repr

/-- The scale position determined by the two finiteness observables a
    fragment's clause typology records: unrestricted TAM marks a fully
    finite clause; among the TAM-restricted clauses, independent tense
    separates F-subjunctives (`[+T]`) from C-subjunctives (`[−T]`)
    ([landau-2004]). Per-language scale maps derive from this single
    classifier rather than restating the case table. -/
def ClauseClass.ofFiniteness (unrestrictedTAM independentTense : Bool) : ClauseClass :=
  if unrestrictedTAM then .finite
  else if independentTense then .fSubjunctive else .cSubjunctive

/-- Map clause class to control tier (when control obtains). -/
def ClauseClass.tier : ClauseClass → Option Tier
  | .cSubjunctive => some .predicative
  | .fSubjunctive => some .logophoric
  | .finite       => none

/-- Whether a clause class structurally permits OC (F-subjunctive OC is
    logophoric and hence blocked only by `[+Agr]`; see `hasOCWithAgr`). -/
def ClauseClass.permitsOC : ClauseClass → Bool
  | .cSubjunctive => true
  | .fSubjunctive => true
  | .finite       => false

/-- Whether OC is realized given Agr status: composes the clause class
    with the OC-NC generalization. C-subjunctives are OC regardless of
    Agr; F-subjunctives are OC only when `[−Agr]`; finite clauses never. -/
def ClauseClass.hasOCWithAgr (c : ClauseClass) (hasAgr : Bool) : Bool :=
  match c.tier with
  | none => false
  | some tier => c.permitsOC && (!hasAgr || !agrBlocksControl tier)

/-- OC obtains exactly on C-subjunctives (any Agr) and `[−Agr]`
    F-subjunctives — the four corollaries below in one characterization. -/
theorem ClauseClass.hasOCWithAgr_eq_true_iff (c : ClauseClass) (agr : Bool) :
    c.hasOCWithAgr agr = true ↔ c = .cSubjunctive ∨ (c = .fSubjunctive ∧ agr = false) := by
  cases c <;> cases agr <;> decide

/-- C-subjunctives have OC regardless of Agr. -/
theorem cSubjunctive_oc_any_agr (agr : Bool) :
    ClauseClass.cSubjunctive.hasOCWithAgr agr = true := by
  cases agr <;> rfl

/-- F-subjunctives have OC when `[−Agr]`. -/
theorem fSubjunctive_oc_without_agr :
    ClauseClass.fSubjunctive.hasOCWithAgr false = true := rfl

/-- F-subjunctives lose OC when `[+Agr]` (the OC-NC generalization). -/
theorem fSubjunctive_no_oc_with_agr :
    ClauseClass.fSubjunctive.hasOCWithAgr true = false := rfl

/-- Fully finite clauses never have OC. -/
theorem finite_no_oc (agr : Bool) :
    ClauseClass.finite.hasOCWithAgr agr = false := by
  cases agr <;> rfl

end Control
