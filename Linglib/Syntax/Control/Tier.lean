/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Control.Calculus

/-!
# Control Theory: Tiers, Predicate Classes, Clause Classes

The Two-Tiered Theory of Control ([landau-2015]): obligatory control in
complement clauses divides into **predicative** control (nonattitude
complements, syntactic predication) and **logophoric** control (attitude
complements, predication + variable binding of a perspectival
coordinate). The [landau-2004] scale classifies complement clauses by
`[±T]`, and the Feature Transmission asymmetry derives the OC-NC
generalization — `[+Agr]` blocks logophoric but not predicative control.

Originates with [landau-2015]; graduated to the theory layer as substrate
for the paper-anchored control studies (`Studies/Landau2015.lean`,
`Studies/Ostrove2026.lean`, `Studies/Chierchia1984.lean`,
`Studies/Allotey2021.lean`).

## Main definitions

- `Control.Tier`: predicative vs. logophoric control; the predicative
  mechanism's grammatical profile is the framework-neutral
  `Control.IsSaturating` (`Syntax/Control/Defs.lean`)
- `Control.PredicateClass`: the eight predicate classes, mapped to tiers
- `Control.ClauseClass`: the `[±T]` scale positions, with the
  Agr-sensitive `ClauseClass.HasOC` and its characterization
  `ClauseClass.hasOC_iff`
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
    an attitude-holder-bound reading — *de se* under subject and
    psych-object control, *de te* under communicative object control
    (the three-way table is encoded in `Studies/Landau2015.lean`). -/
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

/-! ### Predicate classification -/

/-- The control predicate classes ([landau-2000]; (4a–d)/(5a–d) in
    [landau-2015]): classes (4a–d) select untensed complements
    (nonattitude → predicative control), classes (5a–d) tensed ones
    (attitude → logophoric control), [landau-2004]'s correlation.
    Membership is a property of predicate–complement pairs, not lexemes
    (Polish perfective 'persuade' is implicative, the imperfective is
    not), and the evaluative class is the *of*-frame adjectives
    specifically. [pearson-2016] instead classes propositional
    complements with the exhaustive-control predicates. -/
inductive PredicateClass where
  /-- avoid, dare, manage, remember, … (nonattitude) -/
  | implicative
  /-- begin, continue, finish, start, stop (nonattitude) -/
  | aspectual
  /-- have, is able, may, must, need, should (nonattitude) -/
  | modal
  /-- bold, crazy, kind, rude, silly, smart (nonattitude; *of*-frame
      adjectives) -/
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

/-! ### Clause classes -/

/-- [landau-2004]'s scale positions, in [ostrove-2026]'s terminology:
    C-subjunctives are `[−T]` complements (predicative control, whatever
    the Agr value), F-subjunctives `[+T]` complements (logophoric
    control, which `[+Agr]` blocks per the OC-NC generalization), and
    `finite` the fully finite remainder. The positions are tense cells,
    not mood or finiteness categories — `[−T]` covers bare infinitives
    and untensed subjunctives alike, and OC occurs in inflected
    complements. [landau-2015] subsumes the `[±T]` split under
    attitude/nonattitude. -/
inductive ClauseClass where
  /-- `[−T]` complement; predicative control -/
  | cSubjunctive
  /-- `[+T]` complement; logophoric control -/
  | fSubjunctive
  /-- Fully finite: `[+T, +Agr]` on I. No control unless C is fully
      specified too (mutual cancellation, `Spec.hasControl_of_c_rAssigning`) -/
  | finite
  deriving DecidableEq, Repr

/-- The scale position determined by the two clause-typology observables
    of [ostrove-2026]-style fragments: unrestricted TAM marks a fully
    finite clause; among the TAM-restricted clauses, independent tense
    separates `[+T]` from `[−T]` ([landau-2004]'s feature, diagnosed by
    temporal mismatch). Per-language scale maps derive from this single
    classifier rather than restating the case table. -/
def ClauseClass.ofFiniteness (unrestrictedTAM independentTense : Bool) : ClauseClass :=
  if unrestrictedTAM then .finite
  else if independentTense then .fSubjunctive else .cSubjunctive

/-- Map clause class to control tier (when control obtains). -/
def ClauseClass.tier : ClauseClass → Option Tier
  | .cSubjunctive => some .predicative
  | .fSubjunctive => some .logophoric
  | .finite       => none

/-- The `⟨T, Agr⟩` specification a scale position abbreviates, at a given
    Agr value: `[±T]` on I per the position, C unspecified. The scale cannot
    express a fully specified C — mutual cancellation needs the calculus
    directly. -/
def ClauseClass.toSpec (c : ClauseClass) (agr : Bool) : Spec
  | .I => ⟨c ≠ .cSubjunctive, if c = .finite then true else agr⟩
  | .C => ⟨false, false⟩

/-- OC is realized in a clause class iff the calculus leaves control at its
    specification: the elsewhere condition on `toSpec`. -/
def ClauseClass.HasOC (c : ClauseClass) (agr : Bool) : Prop :=
  (c.toSpec agr).HasControl

instance (c : ClauseClass) (agr : Bool) : Decidable (c.HasOC agr) :=
  inferInstanceAs (Decidable (Spec.HasControl _))

/-- OC obtains exactly on C-subjunctives (any Agr) and `[−Agr]`
    F-subjunctives. -/
theorem ClauseClass.hasOC_iff (c : ClauseClass) (agr : Bool) :
    c.HasOC agr ↔ c = .cSubjunctive ∨ (c = .fSubjunctive ∧ agr = false) := by
  cases c <;> cases agr <;> decide

end Control
