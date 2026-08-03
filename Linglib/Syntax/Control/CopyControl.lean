/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/

/-!
# Copy Control and Control Derivation

Copy control ([polinsky-potsdam-2006]): the subject of a control clause
is a phonologically overt copy of its controller. The typology of copy
types and the movement vs. base-generation opposition for deriving
obligatory control, adjudicated by diagnostics such as exempt anaphora
([pollard-sag-1992]: exempt anaphors cannot have quantified
antecedents). Substrate for the overt-PRO studies
(`Studies/Ostrove2026.lean`, `Studies/Allotey2021.lean`).

## Main definitions

- `Control.CopyControlType`: the four copy-control types, with their
  distinguishing properties as predicates
- `Control.Derivation`: base-generation vs. movement, with the
  diagnostic prediction table (`Derivation.predicts`) and the unique
  derivation an observation supports (`Derivation.supportedBy`)
-/

namespace Control

/-! ### Copy control typology -/

/-- Types of copy control ([polinsky-potsdam-2006]), distinguished by
    the nature of the overt copy and its distribution. -/
inductive CopyControlType where
  /-- Full copy: PRO is a full DP copy of the controller.
      Attested in San Lucas Quiaviní Zapotec, Copala Triqui. -/
  | fullCopy
  /-- Logophoric pronominal: PRO is a pronoun, occurs only in
      attitude reports. Attested in Gengbe, Mandarin. -/
  | logophoricPronominal
  /-- Scope-sensitive pronominal: PRO is a pronoun, triggered by
      scope-taking operators (focus). Attested in Italian, Hungarian,
      European Portuguese. -/
  | scopeSensitivePronominal
  /-- Obligatory pronominal: PRO is an overt pronoun in all control
      contexts, showing the full OC signature. Attested in SMPM
      ([ostrove-2026]), Gã ([allotey-2021]), Büli ([sulemana-2021]). -/
  | obligatoryPronominal
  deriving DecidableEq, Repr

/-- The copy shows the full OC signature (bound variable, exhaustive). -/
def CopyControlType.showsOC : CopyControlType → Bool
  | .obligatoryPronominal => true
  | _                     => false

/-- The copy is restricted to attitude-report contexts. -/
def CopyControlType.attitudeOnly : CopyControlType → Bool
  | .logophoricPronominal => true
  | _                     => false

/-- The copy requires a scope-taking operator (focus, *only*). -/
def CopyControlType.requiresScopeOperator : CopyControlType → Bool
  | .scopeSensitivePronominal => true
  | _                         => false

/-- The copy can bear focus — obligatory pronominals, being the only
    copy type showing true OC, cannot. -/
def CopyControlType.copyCanBearFocus : CopyControlType → Bool
  | .obligatoryPronominal => false
  | _                     => true

/-! ### Control derivation -/

/-- The two analyses of obligatory control derivation. -/
inductive Derivation where
  /-- Controller base-generated in matrix; PRO base-generated in the
      embedded clause. Two distinct syntactic positions, linked by
      variable binding. -/
  | baseGeneration
  /-- Controller enters the derivation in embedded subject position and
      moves to the matrix position ([hornstein-1999]-style Movement
      Theory of Control). One DP, two copies. -/
  | movement
  deriving DecidableEq, Repr

namespace Derivation

/-- Observable diagnostics that separate the two derivations. -/
inductive Diagnostic where
  /-- Is an exempt anaphor available with a quantified controller? -/
  | exemptAnaphorWithQuantifiedController
  /-- Can the pronounced embedded element be a lexical-DP copy of the
      controller? -/
  | embeddedLexicalCopy
  deriving DecidableEq, Repr

/-- What each derivation predicts for each diagnostic. Under movement
    the embedded element is a copy of the controller: a quantified
    controller leaves no pronoun to antecede an exempt anaphor, and a
    lexical-DP controller should reappear as a lexical-DP copy. Under
    base-generation the embedded element is an independent pronoun. -/
def predicts : Derivation → Diagnostic → Bool
  | .baseGeneration, .exemptAnaphorWithQuantifiedController => true
  | .baseGeneration, .embeddedLexicalCopy                   => false
  | .movement,       .exemptAnaphorWithQuantifiedController => false
  | .movement,       .embeddedLexicalCopy                   => true

/-- The unique derivation consistent with an observed diagnostic value. -/
def supportedBy (d : Diagnostic) (obs : Bool) : Derivation :=
  if Derivation.baseGeneration.predicts d = obs then .baseGeneration else .movement

/-- The supported derivation predicts the observation. -/
@[simp] theorem predicts_supportedBy (d : Diagnostic) (obs : Bool) :
    (supportedBy d obs).predicts d = obs := by
  cases d <;> cases obs <;> rfl

/-- Only the supported derivation predicts the observation: every
    diagnostic discriminates between the two derivations. -/
theorem eq_supportedBy_of_predicts {dv : Derivation} {d : Diagnostic}
    {obs : Bool} (h : dv.predicts d = obs) : dv = supportedBy d obs := by
  cases dv <;> cases d <;> subst h <;> rfl

end Derivation

end Control
