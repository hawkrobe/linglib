/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/

/-!
# Copy Control

Copy control ([polinsky-potsdam-2006]): the subject of a control clause
is a phonologically overt copy of its controller. The typology of copy
types. The movement vs. base-generation opposition is adjudicated by
occupant-transport refutations (`Control.not_isExhaustive_of_mismatch` in
`Basic.lean`): movement is token identity, so an embedded
occupant differing from its controller — a pronoun where a lexical
copy is predicted (Gã), or a genuine pronoun anteceding an exempt
anaphor under a quantified controller ([pollard-sag-1992]; SMPM) —
refutes it. Substrate for the overt-PRO studies
(`Studies/Ostrove2026.lean`, `Studies/Allotey2021.lean`).

## Main definitions

- `Control.CopyControlType`: the four copy-control types, with their
  distinguishing properties as predicates
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



end Control
