import Linglib.Core.Order.Rat01
import Linglib.Data.Examples.TonhauserBeaverDegen2018
import Linglib.Data.Examples.SolstadBott2024

/-!
# Generalizations.Projectivity — cross-paper prediction target

The Gradient Projection Principle of [tonhauser-beaver-degen-2018] — content
projects to the extent that it is *not* at-issue — predicts a per-expression
projectivity from its at-issueness. This file is the theory-neutral pool against
which rival accounts of that relationship are run.

The empirical generalisation (projectivity is gradient and tracks
not-at-issueness across triggers) predates any one formal account and spans
≥ 2 papers contributing generated `Data.Examples` rows
([tonhauser-beaver-degen-2018]: 9 + 12 English expressions;
[solstad-bott-2024]: occasion + psychological verbs in German), with ≥ 2 rival
accounts consuming the `ProjectionAccount` signature in their study files
(`gppProjection` and `pottsProjection` in `Studies/TonhauserBeaverDegen2018`).

## Main declarations

* `ProjectionAccount` — the prediction signature any account implements: given a
  content's at-issueness, predict its projectivity (`Rat01 → Rat01`).
* `ProjectionDatum` — a typed observed datum (`projectivity`, `atIssueness`),
  lifted from a paper-anchored `LinguisticExample` by `fromExample`.
* `allData` — the pooled test set: every projectivity row from the contributing
  papers' generated `Examples.all`.
* `predictionError` / `predictsWithin` — score an account against an observation.

## Implementation notes

The means are continuous (proportions in `[0, 1]`), so an account is *run* over
`allData` by computation; the kernel-checkable content is each account's
*systematic error*, proved in the study files (string-keyed `paperFeatures` and
`ℚ` comparison do not reduce in the kernel). Papers may store either
`atIssueness` or `notAtIssueness` in `paperFeatures`; `readAtIssueness`
normalises both to at-issueness (the accounts' input). Import rule (Core + Data
only): accounts and divergence theorems live in the consuming study files.
-/

namespace Generalizations.Projectivity

open Core.Order (Rat01)
open Data.Examples (LinguisticExample SourceRef)

/-! ### Prediction signature -/

/-- A theory of projection: predict a content's projectivity from its
    at-issueness. Rival accounts (`gppProjection`, `pottsProjection`) live in the
    study files and are run against `allData`. -/
abbrev ProjectionAccount := Rat01 → Rat01

/-- An observed datum: mean projectivity and at-issueness for one expression,
    with its originating `SourceRef`. -/
structure ProjectionDatum where
  expression   : String
  projectivity : Rat01
  atIssueness  : Rat01
  source       : SourceRef
  deriving Repr

/-- Not-at-issueness is the complement of at-issueness — the quantity the GPP
    equates with projectivity. -/
def ProjectionDatum.notAtIssueness (d : ProjectionDatum) : Rat01 :=
  Rat01.compl d.atIssueness

/-! ### `LinguisticExample` adapter -/

/-- Parse a percent-integer string (e.g. `"96"`) into a `Rat01`; `none` if
    non-numeric or out of range. -/
def parsePercent (s : String) : Option Rat01 :=
  match s.toNat? with
  | some n =>
      if h : n ≤ 100 then
        have h0 : (0 : ℚ) ≤ (n : ℚ) := by exact_mod_cast Nat.zero_le n
        have h1 : (n : ℚ) ≤ 100 := by exact_mod_cast h
        some ⟨(n : ℚ) / 100, by linarith, by linarith⟩
      else none
  | none => none

/-- Read at-issueness from `paperFeatures`: directly from the `atIssueness` key,
    or as the complement of `notAtIssueness`. -/
def readAtIssueness (pf : List (String × String)) : Option Rat01 :=
  match pf.lookup "atIssueness" with
  | some s => parsePercent s
  | none => ((pf.lookup "notAtIssueness").bind parsePercent).map Rat01.compl

/-- Lift a `LinguisticExample` to a `ProjectionDatum` via its `expression`,
    `projectivity`, and (`atIssueness` or `notAtIssueness`) keys; `none` if any
    is missing. -/
def fromExample (e : LinguisticExample) : Option ProjectionDatum :=
  match e.paperFeatures.lookup "expression",
        (e.paperFeatures.lookup "projectivity").bind parsePercent,
        readAtIssueness e.paperFeatures with
  | some expr, some p, some ai =>
      some { expression := expr, projectivity := p, atIssueness := ai, source := e.source }
  | _, _, _ => none

/-! ### Pool -/

/-- The pooled cross-paper projection data. Each rival `ProjectionAccount` is run
    against this list in the study files. -/
def allData : List ProjectionDatum :=
  (TonhauserBeaverDegen2018.Examples.all ++ SolstadBott2024.Examples.all).filterMap fromExample

/-! ### Scoring -/

/-- An account's absolute error on an observation: the gap between its predicted
    projectivity (from the observed at-issueness) and the observed projectivity. -/
def predictionError (acc : ProjectionAccount) (d : ProjectionDatum) : ℚ :=
  |(acc d.atIssueness).val - d.projectivity.val|

/-- An account predicts an observation within tolerance `ε`. -/
def predictsWithin (ε : ℚ) (acc : ProjectionAccount) (d : ProjectionDatum) : Prop :=
  predictionError acc d ≤ ε

instance (ε : ℚ) (acc : ProjectionAccount) (d : ProjectionDatum) :
    Decidable (predictsWithin ε acc d) :=
  inferInstanceAs (Decidable (_ ≤ _))

end Generalizations.Projectivity
