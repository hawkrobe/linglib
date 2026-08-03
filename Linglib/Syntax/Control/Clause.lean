/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Control.Tier
import Linglib.Semantics.Composition.TypeShifting
import Linglib.Features.Complementation
import Linglib.Syntax.Clause.Basic
import Linglib.Syntax.Minimalist.ExtendedProjection.Basic

/-!
# Control Complements: Property vs Proposition

The dual theory's semantic typing of control complements ([landau-2024]
§5.1, (56)/(58); [wurmbrand-2002]; the layer itself is
[chierchia-1984]'s — `Semantics/Composition/TypeShifting.lean`).
Nonattitude predicates select property-denoting FinPs: PRO is the
λ-abstractor whose chain leaves the clause's subject position open.
Attitude predicates select propositional CPs, whose perspectival *pro*
closes the property. Generalization (72) follows: a lexical subject
saturates a property, so only proposition-selecting (attitude)
predicates tolerate one, and nonattitude complements reject lexical
subjects as a type mismatch.

The semantic split is matched by a structural one: predicative
complements project only to Fin, logophoric ones to a full CP, so the
former are properly smaller (`Tier.complSize`, a grade on the
theory-neutral `Clause.Size` scale) and selectively transparent to
dependencies whose opacity boundary is the strong C head — the neutral
reading of the LDA facts in `Studies/Allotey2021.lean`.
-/

namespace Control

open Semantics.Composition.TypeShifting (ClauseLayer)

/-- The semantic layer a control tier's complement inhabits
    ([landau-2024] (56)/(58)): predicative complements are properties,
    logophoric ones propositions. -/
def Tier.complLayer : Tier → ClauseLayer
  | .predicative => .property
  | .logophoric  => .proposition

/-- A complement layer licenses a lexical subject iff it is
    propositional ([landau-2024] (72)): a lexical subject saturates a
    property, yielding a type mismatch with a property-selecting
    predicate. -/
def LicensesLexicalSubject (layer : ClauseLayer) : Prop :=
  layer = .proposition

instance (layer : ClauseLayer) : Decidable (LicensesLexicalSubject layer) :=
  inferInstanceAs (Decidable (_ = _))

/-- Generalization (72), tier form: a tier's complement licenses a
    lexical subject iff the tier is attitude. -/
theorem licensesLexicalSubject_iff_isAttitude (t : Tier) :
    LicensesLexicalSubject t.complLayer ↔ t.isAttitude = true := by
  cases t <;> decide

/-- The semantic layer of a clausal complement type, derived from the
    two `Features` observables: clausal and finite → proposition,
    clausal and nonfinite → property ([chierchia-1984]), `none` for
    non-clausal complements. -/
def complementSemLayer (ct : ComplementType) : Option ClauseLayer :=
  if ct.isClausal then
    some (if ct.isFinite then .proposition else .property)
  else none

/-! ### Size -/

/-- The structural size of a tier's complement, as a grade on the
    neutral `Clause.Size` scale: predicative complements top out at
    Fin, logophoric ones at C ([landau-2024] (56)/(58)). -/
def Tier.complSize : Tier → Clause.Size
  | .predicative => Minimalist.fValue .Fin
  | .logophoric  => Minimalist.fValue .C

/-- Predicative complements are properly smaller than logophoric
    ones — the containment behind the two-tier structure. -/
theorem complSize_predicative_lt_logophoric :
    Tier.predicative.complSize < Tier.logophoric.complSize := by
  decide

/-- Size and layer covary: the propositional complement is the larger
    one (the size half of the attitude asymmetry). -/
theorem complLayer_proposition_iff_lt (t : Tier) :
    t.complLayer = .proposition ↔
      Tier.predicative.complSize < t.complSize := by
  cases t <;> decide

/-- A dependency whose opacity boundary is the strong C head reaches
    exactly the predicative complements (`Clause.transparentTo`). -/
theorem transparentTo_c_iff (t : Tier) :
    Clause.transparentTo t.complSize (Minimalist.fValue .C) ↔
      t = .predicative := by
  cases t <;> decide

end Control
