/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Control.Tier
import Linglib.Semantics.Composition.TypeShifting
import Linglib.Features.Complementation

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
-/

namespace Control

open Semantics.Composition.TypeShifting (ComplSemLayer)

/-- The semantic layer a control tier's complement inhabits
    ([landau-2024] (56)/(58)): predicative complements are properties,
    logophoric ones propositions. -/
def Tier.complLayer : Tier → ComplSemLayer
  | .predicative => .property
  | .logophoric  => .proposition

/-- A complement layer licenses a lexical subject iff it is
    propositional ([landau-2024] (72)): a lexical subject saturates a
    property, yielding a type mismatch with a property-selecting
    predicate. -/
def LicensesLexicalSubject (layer : ComplSemLayer) : Prop :=
  layer = .proposition

instance (layer : ComplSemLayer) : Decidable (LicensesLexicalSubject layer) :=
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
def complementSemLayer (ct : ComplementType) : Option ComplSemLayer :=
  if ct.isClausal then
    some (if ct.isFinite then .proposition else .property)
  else none

end Control
