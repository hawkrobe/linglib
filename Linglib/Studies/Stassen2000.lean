import Linglib.Syntax.Coordination

/-!
# Stassen (2000): AND-languages and WITH-languages

This file formalizes [stassen-2000]'s typological parameter for the encoding of noun phrase
conjunction. A language encodes conjunction by a coordinate strategy, in which the conjuncts
have equal structural rank, form a constituent, trigger plural agreement and are linked by a
marker distinct from the comitative, or by a comitative strategy modelled on the comitative
construction; the diagnostics of an encoding are `Encoding`, and an encoding is coordinate
when it passes all of them (`Encoding.Coordinate`). An AND-language has a coordinate
strategy alongside the comitative one and a WITH-language only the comitative one
(`Language.IsAnd`, `Language.IsWith`, `isAnd_iff_not_isWith`); the marker diagnostic is what
the survey of [wals-2013] records, whether 'and' is identical to 'with', from which
the substrate reads the status (`Syntax.Coordination.ConjComitativeRelation.toAndWithStatus`).
WITH-languages drift towards AND-status: the comitative marker grammaticalizes into a
coordinator, so the drifted language is an AND-language whose new coordinator has a
comitative source and, in the terms of [haspelmath-2007], one of the monosyndetic patterns
(`drift`, `drift_isAnd`, `drift_pattern_monosyndetic`).

## Implementation notes

The article is not accessible from this checkout, so the study keeps to the parameter, the
diagnostics and the drift its abstract states. The areal correspondence the paper reports
between the AND/WITH parameter and the casedness and tensedness parameters is not
formalized: its cross-tabulations over the sample of 260 languages were not available to
transcribe, and a statistical tendency is not a theorem of the parameter.

## References

* [stassen-2000]
* [haspelmath-2007]
* [wals-2013]
-/

namespace Stassen2000

open Syntax.Coordination

/-- The structural diagnostics of a strategy for noun phrase conjunction: the conjuncts have
equal syntactic rank, form a constituent, trigger plural agreement, and are linked by a
marker distinct from the comitative marker. -/
structure Encoding where
  equalRank : Bool
  constituent : Bool
  pluralAgreement : Bool
  distinctMarker : Bool
  deriving DecidableEq, Repr, Fintype

/-- An encoding is a coordinate strategy when it passes every diagnostic; otherwise it is a
comitative strategy. -/
def Encoding.Coordinate (e : Encoding) : Prop :=
  e.equalRank ∧ e.constituent ∧ e.pluralAgreement ∧ e.distinctMarker

instance : DecidablePred Encoding.Coordinate := λ _ =>
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- A comitative strategy shares its marker with the comitative construction. -/
theorem Encoding.not_coordinate_of_not_distinctMarker {e : Encoding}
    (h : e.distinctMarker = false) : ¬ e.Coordinate := by
  simp [Encoding.Coordinate, h]

/-- A language's strategies for noun phrase conjunction. -/
structure Language where
  encodings : List Encoding

/-- An AND-language has a coordinate strategy. -/
def Language.IsAnd (l : Language) : Prop := ∃ e ∈ l.encodings, e.Coordinate

/-- A WITH-language has only comitative strategies. -/
def Language.IsWith (l : Language) : Prop := ∀ e ∈ l.encodings, ¬ e.Coordinate

instance (l : Language) : Decidable l.IsAnd := inferInstanceAs (Decidable (∃ e ∈ _, _))

instance (l : Language) : Decidable l.IsWith := inferInstanceAs (Decidable (∀ e ∈ _, _))

/-- The parameter is binary. -/
theorem isAnd_iff_not_isWith (l : Language) : l.IsAnd ↔ ¬ l.IsWith := by
  simp [Language.IsAnd, Language.IsWith]

/-- A language is an AND-language when its 'and' differs from its 'with', by the marker
diagnostic alone, if the other diagnostics are met. -/
theorem isAnd_of_distinctMarker {l : Language} {e : Encoding} (he : e ∈ l.encodings)
    (h1 : e.equalRank = true) (h2 : e.constituent = true) (h3 : e.pluralAgreement = true)
    (h4 : e.distinctMarker = true) : l.IsAnd :=
  ⟨e, he, h1, h2, h3, h4⟩

/-! ### Drift -/

/-- The drift of a WITH-language towards AND-status: its comitative marker grammaticalizes
into a coordinator, adding a coordinate strategy whose diachronic source is the comitative. -/
def drift (l : Language) (e : Encoding) : Language := ⟨e :: l.encodings⟩

/-- A drifted language is an AND-language once the new strategy passes the diagnostics. -/
theorem drift_isAnd (l : Language) {e : Encoding} (h : e.Coordinate) : (drift l e).IsAnd :=
  ⟨e, List.mem_cons_self, h⟩

/-- Drift is one-directional: it never removes a coordinate strategy. -/
theorem isAnd_drift_of_isAnd (l : Language) (e : Encoding) (h : l.IsAnd) : (drift l e).IsAnd :=
  let ⟨e', he', hc⟩ := h; ⟨e', List.mem_cons_of_mem _ he', hc⟩

/-- A coordinator of comitative source has a monosyndetic pattern in either position, so the
coordinator a WITH-language acquires by drift is monosyndetic. -/
theorem drift_pattern_monosyndetic (pos : CoordinatorPosition) :
    ∀ p ∈ DiachronicSource.pattern .comitative pos, p.syndesis = .monosyndetic := by
  cases pos <;> decide

end Stassen2000
