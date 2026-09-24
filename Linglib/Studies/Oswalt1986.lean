module

public import Linglib.Semantics.Evidential.Basic
public import Linglib.Fragments.Kashaya.Evidentiality
public import Linglib.Data.Examples.Oswalt1986

/-!
# Oswalt (1986): The Evidential System of Kashaya

This file formalizes [oswalt-1986]'s description of the Kashaya evidential suffixes, recorded
in `Fragments/Kashaya/Evidentiality.lean` as the columns of his Table 1. The suffixes of a
column are mutually exclusive, only one appearing on a verb, and cover disjoint sources, so
every column is a well-formed paradigm (`paradigm_wellFormed`). A response to another's words
drops the performative pair, the factual-visual pair taking its place (`paradigm_responsive`,
`performative_notMem_responsive`). The narrative construction simplifies the distinctions to
two, personal experience against the quotative: as a partition of the sources a spontaneous
remark expresses, every column is a coarsening of the spontaneous column
(`spontaneous_le`), the spontaneous column making four distinctions of source and the
narrative and remote columns two (`card_parts_spontaneous`, `card_parts_narrative`). The rows
of the table are a hierarchy, Performative > Factual-Visual > Auditory > Inferential >
Quotative, each with priority over those below it, so the evidential a speaker uses is the
first of the column covering a source at hand (`preferred`). Seeing takes precedence over every
other source (`preferred_of_visual_mem`), the quotative is used exactly when report is at hand
and no other row covers a source at hand (`preferred_eq_quotative_iff`), and the performative
is never chosen on the strength of a parameter (`preferred_ne_performative`). Inferential II
must be followed by another suffix and belongs to no column (`inferentialII_notMem`). The
chapter's examples name the evidential they illustrate and, for the suffixes of the paradigm,
the mode; each lies in the paradigm of its mode for the aspect of its stem
(`examples_mem_paradigm`).

## References

* [oswalt-1986]
-/

@[expose] public section

namespace Oswalt1986

open Evidential Aspect Data.Examples Kashaya.Evidentiality

/-! ### The columns of Table 1 -/

/-- The suffixes of a column are mutually exclusive and cover disjoint sources. -/
theorem paradigm_wellFormed (m : Mode) (a : Perfectivity) : WellFormed (paradigm m a) := by
  cases m <;> cases a <;> decide

/-- A response drops the performative pair, the factual-visual pair taking its place. -/
theorem paradigm_responsive (a : Perfectivity) :
    paradigm .responsive a = (paradigm .spontaneous a).erase (performative a) := by
  cases a <;> rfl

/-- The performative does not take the responsive suffix: *men s̓ímela* 'I have done that' is
normal as an isolated remark, *men s̓ímelam* does not occur. -/
theorem performative_notMem_responsive (a : Perfectivity) :
    performative a ∉ paradigm .responsive a := by
  cases a <;> decide

/-- Inferential II belongs to no column: it is never verb-final. -/
theorem inferentialII_notMem (m : Mode) (a : Perfectivity) : inferentialII ∉ paradigm m a := by
  cases m <;> cases a <;> decide

/-! ### The narrative simplification -/

/-- No column leaves a source unexpressed that a spontaneous remark expresses. -/
theorem expressed_spontaneous_subset (m : Mode) (a : Perfectivity) :
    expressed (paradigm .spontaneous a) ⊆ expressed (paradigm m a) := by
  cases m <;> cases a <;> decide

/-- Every column is a coarsening of the spontaneous column: restricted to the sources a
spontaneous remark expresses, its paradigm is refined by the spontaneous paradigm. -/
theorem spontaneous_le (m : Mode) (a : Perfectivity) :
    Evidential.finpartition (paradigm .spontaneous a) (paradigm_wellFormed _ _) ≤
      (Evidential.finpartition (paradigm m a) (paradigm_wellFormed _ _)).restrict
        (expressed_spontaneous_subset m a) := by
  cases m <;> cases a <;> (show ∀ b ∈ _, ∃ c ∈ _, b ≤ c; decide)

/-- A spontaneous remark makes four distinctions of source in either aspect: the performative,
covering no parameter, adds no block. -/
theorem card_parts_spontaneous (a : Perfectivity) :
    (Evidential.finpartition (paradigm .spontaneous a) (paradigm_wellFormed _ _)).parts.card =
      4 := by
  cases a <;> decide

/-- The narrative construction and the remote past simplify the distinctions to two, personal
experience against the quotative. -/
theorem card_parts_narrative (a : Perfectivity) :
    (Evidential.finpartition (paradigm .narrative a) (paradigm_wellFormed _ _)).parts.card = 2 ∧
    (Evidential.finpartition (paradigm .remote a) (paradigm_wellFormed _ _)).parts.card = 2 := by
  cases a <;> decide

/-! ### The hierarchy -/

/-- The evidential a column prefers for the sources at hand: its first suffix covering one of
them, the rows of Table 1 being ordered so that each has priority over those below. -/
def preferred (es : List Evidential) (sources : Finset Parameter) : Option Evidential :=
  es.find? fun e ↦ (e.covers ∩ sources).Nonempty

/-- Seeing takes priority over every other source: whatever else a speaker has, the
factual-visual is used. -/
theorem preferred_of_visual_mem (a : Perfectivity) {S : Finset Parameter} (h : .visual ∈ S) :
    preferred (paradigm .spontaneous a) S = some (factualVisual a) := by
  cases a <;> simp [preferred, paradigm, List.find?, performative, factualVisual,
    Finset.Nonempty, h]

/-- The quotative is used exactly when report is at hand and no other row of the column covers
a source at hand. -/
theorem preferred_eq_quotative_iff (a : Perfectivity) (S : Finset Parameter) :
    preferred (paradigm .spontaneous a) S = some quotative ↔
      .hearsay ∈ S ∧ ∀ e ∈ paradigm .spontaneous a, e ≠ quotative → Disjoint e.covers S := by
  by_cases hv : .visual ∈ S <;> by_cases hs : .sensory ∈ S <;> by_cases hi : .inference ∈ S <;>
    by_cases hh : .hearsay ∈ S <;> cases a <;>
    simp [preferred, paradigm, List.find?, performative, factualVisual, auditory, inferential,
      quotative, Finset.Nonempty, Finset.disjoint_left, hv, hs, hi, hh]

/-- The performative is never chosen on the strength of a parameter: its source lies outside
them. -/
theorem preferred_ne_performative (a : Perfectivity) (S : Finset Parameter) :
    preferred (paradigm .spontaneous a) S ≠ some (performative a) := fun h ↦ by
  have := List.find?_some h
  cases a <;> simp [performative] at this

/-! ### The examples -/

/-- The mode an example's `mode` feature names. -/
def mode? (r : LinguisticExample) : Option Mode :=
  match r.feature? "mode" with
  | some "spontaneous" => some .spontaneous
  | some "responsive" => some .responsive
  | some "narrative" => some .narrative
  | some "remote" => some .remote
  | _ => none

/-- The aspects an example's stem may have: the one its `aspect` feature names, or either. -/
def aspects (r : LinguisticExample) : List Perfectivity :=
  match r.feature? "aspect" with
  | some "imperfective" => [.imperfective]
  | some "perfective" => [.perfective]
  | _ => [.imperfective, .perfective]

/-- The evidential an example's `evidential` feature names, for a stem of the given aspect. -/
def evidential? (r : LinguisticExample) (a : Perfectivity) : Option Evidential :=
  match r.feature? "evidential" with
  | some "performative" => some (performative a)
  | some "factualVisual" => some (factualVisual a)
  | some "auditory" => some auditory
  | some "inferential" => some inferential
  | some "quotative" => some quotative
  | some "inferentialII" => some inferentialII
  | some "personalExperience" => some personalExperience
  | some "remotePast" => some remotePast
  | _ => none

/-- Every example names an evidential, and every one whose evidential is a suffix of the
paradigm names its mode. -/
theorem examples_named :
    ∀ r ∈ Examples.all, ∀ a ∈ aspects r,
      (evidential? r a).isSome ∧ (evidential? r a ≠ some inferentialII → (mode? r).isSome) := by
  decide

/-- The evidential of each example lies in the paradigm of its mode, for the aspect of its
stem. -/
theorem examples_mem_paradigm :
    ∀ r ∈ Examples.all, ∀ m ∈ mode? r, ∀ a ∈ aspects r, ∀ e ∈ evidential? r a,
      e ∈ paradigm m a := by
  decide

end Oswalt1986
