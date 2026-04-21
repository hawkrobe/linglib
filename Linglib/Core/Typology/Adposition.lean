import Linglib.Core.WALS.Features.F85A

/-!
# Adposition typology: shared record types

@cite{dryer-2013-wals}

Framework-agnostic enum for storing per-language adposition order
(WALS Chapter 85). Lives in `Core/` so both `Fragments/` (per-language
profiles) and `Phenomena/` (cross-linguistic generalizations) can import
without violating layered dependency hierarchy.

Mirror of `Core.Typology.WordOrder` but for adpositions; keeps the
same shape (local enum + WALS converter + ISO lookup), so
`LanguageProfile` extends uniformly across typological domains.
-/

namespace Core.Typology.Adposition

/-- WALS Ch 85: dominant order of adposition and noun phrase, plus a
    `noAdpositions` cell for languages that lack adpositions entirely
    and a `noDominant` cell for mixed systems. -/
inductive AdpositionOrder where
  | prepositional
  | postpositional
  | inpositional
  | noAdpositions
  | noDominant
  deriving DecidableEq, Repr

/-- Convert WALS F85A's `AdpositionNPOrder` to our local `AdpositionOrder`. -/
def fromWALS85A : Core.WALS.F85A.AdpositionNPOrder → AdpositionOrder
  | .prepositions => .prepositional
  | .postpositions => .postpositional
  | .inpositions => .inpositional
  | .noAdpositions => .noAdpositions
  | .noDominantOrder => .noDominant

/-- Look up Ch 85 adposition order for an ISO 639-3 code; `none` if absent
    from WALS. Returns `Option` rather than defaulting to `noDominant`
    because absence-from-WALS and no-dominant-order-in-language are
    different facts; consumers (e.g. `LanguageProfile.adposition`) decide
    how to handle missing data. -/
def adpositionOfWALS (iso : String) : Option AdpositionOrder :=
  match Core.WALS.Datapoint.lookupISO Core.WALS.F85A.allData iso with
  | some d => some (fromWALS85A d.value)
  | none => none

end Core.Typology.Adposition
