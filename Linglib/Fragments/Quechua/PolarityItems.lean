module

public import Linglib.Semantics.Polarity.Licensing

/-!
# Quechua (Ancash) Polarity-Sensitive Items
[haspelmath-1997]

The Ancash Quechua *-pis* series (appendix A.37): interrogative + *-pis*
('also, even'), used in all non-specific functions — questions,
conditionals, both negation functions (direct negation with the
discontinuous negator *mana … -tsu*, A279), comparatives (A277), and free
choice (A278). A dual NPI/FCI on the indefinite-plus-even pattern of
[lahiri-1998].
-/

@[expose] public section

namespace Quechua.PolarityItems

open PolarityItem

/-- *pi-pis* — wh + 'also/even': dual NPI/FCI covering the map's whole
    non-specific span (A.37). -/
def piPis : PolarityItem :=
  { form := "pi-pis"
  , licensor := some .weak
  , freeChoice := true
  , licensingContexts :=
      [.negation, .question, .conditionalAntecedent, .clausalComparative,
       .modalPossibility, .imperative, .generic] }

/-! ### Verification -/

/-- Every attested context admits the item. -/
theorem piPis_licensing_sound :
    ∀ c ∈ piPis.licensingContexts, c.Admits piPis := by
  simp +decide [piPis, LicensingContext.Admits]

end Quechua.PolarityItems
