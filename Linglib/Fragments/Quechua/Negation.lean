import Linglib.Core.Lexical.Word

/-!
# Imbabura Quechua Negation Fragment
@cite{miestamo-2005} @cite{dryer-haspelmath-2013}

Imbabura Quechua expresses standard negation with the preverbal particle
*mana*, optionally reinforced by the suffix *-chu* on the verb.

## SymAsy: Symmetric and Asymmetric (A/NonReal)

WALS classifies Imbabura Quechua as **both symmetric and asymmetric**:

- **Symmetric**: in some constructions, *mana* simply negates without
  further structural change.

- **Asymmetric (A/NonReal)**: in other constructions, negation triggers
  obligatory *-chu* marking on the verb. *-chu* is a **validator** enclitic
  that also appears in polar interrogatives; it expresses assertion
  authority and certainty (@cite{miestamo-2005} p. 158). Its use in
  negatives introduces a non-realized category absent from affirmatives.

The A/NonReal asymmetry is **paradigmatic**: the negative paradigm
obligatorily includes a validator category (*-chu*) that the affirmative
lacks. The clause structure itself does not change (no constructional
asymmetry).
-/

namespace Fragments.Quechua.Negation

/-- The standard negation particle. -/
def negParticle : String := "mana"

/-- The validator enclitic triggered in negative (and interrogative) contexts.
    Glossed as VAL (validator); shared with polar questions. -/
def chuSuffix : String := "-chu"

/-- An Imbabura Quechua negation example. -/
structure NegExample where
  affirmative : String
  negative : String
  glossAff : String
  glossNeg : String
  /-- Does this construction require -chu? -/
  requiresChu : Bool
  /-- Is this construction symmetric? -/
  symmetric : Bool
  deriving Repr, BEq

/-- Simple present: asymmetric (requires -chu, A/NonReal). -/
def present : NegExample :=
  { affirmative := "shamuni", negative := "mana shamu-ni-chu"
  , glossAff := "come-1SG", glossNeg := "NEG come-1SG-VAL"
  , requiresChu := true, symmetric := false }

/-- Progressive: symmetric (mana alone suffices). -/
def progressive : NegExample :=
  { affirmative := "shamucuni", negative := "mana shamucuni"
  , glossAff := "come-PROG-1SG", glossNeg := "NEG come-PROG-1SG"
  , requiresChu := false, symmetric := true }

/-- Past: asymmetric (requires -chu). -/
def past : NegExample :=
  { affirmative := "shamurca", negative := "mana shamurca-chu"
  , glossAff := "come-PST", glossNeg := "NEG come-PST-VAL"
  , requiresChu := true, symmetric := false }

def allExamples : List NegExample :=
  [present, progressive, past]

/-! ## Verification -/

theorem negParticle_is_mana : negParticle = "mana" := rfl
theorem chuSuffix_is_chu : chuSuffix = "-chu" := rfl
theorem example_count : allExamples.length = 3 := by native_decide

/-- Mixed: some symmetric, some asymmetric = SymAsy. -/
theorem symasy_distribution :
    (allExamples.filter (·.symmetric)).length = 1 ∧
    (allExamples.filter (fun e => !e.symmetric)).length = 2 := by
  exact ⟨by native_decide, by native_decide⟩

/-- Asymmetric constructions are exactly those requiring -chu. -/
theorem asymmetric_iff_chu :
    allExamples.all (fun e => e.symmetric == !e.requiresChu) = true := by
  native_decide

end Fragments.Quechua.Negation
