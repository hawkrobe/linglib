import Linglib.Core.Lexical.NegMarker

/-!
# English Negation Fragment
@cite{miestamo-2005} @cite{haspelmath-2013} @cite{dryer-haspelmath-2013}

English expresses standard negation with the particle *not* (contracted *n't*).
WALS classifies English as **both symmetric and asymmetric** (SymAsy):

- **Symmetric**: with modals, *be*, and *have*, negation simply adds *not*
  with no structural change: *He can swim* → *He cannot swim*.

- **Asymmetric (A/Cat)**: with lexical verbs, negation introduces auxiliary
  *do* (do-support): *He eats* → *He does not eat*. This is a category-level
  change — the finite verb becomes an auxiliary, and the lexical verb appears
  as a bare infinitive.

## Negative indefinites (Ch 115)

WALS classifies English as **mixed**:
- *nobody*, *nothing* preclude predicate negation: *Nobody came* / **Nobody didn't come*
- *anything*, *ever* require predicate negation: *I didn't see anything* / **I saw anything*
-/

namespace Fragments.English.Negation

open Core.Lexical.NegMarker

/-- *not* — English's standard negation particle.
    The contracted form *n't* attaches as a clitic to auxiliaries
    (*isn't*, *don't*, *won't*); see `negContracted` for the citation form
    of that allomorph. With lexical verbs, *do*-support is required:
    *He does not eat*, not **He not eats*. -/
def not : NegMarkerEntry :=
  { form := "not"
  , morphemeType := .particle
  , position := .preverbal }

/-- The contracted form *n't*. Phonologically a clitic on the auxiliary;
    syntactically the same negation marker as *not*. Listed for the
    completeness of the citation forms; downstream consumers should
    treat *not* as the canonical entry. -/
def negContracted : String := "n't"

/-- The English negation system: a single preverbal particle.
    The Fragment-side joint consumed by `Phenomena/Negation/Typology.lean`. -/
def negationSystem : NegationSystem :=
  NegationSystem.ofISO "eng" [not]

/-- An English negation example. -/
structure NegExample where
  affirmative : String
  negative : String
  glossAff : String
  glossNeg : String
  /-- Does this construction require do-support? -/
  doSupport : Bool
  /-- Is this construction symmetric (neg = aff + neg marker, no other change)? -/
  symmetric : Bool
  deriving Repr, BEq

/-- Modal *can*: symmetric (no do-support). -/
def modal : NegExample :=
  { affirmative := "he can swim", negative := "he cannot swim"
  , glossAff := "3SG can swim", glossNeg := "3SG can.NEG swim"
  , doSupport := false, symmetric := true }

/-- Copula *be*: symmetric (no do-support). -/
def copula : NegExample :=
  { affirmative := "she is tall", negative := "she is not tall"
  , glossAff := "3SG be tall", glossNeg := "3SG be NEG tall"
  , doSupport := false, symmetric := true }

/-- Auxiliary *have*: symmetric (no do-support). -/
def auxHave : NegExample :=
  { affirmative := "they have eaten", negative := "they have not eaten"
  , glossAff := "3PL have eaten", glossNeg := "3PL have NEG eaten"
  , doSupport := false, symmetric := true }

/-- Lexical verb, present: asymmetric (do-support required). -/
def lexicalPresent : NegExample :=
  { affirmative := "he eats", negative := "he does not eat"
  , glossAff := "3SG eat.3SG", glossNeg := "3SG do.3SG NEG eat"
  , doSupport := true, symmetric := false }

/-- Lexical verb, past: asymmetric (do-support required). -/
def lexicalPast : NegExample :=
  { affirmative := "he ate", negative := "he did not eat"
  , glossAff := "3SG eat.PST", glossNeg := "3SG do.PST NEG eat"
  , doSupport := true, symmetric := false }

def allExamples : List NegExample :=
  [modal, copula, auxHave, lexicalPresent, lexicalPast]

/-! ## Verification -/

theorem all_examples_count : allExamples.length = 5 := by native_decide

/-- 3 symmetric + 2 asymmetric = SymAsy. -/
theorem symasy_distribution :
    (allExamples.filter (·.symmetric)).length = 3 ∧
    (allExamples.filter (fun e => !e.symmetric)).length = 2 := by
  exact ⟨by native_decide, by native_decide⟩

/-- Asymmetric constructions all involve do-support. -/
theorem asymmetric_iff_dosupport :
    allExamples.all (fun e => e.symmetric == !e.doSupport) = true := by
  native_decide

/-- Symmetric constructions do not involve do-support. -/
theorem symmetric_no_dosupport :
    (allExamples.filter (·.symmetric)).all (fun e => !e.doSupport) = true := by
  native_decide

end Fragments.English.Negation
