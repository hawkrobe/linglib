import Linglib.Theories.Semantics.Composition.TypeShifting
import Linglib.Phenomena.Copulas.Typology

/-!
# Partee (1987): Type-Shifting and the Copula
@cite{partee-1987}

Partee's §5 argues that English `be` subcategorizes for an `e` argument and
an `⟨e,t⟩` argument, meaning "apply predicate." The `BE` type-shifting
functor applies to the post-copular NP to convert its GQ meaning (⟨⟨e,t⟩,t⟩)
into a predicative one (⟨e,t⟩):

  BE = λQ.λx. Q(λy. y = x)  :  ⟨⟨e,t⟩,t⟩ → ⟨e,t⟩

The copula's combined effect is thus `BE(⟦NP⟧)(⟦subject⟧)`.
"John is a teacher" composes as `BE(⟦a teacher⟧)(⟦John⟧) = teacher'(john')`.

This connects compositional semantics (Theory) to cross-linguistic copula
typology (Data): languages vary in whether `BE` is lexicalized (verbal
copula), covert (zero copula), or expressed through other strategies.

## Predictions

- **Zero copula** possible → `BE` available as a covert type-shift.
- **Verbal adjectives** → adjectives are already type `⟨e,t⟩` (predicates),
  so no `BE` needed for adjectival predication.
- **Nom/loc split** → different predication types lexicalize different
  type-shifting operations.
-/

namespace Partee1987

open Semantics.Composition.TypeShifting (BE lift ident BE_lift_eq_ident)
open Core.IntensionalLogic (Frame Ty)
open Phenomena.Copulas.Typology

variable {m : Frame}

-- ============================================================================
-- §1: ⟦be⟧ = BE
-- ============================================================================

/-- ⟦be⟧ = BE (Partee §5): the copula IS the type-shifting functor.
    Takes a GQ (⟨⟨e,t⟩,t⟩) and returns a predicate (⟨e,t⟩). -/
abbrev be_sem (m : Frame) : m.Denot Ty.ett → m.Denot Ty.et := BE

/-- The copula is semantically transparent for proper names.
    "John is a teacher" with `⟦John⟧ = lift(j)`:
    `BE(lift(j)) = ident(j) = λx. [j = x]`. -/
theorem be_transparent (j : m.Denot .e) :
    be_sem m (lift j) = ident j :=
  BE_lift_eq_ident j

-- ============================================================================
-- §2: Connecting type-shifting theory to copula typology
-- ============================================================================

/-- A language *requires* overt lexicalization of BE when zero copula
    is impossible for nominal predication. -/
def requiresLexicalBE (p : CopulaProfile) : Bool :=
  p.zeroCopula == .impossible

/-- A language needs BE specifically for adjectival predication when
    adjectives are non-verbal (categorially distinct from verbs).
    If adjectives are verbal, they are already type `⟨e,t⟩` and can
    predicate directly via FA — no type-shift needed. -/
def adjRequiresBE (p : CopulaProfile) : Bool :=
  p.predAdj == .nonVerbal

/-- A language has fully covert access to BE when zero copula is
    widespread (not just restricted to certain tense/person contexts). -/
def beIsFullyCovert (p : CopulaProfile) : Bool :=
  p.zeroCopula == .widespread

-- ============================================================================
-- §3: Per-language verification
-- ============================================================================

-- English: obligatory copula, adjectives need BE
theorem english_requires_be : requiresLexicalBE english = true := rfl
theorem english_adj_needs_be : adjRequiresBE english = true := rfl

-- Mandarin: verbal adjectives → no BE needed for adjectival predication
-- (shu hong 'book red' = 'The book is red', no copula)
theorem mandarin_adj_no_be : adjRequiresBE mandarin = false := rfl

-- Russian: restricted zero copula → BE partly covert
-- (present tense: Ona vrach 'She doctor'; past requires byt')
theorem russian_partial_zero : requiresLexicalBE russian = false := rfl
theorem russian_not_fully_covert : beIsFullyCovert russian = false := rfl

-- Tagalog: widespread zero copula → BE fully covert
-- (doktor siya 'doctor she' = 'She is a doctor')
theorem tagalog_fully_covert : beIsFullyCovert tagalog = true := rfl

-- Arabic: restricted zero copula (present tense only)
theorem arabic_partial_zero : requiresLexicalBE arabic = false := rfl

-- Japanese: mixed — i-adjectives verbal, na-adjectives need copula
theorem japanese_mixed_adj : adjRequiresBE japanese = false := rfl

-- Korean: verbal adjectives, but copula required for nominals
theorem korean_adj_no_be : adjRequiresBE korean = false := rfl
theorem korean_nom_requires_be : requiresLexicalBE korean = true := rfl

-- Spanish: nom/loc split (ser vs estar) → different type-shifts lexicalized
theorem spanish_nom_loc_split : (spanish.nomLoc == .different) = true := rfl

-- English: no split — single copula for all predication types
theorem english_no_split : (english.nomLoc == .identical) = true := rfl

-- ============================================================================
-- §4: Typological generalizations
-- ============================================================================

/-- Every language with verbal adjective encoding allows adjectival
    predication without BE — adjectives are already type `⟨e,t⟩`.

    Verbal adj. languages in sample: Mandarin, Korean, Turkish,
    Swahili, Tagalog, Yoruba, Thai. -/
theorem verbal_adj_implies_no_be :
    (allLanguages.filter (·.predAdj == .verbal)).all
      (fun p => !adjRequiresBE p) = true := by native_decide

/-- Languages with widespread zero copula never require lexical BE —
    the type-shift is freely available without lexicalization.

    Widespread zero-copula languages in sample: Swahili, Tagalog, Yoruba. -/
theorem zero_copula_implies_covert_be :
    (allLanguages.filter (·.zeroCopula == .widespread)).all
      (fun p => !requiresLexicalBE p) = true := by native_decide

/-- The majority of languages in the sample differentiate nominal and
    locational predication strategies. This supports the view that
    different predication types involve distinct type-shifting operations. -/
theorem majority_nom_loc_different :
    (allLanguages.filter (·.nomLoc == .different)).length >
    (allLanguages.filter (·.nomLoc == .identical)).length := by native_decide

end Partee1987
