import Linglib.Core.IntensionalLogic.Frame

/-!
# PTQ Syntactic Categories and the Category-to-Type Correspondence

@cite{dowty-wall-peters-1981} Ch. 7, Definitions 7-1 through 7-3
@cite{montague-1973}

Montague's PTQ fragment defines an infinite set of syntactic categories
recursively, then establishes a uniform correspondence between categories
and IL types. This correspondence is the formal bridge from grammar to
semantics: it guarantees that every expression of a given syntactic category
translates into an IL expression of the corresponding logical type.

## Key definitions

- `PtqCat` — syntactic categories (Def 7-1): `t`, `e`, `A/B`, `A//B`
- `catToTy` — the category-to-type function `f` (Bennett's Def 7-3)
- Named abbreviations for the PTQ categories from Table 7-1

## The slash distinction

`A/B` and `A//B` are syntactically distinct but correspond to the **same
logical type** `⟨⟨s, f(B)⟩, f(A)⟩`. The difference is purely syntactic:
- `A/B`: B is in an extensional position (but the type still takes an intension)
- `A//B`: B is in an intensional (oblique) position

Both slash types take the **intension** of their argument as input. This is
Montague's key design decision: uniformly intensionalize all functor-argument
composition, then recover extensionality via meaning postulates when needed.
-/

namespace Core.IntensionalLogic.CategoryType

open Core.IntensionalLogic

-- ════════════════════════════════════════════════════════════════
-- § Syntactic Categories (DWP Def 7-1)
-- ════════════════════════════════════════════════════════════════

/-- PTQ syntactic categories (@cite{dowty-wall-peters-1981} Def 7-1).

    1. `t` and `e` are syntactic categories.
    2. If `A` and `B` are syntactic categories, then `A/B` and `A//B`
       are syntactic categories.

    `A/B` denotes a functor that combines with an expression of
    category `B` to yield an expression of category `A`. `A//B` is
    syntactically distinct but semantically equivalent (same IL type). -/
inductive PtqCat where
  | t : PtqCat
  | e : PtqCat
  | slash : PtqCat → PtqCat → PtqCat
  | dslash : PtqCat → PtqCat → PtqCat
  deriving Repr, DecidableEq

namespace PtqCat

-- ════════════════════════════════════════════════════════════════
-- § Named Categories (DWP Table 7-1)
-- ════════════════════════════════════════════════════════════════

/-- IV = t/e — intransitive verb (phrase): run, walk, talk. -/
abbrev IV : PtqCat := .slash .t .e

/-- CN = t//e — common noun: man, woman, fish, unicorn. -/
abbrev CN : PtqCat := .dslash .t .e

/-- T = t/IV = t/(t/e) — term phrase (NP): John, Mary, every man. -/
abbrev T : PtqCat := .slash .t IV

/-- TV = IV/T — transitive verb: find, lose, eat, seek. -/
abbrev TV : PtqCat := .slash IV T

/-- IAV = IV//IV — intransitive adverb: rapidly, slowly, allegedly. -/
abbrev IAV : PtqCat := .dslash IV IV

/-- DET = T/CN — determiner: every, the, a(n). -/
abbrev DET : PtqCat := .slash T CN

/-- t/t — sentence adverb: necessarily. -/
abbrev SAdv : PtqCat := .slash .t .t

/-- IV/t — sentence-complement verb: believe, assert. -/
abbrev SCV : PtqCat := .slash IV .t

/-- IV//IV — infinitive-complement verb: try, wish. -/
abbrev ICV : PtqCat := .dslash IV IV

/-- IAV/T — preposition (VP-modifying): in, about. -/
abbrev Prep : PtqCat := .slash IAV T

end PtqCat

-- ════════════════════════════════════════════════════════════════
-- § Category-to-Type Correspondence (DWP Def 7-3, Bennett)
-- ════════════════════════════════════════════════════════════════

/-- The category-to-type function `f` (@cite{dowty-wall-peters-1981} Def 7-3).

    Bennett's simplified system, adopted by DWP for the remainder of the book:

    - `f(t) = t`
    - `f(CN) = f(IV) = ⟨e, t⟩`   (basic syntactic categories)
    - `f(A/B) = f(A//B) = ⟨⟨s, f(B)⟩, f(A)⟩`

    Both slash types map to the same IL type: the functor always takes the
    **intension** `⟨s, f(B)⟩` of its argument, reflecting Montague's uniform
    intensionalization of functor-argument composition. -/
def catToTy : PtqCat → Ty
  | .t => .t
  | .e => .e
  | .slash a b => .fn (.intens (catToTy b)) (catToTy a)
  | .dslash a b => .fn (.intens (catToTy b)) (catToTy a)

-- ════════════════════════════════════════════════════════════════
-- § Verification: Table 7-3
-- ════════════════════════════════════════════════════════════════

/-! Each named category maps to the type listed in DWP Table 7-3
(Bennett's version). These are definitional equalities. -/

/-- CN : ⟨⟨s, e⟩, t⟩ — set of individual concepts. -/
theorem catToTy_CN : catToTy PtqCat.CN = .fn (.intens .e) .t := rfl

/-- IV : ⟨⟨s, e⟩, t⟩ — set of individual concepts.
    CN and IV have the same IL type (both "end in" ⟨e, t⟩ under Bennett). -/
theorem catToTy_IV : catToTy PtqCat.IV = .fn (.intens .e) .t := rfl

/-- CN and IV correspond to the same IL type. -/
theorem catToTy_CN_eq_IV : catToTy PtqCat.CN = catToTy PtqCat.IV := rfl

/-- T : ⟨⟨s, ⟨⟨s, e⟩, t⟩⟩, t⟩ — set of properties of individual concepts. -/
theorem catToTy_T :
    catToTy PtqCat.T = .fn (.intens (.fn (.intens .e) .t)) .t := rfl

/-- TV : ⟨⟨s, ⟨⟨s, ⟨⟨s, e⟩, t⟩⟩, t⟩⟩, ⟨⟨s, e⟩, t⟩⟩ -/
theorem catToTy_TV :
    catToTy PtqCat.TV =
    .fn (.intens (.fn (.intens (.fn (.intens .e) .t)) .t))
        (.fn (.intens .e) .t) := rfl

/-- IAV : ⟨⟨s, ⟨⟨s, e⟩, t⟩⟩, ⟨⟨s, e⟩, t⟩⟩ -/
theorem catToTy_IAV :
    catToTy PtqCat.IAV =
    .fn (.intens (.fn (.intens .e) .t)) (.fn (.intens .e) .t) := rfl

/-- DET : ⟨⟨s, ⟨⟨s, e⟩, t⟩⟩, ⟨⟨s, ⟨⟨s, e⟩, t⟩⟩, t⟩⟩ -/
theorem catToTy_DET :
    catToTy PtqCat.DET =
    .fn (.intens (.fn (.intens .e) .t))
        (.fn (.intens (.fn (.intens .e) .t)) .t) := rfl

/-- t/t : ⟨⟨s, t⟩, t⟩ — set of propositions. -/
theorem catToTy_SAdv :
    catToTy PtqCat.SAdv = .fn (.intens .t) .t := rfl

/-- IV/t : ⟨⟨s, t⟩, ⟨⟨s, e⟩, t⟩⟩ -/
theorem catToTy_SCV :
    catToTy PtqCat.SCV =
    .fn (.intens .t) (.fn (.intens .e) .t) := rfl

-- ════════════════════════════════════════════════════════════════
-- § Properties of the Correspondence
-- ════════════════════════════════════════════════════════════════

/-- Single/double slash erase to the same type. -/
theorem slash_dslash_same_type (a b : PtqCat) :
    catToTy (.slash a b) = catToTy (.dslash a b) := rfl

/-- All functor categories have intension types as their argument type. -/
theorem catToTy_slash_is_intens (a b : PtqCat) :
    catToTy (.slash a b) = .fn (.intens (catToTy b)) (catToTy a) := rfl

/-- A functor category's result type is the type of its output category. -/
theorem catToTy_result (a b : PtqCat) :
    match catToTy (.slash a b) with
    | .fn _ τ => τ = catToTy a
    | _ => False := rfl

/-- A functor category's argument type is the intensionalized type
    of its input category. -/
theorem catToTy_arg (a b : PtqCat) :
    match catToTy (.slash a b) with
    | .fn (.intens σ) _ => σ = catToTy b
    | _ => False := rfl

-- ════════════════════════════════════════════════════════════════
-- § Conjoinability via Category Structure
-- ════════════════════════════════════════════════════════════════

/-- A PTQ category is conjoinable if its corresponding type is. -/
def PtqCat.isConjoinable (c : PtqCat) : Bool := (catToTy c).isConjoinable

/-- Sentences (t) are conjoinable. -/
theorem t_conjoinable : PtqCat.t.isConjoinable = true := rfl

/-- VPs (IV) are conjoinable (⟨⟨s,e⟩, t⟩ ends in t). -/
theorem IV_conjoinable : PtqCat.IV.isConjoinable = true := rfl

/-- Term phrases (T) are conjoinable (⟨⟨s, ⟨⟨s,e⟩,t⟩⟩, t⟩ ends in t). -/
theorem T_conjoinable : PtqCat.T.isConjoinable = true := rfl

/-- Entities (e) are not conjoinable. -/
theorem e_not_conjoinable : PtqCat.e.isConjoinable = false := rfl

end Core.IntensionalLogic.CategoryType
