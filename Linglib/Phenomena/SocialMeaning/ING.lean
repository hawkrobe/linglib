import Mathlib.Data.Fintype.Basic

/-!
# The (ING) variable

Shared type for the phonological variable (ING) — the alternation
between velar [ɪŋ] (*-ing*) and apical [ɪn] (*-in'*) variants of the
English progressive/gerund suffix.

This is arguably the most-studied variable in sociolinguistics
(@cite{labov-2006}, @cite{campbell-kibler-2007}, @cite{eckert-2008},
@cite{burnett-2019}). The shared type is imported by study files
that formalize different aspects of (ING).
-/

set_option autoImplicit false

namespace Phenomena.SocialMeaning.ING

/-- The two variants of the (ING) variable.
    Velar [ɪŋ] is the standard/prestige variant; apical [ɪn] is the
    vernacular variant. -/
inductive INGVariant where
  | velar   -- *-ing* [ɪŋ]
  | apical  -- *-in'* [ɪn]
  deriving DecidableEq, Repr, Inhabited

instance : Fintype INGVariant where
  elems := {.velar, .apical}
  complete := by intro x; cases x <;> simp

end Phenomena.SocialMeaning.ING
