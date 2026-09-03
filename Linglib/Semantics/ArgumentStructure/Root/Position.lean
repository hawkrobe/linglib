import Mathlib.Tactic.DeriveFintype

/-!
# Root position

A verbal root composes with the verbalizing head `v` either as its complement, the
result position of change-of-state roots such as √flat and √drown, or adjoined to it
as a modifier, the manner position of √jog and √hand ([beavers-koontz-garboden-2020]
§4.5.3–4.5.4). Position is the second coordinate of the book's root typology (§5.4.1,
(12)), and an adjoined root escapes both the scope of restitutive *again* (§4.5.4) and
the deletion site of verbal VP ellipsis ([kalyakin-2026] §2.2).

## Main declarations

* `Root.Position`

## References

* [beavers-koontz-garboden-2020]: The Roots of Verbal Meaning.
* [kalyakin-2026]: VP ellipsis and argument structure alternations: Evidence from
  Muira Dargwa complex predicates.
-/

namespace Verb

/-- The position in which a verbal root composes with `v`. -/
inductive Root.Position where
  /-- The complement of `v`, the result position. -/
  | complement
  /-- Adjoined to `v` as a modifier, the manner position. -/
  | adjoined
  deriving DecidableEq, Fintype, Repr

end Verb
