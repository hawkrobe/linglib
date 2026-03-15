import Linglib.Core.Lexical.UD

/-!
# Number Values
@cite{corbett-2000}

The analytical number value inventory from @cite{corbett-2000}'s typological
framework. Eight values organized along two orthogonal dimensions:

- **System membership**: general number is *outside* the number system (a form
  non-committal to cardinality); all others are within it.
- **Determinacy**: values whose cardinality boundary is fixed (singular=1,
  dual=2, trial=3) vs those whose boundary varies by context (paucal ≈ 2–6,
  greater plural ≈ abundance).

This module contains the type, basic predicates, and UD bridges. The full
typological machinery (number systems, animacy profiles, agreement hierarchy,
language data) remains in `Phenomena/Agreement/Studies/Corbett2000.lean`.

-/

namespace Core.Number

-- ============================================================================
-- § 1: Number Values
-- ============================================================================

/-- Number values in @cite{corbett-2000}'s inventory.

    Two orthogonal classifications:
    - **System membership**: general is *outside* the number system; all others
      are within it.
    - **Determinacy**: values whose cardinality boundary is fixed (singular=1,
      dual=2, trial=3) vs those whose boundary varies by context (paucal ≈ 2–6,
      greater plural ≈ all/abundance). -/
inductive Value where
  | general        -- non-committal, outside the number system
  | singular       -- exactly one
  | dual           -- exactly two
  | trial          -- exactly three
  | paucal         -- a few (indeterminate, ~2–6)
  | plural         -- more than one (residual)
  | greaterPaucal  -- indeterminate, larger than paucal
  | greaterPlural  -- abundance / totality (indeterminate)
  deriving DecidableEq, BEq, Repr

namespace Value

/-- A number value is determinate iff its cardinality boundary is fixed. -/
def isDeterminate : Value → Bool
  | .singular | .dual | .trial => true
  | _ => false

/-- A number value participates in the number system (is not general). -/
def isInSystem : Value → Bool
  | .general => false
  | _ => true

end Value

-- ============================================================================
-- § 2: UD Bridges
-- ============================================================================

/-- Map analytical number values to UD.Number (general has no UD equivalent). -/
def Value.toUD : Value → Option UD.Number
  | .general       => none
  | .singular      => some .Sing
  | .dual          => some .Dual
  | .trial         => some .Tri
  | .paucal        => some .Pauc
  | .plural        => some .Plur
  | .greaterPaucal => some .Grpa
  | .greaterPlural => some .Grpl

/-- Map UD.Number to analytical number values (partial).

    Seven core values round-trip cleanly. Three UD values have no analytical
    equivalent:
    - `Inv` (inverse number): marks the *unexpected* number for a given noun —
      plural for some nouns, singular for others. Not a fixed cardinality.
    - `Coll` (collective): denotes a group-as-unit (Russian *листва* 'foliage'),
      distinct from general number which is non-committal to cardinality.
    - `Count` (count form): a special form after numerals (Hungarian, Welsh),
      not equivalent to singular (exactly one). -/
def Value.fromUD : UD.Number → Option Value
  | .Sing  => some .singular
  | .Plur  => some .plural
  | .Dual  => some .dual
  | .Tri   => some .trial
  | .Pauc  => some .paucal
  | .Grpa  => some .greaterPaucal
  | .Grpl  => some .greaterPlural
  | .Inv   => none
  | .Coll  => none
  | .Count => none

-- ============================================================================
-- § 3: Verification
-- ============================================================================

/-- Round-trip: fromUD ∘ toUD = id for all in-system values. -/
theorem roundtrip_fromUD_toUD :
    [Value.singular, .dual, .trial, .paucal, .plural,
     .greaterPaucal, .greaterPlural].all
      (λ v => v.toUD.bind Value.fromUD == some v) = true := by native_decide

end Core.Number
