import Linglib.Morphology.Root.Basic
import Linglib.Data.Forms.Qin2025
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# Qin (2025): Canonical and Non-Canonical Roots: The Diversity of Roots in Mandarin Chinese

This file formalizes [qin-2025]'s canonical typology of roots. The base definition, a
morphologically unanalyzable form that serves as a morphological core of word formation, is the
substrate's `Morphology.Morph.IsCoreIn`, and the paper's *-fer* shows that the judgment is formal
rather than semantic: *-fer* is a core of the primary word *refer* though it has no meaning of its
own (`fer_core`). Four criteria (Table 1), boundness, positional flexibility, phonological
richness, and meaning lexicality, span a space of sixteen cells anchored by the canonical root
that meets all four, and Fig. 1's one way of being canonical against fifteen of being
non-canonical is the binomial count of the tiers (`tier_card`). The case study classifies 122
Mandarin morphemes (Appendix A): the forms carry the appendix's codes on the four criteria, its
five groups are the number of criteria a form fails (`forms_group`), and the property of the
distribution the paper singles out holds of every form, that a phonologically deficient
morpheme, toneless in a tone language, is maximally non-canonical (`deficient_maximal`). The
tiers run from the canonical 厂 *chǎng* of Table 3 through 不 *bù*, 霸 *bà*, and 性 *xìng* to the
toneless 边 *-bian* and 个 *-ge* (`mandarin_tiers`).

## Implementation notes

The appendix is a CLDF `FormTable` whose custom columns are the paper's codes: F or B for
boundness, FLEX, SL, or SR for position, 1 or TL for phonology, and L or NL for meaning. A row
reads the codes as a Boolean judgment on each criterion, the canonical value being `true`; the
two fixed positions SL and SR both count as fixed. The counts of Tables 2 and 4 are the
distribution of the forms and are not restated.

## TODO

The paper says that six of the unattested cells of the space require phonological deficiency;
the appendix leaves seven such cells unattested, since only the maximally non-canonical cell
contains a toneless morpheme, and the cell of free, fixed, toned, lexical morphemes is unattested
as well.

## References

* [qin-2025]
* [bloomfield-1933]
-/

namespace Qin2025

open Morphology Data.Forms

/-! ### The base definition and *-fer* (§3.1) -/

/-- The bound prefix of *refer*. -/
def re : Morph := .pref "re"

/-- *-fer*, a bound root with no identifiable meaning. -/
def fer : Morph := .root "fer"

/-- The bound prefix of *confer*. -/
def con : Morph := .pref "con"

/-- The mini-fragment *refer* and *confer*, both free forms and both primary, since neither
*re-*, *con-*, nor *-fer* is free. -/
def ferWords : List (List Morph) := [[re, fer], [con, fer]]

/-- *-fer* is a morphological core: it occurs in the primary word *refer*. -/
theorem fer_core : fer.IsCoreIn ferWords ferWords := by decide

/-! ### The four criteria and the theoretical space (§3.2, §3.3) -/

/-- A morpheme's judgment on the four criteria of Table 1: free, positionally flexible,
phonologically rich, and lexical in meaning. -/
structure Row where
  /-- C1: free rather than bound. -/
  c1 : Bool
  /-- C2: positionally flexible rather than fixed. -/
  c2 : Bool
  /-- C3: phonologically rich rather than deficient. -/
  c3 : Bool
  /-- C4: lexical rather than less lexical in meaning. -/
  c4 : Bool
  deriving DecidableEq, Repr, Fintype

/-- The number of criteria a row fails, its distance from the canonical root. -/
def Row.violations (r : Row) : ℕ :=
  (if r.c1 then 0 else 1) + (if r.c2 then 0 else 1) + (if r.c3 then 0 else 1) +
    (if r.c4 then 0 else 1)

/-- A canonical root satisfies all four criteria. -/
def Row.IsCanonical (r : Row) : Prop := r.violations = 0

instance (r : Row) : Decidable r.IsCanonical := inferInstanceAs (Decidable (r.violations = 0))

/-- The theoretical space of roots has sixteen cells (Fig. 1). -/
theorem space_card : Fintype.card Row = 16 := by decide

/-- Fig. 1's tiers: `4.choose k` ways to fail exactly `k` criteria, so fifteen ways of being
non-canonical against one of being canonical. -/
theorem tier_card :
    ∀ k : Fin 5, (Finset.univ.filter λ r : Row => r.violations = k).card = Nat.choose 4 k := by
  decide

/-! ### The Mandarin case study (§4, Appendix A) -/

/-- A form's judgments, read from the appendix's codes. -/
def interpret (f : Form) : Option Row := do
  let c1 ← match f.column? "Boundness" with
    | some "F" => some true
    | some "B" => some false
    | _ => none
  let c2 ← match f.column? "Positional_Flexibility" with
    | some "FLEX" => some true
    | some "SL" | some "SR" => some false
    | _ => none
  let c3 ← match f.column? "Phonological_Richness" with
    | some "1" => some true
    | some "TL" => some false
    | _ => none
  let c4 ← match f.column? "Meaning_Lexicality" with
    | some "L" => some true
    | some "NL" => some false
    | _ => none
  pure ⟨c1, c2, c3, c4⟩

/-- The number of criteria a form fails. -/
def violations? (f : Form) : Option ℕ := (interpret f).map Row.violations

/-- The appendix's group of a form: canonical roots, then non-canonical roots by the number of
criteria violated. -/
def group? : String → Option ℕ
  | "1" => some 0
  | "2" => some 1
  | "3" => some 2
  | "4" => some 3
  | "5" => some 4
  | _ => none

/-- Every form is classified on all four criteria, and its group is the number it fails. -/
theorem forms_group :
    ∀ f ∈ Forms.all,
      (f.column? "Group").bind group? = violations? f ∧ (violations? f).isSome := by
  decide +kernel

/-- A phonologically deficient morpheme is maximally non-canonical: only the bottom cell of the
space holds a toneless morpheme. -/
theorem deficient_maximal :
    ∀ f ∈ Forms.all, ∀ row ∈ interpret f, row.c3 = false → row.violations = 4 := by
  decide +kernel

/-- The five tiers: canonical 厂 *chǎng* (Table 3), 不 *bù* deviating on meaning alone, bound and
fixed 霸 *bà*, schematic 性 *xìng*, and the toneless 边 *-bian* and 个 *-ge* meeting no
criterion. -/
theorem mandarin_tiers :
    violations? Forms.chang = some 0 ∧ violations? Forms.bu_2 = some 1 ∧
      violations? Forms.ba_2 = some 2 ∧ violations? Forms.xing_4 = some 3 ∧
      violations? Forms.bian = some 4 ∧ violations? Forms.ge_2 = some 4 := by
  decide

end Qin2025
