import Linglib.Morphology.Root.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# Qin 2025: canonical and non-canonical roots
[qin-2025]

The canonical-typology space of roots over the formal base definition of
`Morphology/Root/Basic.lean`: four canonicity criteria (Table 1) — C1
boundness, C2 positional flexibility, C3 phonological richness, C4 meaning
lexicality — spanning a 16-cell space anchored by the canonical root, with
Fig. 1's tiers counting the ways of failing k criteria. The Mandarin case
study classifies 122 morphemes in the space; flagship rows here run from
canonical 厂 *chǎng* to the maximally non-canonical toneless 边 *-bian* and 个
*-ge* (tonelessness diagnosing phonological deficiency in a tone language).

The paper's *-fer* case makes the base definition's formal character exact:
*-fer* is a morphological core "lacking identifiable meaning", so it fails
[haspelmath-2025-root]'s contentfulness clause — the roothood judgment is
"formal-based", not semantic (`fer_core`, `fer_root_not_contentful`).

## Main results

* `fer_core` / `fer_root_not_contentful` — *-fer* is a core with no root
  class: the formal and semantic definitions come apart.
* `Row`, `Row.violations`, `Row.IsCanonical` — the four-criterion space;
  `space_card`, `tier_card` — Fig. 1's 16 cells and binomial tiers.
* `chang`, `bu`, `ba`, `xing`, `bian`, `ge` — Mandarin rows with their
  paper-assigned judgments (`mandarin_tiers`).
-/

namespace Qin2025

open Morphology

/-! ### The *-fer* witness -/

/-- The bound prefix of *refer*. -/
def re : Morph := .pref "re"
/-- *-fer*, a bound root with no identifiable meaning. -/
def fer : Morph := .root "fer"
/-- The bound prefix of *confer*. -/
def con : Morph := .pref "con"

/-- The mini-fragment: *refer* and *confer*, both free forms, primary since
neither *re-*, *con-*, nor *-fer* is free. -/
def ferWords : List (List Morph) := [[re, fer], [con, fer]]

/-- *-fer* is a morphological core: it occurs in the primary word *refer*. -/
theorem fer_core : fer.IsCoreIn ferWords ferWords := by decide

/-- *-fer* is not a root by [haspelmath-2025-root]'s definition (1): it
denotes no action, object, or property. -/
theorem fer_root_not_contentful :
    ¬ fer.IsRootIn ferWords (fun _ => none) := by decide

/-! ### The four criteria and the theoretical space -/

/-- A morpheme's judgment on the four canonicity criteria (Table 1), as the
survey's classification outcomes: C1 free, C2 positionally flexible, C3
phonologically rich, C4 lexical in meaning. -/
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

/-- The number of criteria a row fails — its distance from the canonical
point. -/
def Row.violations (r : Row) : ℕ :=
  (if r.c1 then 0 else 1) + (if r.c2 then 0 else 1)
    + (if r.c3 then 0 else 1) + (if r.c4 then 0 else 1)

/-- A **canonical root** satisfies all four criteria. -/
def Row.IsCanonical (r : Row) : Prop := r.violations = 0

instance (r : Row) : Decidable r.IsCanonical :=
  inferInstanceAs (Decidable (r.violations = 0))

/-- The theoretical space of roots has 16 cells (Fig. 1). -/
theorem space_card : Fintype.card Row = 16 := by decide

/-- Fig. 1's tiers: `4.choose k` ways to fail exactly `k` criteria — "there
are 15 different ways for an instance to be non-canonical, while only one way
for an instance to be canonical". -/
theorem tier_card :
    ∀ k : Fin 5, ((Finset.univ.filter fun r : Row => r.violations = k).card
      = Nat.choose 4 k) := by decide

/-! ### Mandarin rows (§4, appendix)

Judgments transcribed from the case study; glosses from the paper. -/

/-- 厂 *chǎng* 'a factory': free, flexible (*fúzhuang-chǎng* ~ *chǎng-shang*),
toned, fully referential — canonical. -/
def chang : Row := ⟨true, true, true, true⟩

/-- 不 *bù* 'generalized negation': deviates on C4 alone. -/
def bu : Row := ⟨true, true, true, false⟩

/-- 霸 *-bà* 'a person outstanding in a field': bound and positionally
fixed. -/
def ba : Row := ⟨false, false, true, true⟩

/-- 性 *-xìng* 'to form nouns or adjectives indicating a property': bound,
fixed, and schematic in meaning. -/
def xing : Row := ⟨false, false, true, false⟩

/-- 边 *-bian* 'indicating locality': bound, fixed, toneless, adding almost
no meaning. -/
def bian : Row := ⟨false, false, false, false⟩

/-- 个 *-ge* 'used after a demonstrative pronoun': like *-bian*, meeting none
of the criteria. -/
def ge : Row := ⟨false, false, false, false⟩

/-- The five Mandarin tiers, from canonical 厂 *chǎng* to the maximally
non-canonical 边 *-bian* and 个 *-ge*. -/
theorem mandarin_tiers :
    chang.IsCanonical ∧ bu.violations = 1 ∧ ba.violations = 2
      ∧ xing.violations = 3 ∧ bian.violations = 4 ∧ ge.violations = 4 := by
  decide

end Qin2025
