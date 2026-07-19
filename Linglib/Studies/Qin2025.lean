import Linglib.Morphology.Root.Basic
import Mathlib.Data.List.Infix
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# Qin 2025: canonical and non-canonical roots
[qin-2025]

The canonical-typology answer to "what is a root": a **base definition** that is
purely formal, plus four independent canonicity criteria spanning a 16-cell
space in which rival root notions are located rather than adjudicated.

The base definition: a root is a morphologically unanalyzable form serving as a
**morphological core** of word formation — a morph participating in the
formation of a *primary word* ([bloomfield-1933]: a word containing no free
form as a proper part). The judgment is explicitly "formal-based": English
*-fer* and *-ceive* are root instances despite "lacking identifiable meaning",
so roothood here needs no semantic anchoring — the formal pole of the
definitional space whose semantic pole is [haspelmath-2025-root]'s contentful
morph (`Morph.IsRootIn`), which the *-fer* witness fails
(`fer_root_not_contentful`).

The criteria (Table 1): C1 boundness (free ≻ bound), C2 positional flexibility
(flexible ≻ fixed), C3 phonological richness (rich ≻ deficient), C4 meaning
lexicality (lexical ≻ less lexical) — C1–C2 morphological, C3 phonological, C4
semantic. Canonical roots satisfy all four; Fig. 1's tiers count the ways of
failing k criteria (`tier_card`: 1, 4, 6, 4, 1). The Mandarin case study
classifies 122 morphemes in this space; flagship rows here: canonical 厂
*chǎng*, the C4-only deviant 不 *bù*, the bound-and-fixed 霸 *-bà*, the NC-3
suffix 性 *-xìng*, and the maximally non-canonical toneless 边 *-bian* and 个
*-ge* (tonelessness diagnosing phonological deficiency in a tone language).

## Main declarations

* `IsPrimary`, `IsRootInstance`, `IsTypicalAffix` — the base definition over a
  fragment's word and free-form inventories
* `isRootInstance_of_free_word` — free morphemes forming words are root
  instances; `fer_rootInstance` / `fer_root_not_contentful` — the paper's
  *-fer* case: a root instance with no semantic classification
* `Row`, `Row.violations`, `Row.IsCanonical` — the four-criterion space;
  `space_card`, `tier_card` — Fig. 1's 16 cells and binomial tiers
* `chang`, `bu`, `ba`, `xing`, `bian`, `ge` — Mandarin rows with their
  paper-assigned judgments and tier theorems
-/

namespace Qin2025

open Morphology

/-! ### The base definition -/

/-- A word is **primary** relative to a free-form inventory
([bloomfield-1933], as deployed in [qin-2025]'s base definition): no proper
contiguous part of it is itself a free form. Secondary words — *cats*,
*blackbirds*, *happiness* — contain a free form; primary words — *cat*,
*refer*, Hebrew CV-patterned stems — do not. -/
def IsPrimary (freeForms : List (List Morph)) (w : List Morph) : Prop :=
  ∀ f ∈ freeForms, f.length < w.length → ¬ f <:+: w

instance (freeForms : List (List Morph)) (w : List Morph) :
    Decidable (IsPrimary freeForms w) :=
  inferInstanceAs (Decidable (∀ f ∈ freeForms, _ → _))

/-- A **root instance**: a morph occurring in some primary word — the
morphological core of word formation. The judgment is formal: no semantic
data enters. -/
def IsRootInstance (words freeForms : List (List Morph)) (m : Morph) : Prop :=
  ∃ w ∈ words, IsPrimary freeForms w ∧ m ∈ w

instance (words freeForms : List (List Morph)) (m : Morph) :
    Decidable (IsRootInstance words freeForms m) :=
  inferInstanceAs (Decidable (∃ w ∈ words, _))

/-- A **typical affix** occurs only in secondary words — the base definition's
complement class among bound morphs: *-s* and *-ness* attach to free forms. -/
def IsTypicalAffix (words freeForms : List (List Morph)) (m : Morph) : Prop :=
  ∀ w ∈ words, m ∈ w → ¬ IsPrimary freeForms w

/-- A singleton word is primary whenever the free-form inventory has no empty
form: it has no proper nonempty parts at all. -/
theorem isPrimary_singleton {freeForms : List (List Morph)}
    (h : [] ∉ freeForms) (m : Morph) : IsPrimary freeForms [m] := by
  intro f hf hlen _
  exact h (List.length_eq_zero_iff.mp (Nat.lt_one_iff.mp hlen) ▸ hf)

/-- A free morpheme standing as a word of the fragment is a root instance —
the free half of the base definition's core test. -/
theorem isRootInstance_of_free_word {words freeForms : List (List Morph)}
    {m : Morph} (hw : [m] ∈ words) (h : [] ∉ freeForms) :
    IsRootInstance words freeForms m :=
  ⟨[m], hw, isPrimary_singleton h m, List.mem_singleton_self m⟩

/-! ### The *-fer* witness: roothood without meaning

*re-*, *con-*, and *-fer* are all bound; *refer* and *confer* are free forms
with no free proper part, hence primary — so *-fer* is a root instance,
although it lacks "identifiable meaning" and receives no `RootClass`. The same
morph therefore fails [haspelmath-2025-root]'s contentfulness clause: the two
definitions part exactly where [qin-2025] says roothood is "a formal-based
judgement", not a semantic-core one. -/

/-- The bound Latinate pieces of *refer*/*confer*. -/
def re : Morph := .pref "re"
/-- *-fer*, a bound root with no identifiable meaning. -/
def fer : Morph := .root "fer"
/-- The bound prefix of *confer*. -/
def con : Morph := .pref "con"

/-- The mini-fragment: two primary words, both free forms, no free parts. -/
def ferWords : List (List Morph) := [[re, fer], [con, fer]]

/-- *-fer* is a root instance of the fragment: it occurs in the primary word
*refer*. -/
theorem fer_rootInstance : IsRootInstance ferWords ferWords fer := by decide

/-- *-fer* is not a root by [haspelmath-2025-root]'s definition (1): it denotes
no action, object, or property, so it fails the contentfulness clause under
the fragment's (empty) semantic classification. -/
theorem fer_root_not_contentful :
    ¬ fer.IsRootIn ferWords (fun _ => none) := by decide

/-! ### The four criteria and the theoretical space -/

/-- A morpheme's judgment on the four canonicity criteria (Table 1). The
fields are `Bool` as classification outcomes of the survey: C1 free, C2
positionally flexible, C3 phonologically rich, C4 lexical in meaning. -/
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

/-- Fig. 1's tiers: the ways of being non-canonical in exactly `k` criteria
number `4.choose k` — one canonical cell, then 4, 6, 4, and 1, so "there are
15 different ways for an instance to be non-canonical, while only one way for
an instance to be canonical". -/
theorem tier_card :
    ∀ k : Fin 5, ((Finset.univ.filter fun r : Row => r.violations = k).card
      = Nat.choose 4 k) := by decide

/-! ### Mandarin rows (§4, appendix)

Judgments transcribed from the case study of 122 morphemes; glosses from the
paper. Tonelessness diagnoses phonological deficiency (C3) in a tone
language. -/

/-- 厂 *chǎng* 'a factory': free (monomorphemic word), flexible
(*fúzhuang-chǎng* ~ *chǎng-shang*), toned, fully referential — canonical. -/
def chang : Row := ⟨true, true, true, true⟩

/-- 不 *bù* 'generalized negation': deviates on C4 alone — its meaning is
generalized rather than fully referential and concrete. -/
def bu : Row := ⟨true, true, true, false⟩

/-- 霸 *-bà* 'a person outstanding in a field': bound and positionally fixed,
deviating on C1 and C2. -/
def ba : Row := ⟨false, false, true, true⟩

/-- 性 *-xìng* 'to form nouns or adjectives indicating a property': bound,
fixed, and schematic in meaning — three deviations. -/
def xing : Row := ⟨false, false, true, false⟩

/-- 边 *-bian* 'indicating locality': bound, fixed, toneless, and adding
almost no meaning — none of the four criteria hold. -/
def bian : Row := ⟨false, false, false, false⟩

/-- 个 *-ge* 'used after a demonstrative pronoun': like *-bian*, meeting none
of the criteria; its contribution is grammatical restriction. -/
def ge : Row := ⟨false, false, false, false⟩

/-- The five Mandarin tiers, from the canonical 厂 *chǎng* to the maximally
non-canonical 边 *-bian* and 个 *-ge*. -/
theorem mandarin_tiers :
    chang.IsCanonical ∧ bu.violations = 1 ∧ ba.violations = 2
      ∧ xing.violations = 3 ∧ bian.violations = 4 ∧ ge.violations = 4 := by
  decide

end Qin2025
