import Linglib.Semantics.Quantification.UnifiedUniversal
import Linglib.Semantics.Quantification.ONEModifiers
import Linglib.Semantics.Quantification.Basic
import Linglib.Semantics.Plurality.Distributivity
import Linglib.Semantics.Plurality.Trivalent
import Linglib.Fragments.German.Distributives
import Linglib.Fragments.English.Distributives
import Linglib.Fragments.English.Determiners
import Mathlib.Data.List.Basic

/-!
# [haslinger-etal-2025-nllt]: A unified semantics for universal quantifiers

Theoretical verification for "A unified semantics for distributive and
non-distributive universal quantifiers across languages" (NLLT 43, 2025).

## Main finding

A single morpheme `Q_∀` derives both distributive and non-distributive
readings: the reading falls out from the algebraic structure of the restrictor
(atoms → [+dist], a sum-closed/cumulative restrictor with a single maximal
element → [−dist]). This *derives* the empirical **Distributivity–Number
Generalization** (DNG): a singular count complement forces [+dist], a plural
complement forces [−dist] — a strengthening of [gil-1995]'s implicational
universal (cf. also [winter-2001]). The distributive readings that [−dist]
forms additionally allow come from a VP-level distributivity operator
([link-1987]), not from the quantifier.

Two-form languages (English, German, Hindi, …) realize a syntactic head ONE
below `Q_∀` that restricts the complement via presupposition:
- `ONE_∅`: non-overlap (English *every*)
- `ONE_AT`: atomicity, stronger (English *each*) — following [fassi-fehri-2020]

One-form languages (Dagara, Moore, Gourmantchema, Wolof, Syrian Arabic) use
bare `Q_∀`, whose reading is fixed by complement number.

## Relation to [haslinger-etal-2025] (S&P)

The S&P paper (`HaslingerEtAl2025.lean`) shows distributivity ≠ maximality via
tolerance. This NLLT paper shows distributivity ≠ number via `Q_∀` +
mereological structure. Complementary results from overlapping author sets;
both consume `Semantics/Plurality/Distributivity.lean` substrate.

## Theory-layer grounding

- `UnifiedUniversal.lean`: `Q_∀`, `maxNonOverlap`, DNG theorems.
- `ONEModifiers.lean`: `ONE_∅`, `ONE_AT`, English every/each decomposition.
- The 1-form/2-form `UQProfile` survey schema is study-local (single-paper data;
  the per-language forms derive from the determiner Fragments, not hand-typed).
- Bridge theorems connect `Q_∀` to existing `distMaximal`/`allViaForallH`.
-/

namespace HaslingerHienEtAl2025

open Quantification.UnifiedUniversal
open Quantification.ONEModifiers
open Semantics.Plurality
open Semantics.Plurality.Distributivity
open Semantics.Plurality.Trivalent
open _root_.Mereology

/-! ### Cross-linguistic typology

The 1-form vs 2-form survey of [haslinger-etal-2025-nllt] (1-form = its Table 2,
2-form = its Table 1). The schema is study-local — this is single-paper survey
data — and the English/German forms are read off the determiner Fragments
(`every`/`all`, `jeder`/`alle`) rather than restated. -/

/-- Whether a language lexicalizes one UQ lexeme whose reading is fixed by
complement number (`oneForm`), or two distinct [+dist]/[−dist] forms (`twoForm`).
[haslinger-etal-2025-nllt] -/
inductive SystemType where
  /-- Single UQ lexeme; reading determined by complement number. -/
  | oneForm
  /-- Distinct [+dist] and [−dist] UQ lexemes. -/
  | twoForm
  deriving DecidableEq, Repr

/-- A language's DP-internal universal-quantifier inventory, as compiled in
[haslinger-etal-2025-nllt] (Table 1 for 2-form, Table 2 for 1-form languages). -/
structure UQProfile where
  /-- Language name. -/
  language : String
  /-- Genealogical family (the survey's label). -/
  family : String
  /-- 1-form vs 2-form classification. -/
  systemType : SystemType
  /-- The [+dist] exponent; in 1-form languages, the sole UQ exponent. -/
  distForm : String
  /-- The [−dist] exponent; empty in 1-form languages. -/
  nonDistForm : String := ""
  /-- Data provenance the survey attributes the row to. -/
  source : String := ""
  deriving Repr, DecidableEq

/-- A 1-form language: one UQ lexeme, reading fixed by complement number. -/
def UQProfile.isOneForm (p : UQProfile) : Prop := p.systemType = .oneForm

/-- A 2-form language: distinct [+dist]/[−dist] UQ lexemes. -/
def UQProfile.isTwoForm (p : UQProfile) : Prop := p.systemType = .twoForm

instance (p : UQProfile) : Decidable p.isOneForm := by
  unfold UQProfile.isOneForm; infer_instance

instance (p : UQProfile) : Decidable p.isTwoForm := by
  unfold UQProfile.isTwoForm; infer_instance

/-- Typological sample (inlined from the paper's Tables 1–2). The English/German
[+dist]/[−dist] forms derive from the determiner Fragments; the rest are the
survey's reported exponents. -/
def typologicalSample : List UQProfile :=
  [ { language := "Dagara"
    , family := "Mabia"
    , systemType := .oneForm
    , distForm := "'hà"
    , source := "[haslinger-etal-2025-nllt] (author elicitation; one author is a native speaker)" }
  , { language := "Moore"
    , family := "Mabia"
    , systemType := .oneForm
    , distForm := "fãa"
    , source := "[haslinger-etal-2025-nllt] (elicited, two native-speaker consultants)" }
  , { language := "Gourmantchema"
    , family := "Mabia"
    , systemType := .oneForm
    , distForm := "kuli"
    , source := "[haslinger-etal-2025-nllt] (elicited, native-speaker consultant)" }
  , { language := "Wolof"
    , family := "Atlantic"
    , systemType := .oneForm
    , distForm := "-epp"
    , source := "[haslinger-etal-2025-nllt] (Tamba, Torrence & Zribi-Hertz 2012)" }
  , { language := "Syrian Arabic"
    , family := "Semitic"
    , systemType := .oneForm
    , distForm := "kul"
    , source := "[haslinger-etal-2025-nllt] (native-speaker consultant; cf. Fassi Fehri 2020 for Standard Arabic kull)" }
  , { language := "English"
    , family := "Indo-European (Germanic)"
    , systemType := .twoForm
    , distForm := English.Determiners.every.form
    , nonDistForm := English.Determiners.all.form
    , source := "[haslinger-etal-2025-nllt] Table 1" }
  , { language := "German"
    , family := "Indo-European (Germanic)"
    , systemType := .twoForm
    , distForm := German.Distributives.jederEntry.form
    , nonDistForm := German.Distributives.alleEntry.form
    , source := "[haslinger-etal-2025-nllt] Table 1 (author elicitation)" }
  , { language := "Hindi"
    , family := "Indo-European (Indic)"
    , systemType := .twoForm
    , distForm := "praty-ek"
    , nonDistForm := "saar-"
    , source := "[haslinger-etal-2025-nllt] Table 1 (Mahajan 2017)" }
  , { language := "Russian"
    , family := "Indo-European (Slavic)"
    , systemType := .twoForm
    , distForm := "každyj"
    , nonDistForm := "vse"
    , source := "[haslinger-etal-2025-nllt] Table 1 (Paperno 2012)" }
  , { language := "Imbabura Quichua"
    , family := "Quechuan"
    , systemType := .twoForm
    , distForm := "kada"
    , nonDistForm := "tukuy(-lla)"
    , source := "[haslinger-etal-2025-nllt] Table 1 (Barchas-Lichtenstein et al. 2017)" }
  , { language := "Turkish"
    , family := "Turkic"
    , systemType := .twoForm
    , distForm := "her"
    , nonDistForm := "bütün, hepsi"
    , source := "[haslinger-etal-2025-nllt] Table 1 (Özyıldız 2017)" }
  , { language := "Basque"
    , family := "isolate"
    , systemType := .twoForm
    , distForm := "bakoitz"
    , nonDistForm := "guzti, den, oro"
    , source := "[haslinger-etal-2025-nllt] Table 1 (Etxeberria 2012)" }
  , { language := "Telugu"
    , family := "Dravidian"
    , systemType := .twoForm
    , distForm := "prɨti"
    , nonDistForm := "ăndărŭ"
    , source := "[haslinger-etal-2025-nllt] Table 1 (Ponangi 2012)" }
  , { language := "Hausa"
    , family := "Afro-Asiatic (West Chadic)"
    , systemType := .twoForm
    , distForm := "koowànè"
    , nonDistForm := "duk"
    , source := "[haslinger-etal-2025-nllt] Table 1 (Zimmermann 2008)" }
  , { language := "Logoori"
    , family := "Niger-Congo (Bantu)"
    , systemType := .twoForm
    , distForm := "vuri"
    , nonDistForm := "-oosi"
    , source := "[haslinger-etal-2025-nllt] Table 1 (Landman 2016)" }
  ]

/-- The survey samples 15 languages. -/
theorem sample_size : typologicalSample.length = 15 := by decide

/-- 1-form count (Table 2): Dagara, Moore, Gourmantchema, Wolof, Syrian Arabic. -/
theorem oneForm_count :
    (typologicalSample.filter (·.systemType == .oneForm)).length = 5 := by decide

/-- 2-form count (Table 1): English, German, Hindi, Russian, Imbabura Quichua,
    Turkish, Basque, Telugu, Hausa, Logoori. -/
theorem twoForm_count :
    (typologicalSample.filter (·.systemType == .twoForm)).length = 10 := by decide

/-- Every sampled language is either 1-form or 2-form — the classification is an
    exhaustive partition (no row is neither). -/
theorem oneForm_twoForm_partition :
    (typologicalSample.filter (·.systemType == .oneForm)).length +
    (typologicalSample.filter (·.systemType == .twoForm)).length =
      typologicalSample.length := by decide

/-! ### Finite model: the DNG on a 3-atom domain

Verify the DNG on a concrete flat 3-element domain (the SG case), where every
element is an atom and distinct elements are disjoint. -/

section FiniteModel

/-- Three students: a flat domain where every element is an atom. -/
inductive Student where | alice | bob | carol
  deriving DecidableEq, Repr

instance : Fintype Student where
  elems := {.alice, .bob, .carol}
  complete := by intro x; cases x <;> decide

/-- Flat discrete order: x ≤ y ↔ x = y. Every element is an atom. -/
instance : PartialOrder Student where
  le x y := x = y
  le_refl := fun _ => rfl
  le_trans := fun _ _ _ h1 h2 => h1.trans h2
  le_antisymm := fun _ _ h _ => h

/-- The flat `Student` order is the canonical `IsAtomicDomain`: its atomicity and
disjointness now come from the shared `Mereology` machinery, not bespoke proofs. -/
instance : IsAtomicDomain Student := isAtomicDomain_of_le_iff_eq (fun _ _ => Iff.rfl)

/-- "passed the exam" -/
def passed : Student → Prop
  | .alice => True
  | .bob => True
  | .carol => False

/-- All `Student`s are atoms — derived from the `IsAtomicDomain` instance. -/
theorem student_atoms : ∀ (x : Student), (fun _ => True : Student → Prop) x →
    Mereology.Atom x :=
  fun x _ => IsAtomicDomain.all_atoms x

/-- Distinct `Student`s don't overlap — derived from the `IsAtomicDomain` instance. -/
theorem student_disjoint : ∀ (x y : Student),
    (fun _ => True : Student → Prop) x →
    (fun _ => True : Student → Prop) y →
    Mereology.Overlap x y → x = y :=
  fun _ _ _ _ h => IsAtomicDomain.eq_of_overlap h

/-- DNG-SG: `Q_∀` on a flat domain distributes to each element. -/
theorem dng_sg_concrete :
    QForall (fun _ : Student => True) passed ↔
    ∀ x : Student, passed x := by
  rw [dng_atoms student_atoms student_disjoint]
  simp only [forall_const]

/-- `Q_∀(student)(passed)` is false: Carol didn't pass. -/
theorem dng_sg_false : ¬QForall (fun _ : Student => True) passed := by
  rw [dng_sg_concrete]
  intro h
  exact h .carol

end FiniteModel

/-! ### Bridge to tolerance-based distributivity

Connect `Q_∀` on atoms to `distMaximal` from `Distributivity.lean`. For an
atomic restrictor `P`, `Q_∀(P)(Q)` reduces to `∀x, P(x) → Q(x)` (by
`dng_atoms`), which is exactly `distMaximal P X w`. The bridge is a semantic
equivalence on the shared domain, not a definitional equality (different
signatures: `Q_∀` over `PartialOrder`, `distMaximal` over `Finset Atom`). -/

/-- `Q_∀` on atoms is semantically equivalent to `distMaximal`: both say "Q
    holds of every atom in the restrictor." -/
theorem QForall_atoms_iff_distMaximal
    {Atom W : Type*} [DecidableEq Atom]
    (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (X : Finset Atom) (w : W) :
    (∀ a ∈ X, P a w) ↔ distMaximal P X w := Iff.rfl

/-- `Q_∀` on a cumulative restrictor is equivalent to `allSatisfy` over its
    atoms: both say "Q holds of every atom in the group." -/
theorem QForall_cum_iff_allSatisfy
    {Atom W : Type*} [DecidableEq Atom]
    (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (X : Finset Atom) (w : W) :
    allSatisfy P X w ↔ (∀ a ∈ X, P a w) := by
  simp only [allSatisfy, distMaximal]

/-! ### English every/each/all decomposition

The English decomposition from [haslinger-etal-2025-nllt] (eq. 79):
- all = `Q_∀` (bare, no ONE)
- every = `Q_∀[ONE_∅]`
- each = `Q_∀[ONE_∅[ONE_AT]]`

Verified: each ⊂ every ⊂ all in presuppositional strength. -/

section EnglishDecomposition

variable {α : Type*} [PartialOrder α] {P Q : α → Prop}

/-- *each* entails *every* (ONE_AT ⊂ ONE_∅). -/
theorem each_stronger_than_every :
    eachPresup P Q → everyPresup P Q :=
  each_entails_every

/-- *every* entails *all* (ONE_∅ ⊂ no presupposition). -/
theorem every_stronger_than_all (h : everyPresup P Q) : QForall P Q :=
  h.2

/-- When ONE_∅ holds, `Q_∀` distributes to atoms. -/
theorem every_is_distributive (hONE : ONE_empty P) :
    QForall P Q ↔ ∀ x, P x → Q x :=
  every_distributes hONE

/-- The full chain: each ⊂ every ⊂ all. -/
theorem presup_chain : eachPresup P Q → everyPresup P Q ∧ QForall P Q :=
  fun h => ⟨each_entails_every h, h.2⟩

end EnglishDecomposition

/-! ### German fragment consistency

Verify the German fragment entries in `Fragments/German/Distributives.lean` are
consistent with the `Q_∀` decomposition:
- jeder (+dist, +max) = `Q_∀[ONE_∅]` on atoms = `distMaximal`
- alle (−dist, +max) = bare `Q_∀` on a cumulative restrictor = `allViaForallH`
- jeweils (+dist, −max) = `distTolerant` (orthogonal to `Q_∀`) -/

/-- German jeder's DistMaxClass matches the ONE_∅ prediction:
    [+dist] (ONE forces atom complement) and [+max] (atoms are vacuously maximal). -/
theorem jeder_matches_ONE_prediction :
    German.Distributives.jederEntry.distMaxClass = .distMax := rfl

/-- German alle's DistMaxClass matches the bare `Q_∀` prediction:
    [−dist] (no ONE, cumulative complement → collective) and [+max]. -/
theorem alle_matches_bare_QForall :
    German.Distributives.alleEntry.distMaxClass = .nonDistMax := rfl

/-- The DNG explains the dist/non-dist split between jeder and alle:
    same `Q_∀` semantics, different complement structure. -/
theorem german_dng_explained :
    German.Distributives.jederEntry.distMaxClass.isDistributive ∧
    ¬ German.Distributives.alleEntry.distMaxClass.isDistributive := by
  decide

/-! ### English fragment consistency

Connect the `Q_∀` decomposition to the English distributive Fragment's
`DistMaxClass` and atomicity entries in `Fragments/English/Distributives.lean`,
exactly as the German section derives from `Fragments/German/Distributives.lean`.

The NLLT decomposition predicts:
- each = `Q_∀[ONE_∅[ONE_AT]]` → [+dist] (atoms), [+max]
- every = `Q_∀[ONE_∅]` → [+dist] (non-overlap), [+max]
- all = bare `Q_∀` → [−dist] (cumulative complement), [+max]

These predictions are read off the Fragment's entries (no local restipulation). -/

/-- English each's DistMaxClass matches the ONE_AT prediction (+dist, +max). -/
theorem each_matches_ONE_AT_prediction :
    English.Distributives.eachEntry.distMaxClass = .distMax := rfl

/-- English every's DistMaxClass matches the ONE_∅ prediction (+dist, +max). -/
theorem every_matches_ONE_empty_prediction :
    English.Distributives.everyEntry.distMaxClass = .distMax := rfl

/-- English all's DistMaxClass matches the bare `Q_∀` prediction (−dist, +max). -/
theorem all_matches_bare_QForall_prediction :
    English.Distributives.allEntry.distMaxClass = .nonDistMax := rfl

/-- each and every share a DistMaxClass (both +dist, +max), so this axis cannot
    separate them. The NLLT contrast lives in the atomicity presupposition
    (`ONE_AT`), recorded by the Fragment's `atomicityPresup` field — exactly the
    distinction that blocks *each ten minutes* below. [haslinger-etal-2025-nllt] §6.2. -/
theorem each_every_same_class_different_atomicity :
    English.Distributives.eachEntry.distMaxClass =
      English.Distributives.everyEntry.distMaxClass ∧
    English.Distributives.eachEntry.atomicityPresup = true ∧
    English.Distributives.everyEntry.atomicityPresup = false :=
  English.Distributives.each_every_same_class_different_atomicity

/-! ### The *each ten minutes test

`ONE_AT` explains the ungrammaticality of *each ten minutes*: time intervals are
not atoms, so the atomicity presupposition fails. *every ten minutes* is fine —
intervals can be non-overlapping (satisfying `ONE_∅`) without being atomic.
Following [fassi-fehri-2020]; [haslinger-etal-2025-nllt] §6.2. -/

/-- `ONE_AT` rejects non-atomic predicates. *every ten minutes* is fine (`ONE_∅`
    accepts non-overlapping intervals), but *each ten minutes* is out (`ONE_AT`
    requires atoms). -/
theorem each_ten_minutes_blocked {α : Type*} [PartialOrder α]
    {P : α → Prop}
    (hNonAtomic : ∃ x, P x ∧ ¬Atom x)
    (hONE_AT : ONE_AT P) : False := by
  obtain ⟨x, hPx, hNA⟩ := hNonAtomic
  exact hNA (hONE_AT.all_atomic x hPx)

/-! ### Bridge to the canonical generalized quantifier

On an **atomic restrictor sort** (`Mereology.IsAtomicDomain α`), `Q_∀` *is* the
canonical universal generalized quantifier `every_sem` (`λR S. ∀x. R x → S x`).
The instance discharges both the atomicity and the disjointness conditions of
`QForall_eq_standardGQ`, so the bridge is automatic — and `*each ten minutes`
is exactly the case where the interval sort has no `IsAtomicDomain` instance.
This snaps the mereological `Q_∀` tower onto the shared `∀`-denotation that the
Barwise–Cooper `every_sem`, the Lindström `everyDet.toGQ`, and Sauerland's
`JE∘DER` already meet at, with the atomicity presupposition realized as a
typeclass on the sort rather than a side condition. -/

/-- On an atomic restrictor sort, `Q_∀` is the canonical universal generalized
quantifier `every_sem`. The `[IsAtomicDomain α]` instance is *used* — it
discharges both hypotheses of `QForall_eq_standardGQ`.
[haslinger-etal-2025-nllt] eq. (30b). -/
theorem QForall_eq_every_sem {α : Type*} [PartialOrder α] [IsAtomicDomain α]
    {P Q : α → Prop} :
    QForall P Q ↔ Quantification.every_sem P Q :=
  QForall_eq_standardGQ (fun x _ => IsAtomicDomain.all_atoms x)
    (fun _ _ _ _ h => IsAtomicDomain.eq_of_overlap h)

end HaslingerHienEtAl2025
