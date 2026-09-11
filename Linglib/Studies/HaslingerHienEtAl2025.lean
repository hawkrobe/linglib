import Linglib.Semantics.Quantification.UnifiedUniversal
import Linglib.Semantics.Quantification.ONEModifiers
import Linglib.Semantics.Quantification.Basic
import Linglib.Fragments.German.Distributives
import Linglib.Fragments.English.Determiners

/-!
# Haslinger, Hien, Rosina, Schmitt and Wurm (2025): A unified semantics for universal quantifiers

This file formalizes [haslinger-etal-2025-nllt]'s account of the Distributivity–Number
Generalization: across languages a universal quantifier with a singular count complement is
distributive and one with a plural complement is not, a strengthening of [gil-1995]'s
implicational universal. One morpheme, `QForall`, applies its scope to every maximal
non-overlapping element of its restrictor, so the reading falls out of the restrictor's
algebra: a singular restrictor of atoms gives the distributive reading and a sum-closed plural
restrictor with one maximal element the non-distributive one (`dng_sg_concrete`,
`dng_pl_concrete`). Two-form languages such as English and German realize a head ONE below the
quantifier that presupposes non-overlap (*every*) or atomicity (*each*), following
[fassi-fehri-2020], so that *each* entails *every* entails *all* (`presup_chain`) and *each*
rejects the non-atomic intervals of *ten minutes* while *every* accepts them
(`each_ten_minutes_blocked`); one-form languages use the bare quantifier, whose reading the
complement's number fixes. On an atomic restrictor sort the quantifier is the canonical
universal generalized quantifier (`QForall_eq_every_sem`).

## Implementation notes

The quantifier, the ONE heads and the generalization's two halves live in
`Semantics/Quantification/UnifiedUniversal.lean` and `ONEModifiers.lean`; the study instantiates
them on finite models and records the paper's survey. The survey rows (their Tables 1 and 2)
are study-local data, with the English and German forms read off the determiner fragments; the
distributive readings that plural forms additionally allow come from a VP-level distributivity
operator ([link-1987]), not from the quantifier, and stay outside the models. The S&P paper of
the overlapping author set, `Studies/HaslingerEtAl2025.lean`, separates distributivity from
maximality; this one separates it from number.

## References

* [haslinger-etal-2025-nllt]
* [gil-1995]
* [fassi-fehri-2020]
* [link-1987]
-/

namespace HaslingerHienEtAl2025

open Quantification.UnifiedUniversal Quantification.ONEModifiers Mereology

/-! ### The survey (their Tables 1 and 2) -/

/-- Whether a language has one universal-quantifier lexeme whose reading the complement's
number fixes, or two lexemes, one distributive and one not. -/
inductive SystemType where
  | oneForm
  | twoForm
  deriving DecidableEq, Repr

/-- A language's universal-quantifier inventory as the survey compiles it. -/
structure UQProfile where
  language : String
  family : String
  systemType : SystemType
  /-- The distributive form; in a one-form language, the sole form. -/
  distForm : String
  /-- The non-distributive form; empty in a one-form language. -/
  nonDistForm : String := ""
  deriving Repr, DecidableEq

/-- The fifteen languages of their Tables 1 and 2; the English and German forms are the
fragments'. -/
def typologicalSample : List UQProfile :=
  [ ⟨"Dagara", "Mabia", .oneForm, "'hà", ""⟩,
    ⟨"Moore", "Mabia", .oneForm, "fãa", ""⟩,
    ⟨"Gourmantchema", "Mabia", .oneForm, "kuli", ""⟩,
    ⟨"Wolof", "Atlantic", .oneForm, "-epp", ""⟩,
    ⟨"Syrian Arabic", "Semitic", .oneForm, "kul", ""⟩,
    ⟨"English", "Indo-European (Germanic)", .twoForm, English.Determiners.every.form,
      English.Determiners.all.form⟩,
    ⟨"German", "Indo-European (Germanic)", .twoForm, German.Distributives.jederEntry.form,
      German.Distributives.alleEntry.form⟩,
    ⟨"Hindi", "Indo-European (Indic)", .twoForm, "praty-ek", "saar-"⟩,
    ⟨"Russian", "Indo-European (Slavic)", .twoForm, "každyj", "vse"⟩,
    ⟨"Imbabura Quichua", "Quechuan", .twoForm, "kada", "tukuy(-lla)"⟩,
    ⟨"Turkish", "Turkic", .twoForm, "her", "bütün, hepsi"⟩,
    ⟨"Basque", "isolate", .twoForm, "bakoitz", "guzti, den, oro"⟩,
    ⟨"Telugu", "Dravidian", .twoForm, "prăti:", "ăndărŭ, ăn:ĭ, ănta:"⟩,
    ⟨"Hausa", "Afro-Asiatic (West Chadic)", .twoForm, "koowànè", "duk"⟩,
    ⟨"Logoori", "Niger-Congo (Bantu)", .twoForm, "vuri", "-oosi"⟩ ]

/-! ### Finite models of the generalization -/

section FiniteModels

/-- Three students, a flat domain in which every element is an atom. -/
inductive Student where
  | alice
  | bob
  | carol
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- The flat order: `x ≤ y` iff `x = y`. -/
instance : PartialOrder Student where
  le x y := x = y
  le_refl _ := rfl
  le_trans _ _ _ h₁ h₂ := h₁.trans h₂
  le_antisymm _ _ h _ := h

instance : NoBotOrder Student where
  exists_not_ge
    | .alice => ⟨.bob, Student.noConfusion⟩
    | .bob => ⟨.alice, Student.noConfusion⟩
    | .carol => ⟨.alice, Student.noConfusion⟩

instance : IsAtomicDomain Student := isAtomicDomain_of_le_iff_eq (λ _ _ => Iff.rfl)

/-- Alice and Bob passed, Carol did not. -/
def passed : Student → Prop
  | .alice => True
  | .bob => True
  | .carol => False

/-- The singular half of the generalization: on the atomic domain the quantifier distributes
to each student, and *every student passed* is false because of Carol. -/
theorem dng_sg_concrete :
    (QForall (λ _ : Student => True) passed ↔ ∀ x : Student, passed x) ∧
      ¬ QForall (λ _ : Student => True) passed := by
  have h := dng_atoms (P := λ _ : Student => True) (Q := passed)
    (λ x _ => IsAtomicDomain.all_atoms x (not_isBot x))
    (λ _ _ _ _ hov => IsAtomicDomain.eq_of_overlap hov)
  simp only [forall_const] at h
  exact ⟨h, λ hQ => (h.mp hQ) .carol⟩

/-- The plural domain: nonempty groups of students, ordered by inclusion and closed under
sum. -/
def students (s : Finset Student) : Prop := s.Nonempty

/-- The plural half of the generalization: on the sum-closed restrictor the quantifier applies
its scope to the one maximal element, the sum of all the students. -/
theorem dng_pl_concrete (Q : Finset Student → Prop) :
    QForall students Q ↔ Q Finset.univ :=
  dng_cum' (λ _ hx h => hx.ne_empty (Finset.subset_empty.mp (h ∅)))
    (λ _ hx _ _ => hx.mono Finset.subset_union_left)
    ⟨Finset.univ_nonempty, λ y _ _ => Finset.subset_univ y⟩

end FiniteModels

/-! ### The English decomposition (their (79)) -/

section EnglishDecomposition

variable {α : Type*} [PartialOrder α] {P Q : α → Prop}

/-- *each* entails *every* entails *all*: the atomicity presupposition entails the non-overlap
presupposition, and both leave the bare quantifier. -/
theorem presup_chain : eachPresup P Q → everyPresup P Q ∧ QForall P Q :=
  λ h => ⟨each_entails_every h, h.2⟩

/-- Under the non-overlap presupposition the quantifier distributes to the restrictor's
elements. -/
theorem every_is_distributive (hONE : ONE_empty P) : QForall P Q ↔ ∀ x, P x → Q x :=
  every_distributes hONE

end EnglishDecomposition

/-- The atomicity presupposition of *each* fails on a restrictor with a non-atomic element,
such as the intervals of *ten minutes*; *every* accepts non-overlapping intervals. -/
theorem each_ten_minutes_blocked {α : Type*} [PartialOrder α] {P : α → Prop}
    (hNonAtomic : ∃ x, P x ∧ ¬ Atom x) (hONE_AT : ONE_AT P) : False :=
  let ⟨x, hPx, hNA⟩ := hNonAtomic
  hNA (hONE_AT.all_atomic x hPx)

/-- On an atomic restrictor sort, the quantifier over a restrictor excluding the null
individual is the canonical universal generalized quantifier. -/
theorem QForall_eq_every_sem {α : Type*} [PartialOrder α] [IsAtomicDomain α]
    {P Q : α → Prop} (hP0 : ∀ x, P x → ¬ IsBot x) :
    QForall P Q ↔ Quantification.every_sem P Q :=
  QForall_eq_standardGQ (λ x hx => IsAtomicDomain.all_atoms x (hP0 x hx))
    (λ _ _ _ _ h => IsAtomicDomain.eq_of_overlap h)

end HaslingerHienEtAl2025
