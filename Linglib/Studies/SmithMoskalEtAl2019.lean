import Linglib.Morphology.Paradigm.Degree
import Linglib.Morphology.Exponence.Containment.Contiguity
import Linglib.Data.Forms.SmithMoskalEtAl2019

/-!
# Smith, Moskal, Xu, Kang and Bobaljik (2019): Case and Number Suppletion in Pronouns

This file formalizes [smith-moskal-xu-kang-bobaljik-2019]'s extension of [bobaljik-2012]'s
containment account of suppletion from adjectival degree to pronominal case, over the case
hierarchy of [caha-2009], and to pronominal number, over a hierarchy in which the dual contains
the plural (Greenberg's Universal 34, the paper's (26)). Each hierarchy is a three-grade
containment structure, so Elsewhere insertion over it generates exactly the contiguous
patterns and excludes *ABA (`generable_iff_contiguous`, `aba_not_generable`); the attested
AAA, ABB and ABC patterns are read off the pronoun paradigms of `Data/Forms/SmithMoskalEtAl2019`
(`paradigm`, `lezgian_aaa`, `icelandic_abb`, `russian_abb`, `awtuw_abb`), and the rules (15) for
the Icelandic first person generate its ABB (`icelandic_abb_generated`).

The domains diverge on AAB. Under the structural adjacency [bobaljik-2012] assumes for degree,
terminal rules with adjacent contexts cannot distinguish the second and third grades, so AAB is
unattested for degree (`realize_one_eq_two_of_terminal_adjacent`,
`aab_not_generable_of_terminal_adjacent`); section 3.6 finds genuine AAB in pronominal case,
the absolutive and ergative sharing a base yet remaining distinct where a syncretic
{A=A}B pattern would not (`wardaman_aab`, `khinalugh_aab`, `genuine_aab`, `archi_syncretic`),
and section 4.2 finds it in pronominal number (`yagua_aab`, `wambaya_aab`, `dehu_aab`). The
paper's section 3.7 replaces adjacency by the accessibility domain of Moskal, the first
category-defining node above the root and one node above that: the domain bounds which heads
may condition root suppletion (`DomainLocal`), the plateau reappears for any vocabulary whose
conditioning heads lie in a domain (`realize_const_of_terminal_domainLocal`), terminal
adjacency is its smallest nontrivial instance (`domainLocal_of_terminal_adjacent`), and the
rules (20) for Wardaman, local at the trivial domain of a pronoun, generate the attested AAB
while containment and the Elsewhere condition still exclude ABA (`wardaman_aab_generated`,
`wardaman_realize_contiguous`).

## Implementation notes

* A paradigm is three rows of the form table in the order of the hierarchy, its cells the base
  letters the paper's pattern labels assign (`Base`); the case hierarchy is read as unmarked,
  dependent and oblique, absolutive, ergative and dative in the ergative languages and
  nominative, accusative and dative otherwise, and the number hierarchy as singular, plural
  and dual.
* The paper's counts stay in prose: for case, Table 9 records ABB in fifty-seven languages,
  ABC in two, AAB in ten and a single doubtful ABA, the Archi second person plural; for
  number, Table 32 records forty-eight ABB, nineteen ABC, three AAB and one doubtful ABA in
  Yagua.
* The rules (20) are stated for featural containment and are transposed to the three-cell
  structural hierarchy of section 3.1; the exponent of the number-and-case portmanteau (20a)
  and the affixes (20c) to (20e) fall outside the three cells.

## References

* [smith-moskal-xu-kang-bobaljik-2019]
* [bobaljik-2012]
* [caha-2009]
* [moskal-2015a-dissertation]
* [merlan-1994]

## TODO

Section 4.3's number containment hypothesis, [±augmented] containing [±singular] with the
marked value of a feature visible to suppletion, is not formalized; the number hierarchy is the
containment of section 4.1.
-/

namespace SmithMoskalEtAl2019

open Morphology Morphology.Degree Morphology.Containment

/-! ### Paradigms from the form table -/

/-- The base class the paper's pattern label assigns a form. -/
def baseOf (f : Data.Forms.Form) : ℕ :=
  match f.column? "Base" with
  | some "B" => 1
  | some "C" => 2
  | _ => 0

/-- Three cells in the order of the hierarchy as a paradigm of base classes. -/
def paradigm (a b c : Data.Forms.Form) : Paradigm 3 ℕ := ![baseOf a, baseOf b, baseOf c]

/-- Wardaman third singular, absolutive, ergative and dative (Table 25, [merlan-1994]). -/
def wardaman3sg : Paradigm 3 ℕ :=
  paradigm Forms.wardaman_3sg_abs Forms.wardaman_3sg_erg Forms.wardaman_3sg_dat

/-- Khinalugh second singular (Table 24). -/
def khinalugh2sg : Paradigm 3 ℕ :=
  paradigm Forms.khinalugh_2sg_abs Forms.khinalugh_2sg_erg Forms.khinalugh_2sg_dat

/-- Icelandic first singular, nominative, accusative and dative (Table 6). -/
def icelandic1sg : Paradigm 3 ℕ :=
  paradigm Forms.icelandic_1sg_nom Forms.icelandic_1sg_acc Forms.icelandic_1sg_dat

/-- Russian first singular (Table 10). -/
def russian1sg : Paradigm 3 ℕ :=
  paradigm Forms.russian_1sg_nom Forms.russian_1sg_acc Forms.russian_1sg_dat

/-- Lezgian first singular (Table 11). -/
def lezgian1sg : Paradigm 3 ℕ :=
  paradigm Forms.lezgian_1sg_abs Forms.lezgian_1sg_erg Forms.lezgian_1sg_dat

/-- Awtuw first person, singular, plural and dual (Table 33). -/
def awtuw1 : Paradigm 3 ℕ := paradigm Forms.awtuw_1_sg Forms.awtuw_1_pl Forms.awtuw_1_dl

/-- Yagua second person (Table 46). -/
def yagua2 : Paradigm 3 ℕ := paradigm Forms.yagua_2_sg Forms.yagua_2_pl Forms.yagua_2_dl

/-- Wambaya first inclusive (Table 46). -/
def wambaya1incl : Paradigm 3 ℕ :=
  paradigm Forms.wambaya_1incl_sg Forms.wambaya_1incl_pl Forms.wambaya_1incl_dl

/-- Dehu third masculine (Table 46). -/
def dehu3m : Paradigm 3 ℕ := paradigm Forms.dehu_3m_sg Forms.dehu_3m_pl Forms.dehu_3m_dl

/-! ### Containment excludes ABA, sections 3.3 and 4.2 -/

/-- Over a three-grade containment hierarchy a pattern is generable by Elsewhere insertion
exactly when it is contiguous, for case and for number alike. -/
theorem generable_iff_contiguous (p : Paradigm 3 ℕ) : ElsewhereGenerable p ↔ IsContiguous p :=
  (isContiguous_iff_generable p).symm

/-- No ABA pattern is generable: the reading that excludes the apparent Archi second plural for
case and the doubtful Yagua third person for number. -/
theorem aba_not_generable : ¬ ElsewhereGenerable ![0, 1, 0] :=
  mt (generable_iff_contiguous _).mp (by decide)

/-- The attested patterns of the case hierarchy: Lezgian AAA, Icelandic and Russian ABB. -/
theorem lezgian_aaa : degreeShape lezgian1sg = aaa := by decide

theorem icelandic_abb : degreeShape icelandic1sg = abb := by decide

theorem russian_abb : degreeShape russian1sg = abb := by decide

/-- The attested ABB of the number hierarchy: Awtuw's plural and dual share a base. -/
theorem awtuw_abb : degreeShape awtuw1 = abb := by decide

/-- The rules (15) for the Icelandic first singular: an accusative-conditioned *m-* and an
elsewhere *ég*; by containment the *m-* base spreads to the dative. -/
def icelandicVocab : List (SpanRule 3 String) := [⟨"ég", 0, none⟩, ⟨"m", 0, some 1⟩]

theorem icelandic_abb_generated : degreeShape (realize icelandicVocab) = abb := by decide

/-! ### Structural adjacency and the absence of AAB for degree, section 2 -/

/-- Under [bobaljik-2012]'s structural adjacency, terminal rules with adjacent contexts cannot
distinguish the second grade from the third. -/
theorem realize_one_eq_two_of_terminal_adjacent {v : List (SpanRule 3 ℕ)} (hT : Terminal v)
    (hA : Adjacent v) : realize v 1 = realize v 2 :=
  realize_const_of_terminal_adjacent hT hA

/-- So no AAB pattern is generable under structural adjacency. -/
theorem aab_not_generable_of_terminal_adjacent {v : List (SpanRule 3 ℕ)} (hT : Terminal v)
    (hA : Adjacent v) {a b : ℕ} (hab : a ≠ b) : realize v ≠ ![some a, some a, some b] := by
  intro h
  have h12 := realize_one_eq_two_of_terminal_adjacent hT hA
  rw [h] at h12
  exact hab (by simpa using h12)

/-! ### AAB attested for case, section 3.6, and for number, section 4.2 -/

/-- Wardaman and Khinalugh are AAB: contiguous, the third cell alone suppletive. -/
theorem wardaman_aab : degreeShape wardaman3sg = aab := by decide

theorem khinalugh_aab : degreeShape khinalugh2sg = aab := by decide

/-- Genuine AAB against syncretism: the Wardaman and Khinalugh absolutive and ergative are
distinct forms on one base, where the Archi second singular's are identical, the {A=A}B of
Table 20 the paper sets aside as a two-way contrast. -/
theorem genuine_aab :
    Forms.wardaman_3sg_abs.form ≠ Forms.wardaman_3sg_erg.form ∧
      Forms.khinalugh_2sg_abs.form ≠ Forms.khinalugh_2sg_erg.form := by
  decide

theorem archi_syncretic : Forms.archi_2sg_abs.form = Forms.archi_2sg_erg.form := by decide

/-- The number witnesses of Table 46 are AAB. -/
theorem yagua_aab : degreeShape yagua2 = aab := by decide

theorem wambaya_aab : degreeShape wambaya1incl = aab := by decide

theorem dehu_aab : degreeShape dehu3m = aab := by decide

/-- The attested AAB patterns are contiguous, so containment admits them, yet no terminal
vocabulary under structural adjacency generates them: the adjacency condition is what the
pronominal data refute. -/
theorem aab_contiguous_not_adjacent_generable :
    IsContiguous wardaman3sg ∧ IsContiguous yagua2 ∧
      ∀ v : List (SpanRule 3 ℕ), Terminal v → Adjacent v →
        realize v ≠ ![some 0, some 0, some 1] :=
  ⟨by decide, by decide, λ _ hT hA => aab_not_generable_of_terminal_adjacent hT hA (by decide)⟩

/-! ### Accessibility domains, section 3.7

Adjacency is too strict: Tamil supplets for the dative across the plural morpheme, so
locality may have to appeal to domains rather than adjacency. The accessibility domain of
[moskal-2015a-dissertation], the heads merged when the root's cycle is fixed, bounds which
heads may condition root suppletion; a lexical noun or adjective has a category node that
keeps case and the superlative outside the domain, a pronoun has none and every case head is
visible. -/

/-- Every conditioning head lies within the accessibility domain `[0, d]`: a bound on the
contexts of rules, not on the spans they expone. -/
def DomainLocal {n : ℕ} {F : Type*} (d : Fin n) (v : List (SpanRule n F)) : Prop :=
  ∀ it ∈ v, ∀ c : Fin n, it.context = some c → c ≤ d

instance {n : ℕ} {F : Type*} (d : Fin n) (v : List (SpanRule n F)) :
    Decidable (DomainLocal d v) := by
  unfold DomainLocal; infer_instance

/-- Terminal rules local to a domain have thresholds inside it. -/
theorem threshold_le_of_terminal_domainLocal {n : ℕ} {F : Type*} {d : Fin n}
    {v : List (SpanRule n F)} (hT : Terminal v) (hD : DomainLocal d v) {it : SpanRule n F}
    (hit : it ∈ v) : it.threshold ≤ d := by
  have h0 := hT it hit
  unfold SpanRule.threshold
  cases hc : it.context with
  | none =>
    simp only [Option.getD_none, max_self]
    rw [Fin.le_def]; omega
  | some c =>
    simp only [Option.getD_some]
    exact max_le (by rw [Fin.le_def]; omega) (hD it hit c hc)

/-- The plateau relative to a domain: with terminal rules whose contexts lie in the domain,
realization is constant above it. At the comparative this is the no-AAB plateau of degree
without an adjacency condition. -/
theorem realize_const_of_terminal_domainLocal {n : ℕ} {F : Type*} {d : Fin n}
    {v : List (SpanRule n F)} (hT : Terminal v) (hD : DomainLocal d v) {g g' : Fin n}
    (hg : d ≤ g) (hg' : d ≤ g') : realize v g = realize v g' :=
  realize_const_of_cap (λ _ hit => threshold_le_of_terminal_domainLocal hT hD hit) hg hg'

/-- Terminal adjacency is locality at any domain containing the first head. -/
theorem domainLocal_of_terminal_adjacent {n : ℕ} {F : Type*} {d : Fin n} (hd : 1 ≤ (d : ℕ))
    {v : List (SpanRule n F)} (hT : Terminal v) (hA : Adjacent v) : DomainLocal d v := by
  intro it hit c hc
  have h1 := hA it hit c hc
  have h0 := hT it hit
  rw [Fin.le_def]; omega

/-- The rules (20b) and (20f) for the Wardaman third person: a dative-conditioned *gunga* and
an elsewhere *narnaj*. -/
def wardamanVocab : List (SpanRule 3 String) := [⟨"narnaj", 0, none⟩, ⟨"gunga", 0, some 2⟩]

/-- The Wardaman vocabulary is antihomophonous and local at the trivial domain of a pronoun,
and generates the attested AAB. -/
theorem wardaman_aab_generated :
    Antihomophonous wardamanVocab ∧ DomainLocal 2 wardamanVocab ∧
      degreeShape (realize wardamanVocab) = aab := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- The same vocabulary satisfies neither structural adjacency nor [bobaljik-2012]'s
markedness condition (202): the attested pronominal AAB refutes both as conditions on
suppletion in general. -/
theorem wardaman_not_adjacent_not_grounded :
    ¬ Adjacent wardamanVocab ∧ ¬ Grounded wardamanVocab := by
  refine ⟨?_, ?_⟩ <;> decide

/-- ABA stays excluded at the trivial domain: containment with the Elsewhere condition
suffices. -/
theorem wardaman_realize_contiguous : IsContiguous (realize wardamanVocab) :=
  isContiguous_realize (by decide)

end SmithMoskalEtAl2019
