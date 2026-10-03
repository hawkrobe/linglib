module

public import Linglib.Morphology.Exponence.Containment.Contiguity
public import Linglib.Morphology.DistributedMorphology.Merger
public import Linglib.Fragments.English.Adjectives
public import Linglib.Fragments.Latin.Adjectives
public import Linglib.Fragments.Slavic.Russian.Adjectives

/-!
# Universals in comparative morphology

[bobaljik-2012] surveys comparative and superlative suppletion in some 300
languages and finds three root patterns — AAA, ABB, ABC — with *ABA and
*AAB unattested: the Comparative-Superlative Generalization (1)–(2), beside
the Synthetic Superlative Generalization (3), the Root Suppletion
Generalization (4), and Lesslessness (5). All but the last follow from the
Containment Hypothesis (6) — the superlative contains the comparative —
under Late Insertion, Elsewhere ordering, and locality (8). A comparative
root allomorph is chosen in the superlative too, so ABA needs an accidental
homophony that Antihomophony (44) excludes; AAB needs a
superlative-conditioned allomorph with no comparative counterpart, which
adjacency (190) or the markedness condition (202) excludes; and a root sees
CMPR only when Merger has made the comparative synthetic (90), which is the
RSG, with the SSG as Merger's downward closure. The same locality condition
limits CSG1 to periphrastic superlatives that embed the comparative (§3.3.3),
so Russian *plox-oj – xuž-e – samyj plox-oj*, whose superlative embeds the
positive, is ABA without any homophony.

## Main definitions

* `czechBad`, `englishGood`, `englishBad`, `welshGood`, `latinBonus`: the
  book's vocabularies (39), (203), (194), (198), (204) as `SpanRule`s.
* `aabContextual`, `welshAAB`, `fakeAba`: the vocabularies behind the
  unattested shapes — (190), (201), and the homophony loophole of (44).
* `greekBad`, `russianBad`: the Modern Greek vocabulary (93) and its Russian
  counterpart.
* `positiveEmbedding`: the word extents of a superlative embedding the positive.
* `latinBonusNS`: the Latin entries in nanosyntax form.
* `Periphrastic`: a two-word grade form.

## Main results

* `english_patterns`, `latin_patterns`, `latin_all_three`: the Fragments
  show the attested patterns of (191) and no others.
* `english_ssg`, `english_rsg`: (3) and (4) on the English Fragment.
* `czech_bad_abb`, `latin_realize_abc`, `welsh_good_abc`: the engine derives
  the book's paradigms.
* `aabContextual_not_adjacent`, `welshAAB_not_grounded`,
  `fakeAba_not_antihomophonous`: each unattested shape violates exactly one
  condition.
* `latin_sprl_needs_portmanteau`: ABC needs a portmanteau ((199)).
* `greek_comparative`: *pjo kak-ós*, not *pjo cheir-ós* ((94)).
* `csg1_iff_one_le`: with a suppletive comparative, CSG1 holds of the
  superlative exactly when its adjective word contains CMPR (§3.3.3).
* `greek_superlative`, `russian_bad_eq_ploxoj`: the Greek superlative inherits
  the suppletive root ((106a)) and the Russian one does not ((106d)), whose
  pattern the Fragment records.
* `periphrastic_of_aba`: on the Fragments every ABA has a periphrastic
  superlative.
* `latin_ns_eq_dm`: nanosyntax and DM realize Latin alike.

## Implementation notes

Lesslessness (5) — no language has a synthetic comparative of inferiority
((278)–(279)) — is the book's most robust generalization but is not
derived here: its account, a polarity-reversing head under the Complexity
Condition, is a sketch in the book as well. The generalizations concern
relative superlatives only; absolute superlatives lack the comparative
component and its structure.

The book gives no Russian vocabulary. `russianBad` is built in the format of
the Greek (93), with the comparative root *xud-* that §6.4.4 identifies in
*xuž-e*.

## References

* [bobaljik-2012]
* [caha-2009]
-/

@[expose] public section

namespace Bobaljik2012

open Morphology Morphology.Containment DistributedMorphology
open English.Adjectives

/-! ### The patterns on the Fragments (ch. 4) -/

/-- The English Fragment shows only AAA and ABB. -/
theorem english_patterns :
    ∀ e ∈ allEntries,
      Setoid.ker e.comparison.suppletion = Setoid.ker Paradigm.aaa ∨
        Setoid.ker e.comparison.suppletion = Setoid.ker Paradigm.abb := by
  decide

/-- The Latin Fragment shows only the attested patterns of (191). -/
theorem latin_patterns :
    ∀ e ∈ Latin.Adjectives.allEntries,
      Setoid.ker e.comparison.suppletion = Setoid.ker Paradigm.aaa ∨
        Setoid.ker e.comparison.suppletion = Setoid.ker Paradigm.abb ∨
        Setoid.ker e.comparison.suppletion = Setoid.ker Paradigm.abc := by
  decide

/-- Latin shows all three patterns, in *longus*, *parvus* and *bonus*. -/
theorem latin_all_three :
    (∃ e ∈ Latin.Adjectives.allEntries,
        Setoid.ker e.comparison.suppletion = Setoid.ker Paradigm.aaa) ∧
      (∃ e ∈ Latin.Adjectives.allEntries,
        Setoid.ker e.comparison.suppletion = Setoid.ker Paradigm.abb) ∧
      ∃ e ∈ Latin.Adjectives.allEntries,
        Setoid.ker e.comparison.suppletion = Setoid.ker Paradigm.abc := by
  decide

/-- In a contiguous pattern a suppletive comparative, whose root differs from the positive's,
forces a suppletive superlative. This is CSG1 (1). -/
theorem csg1 {F : Type*} {p : Paradigm 3 F} (hc : IsContiguous p) (h : p 1 ≠ p 0) :
    p 2 ≠ p 0 :=
  fun h2 ↦ h (hc (i := 0) (j := 1) (k := 2) (by decide) (by decide) h2.symm).symm

/-- *Best* does not return to the root of *good*, as CSG1 requires. -/
theorem good_csg1 : good.comparison.suppletion 2 ≠ good.comparison.suppletion 0 :=
  csg1 (by decide) (by decide)

/-- A form of two words, such as periphrastic *more X*. -/
def Periphrastic (f : String) : Prop := ' ' ∈ f.toList

instance (f : String) : Decidable (Periphrastic f) := inferInstanceAs (Decidable (_ ∈ _))

/-- On the English Fragment a synthetic superlative comes with a synthetic comparative. This is
the SSG (3), which `Synthesis.syntheticAt_of_le` derives structurally. -/
theorem english_ssg :
    ∀ e ∈ allEntries, ∀ s ∈ e.comparison.formSuper,
      ¬ Periphrastic s → ∃ c ∈ e.comparison.formComp, ¬ Periphrastic c := by
  decide

/-- On the English Fragment a suppletive comparative is synthetic (*better*, *worse*, never
*more bett*). This is the RSG (4). -/
theorem english_rsg :
    ∀ e ∈ allEntries, e.comparison.suppletion 1 ≠ e.comparison.suppletion 0 →
      ∃ c ∈ e.comparison.formComp, ¬ Periphrastic c := by
  decide

/-! ### The book's vocabularies (ch. 2, ch. 5)

Each vocabulary is run through the Elsewhere engine of
`Morphology/Exponence/Containment/Contiguity.lean`; the syncretism of the
realized cells is the root pattern. -/

/-- Czech BAD (39), with *hor-* under CMPR and *špatn-* elsewhere. -/
def czechBad : List (SpanRule 3 String) := [⟨"špatn", 0, none⟩, ⟨"hor", 0, some 1⟩]

/-- The comparative allomorph is chosen in the superlative, *špatn-ý, hor-ší, nej-hor-ší*, since
the superlative contains its context. -/
theorem czech_bad_realize : realize czechBad = ![some "špatn", some "hor", some "hor"] := by
  decide

theorem czech_bad_abb : Setoid.ker (realize czechBad) = Setoid.ker Paradigm.abb := by decide

/-- English GOOD (203), with *bett-* under CMPR and *good* elsewhere. -/
def englishGood : List (SpanRule 3 String) := [⟨"good", 0, none⟩, ⟨"bett", 0, some 1⟩]

theorem english_good_abb : Setoid.ker (realize englishGood) = Setoid.ker Paradigm.abb := by decide

/-- English BAD (194), with the √ROOT+CMPR portmanteau *worse* and *bad* elsewhere. -/
def englishBad : List (SpanRule 3 String) := [⟨"bad", 0, none⟩, ⟨"worse", 1, none⟩]

theorem english_bad_abb : Setoid.ker (realize englishBad) = Setoid.ker Paradigm.abb := by decide

/-- Welsh GOOD (198), with the √ROOT+CMPR portmanteaus *gor-* under SPRL and *gwell*, and *da*
elsewhere. -/
def welshGood : List (SpanRule 3 String) :=
  [⟨"da", 0, none⟩, ⟨"gwell", 1, none⟩, ⟨"gor", 1, some 2⟩]

/-- Welsh *da, gwell, gor-au* is ABC, since the superlative exponent is a portmanteau. -/
theorem welsh_good_abc : Setoid.ker (realize welshGood) = Setoid.ker Paradigm.abc := by decide

/-- Latin GOOD (204), with the √ROOT+CMPR portmanteau *opt-* under SPRL, the root allomorph
*mel-* under CMPR, and *bon* elsewhere. Since *opt-* expones the CMPR cell, *-ior* has nothing to
realize, which gives *opt-imus* and not *\*opt-ior-imus*. -/
def latinBonus : List (SpanRule 3 String) :=
  [⟨"bon", 0, none⟩, ⟨"mel", 0, some 1⟩, ⟨"opt", 1, some 2⟩]

theorem latin_bonus_realize : realize latinBonus = ![some "bon", some "mel", some "opt"] := by
  decide

theorem latin_realize_abc : Setoid.ker (realize latinBonus) = Setoid.ker Paradigm.abc := by decide

/-- Latin satisfies every condition the CSG2 derivation uses. -/
theorem latin_wellformed :
    Adjacent latinBonus ∧ Grounded latinBonus ∧ Antihomophonous latinBonus := by decide

/-- Latin is not terminal, and must not be, since terminal adjacent rules plateau at the
comparative (`realize_const_of_terminal_adjacent`), which would exclude ABC. -/
theorem latin_not_terminal : ¬ Terminal latinBonus := by decide

/-- The superlative winner is the portmanteau *opt-*. -/
theorem latin_superlative_portmanteau : winner latinBonus 2 = some ⟨"opt", 1, some 2⟩ := by
  decide

/-- ABC needs a portmanteau ((199), §5.3.1). Under adjacency, distinct comparative and
superlative cells force a winner exponing more than the root. -/
theorem latin_sprl_needs_portmanteau :
    ∃ it ∈ latinBonus, winner latinBonus 2 = some it ∧ 0 < (it.spans : ℕ) :=
  exists_portmanteau_of_ne (by decide) (by decide)

/-! ### The unattested shapes

AAB has two routes, each closed by one condition: a root allomorph
conditioned by a nonadjacent SPRL ((190), (45)), and a portmanteau
conditioned by SPRL with no comparative-level counterpart ((201)). Surface
ABA has one, accidental homophony, closed by Antihomophony ((44)). -/

/-- The vocabulary (190), with *be(tt)-* conditioned by SPRL across the comparative. -/
def aabContextual : List (SpanRule 3 String) := [⟨"good", 0, none⟩, ⟨"bett", 0, some 2⟩]

theorem aabContextual_realizes_aab :
    Setoid.ker (realize aabContextual) = Setoid.ker Paradigm.aab := by decide

/-- Its context skips the comparative, so adjacency excludes it. -/
theorem aabContextual_not_adjacent : ¬ Adjacent aabContextual := by decide

/-- The vocabulary (201), with *gor-* restricted to the superlative and no comparative-level
counterpart, which gives *\*da – da-ch – gor-au*. -/
def welshAAB : List (SpanRule 3 String) := [⟨"da", 0, none⟩, ⟨"gor", 1, some 2⟩]

theorem welshAAB_realizes_aab : Setoid.ker (realize welshAAB) = Setoid.ker Paradigm.aab := by decide

/-- The node [GOOD, CMPR] has a context-sensitive rule and no context-free one, which (202)
excludes. -/
theorem welshAAB_not_grounded : ¬ Grounded welshAAB := by decide

/-- By `realize_const_of_grounded`, the AAB cells refute Antihomophony and (202) together. -/
theorem welshAAB_blocked : ¬ (Antihomophonous welshAAB ∧ Grounded welshAAB) :=
  fun ⟨hAH, hG⟩ ↦
    absurd (realize_const_of_grounded hAH hG (by decide) (by decide)) (by decide)

/-- A superlative allomorph accidentally homophonous with the positive yields surface ABA, the
loophole that Antihomophony (44) closes. -/
def fakeAba : List (SpanRule 3 String) :=
  [⟨"A", 0, none⟩, ⟨"B", 0, some 1⟩, ⟨"A", 0, some 2⟩]

theorem fakeAba_realizes_aba : Setoid.ker (realize fakeAba) = Setoid.ker Paradigm.aba := by decide

theorem fakeAba_not_antihomophonous : ¬ Antihomophonous fakeAba := by decide

/-! ### Periphrasis and locality (§3.3) -/

/-- Modern Greek BAD (93), with *cheiró-* under CMPR and *kak-* elsewhere. -/
def greekBad : List (SpanRule 3 String) := [⟨"kak", 0, none⟩, ⟨"cheiró", 0, some 1⟩]

/-- With Merger the comparative is *cheiró-ter-os*. Without it the root cannot see CMPR, and the
periphrastic comparative is *pjo kak-ós*, not *\*pjo cheir-ós* (94), which is the RSG from
locality (90). -/
theorem greek_comparative :
    realizeIn (⟨1⟩ : Synthesis 3) greekBad 1 = some "cheiró" ∧
      realizeIn (⟨0⟩ : Synthesis 3) greekBad 1 = some "kak" := by
  decide

/-- Greek's distinct root forms certify its comparative as synthetic, by the engine's RSG. -/
theorem greek_rsg : (Synthesis.mk 1 : Synthesis 3).SyntheticAt 1 :=
  rsg (s := ⟨1⟩) (v := greekBad) (g := 1) (g' := 0) (by decide)

/-! ### Periphrastic superlatives (§3.3.3)

A periphrastic superlative may embed the comparative word, as Greek
*o cheiró-ter-os* does, or the positive, as Russian *samyj plox-oj* does. By
locality (90) only the first inherits a suppletive comparative root, so CSG1
holds of the first type and fails for the second. -/

/-- With a suppletive comparative, CSG1 holds of the superlative exactly when the superlative's
adjective word contains the comparative head. -/
theorem csg1_iff_one_le {F : Type*} {e : Fin 3 → Fin 3} (he : ∀ g, e g ≤ g)
    {v : List (SpanRule 3 F)} (hAH : Antihomophonous v) (h : realize v (e 1) ≠ realize v (e 0)) :
    realize v (e 2) ≠ realize v (e 0) ↔ 1 ≤ e 2 := by
  have h0 : e 0 = 0 := Fin.le_zero_iff.mp (he 0)
  have h1 : e 1 = 1 := by
    have := he 1
    by_contra hne
    exact h (by rw [h0, show e 1 = 0 by omega])
  refine ⟨fun h2 ↦ ?_, fun h2 h20 ↦ h ?_⟩
  · by_contra hlt
    exact h2 (by rw [h0, show e 2 = 0 by omega])
  · rw [h0] at h20 ⊢
    rw [h1]
    exact (isContiguous_realize hAH (Fin.zero_le _) h2 h20.symm).symm

/-- The periphrastic superlative *o cheiró-ter-os* (106a) embeds the comparative word, so it
inherits the suppletive root. -/
theorem greek_superlative : realizeIn (⟨1⟩ : Synthesis 3) greekBad 2 = some "cheiró" := by
  decide

/-- Russian BAD, with *xud-* under CMPR and *plox-* elsewhere. -/
def russianBad : List (SpanRule 3 String) := [⟨"plox", 0, none⟩, ⟨"xud", 0, some 1⟩]

theorem russianBad_antihomophonous : Antihomophonous russianBad := by decide

/-- The word extents of a synthetic comparative and a superlative embedding the positive, as in
*samyj sux-oj* (107d). -/
def positiveEmbedding : Fin 3 → Fin 3 := ![0, 1, 0]

/-- *Plox-oj, xuž-e, samyj plox-oj* (106d) is ABA although the vocabulary is antihomophonous,
since the superlative's adjective word lacks CMPR. The derived pattern is the one the Russian
Fragment records. -/
theorem russian_bad_eq_ploxoj :
    Setoid.ker (realize russianBad ∘ positiveEmbedding) =
      Setoid.ker Russian.Adjectives.ploxoj.comparison.suppletion := by
  decide

/-- With a superlative embedding the comparative, as in Greek, the same vocabulary is ABB. -/
theorem russian_bad_comparative_embedding :
    Setoid.ker (realizeIn ⟨1⟩ russianBad) = Setoid.ker Paradigm.abb := by
  decide

/-- The literary synthetic superlative *nai-xud-š-ij* is built on the suppletive root, so the
fully synthetic paradigm is ABB, as the locality condition predicts. -/
theorem russian_bad_synthetic_abb : Setoid.ker (realize russianBad) = Setoid.ker Paradigm.abb := by
  decide

/-- In the English, Latin and Russian Fragments every ABA root pattern has a periphrastic
superlative, so every morphological superlative satisfies CSG1. -/
theorem periphrastic_of_aba :
    ∀ e ∈ allEntries.map (·.toAdjective) ++ Latin.Adjectives.allEntries ++
        Russian.Adjectives.allEntries,
      Setoid.ker e.comparison.suppletion = Setoid.ker Paradigm.aba →
        e.comparison.superlativeStrategy = .periphrastic := by
  simp only [List.mem_append, or_imp, forall_and, List.forall_mem_map]
  exact ⟨⟨by decide, by decide⟩, by decide⟩

/-! ### The nanosyntax reading

The book treats *opt-* and *gor-* as portmanteaus by Fusion or insertion at
a nonterminal node, citing [caha-2009] among others (§5.3.1). Caha's
lexicon does it with context-free entries storing successively larger
constituents, competing under the Superset Principle. -/

/-- The Latin entries as a nanosyntax lexicon. -/
def latinBonusNS : List (SpanRule 3 String) :=
  [⟨"bon", 0, none⟩, ⟨"mel", 1, none⟩, ⟨"opt", 2, none⟩]

theorem latin_ns_contextFree : ContextFree latinBonusNS := by decide

/-- Superset spellout derives the same paradigm with no contextual
apparatus. -/
theorem latin_ns_spellout : spellout latinBonusNS = ![some "bon", some "mel", some "opt"] := by
  decide

/-- The two frameworks realize Latin cell for cell — the concrete face of
`spelloutGenerable_iff_generable`. -/
theorem latin_ns_eq_dm : spellout latinBonusNS = realize latinBonus :=
  latin_ns_spellout.trans latin_bonus_realize.symm

end Bobaljik2012
