import Linglib.Morphology.Paradigm.Degree
import Linglib.Morphology.Exponence.Containment.Contiguity
import Linglib.Morphology.DistributedMorphology.Merger
import Linglib.Fragments.English.Modifiers.Adjectives
import Linglib.Fragments.Latin.Adjectives

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
RSG, with the SSG as Merger's downward closure.

## Main definitions

* `czechBad`, `englishGood`, `englishBad`, `welshGood`, `latinBonus`: the
  book's vocabularies (39), (203), (194), (198), (204) as `SpanRule`s.
* `aabContextual`, `welshAAB`, `fakeAba`: the vocabularies behind the
  unattested shapes — (190), (201), and the homophony loophole of (44).
* `greekBad`: the Modern Greek vocabulary (93).
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
* `greek_comparative`, `greek_superlative`: *pjo kak-ós*, not *pjo
  cheir-ós* ((94)), and a periphrastic superlative embedding the comparative
  inherits its root ((106)).
* `latin_ns_eq_dm`: nanosyntax and DM realize Latin alike.

## Implementation notes

Lesslessness (5) — no language has a synthetic comparative of inferiority
((278)–(279)) — is the book's most robust generalization but is not
derived here: its account, a polarity-reversing head under the Complexity
Condition, is a sketch in the book as well. The generalizations concern
relative superlatives only; absolute superlatives lack the comparative
component and its structure.
-/

namespace Bobaljik2012

open Morphology.Degree Morphology.Containment DistributedMorphology
open English.Modifiers.Adjectives (AdjModifierEntry allEntries good)

/-! ### The patterns on the Fragments (ch. 4) -/

/-- The English Fragment shows only AAA and ABB. -/
theorem english_patterns : ∀ e ∈ allEntries, e.suppletion = aaa ∨ e.suppletion = abb := by
  decide

/-- The Latin Fragment shows only the attested patterns of (191). -/
theorem latin_patterns :
    ∀ e ∈ Latin.Adjectives.allEntries,
      e.suppletion = aaa ∨ e.suppletion = abb ∨ e.suppletion = abc := by
  decide

/-- Latin shows all three: *longus*, *parvus*, *bonus*. -/
theorem latin_all_three :
    (∃ e ∈ Latin.Adjectives.allEntries, e.suppletion = aaa) ∧
      (∃ e ∈ Latin.Adjectives.allEntries, e.suppletion = abb) ∧
      ∃ e ∈ Latin.Adjectives.allEntries, e.suppletion = abc := by
  decide

/-- CSG1 (1) on *good*: a suppletive comparative forces a suppletive
superlative, by contiguity. -/
theorem good_csg1 : good.suppletion.SprlSuppletive :=
  csg_part1 good.suppletion (by decide) (by decide)

/-- A two-word form: periphrastic *more X*. -/
def Periphrastic (f : String) : Prop := ' ' ∈ f.toList

instance (f : String) : Decidable (Periphrastic f) := inferInstanceAs (Decidable (_ ∈ _))

/-- SSG (3) on the Fragment: a synthetic superlative comes with a synthetic
comparative — structurally, `Synthesis.syntheticAt_of_le`. -/
theorem english_ssg :
    ∀ e ∈ allEntries, ∀ s ∈ e.formSuper, ¬ Periphrastic s →
      ∃ c ∈ e.formComp, ¬ Periphrastic c := by
  decide

/-- RSG (4) on the Fragment: a suppletive comparative is synthetic —
*better*, *worse*, never *more bett*. -/
theorem english_rsg :
    ∀ e ∈ allEntries, e.suppletion.CmprSuppletive → ∃ c ∈ e.formComp, ¬ Periphrastic c := by
  decide

/-! ### The book's vocabularies (ch. 2, ch. 5)

Each vocabulary is run through the Elsewhere engine of
`Morphology/Exponence/Containment/Contiguity.lean`; `degreeShape` reads the
root pattern off the realized cells. -/

/-- Czech BAD (39): *hor-* under CMPR, elsewhere *špatn-*. -/
def czechBad : List (SpanRule 3 String) := [⟨"špatn", 0, none⟩, ⟨"hor", 0, some 1⟩]

/-- *špatn-ý, hor-ší, nej-hor-ší*: the comparative allomorph is chosen in the
superlative, since the superlative contains its context. -/
theorem czech_bad_realize : realize czechBad = ![some "špatn", some "hor", some "hor"] := by
  decide

theorem czech_bad_abb : degreeShape (realize czechBad) = abb := by decide

/-- English GOOD (203): *bett-* under CMPR, elsewhere *good*. -/
def englishGood : List (SpanRule 3 String) := [⟨"good", 0, none⟩, ⟨"bett", 0, some 1⟩]

theorem english_good_abb : degreeShape (realize englishGood) = abb := by decide

/-- English BAD (194): *worse* as a √ROOT+CMPR portmanteau, elsewhere
*bad*. -/
def englishBad : List (SpanRule 3 String) := [⟨"bad", 0, none⟩, ⟨"worse", 1, none⟩]

theorem english_bad_abb : degreeShape (realize englishBad) = abb := by decide

/-- Welsh GOOD (198): *gor-* under SPRL and *gwell*, both √ROOT+CMPR
portmanteaus, elsewhere *da*. -/
def welshGood : List (SpanRule 3 String) :=
  [⟨"da", 0, none⟩, ⟨"gwell", 1, none⟩, ⟨"gor", 1, some 2⟩]

/-- *da, gwell, gor-au*: ABC, since the superlative exponent is a
portmanteau. -/
theorem welsh_good_abc : degreeShape (realize welshGood) = abc := by decide

/-- Latin GOOD (204): *opt-* a √ROOT+CMPR portmanteau under SPRL, *mel-* a
root allomorph under CMPR, elsewhere *bon*. Since *opt-* expones the CMPR
cell, *-ior* has nothing to realize: *opt-imus*, not *\*opt-ior-imus*. -/
def latinBonus : List (SpanRule 3 String) :=
  [⟨"bon", 0, none⟩, ⟨"mel", 0, some 1⟩, ⟨"opt", 1, some 2⟩]

theorem latin_bonus_realize : realize latinBonus = ![some "bon", some "mel", some "opt"] := by
  decide

theorem latin_realize_abc : degreeShape (realize latinBonus) = abc := by decide

/-- Latin satisfies every condition the CSG2 derivation uses. -/
theorem latin_wellformed :
    Adjacent latinBonus ∧ Grounded latinBonus ∧ Antihomophonous latinBonus := by decide

/-- Latin is not terminal — it must not be, since terminal adjacent rules
plateau at the comparative (`realize_const_of_terminal_adjacent`), which
would exclude ABC. -/
theorem latin_not_terminal : ¬ Terminal latinBonus := by decide

/-- The superlative winner is the portmanteau *opt-*. -/
theorem latin_superlative_portmanteau : winner latinBonus 2 = some ⟨"opt", 1, some 2⟩ := by
  decide

/-- ABC needs a portmanteau ((199), §5.3.1): under adjacency, distinct
comparative and superlative cells force a winner exponing more than the
root. -/
theorem latin_sprl_needs_portmanteau :
    ∃ it ∈ latinBonus, winner latinBonus 2 = some it ∧ 0 < (it.spans : ℕ) :=
  exists_portmanteau_of_ne (by decide) (by decide)

/-! ### The unattested shapes

AAB has two routes, each closed by one condition: a root allomorph
conditioned by a nonadjacent SPRL ((190), (45)), and a portmanteau
conditioned by SPRL with no comparative-level counterpart ((201)). Surface
ABA has one, accidental homophony, closed by Antihomophony ((44)). -/

/-- (190): *be(tt)-* conditioned by SPRL across the comparative. -/
def aabContextual : List (SpanRule 3 String) := [⟨"good", 0, none⟩, ⟨"bett", 0, some 2⟩]

theorem aabContextual_realizes_aab : degreeShape (realize aabContextual) = aab := by decide

/-- Its context skips the comparative: adjacency excludes it. -/
theorem aabContextual_not_adjacent : ¬ Adjacent aabContextual := by decide

/-- (201): *gor-* restricted to the superlative with no comparative-level
counterpart — *\*da – da-ch – gor-au*. -/
def welshAAB : List (SpanRule 3 String) := [⟨"da", 0, none⟩, ⟨"gor", 1, some 2⟩]

theorem welshAAB_realizes_aab : degreeShape (realize welshAAB) = aab := by decide

/-- The node [GOOD, CMPR] has a context-sensitive rule and no context-free
one: (202) excludes it. -/
theorem welshAAB_not_grounded : ¬ Grounded welshAAB := by decide

/-- `realize_const_of_grounded` applied: the AAB cells refute Antihomophony
and (202) together. -/
theorem welshAAB_blocked : ¬ (Antihomophonous welshAAB ∧ Grounded welshAAB) :=
  λ ⟨hAH, hG⟩ =>
    absurd (realize_const_of_grounded hAH hG (by decide) (by decide)) (by decide)

/-- The homophony loophole of (44): a superlative allomorph accidentally
homophonous with the positive yields surface ABA. -/
def fakeAba : List (SpanRule 3 String) :=
  [⟨"A", 0, none⟩, ⟨"B", 0, some 1⟩, ⟨"A", 0, some 2⟩]

theorem fakeAba_realizes_aba : degreeShape (realize fakeAba) = aba := by decide

theorem fakeAba_not_antihomophonous : ¬ Antihomophonous fakeAba := by decide

/-! ### Periphrasis and locality (§3.3) -/

/-- Modern Greek BAD (93): *cheiró-* under CMPR, elsewhere *kak-*. -/
def greekBad : List (SpanRule 3 String) := [⟨"kak", 0, none⟩, ⟨"cheiró", 0, some 1⟩]

/-- (94): with Merger the comparative is *cheiró-ter-os*; without it the
root cannot see CMPR, and the periphrastic comparative is *pjo kak-ós*, not
*\*pjo cheir-ós* — the RSG from locality (90). -/
theorem greek_comparative :
    realizeIn (⟨1⟩ : Synthesis 3) greekBad 1 = some "cheiró" ∧
      realizeIn (⟨0⟩ : Synthesis 3) greekBad 1 = some "kak" := by
  decide

/-- The engine's RSG applied: Greek's distinct root forms certify its
comparative as synthetic. -/
theorem greek_rsg : (Synthesis.mk 1 : Synthesis 3).SyntheticAt 1 :=
  rsg (s := ⟨1⟩) (v := greekBad) (g := 1) (g' := 0) (by decide)

/-- (106a): the periphrastic superlative *o cheiró-ter-os* embeds the
comparative word, so it inherits the suppletive root — CSG1 holds of a
periphrastic superlative exactly when it embeds the comparative (§3.3.3). -/
theorem greek_superlative : realizeIn (⟨1⟩ : Synthesis 3) greekBad 2 = some "cheiró" := by
  decide

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
