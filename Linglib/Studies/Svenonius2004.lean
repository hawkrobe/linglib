import Mathlib.Tactic.FinCases
import Linglib.Data.Examples.Svenonius2004
import Linglib.Fragments.Slavic.Russian.Verbs
import Linglib.Fragments.Slavic.Polish.Verbs
import Linglib.Fragments.Slavic.Bulgarian.Verbs
import Linglib.Morphology.Word.Tree

/-!
# Svenonius (2004): Slavic Prefixes Inside and Outside VP

[svenonius-2004] splits Slavic verbal prefixes into two classes: **lexical**
prefixes are R-heads inside VP (resultative, particle-like, connecting to
[dendikken-1995]'s treatment of Germanic verb particles), while
**superlexical** prefixes are Asp-heads outside VP (aspectual operators).
The same prefix realises either class — his §1 exx. (1a)/(1c) use Russian
*za-* both ways, on the shared fragment morph `Russian.Verbs.za`.
The classification is contested rather than consensus: [romanova-2004]
documents diagnostic mismatches, and Tatevosov's later work posits an
intermediate class.

The syntactic height cut named here is the same one `Minimalist.AspFlavor`
(outer vs inner aspect, Travis/Cinque) carries for Sinitic split-aspect;
the types are kept separate because the commitments differ (lexical =
resultative R-head, not merely inner-Asp host).

Data flow: attested examples live in `Data.Examples.Svenonius2004`
(generated from JSON); prefix morphs and stems are fragment entries; an
`Analysis` pairs an example with a stem and a classified prefix sequence —
the classification is this paper's analytical act, applied to shared data,
never a fragment field.

## Main definitions

* `SuperlexicalSubtype`, `PrefixClass`, `PrefixClass.IsSuperlexical` — a
  selection of superlexical Aktionsart subtypes (his §4, and
  [istratkova-2004]'s taxonomy; not a closed set), and the two-way class.
* `Analysis` — an attested example, its fragment stem, and its classified
  prefix sequence (outermost first), with derived word-formation `tree`.
* `WellStacked` — no lexical prefix outside a superlexical one (§1: "the
  superlexical prefix always appears outside the lexical prefix").
* `analyses` — this paper's classified examples (Russian, one Polish, two
  Bulgarian stacks cited from [istratkova-2004]).

## Main results

* `analyses_wellStacked` / `reverse_4a_not_wellStacked` — the stacking
  generalization holds across the analyses, and the attested ungrammatical
  reversal (4b) *vy-po-brasyvatj* violates it.
* `stemAspect_imperfective_of_isSuperlexical` — diagnostic (56c) (§4.1)
  over the Russian analyses: superlexical prefixes select imperfective
  stems. (Russian-scoped: his Bulgarian stacks attach to the quantized
  perfective *razkaža*, per [istratkova-2004].)
* `analyses_match_segmentation` — for citation-form examples, the paper's
  hyphen segmentation equals the analysis' prefix-stem decomposition.
-/

namespace Svenonius2004

open Data.Examples (LinguisticExample)
open Morphology (Morph)
open Morphology.Word (Tree)
open Semantics.Aspect (Perfectivity)
open Verb (Stem)

/-- Aspectual subtypes of the superlexical class — the labels recurring
    in [svenonius-2004] §4 (his Bulgarian ordering (57)) and in
    [istratkova-2004]'s prefix-by-prefix taxonomy. A selection, not a
    closed set: excessive, terminative, and perdurative also occur in
    the literature. -/
inductive SuperlexicalSubtype
  | delimitative
  | cumulative
  | completive
  | repetitive
  | inceptive
  | distributive
  | attenuative
  deriving DecidableEq

/-- [svenonius-2004]'s lexical / superlexical split as a single ADT —
    the superlexical case carries its subtype. -/
inductive PrefixClass
  | lexical
  | superlexical (subtype : SuperlexicalSubtype)
  deriving DecidableEq

namespace PrefixClass

/-- A `PrefixClass` is *superlexical* iff it is the `superlexical _` case. -/
def IsSuperlexical : PrefixClass → Prop
  | .lexical        => False
  | .superlexical _ => True

instance : DecidablePred IsSuperlexical
  | .lexical        => isFalse id
  | .superlexical _ => isTrue trivial

end PrefixClass

/-- A classified prefix sequence (surface order, outermost first) is
    *well-stacked* when no lexical prefix appears outside a superlexical
    one — [svenonius-2004] §1: "the superlexical prefix always appears
    outside the lexical prefix". -/
def WellStacked (prefixes : List (Morph × PrefixClass)) : Prop :=
  prefixes.Pairwise fun outer inner =>
    inner.2.IsSuperlexical → outer.2.IsSuperlexical

instance : DecidablePred WellStacked := fun prefixes =>
  inferInstanceAs (Decidable (prefixes.Pairwise fun outer inner =>
    inner.2.IsSuperlexical → outer.2.IsSuperlexical))

/-- An analysis of an attested example: the fragment stem it is built on
    and its prefix sequence (outermost first), each prefix a fragment
    morph paired with this paper's class assignment. -/
structure Analysis where
  /-- The attested example (from `Data.Examples`). -/
  ex       : LinguisticExample
  /-- The fragment verb-stem entry. -/
  stem     : Stem
  /-- Classified fragment prefix morphs, outermost first. -/
  prefixes : List (Morph × PrefixClass)

namespace Analysis

/-- The word-formation tree: the prefix morphs folded, innermost-last,
    over the stem root. -/
def tree (a : Analysis) : Tree Morph :=
  a.prefixes.foldr (fun p t => .prefixed p.1 t)
    (.root (Morph.root a.stem.form))

/-- Every analysis tree is concatenative: prefixation only. -/
theorem tree_isConcatenative (a : Analysis) : a.tree.IsConcatenative := by
  unfold tree
  induction a.prefixes with
  | nil => trivial
  | cons p ps ih => exact ih

/-- The example's hyphen-segmented text equals the analysis'
    decomposition into prefix forms plus stem. Applicable to
    citation-form examples (not sentence examples or inflected tokens). -/
def MatchesSegmentation (a : Analysis) : Prop :=
  a.ex.primaryText =
    String.intercalate "-" (a.prefixes.map (·.1.form) ++ [a.stem.form])

instance : DecidablePred MatchesSegmentation := fun _ =>
  decEq _ _

end Analysis

/-! ### The paper's analyses

Russian from §1 and §4.1; the Polish (4c) and the Bulgarian stacks (3a),
(3e) as he classifies them (for (3a) [istratkova-2004]'s own finer
taxonomy diverges — her attenuative *po-* — see
`Studies/Istratkova2004.lean`). -/

section Russian
open Russian.Verbs

/-- (1a) *za-brosil* — lexical spatial *za-* on perfective *brositj*. -/
def a1a : Analysis := ⟨Examples.ex_1a, brosit, [(za, .lexical)]⟩

/-- (1b) *za-brosil* 'gave up' — the same lexical *za-*, idiomatic. -/
def a1b : Analysis := ⟨Examples.ex_1b, brosit, [(za, .lexical)]⟩

/-- (1c) *za-brosal* — superlexical inceptive *za-* on imperfective
    *brosatj*: the minimal pair with `a1a` on the same fragment morph. -/
def a1c : Analysis := ⟨Examples.ex_1c, brosat, [(za, .superlexical .inceptive)]⟩

/-- (4a) *po-vy-brasyvatj* — superlexical distributive *po-* outside
    lexical *vy-* on the secondary-imperfective stem. -/
def a4a : Analysis :=
  ⟨Examples.ex_4a, brasyvat, [(po, .superlexical .distributive), (vy, .lexical)]⟩

/-- (58) discussion: *za-kuritj* — superlexical inceptive *za-*. -/
def a58za : Analysis := ⟨Examples.ex_58za, kurit, [(za, .superlexical .inceptive)]⟩

/-- (58) discussion: *po-čitatj* — superlexical attenuative *po-*. -/
def a58po : Analysis := ⟨Examples.ex_58po, chitat, [(po, .superlexical .attenuative)]⟩

/-- The Russian analyses. -/
def russianAnalyses : List Analysis := [a1a, a1b, a1c, a4a, a58za, a58po]

end Russian

section Polish
open Polish.Verbs

/-- (4c) *po-w-chodzili* — superlexical distributive *po-* outside
    lexical *w-* (Polish counterpart of `a4a`). -/
def a4c : Analysis :=
  ⟨Examples.ex_4c, chodzic, [(po, .superlexical .distributive), (w, .lexical)]⟩

end Polish

section Bulgarian
open Bulgarian.Verbs

/-- (3a) *po-na-razkaža* — his gloss DLMT-CMLT on perfective *razkaža*. -/
def a3a : Analysis :=
  ⟨Examples.ex_3a, razkazha,
    [(po, .superlexical .delimitative), (na, .superlexical .cumulative)]⟩

/-- (3e) *iz-po-na-pre-razkaža* — his gloss CMPL-DSTR-CMLT-RPET, the
    deepest stack he cites from [istratkova-2004]. -/
def a3e : Analysis :=
  ⟨Examples.ex_3e, razkazha,
    [(iz, .superlexical .completive), (po, .superlexical .distributive),
     (na, .superlexical .cumulative), (pre, .superlexical .repetitive)]⟩

end Bulgarian

/-- All analyses of this study. -/
def analyses : List Analysis :=
  [a1a, a1b, a1c, a4a, a58za, a58po, a4c, a3a, a3e]

/-! ### Results -/

/-- Every analysis is well-stacked. -/
theorem analyses_wellStacked (a : Analysis) (ha : a ∈ analyses) :
    WellStacked a.prefixes := by
  fin_cases ha <;> decide

/-- The attested ungrammatical reversal (4b) *vy-po-brasyvatj*
    (recorded as the `alternatives` of (4a)) violates well-stackedness:
    it would put the lexical prefix outside the superlexical one. -/
theorem reverse_4a_not_wellStacked : ¬ WellStacked a4a.prefixes.reverse := by
  decide

/-- Likewise the Polish reversal (4d) *w-po-chodzili*. -/
theorem reverse_4c_not_wellStacked : ¬ WellStacked a4c.prefixes.reverse := by
  decide

/-- Diagnostic (56c) (§4.1) over the Russian analyses: a superlexically
    prefixed verb is built on an imperfective stem. Russian-scoped:
    his Bulgarian stacks attach to the quantized perfective *razkaža*
    ([istratkova-2004]), so (56c) is not a Bulgarian diagnostic. -/
theorem stemAspect_imperfective_of_isSuperlexical
    (a : Analysis) (ha : a ∈ russianAnalyses)
    (hs : ∃ p ∈ a.prefixes, p.2.IsSuperlexical) :
    a.stem.aspect = Perfectivity.imperfective := by
  fin_cases ha <;> first | rfl | exact absurd hs (by decide)

/-- For the citation-form examples, the paper's hyphen segmentation
    equals the analysis' decomposition. (Sentence examples (1a)-(1c)
    and the inflected Polish token (4c) are excluded.) -/
theorem analyses_match_segmentation
    (a : Analysis) (ha : a ∈ [a4a, a58za, a58po, a3a, a3e]) :
    a.MatchesSegmentation := by
  fin_cases ha <;> decide

-- Every analysis tree is kind-coherent (prefix morphs over a root morph).
example : ∀ a ∈ analyses, a.tree.IsKindCoherent := by decide

end Svenonius2004
