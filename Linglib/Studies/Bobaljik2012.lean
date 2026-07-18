import Linglib.Morphology.DegreeContainment
import Linglib.Morphology.Exponence.Hierarchy
import Linglib.Morphology.Nanosyntax.Superset
import Linglib.Morphology.DM.Merger
import Linglib.Morphology.InflectionRules
import Linglib.Semantics.Alternatives.Lexical
import Linglib.Fragments.English.Modifiers.Adjectives
import Linglib.Fragments.Latin.Adjectives

/-!
# Bobaljik (2012): Universals in Comparative Morphology
[bobaljik-2012]

## Overview

[bobaljik-2012] surveys comparative and superlative morphology
across languages and derives several cross-linguistic generalizations
from the **containment hypothesis**: the superlative structurally
contains the comparative (`[[[ADJ] CMPR] SPRL]`).

## Key Generalizations

1. **CSG (Comparative-Superlative Generalizations)**: two directions.
   CSG1: a suppletive comparative forces a suppletive superlative
   (*ABA excluded); CSG2: a suppletive superlative forces a suppletive
   comparative (*AAB excluded). Attested: AAA, ABB, ABC. Unattested:
   *ABA, *AAB. The derivations are asymmetric — CSG1 needs containment
   + Elsewhere + Antihomophony, CSG2 additionally portmanteau exponence,
   adjacency, and the markedness condition (202) — in the formalization
   adjacency's AAB-blocking role is absorbed into `Grounded`; see
   `Morphology/Exponence/Hierarchy.lean`. Both are instantiated on
   the book's worked vocabularies below.
   **Scope**: relative superlatives only, not absolute superlatives /
   elatives (p. 2, p. 28). The CSG ranges over synthetic grades; among
   periphrastic superlatives it holds exactly of those embedding the
   comparative form (p. 30, p. 78).

2. **SSG (Synthetic Superlative Generalization)**: No language has a
   morphological (synthetic) superlative without also having a
   morphological comparative.

3. **RSG (Root Suppletion Generalization)**: Root suppletion is
   limited to synthetic (morphological) comparatives. No language
   has a periphrastic comparative with a suppletive root
   (*good → more bett).

4. **Lesslessness**: No language has a synthetic comparative of
   inferiority. "Less tall" is always periphrastic.

## English and Latin Fragment Verification

This module verifies the CSG, SSG, RSG, and lesslessness against
both the English adjective fragment (`Fragments/English/Modifiers/
Adjectives.lean`) and the Latin adjective fragment (`Fragments/Latin/
Adjectives.lean`), using the `suppletion` field on each entry to
encode empirically observed root-class patterns.
-/

/-! ### Scale-Generation Substrate -/

/-! Connects morphological infrastructure (`Morphology`) to scalar-
alternative infrastructure (`Semantics/Alternatives/HornScale.lean`),
enabling automatic generation of the alternatives needed for scalar
implicature computation. Lives in this study file because it is the
sole consumer. [horn-1972] [kennedy-2007] -/

namespace Bobaljik2012.ScaleFromParadigm

open Morphology
open Alternatives (HornScale)

/-- A morphologically-derived Horn scale. -/
structure MorphScale where
  positive : String
  comparative : String
  superlative : String
  deriving Repr, BEq

/-- Convert a `MorphScale` to a `HornScale String`, weakest-to-strongest. -/
def MorphScale.toHornScale (ms : MorphScale) : HornScale String :=
  ⟨[ms.positive, ms.comparative, ms.superlative]⟩

/-- Extract a degree scale from a stem's paradigm. -/
def adjectiveScale {σ : Type} (stem : Stem σ) : Option MorphScale :=
  let compRule := stem.paradigm.find? (λ r => r.category == .degree && r.value == "comp")
  let superRule := stem.paradigm.find? (λ r => r.category == .degree && r.value == "super")
  match compRule, superRule with
  | some comp, some super_ =>
    some { positive := stem.lemma_
         , comparative := comp.formRule stem.lemma_
         , superlative := super_.formRule stem.lemma_ }
  | _, _ => none

/-- Paradigm-mates as scalar alternatives, scale order preserved. -/
def morphologicalAlternatives {σ : Type} (stem : Stem σ) (form : String) :
    List String :=
  match adjectiveScale stem with
  | none => []
  | some ms =>
    let scale := ms.toHornScale
    scale.members.filter (· != form)

end Bobaljik2012.ScaleFromParadigm

namespace Bobaljik2012

open Morphology.DegreeContainment
open English.Modifiers.Adjectives

/-! ### Pattern Verification (English) -/

/-- Regular adjectives have AAA suppletion patterns. -/
theorem tall_aaa : tall.suppletion = aaa := rfl
theorem short_aaa : short.suppletion = aaa := rfl
theorem happy_aaa : happy.suppletion = aaa := rfl
theorem hot_aaa : hot.suppletion = aaa := rfl
theorem expensive_aaa : expensive.suppletion = aaa := rfl
theorem dry_aaa : dry.suppletion = aaa := rfl

/-- Suppletive adjectives have ABB suppletion patterns. -/
theorem good_abb : good.suppletion = abb := rfl
theorem bad_abb : bad.suppletion = abb := rfl

/-! ### CSG Verification (English) -/

/-- **CSG**: All English adjective entries satisfy contiguity
    (no *ABA violations). -/
theorem english_no_aba :
    ∀ e ∈ allEntries, e.suppletion.IsContiguous := by decide

/-- CSG Part I applied to English data: "good" and "bad" have
    suppletive comparatives, so by `csg_part1` their superlatives
    must be suppletive too — and they are. -/
theorem good_csg : good.suppletion.SprlSuppletive :=
  csg_part1 good.suppletion (by decide) (by decide)

theorem bad_csg : bad.suppletion.SprlSuppletive :=
  csg_part1 bad.suppletion (by decide) (by decide)

/-- CSG Part II on the English data: if the superlative is suppletive,
    the comparative is too. Data-level check; the engine derivation
    (`Morphology.Containment.realize_const_of_grounded`) is instantiated at
    `welshAAB_blocked` below. -/
theorem good_csg_part2 : good.suppletion.CmprSuppletive := by decide
theorem bad_csg_part2 : bad.suppletion.CmprSuppletive := by decide

/-! ### Attestedness Verification (English) -/

/-- All English root suppletion patterns satisfy both contiguity (no
    *ABA — `csg_part1`) and the terminal-adjacent plateau (CMPR cell =
    SPRL cell —
    `Morphology.Containment.realize_const_of_terminal_adjacent`). The
    conjunction restricts root patterns to AAA / ABB. Stated as the
    explicit conjunction so the underlying derivation is visible at use
    site, rather than packaged as a stipulated `isAttested` field. -/
theorem english_all_attested :
    ∀ e ∈ allEntries,
      e.suppletion.IsContiguous ∧ e.suppletion.cmpr = e.suppletion.sprl := by
  decide

/-! ### SSG (Synthetic Superlative Generalization) -/

/-- **SSG** ([bobaljik-2012]): If an entry has a synthetic
    superlative form, it also has a synthetic comparative form.
    No English adjective has `-est` without `-er`. -/
theorem english_ssg :
    ∀ e ∈ allEntries, e.formSuper.isSome → e.formComp.isSome := by decide

/-! ### RSG (Root Suppletion Generalization) -/

/-- The comparative form is synthetic (a single morphological word,
    not periphrastic "more X"), detected as the absence of a space in
    the form string. Structural counterpart:
    `Morphology.DM.Synthesis` (see the worked vocabularies
    below). -/
def IsSyntheticComp (e : AdjModifierEntry) : Prop :=
  ∃ f ∈ e.formComp, ' ' ∉ f.toList

instance (e : AdjModifierEntry) : Decidable (IsSyntheticComp e) := by
  unfold IsSyntheticComp; infer_instance

/-- **RSG** ([bobaljik-2012]): Root suppletion is limited to
    synthetic comparatives. If an entry has a suppletive root (CMPR
    differs from POS), then its comparative form is synthetic (not
    periphrastic).

    This rules out patterns like *good → more bett: a language
    cannot have a periphrastic comparative with a suppletive root.

    Verified: "good" → "better" (synthetic), "bad" → "worse" (synthetic).
    Contrast: "expensive" → "more expensive" (periphrastic, but
    non-suppletive root — AAA, not ABB). -/
theorem english_rsg :
    ∀ e ∈ allEntries, e.suppletion.CmprSuppletive → IsSyntheticComp e := by
  decide

/-! ### Lesslessness -/

/-! **Lesslessness** ([bobaljik-2012] (5), ch. 7): no language has a
synthetic comparative of inferiority — "less tall" is always
periphrastic. The book's empirically strongest generalization but its
least derived: the proposed account (CMPR plus a polarity-reversal
head, with synthetic spellout blocked by the polar antonym's
comparative) is a sketch the book itself flags as incomplete, so it is
recorded as data-level prose, not as a theorem of the ch. 2–5
axioms. -/

/-! ### Fragment Cross-Check -/

/-- The fragment records suppletive forms for "good" and "bad". -/
theorem good_forms :
    good.formComp = some "better" ∧ good.formSuper = some "best" :=
  ⟨rfl, rfl⟩

theorem bad_forms :
    bad.formComp = some "worse" ∧ bad.formSuper = some "worst" :=
  ⟨rfl, rfl⟩

/-- The suppletion field agrees with the surface forms:
    "good" → "better" → "best" is ABB (suppletive root shared
    across CMPR and SPRL). -/
theorem good_abb_from_forms :
    good.suppletion = abb ∧
    good.formComp = some "better" ∧
    good.formSuper = some "best" :=
  ⟨rfl, rfl, rfl⟩

/-! ### Cross-Linguistic Pattern Inventory -/

/-- The three attested degree-suppletive patterns. -/
def attestedPatterns : List (String × DegreePattern) :=
  [ ("AAA (tall–taller–tallest)",       aaa)
  , ("ABB (good–better–best)",          abb)
  , ("ABC (bonus–melior–optimus)",      abc) ]

/-- All attested patterns are contiguous. -/
theorem attested_all_contiguous :
    ∀ pair ∈ attestedPatterns, pair.2.IsContiguous := by decide

/-- The unattested *ABA pattern is not contiguous. -/
theorem aba_unattested : ¬ aba.IsContiguous := by decide

/-! ### Cross-Linguistic Verification (Latin) -/

open Latin.Adjectives in
/-- **Latin CSG**: All Latin adjective entries satisfy contiguity. -/
theorem latin_no_aba :
    ∀ e ∈ Latin.Adjectives.allEntries, e.suppletion.IsContiguous := by
  decide

open Latin.Adjectives in
/-- Latin *bonus – melior – optimus* derives ABC. -/
theorem latin_bonus_abc : bonus.suppletion = abc := rfl

open Latin.Adjectives in
/-- Latin exhibits all three attested patterns (AAA, ABB, ABC),
    confirming the cross-linguistic pattern inventory against a
    language with richer suppletion than English. -/
theorem latin_all_three_patterns :
    (∃ e ∈ Latin.Adjectives.allEntries, e.suppletion = aaa) ∧
    (∃ e ∈ Latin.Adjectives.allEntries, e.suppletion = abb) ∧
    (∃ e ∈ Latin.Adjectives.allEntries, e.suppletion = abc) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ### The Realizational Derivation: the Book's Worked Vocabularies -/

/-! The engine of `Morphology/Exponence/Hierarchy.lean` run on the
vocabularies [bobaljik-2012] actually writes down. `ExponenceRule`s record
exponent, exponed span, and conditioning context; `realize` runs
Elsewhere insertion; `degreeShape` reads the root-suppletion class off
the realized cells. The hypotheses of the engine's theorems
(`realize_const_of_grounded`, `exists_portmanteau_of_ne`) are
`decide`-checked on each vocabulary,
and the two unattested shapes are exhibited as violations of exactly
one condition each: AAB violates `Grounded` ((202)), surface ABA
violates `Antihomophonous` ((44)). -/

open Morphology.Containment Morphology.DM

/-- Czech BAD ([bobaljik-2012] (39)): root allomorph `hor-` conditioned
    by CMPR, elsewhere `špatn-`. -/
def czechBad : List (ExponenceRule 3 String) :=
  [⟨"špatn", 0, none⟩, ⟨"hor", 0, some 1⟩]

/-- Elsewhere insertion realizes *špatn-ý, hor-ší, nej-hor-ší*: ABB. -/
theorem czech_bad_realize :
    realize czechBad = ![some "špatn", some "hor", some "hor"] := by decide

theorem czech_bad_abb : degreeShape (realize czechBad) = abb := by decide

/-- English GOOD ([bobaljik-2012] (203)): `bett- / __]CMPR]`, elsewhere
    `good`. Terminal and adjacent, so the plateau applies. -/
def englishGood : List (ExponenceRule 3 String) :=
  [⟨"good", 0, none⟩, ⟨"bett", 0, some 1⟩]

theorem english_good_abb : degreeShape (realize englishGood) = abb := by decide

/-- English BAD ([bobaljik-2012] (194)): `worse` as a √ROOT+CMPR
    portmanteau, elsewhere `bad`. ABB arises on the portmanteau route
    too — `worse` simply realizes the whole comparative node. -/
def englishBad : List (ExponenceRule 3 String) :=
  [⟨"bad", 0, none⟩, ⟨"worse", 1, none⟩]

theorem english_bad_abb : degreeShape (realize englishBad) = abb := by decide

/-- Welsh GOOD ([bobaljik-2012] (198)): `gor- / __]SPRL]` and `gwell`,
    both √ROOT+CMPR portmanteaux, elsewhere `da`. -/
def welshGood : List (ExponenceRule 3 String) :=
  [⟨"da", 0, none⟩, ⟨"gwell", 1, none⟩, ⟨"gor", 1, some 2⟩]

/-- *da, gwell, gor-au*: ABC, generable because the C-exponent is a
    portmanteau. -/
theorem welsh_good_abc : degreeShape (realize welshGood) = abc := by decide

/-- Latin GOOD ([bobaljik-2012] (204)): `opt-` a √ROOT+CMPR portmanteau
    conditioned by SPRL, `mel-` a root allomorph conditioned by CMPR,
    elsewhere `bon`. The span structure also explains *\*opt-ior-imus*:
    `opt-` swallows the CMPR cell, so regular `-ior` has nothing to
    realize. -/
def latinBonus : List (ExponenceRule 3 String) :=
  [⟨"bon", 0, none⟩, ⟨"mel", 0, some 1⟩, ⟨"opt", 1, some 2⟩]

/-- *bon-us, mel-ior, opt-imus*: the engine derives the book's star
    ABC paradigm. -/
theorem latin_bonus_realize :
    realize latinBonus = ![some "bon", some "mel", some "opt"] := by decide

theorem latin_realize_abc : degreeShape (realize latinBonus) = abc := by decide

/-- Latin satisfies every condition the CSG2 derivation needs. -/
theorem latin_wellformed :
    Adjacent latinBonus ∧ Grounded latinBonus ∧ Antihomophonous latinBonus := by
  decide

/-- Latin is *not* terminal — and must not be: the terminal-adjacent
    plateau (`realize_const_of_terminal_adjacent`) would force
    CMPR = SPRL, wrongly excluding ABC. The portmanteau rule is what
    escapes it. -/
theorem latin_not_terminal : ¬ Terminal latinBonus := by decide

/-- Latin's superlative winner computed concretely: the portmanteau
    `opt-` — the ABC-requires-portmanteau consequence
    ([bobaljik-2012] §5.3.1, generalized there as (199)). -/
theorem latin_superlative_portmanteau :
    winner latinBonus 2 = some ⟨"opt", 1, some 2⟩ := by decide

/-- The engine theorem applied: since Latin's comparative and
    superlative cells diverge, `exists_portmanteau_of_ne` forces a
    portmanteau winner at the superlative. -/
theorem latin_sprl_needs_portmanteau :
    ∃ it ∈ latinBonus, winner latinBonus 2 = some it ∧ 0 < (it.spans : ℕ) :=
  exists_portmanteau_of_ne (by decide) (by decide)

/-- The nanosyntax lexicon for Latin GOOD, in the [caha-2009] method
    (the degree application is later literature; see
    `Morphology/Nanosyntax/Superset.lean`): context-free entries
    storing successively larger constituents, competing under the
    Superset Principle. -/
def latinBonusNS : List (ExponenceRule 3 String) :=
  [⟨"bon", 0, none⟩, ⟨"mel", 1, none⟩, ⟨"opt", 2, none⟩]

theorem latin_ns_contextFree : ContextFree latinBonusNS := by decide

/-- Superset spellout derives the same ABC paradigm with no contextual
    apparatus — the entries are portmanteaus by constituent size alone,
    doing the work of DM's context-restricted ch. 5 machinery. -/
theorem latin_ns_spellout :
    spellout latinBonusNS = ![some "bon", some "mel", some "opt"] := by decide

/-- Cross-framework agreement on the data: the nanosyntax lexicon and
    the DM vocabulary (204) realize the same paradigm cell for cell
    (the concrete face of
    `Morphology.Containment.spelloutGenerable_iff_generable`). -/
theorem latin_ns_eq_dm : spellout latinBonusNS = realize latinBonus :=
  latin_ns_spellout.trans latin_bonus_realize.symm

/-- The hypothetical AAB vocabulary ([bobaljik-2012] (201)): `gor-`
    restricted to the superlative with no comparative-level
    counterpart. It generates the unattested AAB shape
    (*\*da – da-ch – gor-au*)... -/
def welshAAB : List (ExponenceRule 3 String) :=
  [⟨"da", 0, none⟩, ⟨"gor", 1, some 2⟩]

theorem welshAAB_realizes_aab : degreeShape (realize welshAAB) = aab := by decide

/-- ...and is excluded by exactly one condition: its threshold set
    skips the comparative grade, violating `Grounded` ((202)). -/
theorem welshAAB_not_grounded : ¬ Grounded welshAAB := by decide

/-- The engine theorem `realize_const_of_grounded` applied: no vocabulary
    realizing the AAB cells can satisfy both Antihomophony and `Grounded` —
    the AAB realization itself refutes the conjunction. -/
theorem welshAAB_blocked : ¬ (Antihomophonous welshAAB ∧ Grounded welshAAB) :=
  λ ⟨hAH, hG⟩ =>
    absurd (realize_const_of_grounded hAH hG (by decide) (by decide)) (by decide)

/-- The homophonous-ABC loophole ([bobaljik-2012] (44) discussion):
    without Antihomophony, surface ABA is generable — a superlative
    root allomorph accidentally homophonous with the positive. -/
def fakeAba : List (ExponenceRule 3 String) :=
  [⟨"A", 0, none⟩, ⟨"B", 0, some 1⟩, ⟨"A", 0, some 2⟩]

theorem fakeAba_realizes_aba : degreeShape (realize fakeAba) = aba := by decide

theorem fakeAba_not_antihomophonous : ¬ Antihomophonous fakeAba := by decide

/-! ### Synthesis: the Merger layer on the worked vocabularies -/

/-- The structural synthetic/analytic notion
    (`Morphology.DM.Synthesis`) on English `good`: the word
    merges through the superlative (`wordTop = 2`), and since the
    word-internal realization shows distinct root forms at the positive
    and comparative grades, `rsg` certifies the comparative as
    synthetic — the structural counterpart of `english_rsg`'s
    string-level check. -/
theorem english_good_synthetic_comparative :
    (Synthesis.mk 2 : Synthesis 3).SyntheticAt 1 :=
  rsg (s := ⟨2⟩) (v := englishGood) (g := 1) (g' := 0) (by decide)

/-- A lexeme with no Merger (`wordTop = 0`, fully periphrastic
    paradigm) cannot exhibit root suppletion even with a suppletive
    vocabulary — the RSG direction made constructive: *more bett* is
    underivable because `bett-`'s conditioning CMPR head sits outside
    the word. -/
example : realizeIn ⟨0⟩ englishGood 1 = realizeIn ⟨0⟩ englishGood 0 :=
  realizeIn_const_of_wordTop_eq_zero rfl 1 0

/-! ### Scale Generation from Degree Paradigms -/

/-! `ScaleFromParadigm` (the Scale-Generation Substrate section above)
derives Horn scales from degree paradigms: a stem with comparative + superlative rules
yields a 3-point scale `[positive, comparative, superlative]`. The tests
below verify the extractor on the English adjective fragment. -/

open Bobaljik2012.ScaleFromParadigm

private def tallStem := tall.toStem Unit
private def goodStem := good.toStem Unit
private def expensiveStem := expensive.toStem Unit
private def deadStem := dead.toStem Unit
private def pregnantStem := pregnant.toStem Unit

/-- Gradable adjectives produce a scale; non-gradables do not. -/
theorem tall_scale_exists : (adjectiveScale tallStem).isSome = true := rfl

theorem dead_no_scale : (adjectiveScale deadStem).isNone = true := rfl

theorem pregnant_no_scale : (adjectiveScale pregnantStem).isNone = true := rfl

/-- Regular paradigm yields the expected 3-point scale. -/
theorem tall_scale_members :
    (adjectiveScale tallStem).map (·.toHornScale.members)
    = some ["tall", "taller", "tallest"] := rfl

/-- Suppletive paradigm yields the irregular forms in scale position. -/
theorem good_scale_members :
    (adjectiveScale goodStem).map (·.toHornScale.members)
    = some ["good", "better", "best"] := rfl

/-- Periphrastic paradigm yields multi-word scale members. -/
theorem expensive_scale_members :
    (adjectiveScale expensiveStem).map (·.toHornScale.members)
    = some ["expensive", "more expensive", "most expensive"] := rfl

/-! ### Morphological Alternatives -/

/-! `morphologicalAlternatives stem form` returns paradigm-mates of `form`
preserving scale order — the input shape scalar-implicature reasoning
expects. Tests confirm filter-by-equality semantics across the three
scale positions, plus the empty-list result for non-gradable stems. -/

theorem tall_alternatives :
    morphologicalAlternatives tallStem "tall" = ["taller", "tallest"] := rfl

theorem taller_alternatives :
    morphologicalAlternatives tallStem "taller" = ["tall", "tallest"] := rfl

theorem tallest_alternatives :
    morphologicalAlternatives tallStem "tallest" = ["tall", "taller"] := rfl

theorem dead_no_alternatives :
    morphologicalAlternatives deadStem "dead" = [] := rfl

end Bobaljik2012
