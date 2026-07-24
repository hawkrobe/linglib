import Linglib.Data.Examples.Istratkova2004
import Linglib.Studies.Svenonius2004

/-!
# Istratkova (2004): On Multiple Prefixation in Bulgarian

[istratkova-2004] documents the Bulgarian-distinctive feature of
**multiple prefixation**: up to seven prefixes can stack on a single
verbal root, with superlexical prefixes systematically outside lexical
ones and outer prefixes taking scope over inner ones. Prefixes attach to
both perfective and imperfective stems, and the large class of simplex
*homogeneous* verbs (her ex. (2)) has no perfective counterparts and
"remains aspectless", behaving as imperfective only by default — her
analytical reclassification of the dictionary-imperfective simplexes,
encoded as the study-level `homogeneousSimplexes` class (the fragment
records the consensus imperfective value).

Her *po-* taxonomy distinguishes three superlexical *po-*'s:
delimitative ('for a while', which does not stack), distributive
(occurring only after *iz-*), and attenuative ('to a low degree', the
one that stacks over other superlexicals). Where [svenonius-2004]'s (3a)
glosses stacked *po-* as DLMT, the analyses here follow her own labels
(attenuative in `a23c`, distributive after *iz-* in `a22b`).

## Main definitions

* `homogeneousSimplexes` — her ex. (2) class: the simplexes she analyses
  as aspectless (imperfective only by default).
* `analyses` — her classified examples: the (1)/(3) single-prefix
  derivations on homogeneous simplexes, and the (22b)/(23c) stacks on
  *pro-dam* 'sell'.

## Main results

* `analyses_wellStacked` — every stack keeps superlexicals outside
  lexicals (`Svenonius2004.WellStacked`).
* `pairsTable_stems_homogeneous` — the (1)/(3)-table derivations attach
  to her homogeneous class, her quantization claim; per
  `homogeneous_imperfective` that class is dictionary-imperfective.
* `analyses_match_segmentation` — her hyphen segmentation equals each
  analysis' prefix-stem decomposition (all rows are citation forms).
-/

namespace Istratkova2004

open Semantics.Aspect (ViewpointAspectB)
open Verb (Stem)
open Svenonius2004 (Analysis WellStacked)
open Bulgarian.Verbs

/-- Her ex. (2) class: the simplex homogeneous verbs, which she analyses
    as aspectless — with no perfective counterparts, imperfective only
    by default. An analytical reclassification of fragment stems, so it
    lives here rather than as a fragment field. -/
def homogeneousSimplexes : List Stem :=
  [pisha, misla, znam, blesta, obicham, cheta]

/-! ### Single-prefix analyses (her (1)/(3) tables) -/

/-- (1a) *za-piša* 'put down in writing' — lexical *za-* on *piša*. -/
def a1a : Analysis := ⟨Examples.ex_1a, pisha, [(za, .lexical)]⟩

/-- (3a) *iz-misl'a* 'make up (a story)' — lexical *iz-* (idiosyncratic
    meaning shift) on *misl'a*. -/
def a3a : Analysis := ⟨Examples.ex_3a, misla, [(iz, .lexical)]⟩

/-- (3b) *za-običam* 'start to love' — superlexical inceptive *za-*. -/
def a3b : Analysis := ⟨Examples.ex_3b, obicham, [(za, .superlexical .inceptive)]⟩

/-- (3c) *po-znam* 'guess' — lexical *po-*: the fully idiosyncratic
    meaning is [svenonius-2004]'s own lexicality diagnostic (56e); her
    table assigns no superlexical label. -/
def a3c : Analysis := ⟨Examples.ex_3c, znam, [(po, .lexical)]⟩

/-- (3d) *za-blest'a* 'start to glitter' — superlexical inceptive
    *za-*. -/
def a3d : Analysis := ⟨Examples.ex_3d, blesta, [(za, .superlexical .inceptive)]⟩

/-- (3i) *pro-četa* 'read completely' — lexical (quantizing) *pro-*:
    not in her superlexical inventory; the default perfectivization of
    *četa*. -/
def a3i : Analysis := ⟨Examples.ex_3i, cheta, [(pro, .lexical)]⟩

/-! ### Multi-prefix analyses (her §4 stacking data) -/

/-- (22b) *iz-po-na-pro-dam* — completive *iz-*, distributive *po-*
    (her distributive *po-* occurs only after *iz-*), cumulative *na-*,
    all outside lexical *pro-* on *dam*. -/
def a22b : Analysis :=
  ⟨Examples.ex_22b, dam,
    [(iz, .superlexical .completive), (po, .superlexical .distributive),
     (na, .superlexical .cumulative), (pro, .lexical)]⟩

/-- (23c) *po-na-pro-dam* 'sell a few things' — attenuative *po-* over
    cumulative *na-* over lexical *pro-*: the stacking *po-* is her
    attenuative one (contrast [svenonius-2004]'s DLMT gloss of (3a)). -/
def a23c : Analysis :=
  ⟨Examples.ex_23c, dam,
    [(po, .superlexical .attenuative), (na, .superlexical .cumulative),
     (pro, .lexical)]⟩

/-- All analyses of this study. -/
def analyses : List Analysis := [a1a, a3a, a3b, a3c, a3d, a3i, a22b, a23c]

/-! ### Results -/

/-- Every analysis is well-stacked: superlexicals outside lexicals. -/
theorem analyses_wellStacked (a : Analysis) (ha : a ∈ analyses) :
    WellStacked a.prefixes := by
  fin_cases ha <;> decide

/-- The (1)/(3)-table derivations attach to her homogeneous class:
    prefixation quantizes these verbs, after which they come in
    perfective-imperfective pairs. -/
theorem pairsTable_stems_homogeneous
    (a : Analysis) (ha : a ∈ [a1a, a3a, a3b, a3c, a3d, a3i]) :
    a.stem ∈ homogeneousSimplexes := by
  fin_cases ha <;> decide

/-- The homogeneous class is dictionary-imperfective — the consensus
    value her aspectless analysis reinterprets as default behaviour. -/
theorem homogeneous_imperfective
    (s : Stem) (hs : s ∈ homogeneousSimplexes) :
    s.aspect = ViewpointAspectB.imperfective := by
  fin_cases hs <;> rfl

/-- Her hyphen segmentation equals each analysis' decomposition (all
    rows are 1sg-present citation forms). -/
theorem analyses_match_segmentation (a : Analysis) (ha : a ∈ analyses) :
    a.MatchesSegmentation := by
  fin_cases ha <;> decide

end Istratkova2004
