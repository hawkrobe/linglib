import Linglib.Semantics.Lexical.Roots.Closure

/-!
# Beavers & Koontz-Garboden (2020): The Roots of Verbal Meaning

[beavers-koontz-garboden-2020]

The six representative roots of the book's root typology (ch. 5), and
the falsification of the Bifurcation Thesis of Roots ([embick-2009];
[arad-2005]) and of Manner/Result Complementarity
([rappaport-hovav-levin-2010]).

| Root     | manner | cause | result | state | position   |
|----------|--------|-------|--------|-------|------------|
| √flat    |        |       |        |   ✓   | complement |
| √blossom |        |       |   ✓    |   ✓   | complement |
| √crack   |        |   ✓   |   ✓    |   ✓   | complement |
| √jog     |   ✓    |       |        |       | adjoined   |
| √hand    |   ✓    |   ✓   |   ✓    |   ✓   | adjoined   |
| √drown   |   ✓    |   ✓   |   ✓    |   ✓   | complement |

The +state cells of √blossom, √crack, √hand, √drown are *derived*:
the book's typology values are the collocational closures
(`Root.closedFeatureSignature`) of the base atom kinds, and each
closed signature is one of the canonical typology rows
(`Root.FeatureSignature.pureResult`, `causativeResult`, `fullSpec`).
√blossom falsifies Bifurcation on its own, since change of state is
templatic (`v_become`) content. √hand and √drown additionally falsify
Manner/Result Complementarity; they differ only in root position
(adjoined vs complement), the contrast carrying the book's account of
which root types are attested.

## Main declarations

* `flat`, `jog`, `blossom`, `crack`, `hand`, `drown`
* `exists_violatesBifurcation`, `bifurcation_thesis_false`
* `exists_hasMannerAndResult`, `manner_result_complementarity_false`
-/

namespace BeaversKoontzGarboden2020

/-! ### The six representative roots -/

/-- √flat — pure state. -/
def flat : Root := ⟨"flat", {.hasState "flat"}, none⟩

/-- √jog — pure manner of motion. -/
def jog : Root := ⟨"jog", {.hasManner "jogging-gait", .motion}, none⟩

/-- √blossom — result with no specified manner or cause (an
    internally caused change of state). -/
def blossom : Root := ⟨"blossom", {.becomesState "flowering"}, none⟩

/-- √crack — caused result without specified manner. -/
def crack : Root := ⟨"crack", {.becomesState "fissured", .hasCause}, none⟩

/-- √hand — manner + cause + result, adjoined position. The
    possession result is non-cancelable ("#Mary handed John the book,
    but he never got it"), so it is root-entailed rather than
    implicated ([beavers-koontz-garboden-2020] ch. 3). -/
def hand : Root := ⟨"hand",
  {.hasManner "by-hand-transfer",
   .becomesState "in-recipient-possession",
   .hasCause}, none⟩

/-- √drown — manner of killing (Levin 1993's *crucify, drown, hang,
    electrocute* class; [beavers-koontz-garboden-2020] ch. 4):
    manner + cause + result, complement position. -/
def drown : Root := ⟨"drown",
  {.hasManner "submersion-in-liquid", .becomesState "dead", .hasCause}, none⟩

/-! ### Feature signatures

Base signatures record the atom kinds; closed signatures are their
collocational closures, and coincide with the canonical rows of the
book's typology. -/

theorem flat_featureSignature : flat.featureSignature = {.state} := by
  decide

theorem jog_featureSignature : jog.featureSignature = {.manner} := by
  decide

theorem blossom_featureSignature :
    blossom.featureSignature = {.result} := by decide

theorem crack_featureSignature :
    crack.featureSignature = {.result, .cause} := by decide

theorem hand_featureSignature :
    hand.featureSignature = {.manner, .result, .cause} := by decide

theorem drown_featureSignature :
    drown.featureSignature = {.manner, .result, .cause} := by decide

theorem flat_closedFeatureSignature :
    flat.closedFeatureSignature = Root.FeatureSignature.propertyConcept := by
  decide

theorem jog_closedFeatureSignature :
    jog.closedFeatureSignature = Root.FeatureSignature.pureManner := by decide

theorem blossom_closedFeatureSignature :
    blossom.closedFeatureSignature = Root.FeatureSignature.pureResult := by
  decide

theorem crack_closedFeatureSignature :
    crack.closedFeatureSignature = Root.FeatureSignature.causativeResult := by
  decide

theorem hand_closedFeatureSignature :
    hand.closedFeatureSignature = Root.FeatureSignature.fullSpec := by decide

theorem drown_closedFeatureSignature :
    drown.closedFeatureSignature = Root.FeatureSignature.fullSpec := by decide

/-! ### Falsifying the Bifurcation Thesis -/

/-- √blossom entails change of state — templatic (`v_become`) content
    in the root — falsifying Bifurcation without any manner or cause
    entailment. -/
theorem blossom_violatesBifurcation : blossom.ViolatesBifurcation := by
  decide

theorem crack_violatesBifurcation : crack.ViolatesBifurcation := by
  decide

theorem hand_violatesBifurcation : hand.ViolatesBifurcation := by decide

theorem drown_violatesBifurcation : drown.ViolatesBifurcation := by
  decide

/-- Some root carries templatic content. -/
theorem exists_violatesBifurcation : ∃ r : Root, r.ViolatesBifurcation :=
  ⟨blossom, blossom_violatesBifurcation⟩

/-- The universal closure of the Bifurcation Thesis is false. -/
theorem bifurcation_thesis_false :
    ¬ ∀ r : Root, r.RespectsBifurcation := fun h =>
  h blossom blossom_violatesBifurcation

/-! ### Falsifying Manner/Result Complementarity -/

/-- √hand entails both a manner (by-hand transfer) and a result
    (recipient possession). -/
theorem hand_hasMannerAndResult : hand.HasMannerAndResult := by decide

/-- √drown entails both a manner (submersion) and a result (death);
    it differs from √hand in root position. -/
theorem drown_hasMannerAndResult : drown.HasMannerAndResult := by decide

/-- Some root entails both a manner and a result. -/
theorem exists_hasMannerAndResult : ∃ r : Root, r.HasMannerAndResult :=
  ⟨hand, hand_hasMannerAndResult⟩

/-- The universal closure of Manner/Result Complementarity is false. -/
theorem manner_result_complementarity_false :
    ¬ ∀ r : Root, r.RespectsMannerResultComplementarity := fun h =>
  h hand hand_hasMannerAndResult

/-! ### Roots respecting each constraint -/

/-- √flat (pure state) respects Bifurcation: its signature is bounded
    by the ontological kinds. -/
theorem flat_respectsBifurcation : flat.RespectsBifurcation := by decide

/-- √jog (pure manner) respects Bifurcation. -/
theorem jog_respectsBifurcation : jog.RespectsBifurcation := by decide

/-- √crack (cause + result, no manner) respects Manner/Result
    Complementarity. -/
theorem crack_respectsMannerResultComplementarity :
    crack.RespectsMannerResultComplementarity := by decide

end BeaversKoontzGarboden2020
