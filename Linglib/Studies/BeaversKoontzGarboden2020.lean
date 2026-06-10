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
a `becomesState` atom yields the corresponding `hasState` atom under
entailment closure (`Root.closedFeatureSignature`); the base
`featureSignature` records only the atoms. √blossom falsifies
Bifurcation on its own, since change of state is templatic
(`v_become`) content. √hand and √drown additionally falsify
Manner/Result Complementarity; they differ only in root position
(adjoined vs complement), the contrast carrying the book's account of
which root types are attested.

## Main declarations

* `flat`, `jog`, `blossom`, `crack`, `hand`, `drown`
* `exists_violatesBifurcation`, `bifurcation_thesis_false`
* `exists_hasMannerAndResult`, `manner_result_complementarity_false`
-/

namespace BeaversKoontzGarboden2020

open Semantics.Lexical.Roots

/-! ### The six representative roots -/

/-- √flat — pure state. -/
def flat : Root := ⟨"flat", [.hasState "flat"]⟩

/-- √jog — pure manner of motion. -/
def jog : Root := ⟨"jog", [.hasManner "jogging-gait", .motion]⟩

/-- √blossom — result with no specified manner or cause (an
    internally caused change of state). -/
def blossom : Root := ⟨"blossom", [.becomesState "flowering"]⟩

/-- √crack — caused result without specified manner. -/
def crack : Root := ⟨"crack", [.becomesState "fissured", .hasCause]⟩

/-- √hand — manner + cause + result, adjoined position. The
    possession result is non-cancelable ("#Mary handed John the book,
    but he never got it"), so it is root-entailed rather than
    implicated ([beavers-koontz-garboden-2020] ch. 3). -/
def hand : Root := ⟨"hand",
  [.hasManner "by-hand-transfer",
   .becomesState "in-recipient-possession",
   .hasCause]⟩

/-- √drown — manner of killing (Levin 1993's *crucify, drown, hang,
    electrocute* class; [beavers-koontz-garboden-2020] ch. 4):
    manner + cause + result, complement position. -/
def drown : Root := ⟨"drown",
  [.hasManner "submersion-in-liquid", .becomesState "dead", .hasCause]⟩

/-! ### Feature signatures

Base signatures record the atoms; closed signatures additionally
derive `state` from `becomesState` atoms. The book's typology values
are the closed ones. -/

theorem flat_featureSignature :
    flat.featureSignature =
      { state := true, manner := false, result := false, cause := false } :=
  rfl

theorem jog_featureSignature :
    jog.featureSignature =
      { state := false, manner := true, result := false, cause := false } :=
  rfl

theorem blossom_featureSignature :
    blossom.featureSignature =
      { state := false, manner := false, result := true, cause := false } :=
  rfl

theorem crack_featureSignature :
    crack.featureSignature =
      { state := false, manner := false, result := true, cause := true } :=
  rfl

theorem hand_featureSignature :
    hand.featureSignature =
      { state := false, manner := true, result := true, cause := true } :=
  rfl

theorem drown_featureSignature :
    drown.featureSignature =
      { state := false, manner := true, result := true, cause := true } :=
  rfl

theorem blossom_closedFeatureSignature :
    blossom.closedFeatureSignature =
      { state := true, manner := false, result := true, cause := false } :=
  rfl

theorem crack_closedFeatureSignature :
    crack.closedFeatureSignature =
      { state := true, manner := false, result := true, cause := true } :=
  rfl

theorem hand_closedFeatureSignature :
    hand.closedFeatureSignature =
      { state := true, manner := true, result := true, cause := true } :=
  rfl

theorem drown_closedFeatureSignature :
    drown.closedFeatureSignature =
      { state := true, manner := true, result := true, cause := true } :=
  rfl

/-! ### Falsifying the Bifurcation Thesis -/

/-- √blossom entails change of state — templatic (`v_become`) content
    in the root — falsifying Bifurcation without any manner or cause
    entailment. -/
theorem blossom_violatesBifurcation : blossom.ViolatesBifurcation :=
  .inl rfl

theorem crack_violatesBifurcation : crack.ViolatesBifurcation :=
  .inl rfl

theorem hand_violatesBifurcation : hand.ViolatesBifurcation :=
  .inl rfl

theorem drown_violatesBifurcation : drown.ViolatesBifurcation :=
  .inl rfl

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
theorem hand_hasMannerAndResult : hand.HasMannerAndResult := ⟨rfl, rfl⟩

/-- √drown entails both a manner (submersion) and a result (death);
    it differs from √hand in root position. -/
theorem drown_hasMannerAndResult : drown.HasMannerAndResult := ⟨rfl, rfl⟩

/-- Some root entails both a manner and a result. -/
theorem exists_hasMannerAndResult : ∃ r : Root, r.HasMannerAndResult :=
  ⟨hand, hand_hasMannerAndResult⟩

/-- The universal closure of Manner/Result Complementarity is false. -/
theorem manner_result_complementarity_false :
    ¬ ∀ r : Root, r.RespectsMannerResultComplementarity := fun h =>
  h hand hand_hasMannerAndResult

/-! ### Roots respecting each constraint -/

/-- √flat (pure state) respects Bifurcation. -/
theorem flat_respectsBifurcation : flat.RespectsBifurcation := by decide

/-- √jog (pure manner) respects Bifurcation. -/
theorem jog_respectsBifurcation : jog.RespectsBifurcation := by decide

/-- √crack (cause + result, no manner) respects Manner/Result
    Complementarity. -/
theorem crack_respectsMannerResultComplementarity :
    crack.RespectsMannerResultComplementarity := by decide

end BeaversKoontzGarboden2020
