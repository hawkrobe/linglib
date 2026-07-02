import Linglib.Semantics.Verb.Root.Closure
import Linglib.Semantics.Verb.Denotation
import Linglib.Semantics.Lexical.EventStructure

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
(`Root.closedKinds`) of the base atom kinds, and each
closed signature is one of the canonical typology rows
(`Root.Kinds.pureResult`, `causativeResult`, `fullSpec`).
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

open Verb

/-! ### The six representative roots -/

/-- √flat — pure state. -/
def flat : Root := ⟨"flat", {.hasState "flat"}, none, {}⟩

/-- √jog — pure manner of motion. -/
def jog : Root := ⟨"jog", {.hasManner "jogging-gait"}, none, {}⟩

/-- √blossom — result with no specified manner or cause (an
    internally caused change of state). -/
def blossom : Root := ⟨"blossom", {.becomesState "flowering"}, none, {}⟩

/-- √crack — caused result without specified manner. -/
def crack : Root := ⟨"crack", {.becomesState "fissured", .hasCause}, none, {}⟩

/-- √hand — manner + cause + result, adjoined position. The
    possession result is non-cancelable ("#Mary handed John the book,
    but he never got it"), so it is root-entailed rather than
    implicated ([beavers-koontz-garboden-2020] ch. 3). -/
def hand : Root := ⟨"hand",
  {.hasManner "by-hand-transfer",
   .becomesState "in-recipient-possession",
   .hasCause}, none, {}⟩

/-- √drown — manner of killing (Levin 1993's *crucify, drown, hang,
    electrocute* class; [beavers-koontz-garboden-2020] ch. 4):
    manner + cause + result, complement position. -/
def drown : Root := ⟨"drown",
  {.hasManner "submersion-in-liquid", .becomesState "dead", .hasCause}, none, {}⟩

/-! ### Kind signatures

Base signatures record the atom kinds; closed signatures are their
collocational closures, and coincide with the canonical rows of the
book's typology. -/

theorem flat_kinds : flat.kinds = {.state} := by
  decide

theorem jog_kinds : jog.kinds = {.manner} := by
  decide

theorem blossom_kinds :
    blossom.kinds = {.result} := by decide

theorem crack_kinds :
    crack.kinds = {.result, .cause} := by decide

theorem hand_kinds :
    hand.kinds = {.manner, .result, .cause} := by decide

theorem drown_kinds :
    drown.kinds = {.manner, .result, .cause} := by decide

theorem flat_closedKinds :
    flat.closedKinds = Root.Kinds.propertyConcept := by
  decide

theorem jog_closedKinds :
    jog.closedKinds = Root.Kinds.pureManner := by decide

theorem blossom_closedKinds :
    blossom.closedKinds = Root.Kinds.pureResult := by
  decide

theorem crack_closedKinds :
    crack.closedKinds = Root.Kinds.causativeResult := by
  decide

theorem hand_closedKinds :
    hand.closedKinds = Root.Kinds.fullSpec := by decide

theorem drown_closedKinds :
    drown.closedKinds = Root.Kinds.fullSpec := by decide

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

/-! ### The roots cash out denotationally ([beavers-koontz-garboden-2020] §1.3.2)

Threading the roots through the change-of-state denotation (`Verb.CosModel`): a
verb's denotation is dispatched on its root's `kinds`, so the kinds
proven above *select the event template* and the result entailment of (6)
follows from the signature. √crack (`+cause+result`) entails a result state in
any model; √jog (pure manner) does not — the *break*/*hit* contrast. -/

/-- `crack` the change-of-state verb (`Mary cracked the vase`). -/
def crackV : Verb := { form := "crack", frames := [Frame.np], root := crack }

/-- `jog` the pure-manner activity verb (`Mary jogged`). -/
def jogV : Verb := { form := "jog", frames := [], root := jog }

/-- √crack carries `.result`, so in **any** model its denotation entails the
    result state — the non-cancelable result of [beavers-koontz-garboden-2020]
    (6), derived from crack's signature rather than stipulated. -/
theorem crack_denote_entails_result {Entity State Time : Type*} [LinearOrder Time]
    (M : Verb.CosModel Entity State Time) (y x : Entity) (e : Event Time)
    (h : M.denote crackV y x e) : ∃ e' s, M.become s e' ∧ M.rootState crackV x s :=
  M.denote_result_entails_resultState crackV y x e (by decide) h

/-- √jog has no `.result` (nor `.cause`), so its denotation is the bare manner
    core — no `become`, no result state. Only the change-of-state root entails a
    result. -/
theorem jog_denote_eq_manner {Entity State Time : Type*} [LinearOrder Time]
    (M : Verb.CosModel Entity State Time) (y x : Entity) :
    M.denote jogV y x = M.manner jogV := by
  unfold Verb.CosModel.denote
  rw [if_neg (by decide), if_neg (by decide)]

/-! ### The same contrast at the template level ([rappaport-hovav-levin-1998])

`Verb.Root.template` reads the event-structure template off a root's
collocational closure; the kinds proven above fix it, and `HasResultState`
reduces to carrying `result` (`Verb.Root.template_hasResultState_iff`). So the
denotational result entailment (√crack) and the template result diagnostic are
*one fact* seen through `kinds`. -/

theorem flat_template : flat.template = .state := by decide
theorem jog_template : jog.template = .activity := by decide
theorem blossom_template : blossom.template = .achievement := by decide
theorem crack_template : crack.template = .accomplishment := by decide

/-- √crack's template embeds a result state (it carries `result`); √jog's does
    not — the *break*/*hit* contrast, now at the template layer and provably the
    same signature fact as `crack_denote_entails_result`. -/
theorem crack_template_hasResultState : crack.template.HasResultState := by decide

theorem jog_template_no_resultState : ¬ jog.template.HasResultState := by decide

/-- √crack's template embeds a result state, so by `denote_result_from_template`
    its denotation entails the result state in any model — the template diagnostic
    and the denotational entailment are *one* fact through `crack`'s `kinds`. -/
theorem crack_template_forces_denote_result {Entity State Time : Type*}
    [LinearOrder Time] (M : Verb.CosModel Entity State Time) (y x : Entity)
    (e : Event Time) (h : M.denote crackV y x e) :
    ∃ e' s, M.become s e' ∧ M.rootState crackV x s :=
  M.denote_result_from_template crackV crack_template_hasResultState y x e h

end BeaversKoontzGarboden2020
