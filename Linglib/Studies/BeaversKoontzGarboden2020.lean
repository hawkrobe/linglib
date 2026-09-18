import Linglib.Semantics.Root.Defs
import Linglib.Semantics.ArgumentStructure.Verb
import Linglib.Semantics.ArgumentStructure.EventStructure
import Linglib.Semantics.ArgumentStructure.LevinTheory
import Linglib.Semantics.ArgumentStructure.LevinClass.Properties
import Linglib.Semantics.Presupposition.Iterative
import Linglib.Data.Examples.BeaversKoontzGarboden2020

/-!
# Beavers & Koontz-Garboden (2020): The Roots of Verbal Meaning

This file formalizes the root typology of Beavers and Koontz-Garboden's book and the two theses
it refutes. A root carries entailments of four kinds, manner, cause, result and state. The
Bifurcation Thesis holds that a root carries only a state or a manner, all eventive content
belonging to the verbal template, and Manner/Result Complementarity holds that no root entails
both a manner and a result. The root of *blossom* entails a change and so falsifies the first
(`bifurcation_thesis_false`); the roots of *hand* and *drown* entail both a manner and a result
and so falsify the second (`manner_result_complementarity_false`).

The modifier *again* attaches to the root, to `vbecome` or to `vcause`, and the entailments
among its three readings follow from the monotonicity of the presupposition of
`Presupposition.again`. The book's hypothesis about which roots alternate between a causative
and an inchoative is compared with the class pages of Levin's *English Verb Classes and
Alternations* (`rootHypothesis_matches_profile`).

## Implementation notes

* The state entailments of the result roots are derived by the collocational closure of the
  kind signature (`Root.closedKinds`).
* The thesis predicates are the apparatus of this study alone.

## References

* [beavers-koontz-garboden-2020]
* [levin-1993]
* [embick-2009]
* [arad-2005]
* [rappaport-hovav-levin-2010]
* [von-stechow-1996]
-/

namespace Semantics.Root.Kinds

/-! ### The two theses, at signature level -/

/-- The ontological kinds are all that the Bifurcation Thesis allows a root to carry. -/
def ontological : Root.Kinds := {.state, .manner}

/-- A signature violates the Bifurcation Thesis when it carries templatic, eventive content,
that is, when it is not bounded by `ontological`. -/
def ViolatesBifurcation (s : Root.Kinds) : Prop := ¬ s ≤ ontological

instance (s : Root.Kinds) : Decidable s.ViolatesBifurcation :=
  inferInstanceAs (Decidable (¬ _ ≤ _))

/-- Violation is carrying a `result` or `cause` kind. -/
theorem violatesBifurcation_iff :
    ∀ s : Root.Kinds,
      s.ViolatesBifurcation ↔ .result ∈ s ∨ .cause ∈ s := by decide

/-- Bifurcation violation is monotone, so adding entailments cannot repair a violation. -/
theorem violatesBifurcation_mono :
    ∀ {s t : Root.Kinds}, s ≤ t →
      s.ViolatesBifurcation → t.ViolatesBifurcation := by decide

/-- A signature has both manner and result, the configuration that Manner/Result
Complementarity claims no root realizes. -/
def HasMannerAndResult (s : Root.Kinds) : Prop :=
  {Root.Kind.manner, Root.Kind.result} ≤ s

instance (s : Root.Kinds) : Decidable s.HasMannerAndResult :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- MRC violation is monotone in the signature order. -/
theorem hasMannerAndResult_mono :
    ∀ {s t : Root.Kinds}, s ≤ t →
      s.HasMannerAndResult → t.HasMannerAndResult := by decide

/-- Bifurcation is invariant under collocational closure, since `close` only adds the `state`
and `result` kinds forced by `cause`, never `manner`. -/
theorem violatesBifurcation_close_iff :
    ∀ s : Root.Kinds,
      (close s).ViolatesBifurcation ↔ s.ViolatesBifurcation := by decide

theorem hasMannerAndResult_close_iff :
    ∀ s : Root.Kinds,
      (close s).HasMannerAndResult ↔
        s.HasMannerAndResult ∨ (.manner ∈ s ∧ .cause ∈ s) := by decide

/-! ### The typology -/

/-- The seven rows of the typology (12). -/
def typology : Finset Root.Kinds :=
  {propertyConcept, pureResult, causativeResult, pureManner, {.state, .manner},
   {.state, .manner, .result}, fullSpec}

/-- The typology (12) is exhaustive, since the signatures respecting the collocational
    restrictions are its seven rows and `∅`. -/
theorem wellFormed_iff_mem_typology :
    ∀ s : Root.Kinds, s.WellFormed ↔ s = ∅ ∨ s ∈ typology := by decide

/-- The filled cells of (12), pairs of a closed signature and a position. -/
def attestedCells : Finset (Root.Kinds × Root.Position) :=
  {(propertyConcept, .complement), (pureResult, .complement), (causativeResult, .complement),
   (pureManner, .adjoined), (fullSpec, .adjoined), (fullSpec, .complement)}

end Semantics.Root.Kinds

namespace Semantics.Root

/-! ### The two theses, at root level -/

/-- A root violates Bifurcation when it itself carries templatic, eventive meaning, a change of
state or a cause. -/
def ViolatesBifurcation (r : Root) : Prop :=
  r.kinds.ViolatesBifurcation

instance (r : Root) : Decidable r.ViolatesBifurcation :=
  inferInstanceAs (Decidable (Root.Kinds.ViolatesBifurcation _))

/-- A root respects Bifurcation when it carries only the ontological entailments, state and
manner. -/
def RespectsBifurcation (r : Root) : Prop :=
  ¬ r.ViolatesBifurcation

instance (r : Root) : Decidable r.RespectsBifurcation :=
  inferInstanceAs (Decidable (¬ _))

/-- A root respects Bifurcation iff its signature is bounded by the ontological kinds. -/
theorem respectsBifurcation_iff_le {r : Root} :
    r.RespectsBifurcation ↔
      r.kinds ≤ Root.Kinds.ontological :=
  not_not

/-- A root has both manner and result entailments, which Manner/Result Complementarity claims
no root does. -/
def HasMannerAndResult (r : Root) : Prop :=
  r.kinds.HasMannerAndResult

instance (r : Root) : Decidable r.HasMannerAndResult :=
  inferInstanceAs (Decidable (Root.Kinds.HasMannerAndResult _))

/-- Negation of `HasMannerAndResult`. -/
def RespectsMannerResultComplementarity (r : Root) : Prop :=
  ¬ r.HasMannerAndResult

instance (r : Root) : Decidable r.RespectsMannerResultComplementarity :=
  inferInstanceAs (Decidable (¬ _))

end Semantics.Root

section Again

open Presupposition

namespace Verb.CosModel

/-! ### Sublexical *again* and the hierarchy of its readings, (25)–(27)

*Again* is a presupposition trigger that can attach at three points in the change-of-state
structure, the root, `vbecome` and `vcause`, which yields the three readings of *Mary flattened
the rug again* in (25): the restitutive one, that the rug had been flat, the repetitive one over
the change, that it had flattened, and the repetitive one over the causation, that Mary had
flattened it. The entry (26) is `Presupposition.again`, with `≪` the precedence between
eventualities. The hierarchy of the readings, (25c) entailing (25b) entailing (25a), and the
collapse of the restitutive reading for result roots, (43) and (45), follow from the
change-of-state entailments of `Verb.CosModel` by the monotonicity of the presupposition. -/

variable {Entity State T : Type*} [LinearOrder T] (M : CosModel Entity State T)
  {ltS : State → State → Prop} {ltE : Event T → Event T → Prop} {v : Verb} {x y : Entity}

/-- In (27a) *again* attaches low, to the root, and modifies the root state, which is the
restitutive reading. -/
def againRestitutive (ltS : State → State → Prop) (v : Verb) (x : Entity) : PartialProp State :=
  again ltS (M.rootState v x)

/-- In (27b) *again* attaches to `vbecomeP`, which is the repetitive reading over the change. -/
def againRepetitiveBecome (ltE : Event T → Event T → Prop) (v : Verb) (x : Entity) :
    PartialProp (Event T) :=
  again ltE (M.inchoative v x)

/-- In (27c) *again* attaches high, to `vcauseP`, which is the repetitive reading over the
causation. -/
def againRepetitiveCause (ltE : Event T → Event T → Prop) (v : Verb) (y x : Entity) :
    PartialProp (Event T) :=
  again ltE (M.causative v y x)

/-- In the upper step of the hierarchy in (25), the presupposition of the repetitive reading
over the causation gives an earlier change, since a causing event brings one about. -/
theorem againRepetitiveCause_presup_entails_become {w : Event T}
    (h : (M.againRepetitiveCause ltE v y x).presup w) :
    ∃ w', ltE w' w ∧ ∃ e, M.inchoative v x e :=
  again_presup_mono (Q := fun _ ↦ ∃ e, M.inchoative v x e)
    (fun w' ↦ M.causative_entails_inchoative v y x w') w h

/-- In the lower step of the hierarchy in (25), the presupposition of the repetitive reading
over the change gives an earlier root state, since a change brings one about. -/
theorem againRepetitiveBecome_presup_entails_state {e : Event T}
    (h : (M.againRepetitiveBecome ltE v x).presup e) :
    ∃ e', ltE e' e ∧ ∃ s, M.become s e' ∧ M.rootState v x s :=
  h

/-- End to end, the hierarchy in (25) says that Mary's having flattened the rug before entails
that it had been flat before. -/
theorem againRepetitiveCause_presup_entails_state {w : Event T}
    (h : (M.againRepetitiveCause ltE v y x).presup w) :
    ∃ w', ltE w' w ∧ ∃ e s, M.become s e ∧ M.rootState v x s :=
  again_presup_mono (Q := fun _ ↦ ∃ e s, M.become s e ∧ M.rootState v x s)
    (fun w' ↦ M.causative_entails_resultState v y x w') w h

/-- For a result root the root state itself entails a prior change, so even the restitutive
attachment of *again* presupposes a change, (45): result roots never admit a truly restitutive
reading. -/
theorem againRestitutive_presup_entails_change {s : State}
    (hres : ∀ s, M.rootState v x s → ∃ e, M.become s e)
    (h : (M.againRestitutive ltS v x).presup s) : ∃ s', ltS s' s ∧ ∃ e, M.become s' e :=
  again_presup_mono (Q := fun s' ↦ ∃ e, M.become s' e) hres s h

end Verb.CosModel

end Again

namespace BeaversKoontzGarboden2020

open Verb
open Semantics

/-! ### The six representative roots -/

/-- √flat is a pure state root. -/
def flat : Root := { name := "flat", entailments := {.state "flat"}, position := some .complement }

/-- √jog is a pure manner-of-motion root. -/
def jog : Root :=
  { name := "jog", entailments := {.manner "jogging-gait"}, position := some .adjoined }

/-- √blossom is a result root with no specified manner or cause, an internally caused change
of state. -/
def blossom : Root :=
  { name := "blossom", entailments := {.result "flowering"}, position := some .complement }

/-- √crack is a caused-result root without a specified manner. -/
def crack : Root :=
  { name := "crack", entailments := {.result "fissured", .cause}, position := some .complement }

/-- √hand carries manner, cause and result in the adjoined position. The possession result is
not cancelable (*Mary handed John the book, #but it never came to be on his person*), so it is
entailed by the root rather than implicated. -/
def hand : Root :=
  { name := "hand",
    entailments := {.manner "by-hand-transfer", .result "in-recipient-possession", .cause},
    position := some .adjoined }

/-- √drown is a manner-of-killing root, carrying manner, cause and result in the complement
position. -/
def drown : Root :=
  { name := "drown",
    entailments := {.manner "submersion-in-liquid", .result "dead", .cause},
    position := some .complement }

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

/-- Each of the six roots fills a cell of (12). -/
theorem cells_attested :
    ∀ r ∈ [flat, jog, blossom, crack, hand, drown],
      ∃ p, r.position = some p ∧ (r.closedKinds, p) ∈ Root.Kinds.attestedCells := by decide

/-- √hand and √drown share a signature and differ only in position. -/
theorem hand_drown_differ_in_position :
    hand.closedKinds = drown.closedKinds ∧ hand.position ≠ drown.position := by decide

/-! ### Falsifying the Bifurcation Thesis -/

/-- √blossom entails a change of state, the templatic content of `v_become`, in the root, and so
falsifies Bifurcation without any manner or cause entailment. -/
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

/-- √flat, a pure state root, respects Bifurcation, its signature being bounded by the
ontological kinds. -/
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
def crackV : Verb := { form := "crack", frames := [ArgumentFrame.np], root := crack }

/-- `jog` the pure-manner activity verb (`Mary jogged`). -/
def jogV : Verb := { form := "jog", frames := [ArgumentFrame.intransitive], root := jog }

/-- √crack carries `.result`, so in any model its denotation entails the result state. The
non-cancelable result is derived from the signature of the root rather than stipulated. -/
theorem crack_denote_entails_result {Entity State T : Type*} [LinearOrder T]
    (M : Verb.CosModel Entity State T) (y x : Entity) (e : Event T)
    (h : M.denote crackV y x e) : ∃ e' s, M.become s e' ∧ M.rootState crackV x s :=
  M.denote_result_entails_resultState crackV y x e (by decide) h

/-- √jog has neither `.result` nor `.cause`, so its denotation is the bare manner core, with no
`become` and no result state. -/
theorem jog_denote_eq_manner {Entity State T : Type*} [LinearOrder T]
    (M : Verb.CosModel Entity State T) (y x : Entity) :
    M.denote jogV y x = M.manner jogV := by
  unfold Verb.CosModel.denote
  rw [ite_eq_right (by decide), ite_eq_right (by decide)]

/-! ### The same contrast at the template level ([rappaport-hovav-levin-1998])

`Semantics.Root.template` reads the event-structure template off a root's
collocational closure; the kinds proven above fix it, and `HasResultState`
reduces to carrying `result` (`Semantics.Root.template_hasResultState_iff`). So the
denotational result entailment (√crack) and the template result diagnostic are
*one fact* seen through `kinds`. -/

theorem flat_template : flat.template = .state := by decide
theorem jog_template : jog.template = .activity := by decide
theorem blossom_template : blossom.template = .achievement := by decide
theorem crack_template : crack.template = .accomplishment := by decide

/-- The template of √crack embeds a result state and that of √jog does not, which is the
*break* and *hit* contrast at the template layer. -/
theorem crack_template_hasResultState : crack.template.HasResultState := by decide

theorem jog_template_no_resultState : ¬ jog.template.HasResultState := by decide

/-- The template of √crack embeds a result state, so its denotation entails the result state in
any model. The template diagnostic and the denotational entailment are one fact about the kinds
of the root. -/
theorem crack_template_forces_denote_result {Entity State T : Type*}
    [LinearOrder T] (M : Verb.CosModel Entity State T) (y x : Entity)
    (e : Event T) (h : M.denote crackV y x e) :
    ∃ e' s, M.become s e' ∧ M.rootState crackV x s :=
  M.denote_result_from_template crackV crack_template_hasResultState y x e h

/-! ### The root hypothesis against Levin's class profiles -/

open ArgumentStructure

/-- A class Part II of [levin-1993] tests for the causative alternation and whose root
signature is recorded. -/
def TestedForCausative (c : LevinClass) : Prop :=
  c.rootEntailments.isSome ∧ c.Tests .causativeInchoative

instance : DecidablePred TestedForCausative := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- The tested classes on which the root hypothesis and the class pages disagree. The verbs of
creation and the psych causatives have causative-result roots that the hypothesis predicts to
alternate although the pages star the alternation. The other classes have pages that attest it
without a manner-free causative root, namely the manner-and-result roots, the internally caused
results, the pure-manner roots with causative uses, and the property-concept roots of the
emission classes. -/
def rootHypothesisResidue : Finset LevinClass :=
  {LevinClass.build, .create, .engender, .amuse,
    .split, .knead, .cooking, .grow, .calibratableChangeOfState, .pour, .coil, .roll, .rush,
    .lightEmission, .soundEmission, .substanceEmission}

/-- Outside the residue, the root hypothesis agrees with every tested class page. -/
theorem rootHypothesis_matches_profile :
    ∀ c : LevinClass, TestedForCausative c → c ∉ rootHypothesisResidue →
      (c.RootPredictsCausative ↔ c.Participates .causativeInchoative) := by
  decide +kernel

/-- The residue is exactly the tested classes on which they disagree. -/
theorem rootHypothesisResidue_disagrees :
    ∀ c ∈ rootHypothesisResidue, TestedForCausative c ∧
      ¬ (c.RootPredictsCausative ↔ c.Participates .causativeInchoative) := by
  decide +kernel

end BeaversKoontzGarboden2020
