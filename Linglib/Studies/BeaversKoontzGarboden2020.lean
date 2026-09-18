import Linglib.Semantics.Root.Defs
import Linglib.Semantics.ArgumentStructure.Verb
import Linglib.Semantics.ArgumentStructure.ChangeOfState
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

namespace BeaversKoontzGarboden2020

section Again

open Presupposition ArgumentStructure

/-! ### Sublexical *again* and the hierarchy of its readings

*Again* is a presupposition trigger that can attach at three points in the change-of-state
structure, the root, `vbecome` and `vcause`, which yields the three readings of *Mary flattened
the rug again*: the restitutive one, that the rug had been flat, the repetitive one over the
change, that it had flattened, and the repetitive one over the causation, that Mary had
flattened it. The entry for *again* is `Presupposition.again`, with the precedence between
eventualities as its relation. The hierarchy of the readings and the collapse of the
restitutive reading for result roots follow from the change-of-state entailments by the
monotonicity of the presupposition. -/

variable {Entity State Event : Type*} (M : ChangeOfStateModel Entity State Event)
  {ltS : State → State → Prop} {ltE : Event → Event → Prop} {P : Entity → State → Prop}
  {x y : Entity}

/-- *Again* attached low, to the root, modifies the root's state predicate `P`, which is the
restitutive reading. -/
def againRestitutive (ltS : State → State → Prop) (P : Entity → State → Prop) (x : Entity) :
    PartialProp State :=
  again ltS (P x)

/-- *Again* attached to `vbecomeP` is the repetitive reading over the change. -/
def againRepetitiveBecome (ltE : Event → Event → Prop) (P : Entity → State → Prop)
    (x : Entity) : PartialProp Event :=
  again ltE (M.vBecome P x)

/-- *Again* attached high, to `vcauseP`, is the repetitive reading over the causation. -/
def againRepetitiveCause (ltE : Event → Event → Prop) (P : Entity → State → Prop)
    (y x : Entity) : PartialProp Event :=
  again ltE (M.vCause (M.vBecome P x) y)

variable {M}

/-- In the upper step of the hierarchy, the presupposition of the repetitive reading over the
causation gives an earlier change, since a causing event brings one about. -/
theorem againRepetitiveCause_presup_entails_become {w : Event}
    (h : (againRepetitiveCause M ltE P y x).presup w) :
    ∃ w', ltE w' w ∧ ∃ e, M.vBecome P x e :=
  again_presup_mono (Q := fun _ ↦ ∃ e, M.vBecome P x e)
    (fun _ ↦ ChangeOfStateModel.exists_of_vCause) w h

/-- In the lower step of the hierarchy, the presupposition of the repetitive reading over the
change gives an earlier root state, since a change brings one about. -/
theorem againRepetitiveBecome_presup_entails_state {e : Event}
    (h : (againRepetitiveBecome M ltE P x).presup e) :
    ∃ e', ltE e' e ∧ ∃ s, M.become s e' ∧ P x s :=
  h

/-- End to end, the hierarchy says that Mary's having flattened the rug before entails that it
had been flat before. -/
theorem againRepetitiveCause_presup_entails_state {w : Event}
    (h : (againRepetitiveCause M ltE P y x).presup w) :
    ∃ w', ltE w' w ∧ ∃ e s, M.become s e ∧ P x s :=
  again_presup_mono (Q := fun _ ↦ ∃ e s, M.become s e ∧ P x s)
    (fun _ ↦ ChangeOfStateModel.exists_of_vCause) w h

/-- For a state predicate that entails change, even the restitutive attachment of *again*
presupposes a change, so result roots never admit a truly restitutive reading. -/
theorem againRestitutive_presup_entails_change {s : State} (hres : M.EntailsChange P)
    (h : (againRestitutive ltS P x).presup s) : ∃ s', ltS s' s ∧ ∃ e, M.become s' e :=
  again_presup_mono (Q := fun s' ↦ ∃ e, M.become s' e) (hres x) s h

end Again

end BeaversKoontzGarboden2020


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

/-! ### The entailments of the roots in a model

The kinds of a root are meaning postulates on its state predicate
(`ChangeOfStateModel.Respects`). In a model that respects the signature of √crack, a cracked
state arises from a caused change whatever template the root occurs in, while a model that
respects the signature of √flat may have a flat state that no change gave rise to. -/

section Model

open ArgumentStructure

variable {Entity State Event : Type*} {M : ChangeOfStateModel Entity State Event}
  {P : Entity → State → Prop} {Q : Event → Prop} {x : Entity} {s : State}

/-- In a model that respects the signature of √crack, a cracked state arises from a change
that some event causes. -/
theorem crack_entails_cause (h : M.Respects P Q crack.kinds) (hs : P x s) :
    ∃ e v, M.become s e ∧ M.cause v e :=
  h .cause (by decide) x s hs

/-- In a model that respects the signature of √drown, a drowned state arises from a change
whose every cause is an event of the root's manner. -/
theorem drown_entails_manner (h : M.Respects P Q drown.kinds) (hs : P x s) :
    ∃ e, M.become s e ∧ ∀ v, M.cause v e → Q v :=
  h .manner (by decide) x s hs

end Model

/-- A model without changes. -/
def unchanging : ArgumentStructure.ChangeOfStateModel Unit Unit Unit where
  become _ _ := False
  cause _ _ := False
  effector _ _ := False

/-- A model in which every state arises from a caused change. -/
def changing : ArgumentStructure.ChangeOfStateModel Unit Unit Unit where
  become _ _ := True
  cause _ _ := True
  effector _ _ := True

/-- The signature of √flat does not entail change, since the model without changes respects it
for a state predicate that holds. -/
theorem flat_not_entailsChange :
    unchanging.Respects (fun _ _ ↦ True) (fun _ ↦ True) flat.kinds ∧
      ¬ unchanging.EntailsChange (fun _ _ ↦ True) :=
  ⟨fun k hk ↦ by
      obtain rfl : k = .state := by revert k; decide
      trivial,
    fun h ↦ let ⟨_, he⟩ := h () () trivial; he⟩

/-- The signature of √crack is respected for a state predicate that holds, in the model where
every state arises from a caused change, and is not respected in the model without changes. -/
theorem crack_respects :
    changing.Respects (fun _ _ ↦ True) (fun _ ↦ True) crack.kinds ∧
      ¬ unchanging.Respects (fun _ _ ↦ True) (fun _ ↦ True) crack.kinds :=
  ⟨fun k hk ↦ by
      have : k = .result ∨ k = .cause := by revert k; decide
      rcases this with rfl | rfl
      · exact fun _ _ _ ↦ ⟨(), trivial⟩
      · exact fun _ _ _ ↦ ⟨(), (), trivial, trivial⟩,
    fun h ↦ let ⟨_, _, he, _⟩ := crack_entails_cause h (x := ()) (s := ()) trivial; he⟩

/-! ### The templates of the canonical realization rules

`Semantics.Root.template` reads a template off the collocational closure of a root's signature,
the canonical realization of Rappaport Hovav and Levin. The book does not adopt such rules; the
templates are used below only to state its hypothesis about the causative alternation. -/

theorem flat_template : flat.template = .state := by decide
theorem jog_template : jog.template = .activity := by decide
theorem blossom_template : blossom.template = .achievement := by decide
theorem crack_template : crack.template = .accomplishment := by decide

/-- The template of √crack embeds a result state and that of √jog does not, which is the
*break* and *hit* contrast at the template layer. -/
theorem crack_template_hasResultState : crack.template.HasResultState := by decide

theorem jog_template_no_resultState : ¬ jog.template.HasResultState := by decide

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
