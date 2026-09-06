import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.DeriveFintype
import Mathlib.Order.BooleanSubalgebra
import Mathlib.Order.Hom.CompleteLattice
import Linglib.Logic.Modal.Defs
import Linglib.Logic.Trivalent.Prop3
import Linglib.Data.Examples.Coppock2018

/-!
# Coppock's outlook-based semantics

Statements of opinion are evaluated at outlooks, refinements of possible worlds that settle
matters of opinion as well as of fact, in place of worlds supplemented with a judge. A
proposition is a function from outlooks to three truth values; it is objective when no
world's refinements split it into true and false, discretionary when some world's do, and
strongly discretionary when every world's do, each notion relative to an information state.
Faultless disagreement follows: asserting a proposition puts one at fault only if it is
objectively false at the world of the context, which no strongly discretionary proposition
ever is, while two agents whose doxastic states over outlooks accept and reject it genuinely
disagree. The Swedish subjective attitude verb *tycka* differs from *think* only in
presupposing, through the ∂ operator of the paper's Weak Kleene logic, that its complement
is strongly discretionary relative to the common ground, and the paper offers, as a parallel
to Kennedy and Willer, that *find* and *consider* would demand strong and mere
discretionariness. The paper's four-outlook model of accessibility and its Swedish and
English judgments are the rows of `Data/Examples/Coppock2018.json`, against which the
conditions on the three verbs are checked.

## Implementation notes

* The refinement relation is a map `ρ : Ω → W`, whose fibres are the refinement classes;
  that every world has an inhabited class, implicit in the paper's set-based definition of
  strong discretionariness and in its footnote 8, is the hypothesis `Function.Surjective ρ`
  where it matters. The classification predicates take the information state as a
  parameter, the unrelativised notions being the case of the universal state.
* The objective propositions of §3.1 form a Boolean subalgebra of the powerset of the
  outlooks, the image of the powerset of the worlds under preimage, and are order-isomorphic
  to it when every world is refined, the paper's footnote 8.
* Acceptance is the Kripke box over the agent's accessibility relation on outlooks, from
  `Logic/Modal/Defs.lean`, and rejection the box of falsity, stronger than the paper's
  gloss "holds in none" on a trivalent proposition but the reading its analysis of (38)
  uses. *Think* and *tycka* are trivalent propositions built with the Weak Kleene
  conjunction and ∂ of `Core/Data/Trivalent.lean`, so that presupposition projection
  through negation is the logic's rather than a stipulation.
* The formal fragment's syntax and translations (§5.1, §5.3), the context-of-utterance
  parameter, and the §4 pragmatics of assertion as a proposal are not modelled.

## TODO

* The felicity conditions on coordination and quantification under *tycka* ((20)–(27))
  need the issues raised by the complement, which the paper leaves to a theory of manner;
  their rows carry no model classification.
* A world-judge relativist rendering of the same data (§2, §3.4, §3.5.2) would let the
  contrast on opinionatedness (38) be stated as a theorem rather than prose.
* The paper argues (33) over the outlooks where its presupposition holds; on an open
  information state its own definition fails at the other world, so the row's common ground
  entails the presupposition, and the general condition on states wants stating.
* The prose on Fig. 2 says that from `o₁₀` and `o₀₀` agent `a` reaches "the one in which
  both `p` and `q` hold" while also rejecting `q`; the figure has `a` reach `o₁₀`, which the
  model follows.
* The footnote 8 isomorphism holds only when every world is refined; the paper does not
  state the hypothesis.
* Footnote 15 reports the presupposition filtered in a conditional, which the Weak Kleene
  connectives cannot do; the Middle Kleene conjunction of the substrate could, and the
  contrast wants stating as a theorem.
* [kennedy-willer-2022]'s pragmatic reworking of counterstance contingency and
  [anand-korotkova-2022]'s *de re* readings of *find* are the data on which the strong
  against mere discretionariness split could be tested rather than coded.

## References

* [E. Coppock, *Outlook-based semantics* (2018)][coppock-2018]
* [M. Kölbel, *Truth Without Objectivity* (2002)][kolbel-2002]
* [M. Kölbel, *Faultless disagreement* (2003)][kolbel-2003]
* [P. Lasersohn, *Context dependence, disagreement, and predicates of personal taste*
  (2005)][lasersohn-2005]
* [C. Kennedy, M. Willer, *Subjective attitudes and counterstance contingency*
  (2016)][kennedy-willer-2016]
* [D. Beaver, E. Krahmer, *A Partial Account of Presupposition Projection*
  (2001)][beaver-krahmer-2001]
* [S. C. Kleene, *Introduction to Metamathematics* (1952)][kleene-1952]
* [K. J. Sæbø, *Judgment Ascriptions* (2009)][saebo-2009]
* [T. Stephenson, *Judge Dependence, Epistemic Modals, and Predicates of Personal Taste*
  (2007)][stephenson-2007]
* [C. Kennedy, M. Willer, *Familiarity Inferences, Subjective Attitudes and Counterstance
  Contingency* (2022)][kennedy-willer-2022]
* [P. Anand, N. Korotkova, *How to Theorize about Subjective Language* (2022)][anand-korotkova-2022]
-/

namespace Coppock2018

open Trivalent ModalLogic

variable {W Ω : Type*} (ρ : Ω → W) (R : Ω → Ω → Prop) (p : Prop3 Ω) (C : Set Ω)

/-! ### Refinement and objective propositions (§3.1)

Outlooks refine worlds: each settles the facts of its world and the matters of opinion
besides. The refinement structure is a map from outlooks to worlds, the refinement class of a
world being its fibre, so classes are disjoint and in one-to-one correspondence with the
refined worlds, the paper's `∝`. -/

/-- A set of outlooks is an objective proposition when it corresponds to a set of worlds, a
union of refinement classes: a preimage of a set of worlds. A discretionary proposition is
one that is not. -/
def Objective (O : Set Ω) : Prop := ∃ V : Set W, O = ρ ⁻¹' V

/-- Objectivity is invariance across each refinement class: membership depends only on the
refined world. -/
theorem objective_iff_forall_mem_iff (O : Set Ω) :
    Objective ρ O ↔ ∀ o o', ρ o = ρ o' → (o ∈ O ↔ o' ∈ O) := by
  constructor
  · rintro ⟨V, rfl⟩ o o' h
    simp [h]
  · intro h
    refine ⟨ρ '' O, Set.Subset.antisymm (λ o ho => ⟨o, ho, rfl⟩) ?_⟩
    rintro o ⟨o', ho', heq⟩
    exact (h o' o heq).mp ho'

/-- Objectivity is saturation under the refinement map: the proposition already contains
every outlook sharing a world with one of its members. -/
theorem objective_iff_preimage_image (O : Set Ω) :
    Objective ρ O ↔ ρ ⁻¹' (ρ '' O) = O := by
  refine ⟨λ h => Set.Subset.antisymm ?_ (Set.subset_preimage_image ρ O), λ h => ⟨ρ '' O, h.symm⟩⟩
  rintro o ⟨o', ho', heq⟩
  exact ((objective_iff_forall_mem_iff ρ O).mp h o' o heq).mp ho'

/-- The objective propositions form a Boolean subalgebra of the powerset of the outlooks:
the image of the powerset of the worlds under preimage, so closure under `⊔`, `⊓` and `ᶜ` is
inherited wholesale. -/
def objectiveSubalgebra : BooleanSubalgebra (Set Ω) :=
  .map (CompleteLatticeHom.setPreimage ρ).toBoundedLatticeHom ⊤

@[simp] theorem mem_objectiveSubalgebra {O : Set Ω} :
    O ∈ objectiveSubalgebra ρ ↔ Objective ρ O := by
  simp [objectiveSubalgebra, Objective, eq_comm]

/-- When every world is refined by some outlook, the objective subalgebra is order-isomorphic
to the powerset of the worlds, the paper's footnote 8. -/
def objectiveOrderIso (hρ : Function.Surjective ρ) : Set W ≃o objectiveSubalgebra ρ where
  toFun V := ⟨ρ ⁻¹' V, (mem_objectiveSubalgebra ρ).mpr ⟨V, rfl⟩⟩
  invFun O := ρ '' O.1
  left_inv V := hρ.image_preimage V
  right_inv O := Subtype.ext
    ((objective_iff_preimage_image ρ O.1).mp ((mem_objectiveSubalgebra ρ).mp O.2))
  map_rel_iff' := hρ.preimage_subset_preimage_iff

/-! ### The three-valued classification relative to an information state (§3.5)

To carry presupposition, propositions are total functions from outlooks to true, false and
undefined; an information state is a set of outlooks, and the classification quantifies over
each refinement class restricted to the state. The unrelativised notions of the paper are the
case of the universal state. -/

/-- `p` is objectively false at `w`: false at every refinement of `w`. -/
def ObjectivelyFalseAt (w : W) : Prop := ∀ o, ρ o = w → p o = .false

/-- Objective relative to `C`: no refinement class restricted to `C` assigns `p` both true
and false. -/
def ObjectiveOn : Prop := ∀ o ∈ C, ∀ o' ∈ C, ρ o = ρ o' → p o = .true → p o' ≠ .false

/-- Discretionary relative to `C`: some refinement class restricted to `C` assigns `p` both
true and false. -/
def DiscretionaryOn : Prop := ∃ o ∈ C, ∃ o' ∈ C, ρ o = ρ o' ∧ p o = .true ∧ p o' = .false

/-- Strongly discretionary relative to `C`: every refinement class the state leaves nonempty
assigns `p` both true and false, a cut within every world the state leaves open. -/
def StronglyDiscretionaryOn : Prop :=
  ∀ w, (∃ o ∈ C, ρ o = w) → ∃ o ∈ C, ∃ o' ∈ C, ρ o = w ∧ ρ o' = w ∧ p o = .true ∧ p o' = .false

/-- Discretionary is exactly the failure of objective. -/
theorem discretionaryOn_iff_not_objectiveOn : DiscretionaryOn ρ p C ↔ ¬ ObjectiveOn ρ p C := by
  simp [DiscretionaryOn, ObjectiveOn]

/-- Strong discretionariness entails discretionariness on any nonempty state: the paper's
rendering of Kennedy and Willer, on which *find* demands radical counterstance contingency
and *consider* mere counterstance contingency, so whatever embeds under *find* embeds under
*consider*. -/
theorem StronglyDiscretionaryOn.discretionaryOn (h : StronglyDiscretionaryOn ρ p C)
    (hC : C.Nonempty) : DiscretionaryOn ρ p C :=
  let ⟨o₀, ho₀⟩ := hC
  let ⟨o, ho, o', ho', hwo, hwo', ht, hf⟩ := h (ρ o₀) ⟨o₀, ho₀, rfl⟩
  ⟨o, ho, o', ho', hwo.trans hwo'.symm, ht, hf⟩

/-- On the universal state, when every world is refined, strong discretionariness is the
paper's unrelativised definition: every world's refinements split `p`. -/
theorem stronglyDiscretionaryOn_univ_iff (hρ : Function.Surjective ρ) :
    StronglyDiscretionaryOn ρ p Set.univ ↔
      ∀ w, ∃ o o', ρ o = w ∧ ρ o' = w ∧ p o = .true ∧ p o' = .false :=
  ⟨λ h w => let ⟨o, _, o', _, h₁, h₂, h₃, h₄⟩ := h w (let ⟨o, ho⟩ := hρ w; ⟨o, trivial, ho⟩)
    ⟨o, o', h₁, h₂, h₃, h₄⟩,
   λ h w _ => let ⟨o, o', h₁, h₂, h₃, h₄⟩ := h w; ⟨o, trivial, o', trivial, h₁, h₂, h₃, h₄⟩⟩

/-- For a bivalent proposition the revised classification agrees with the set-based one of
§3.1 on its positive extension. -/
theorem objectiveOn_univ_iff_objective_posExt (h : p.isBivalent) :
    ObjectiveOn ρ p Set.univ ↔ Objective ρ p.posExt := by
  rw [objective_iff_forall_mem_iff]
  constructor
  · intro hobj o o' hoo'
    have key : ∀ a b, ρ a = ρ b → p a = .true → p b = .true := λ a b hab ha =>
      (h b).resolve_right (hobj a trivial b trivial hab ha)
    exact ⟨key o o' hoo', key o' o hoo'.symm⟩
  · intro hinv o _ o' _ hoo' ht hf
    exact nomatch ((hinv o o' hoo').1 ht).symm.trans hf

section Decidability

variable [Fintype Ω] [DecidableEq W] [DecidablePred (· ∈ C)]

instance (w : W) : Decidable (ObjectivelyFalseAt ρ p w) := by
  unfold ObjectivelyFalseAt; infer_instance

instance : Decidable (ObjectiveOn ρ p C) := by unfold ObjectiveOn; infer_instance

instance : Decidable (DiscretionaryOn ρ p C) := by unfold DiscretionaryOn; infer_instance

instance [Fintype W] : Decidable (StronglyDiscretionaryOn ρ p C) := by
  unfold StronglyDiscretionaryOn; infer_instance

end Decidability

/-! ### The norm of accuracy and faultlessness (§3.2)

Being at fault is relative to the world of the context of utterance, which determines a
world and not an outlook: one is at fault for asserting a proposition iff it is objectively
false there. A strongly discretionary proposition is true at some refinement of every world
the state leaves open, so no one is ever at fault for asserting it, the faultlessness half of
faultless disagreement; contradiction is supplied by the propositions being complements. -/

/-- `p` splits `w`: some refinement makes it true and another false. A disagreement about
`p` at such a world is faultless, the paper's footnote 12. -/
def SplitsAt (w : W) : Prop := (∃ o, ρ o = w ∧ p o = .true) ∧ ∃ o, ρ o = w ∧ p o = .false

/-- The norm of accuracy: at a world the proposition splits, no asserter of it is at fault. -/
theorem SplitsAt.not_objectivelyFalseAt {w : W} (h : SplitsAt ρ p w) :
    ¬ ObjectivelyFalseAt ρ p w := λ hf =>
  let ⟨⟨o, hwo, ht⟩, _⟩ := h
  nomatch (hf o hwo).symm.trans ht

/-- A strongly discretionary proposition splits every world the state leaves open, so any
disagreement about it there is faultless. -/
theorem splitsAt_of_stronglyDiscretionaryOn (h : StronglyDiscretionaryOn ρ p C) {w : W}
    (hw : ∃ o ∈ C, ρ o = w) : SplitsAt ρ p w :=
  let ⟨o, _, o', _, hwo, hwo', ht, hf⟩ := h w hw
  ⟨⟨o, hwo, ht⟩, ⟨o', hwo', hf⟩⟩

/-- A strongly discretionary proposition is never objectively false at a world the state
leaves open: its asserter is never at fault. -/
theorem not_objectivelyFalseAt_of_stronglyDiscretionaryOn (h : StronglyDiscretionaryOn ρ p C)
    {w : W} (hw : ∃ o ∈ C, ρ o = w) : ¬ ObjectivelyFalseAt ρ p w :=
  (splitsAt_of_stronglyDiscretionaryOn ρ p C h hw).not_objectivelyFalseAt

/-! ### Doxastic states, acceptance and disagreement (§3.3)

An agent's doxastic state at an outlook is the set of outlooks accessible from it, so states
vary from outlook to outlook: whether an agent holds a belief is itself settled by outlooks.
To accept a proposition is for it to hold throughout one's accessible outlooks, the Kripke
box over outlooks with the proposition's truth as valuation. -/

/-- An agent with accessibility `R` accepts `p` at `o`: `p` is true at every accessible
outlook. -/
def Accepts : Ω → Prop := box R (p · = .true)

/-- An agent with accessibility `R` rejects `p` at `o`: `p` is false at every accessible
outlook, which is stronger than not accepting it. -/
def Rejects : Ω → Prop := box R (p · = .false)

/-- Two agents disagree about `p` at `o` when one accepts it and the other rejects it. -/
def DisagreeAt (R₁ R₂ : Ω → Ω → Prop) (o : Ω) : Prop := Accepts R₁ p o ∧ Rejects R₂ p o

/-- An agent is opinionated about `p` at `o` when they accept or reject it; the paper's (38)
denies opinionatedness without contradiction. -/
def Opinionated (o : Ω) : Prop := Accepts R p o ∨ Rejects R p o

/-- An accessibility relation is a matter of fact when it depends on an outlook only through
the world it refines: the paper's assumption that whether an agent holds a belief is settled
by worlds. -/
def ObjectiveRel : Prop := ∀ o o' o'', ρ o = ρ o' → (R o o'' ↔ R o' o'')

/-- Acceptance under a factual accessibility relation is constant across a refinement class,
so disagreement at an outlook is disagreement at its world. -/
theorem accepts_iff_of_objectiveRel (hR : ObjectiveRel ρ R) {o o' : Ω} (h : ρ o = ρ o') :
    Accepts R p o ↔ Accepts R p o' :=
  box_congr_left λ o'' => hR o o' o'' h

section Decidability

variable [Fintype Ω] [DecidableRel R] (o : Ω)

instance : Decidable (Accepts R p o) := by unfold Accepts box; infer_instance

instance : Decidable (Rejects R p o) := by unfold Rejects box; infer_instance

instance (R₂ : Ω → Ω → Prop) [DecidableRel R₂] : Decidable (DisagreeAt p R R₂ o) := by
  unfold DisagreeAt; infer_instance

instance : Decidable (Opinionated R p o) := by unfold Opinionated; infer_instance

instance [DecidableEq W] : Decidable (ObjectiveRel ρ R) := by unfold ObjectiveRel; infer_instance

end Decidability

/-! ### Subjective attitude verbs (§3.5, §5)

English *think* and Swedish *tycka* 'think[opinion]' both denote doxastic acceptance; *tycka*
alone carries the presupposition that its complement is strongly discretionary relative to the
information state, (32) `∂(discretionary(φ)) ∧ □φ` in the paper's Weak Kleene logic, on
which an undefined conjunct makes the conjunction undefined. -/

variable [DecidablePred (Accepts R p)]

/-- *think* (31): bare doxastic acceptance. -/
def think : Prop3 Ω := λ o => ofProp (Accepts R p o)

variable [Decidable (StronglyDiscretionaryOn ρ p C)]

/-- *tycka* (32): the presupposition that the complement is strongly discretionary relative
to `C`, conjoined by Weak Kleene conjunction with acceptance. -/
def tycka : Prop3 Ω := λ o =>
  meetWeak (presuppose (ofProp (StronglyDiscretionaryOn ρ p C))) (ofProp (Accepts R p o))

variable (o : Ω)

/-- A *tycka* report is undefined exactly when its complement is not strongly discretionary
relative to the state: the subjectivity requirement is a presupposition, (28)–(29). -/
theorem tycka_eq_indet_iff : tycka ρ R p C o = .indet ↔ ¬ StronglyDiscretionaryOn ρ p C := by
  simp [tycka, meetWeak_presuppose_eq_indet_iff]

/-- A *tycka* report is true iff its complement is strongly discretionary and the agent
accepts it. -/
theorem tycka_eq_true_iff :
    tycka ρ R p C o = .true ↔ StronglyDiscretionaryOn ρ p C ∧ Accepts R p o := by
  simp [tycka, meetWeak_presuppose_eq_true_iff]

/-- *tycka* and *think* agree wherever the former is defined: the verbs differ only in the
presupposition. -/
theorem tycka_eq_think_of_ne_indet (h : tycka ρ R p C o ≠ .indet) :
    tycka ρ R p C o = think R p o := by
  have hS := not_not.1 ((tycka_eq_indet_iff ρ R p C o).not.1 h)
  simp only [tycka, think, hS, ofProp_true, presuppose_true, meetWeak_true_left]

/-- The presupposition projects through negation: *I don't think[opinion] it's Tuesday* is
undefined in the same states as the unnegated report, (28). -/
theorem neg_tycka_eq_indet_iff :
    neg (tycka ρ R p C o) = .indet ↔ ¬ StronglyDiscretionaryOn ρ p C :=
  neg_eq_indet_iff.trans (tycka_eq_indet_iff ρ R p C o)

/-- An objective complement is presupposition failure for *tycka* on any nonempty state:
the *#I think[opinion] it's Tuesday* effect, (2b), (28). -/
theorem tycka_eq_indet_of_objectiveOn (hobj : ObjectiveOn ρ p C) (hC : C.Nonempty) :
    tycka ρ R p C o = .indet :=
  (tycka_eq_indet_iff ρ R p C o).2 λ h =>
    let ⟨o₀, ho₀⟩ := hC
    let ⟨o₁, ho₁, o₂, ho₂, hw₁, hw₂, ht, hf⟩ := h (ρ o₀) ⟨o₀, ho₀, rfl⟩
    hobj o₁ ho₁ o₂ ho₂ (hw₁.trans hw₂.symm) ht hf

/-! ### The chili model (§3.3, Fig. 2)

Four outlooks `o_pq` settle whether the chili is tasty, `p`, and whether the speaker is an
opera singer, `q`; worlds settle only `q`. Agent `a` reaches from every outlook the one
tasty outlook of its world, and agent `b` reaches the non-tasty singer outlook from the
singer world and both tasty outlooks from the other, so `a` accepts `p` everywhere while
`b` accepts it in the non-singer world and rejects it in the singer world: the two disagree
about `p` at `o₁₁` and `o₀₁` and agree about `q` there, and `b` is unopinionated about `q`
elsewhere. Both relations are matters of fact, so acceptance is constant across each
refinement class. The hybrid (10) and the presupposing complements (33) and (34), for which
the paper gives no model, are read on the same two coordinates. -/

namespace Chili

/-- An outlook `(tasty?, singer?)`. -/
abbrev Outlook := Bool × Bool

/-- Worlds settle the objective coordinate. -/
def world : Outlook → Bool := Prod.snd

/-- `p`, *the chili is tasty*. -/
def tasty : Prop3 Outlook := λ o => ofBool o.1

/-- `q`, *I am an opera singer*. -/
def opera : Prop3 Outlook := λ o => ofBool o.2

/-- *John is a sexy linguist* (10), the objective coordinate read as linguisthood. -/
def sexyLinguist : Prop3 Outlook := λ o => ofBool (o.1 && o.2)

/-- *It's terrible that he dumped her* (33): defined only where he did, the objective
coordinate, and then settled by the discretionary one. -/
def terribleDumped : Prop3 Outlook := λ o => if o.2 then ofBool o.1 else .indet

/-- *She doesn't care that he is an idiot* (34): defined only where he is, the discretionary
coordinate, and then settled by the objective one. -/
def caresNotIdiot : Prop3 Outlook := λ o => if o.1 then ofBool o.2 else .indet

/-- Agent `a` reaches the tasty outlook of the current world. -/
def accessA : Outlook → Outlook → Prop := λ o o' => o' = (.true, o.2)

instance : DecidableRel accessA := λ _ _ => by unfold accessA; infer_instance

/-- Agent `b` reaches the non-tasty outlook from the singer world and both tasty outlooks
from the other. -/
def accessB : Outlook → Outlook → Prop :=
  λ o o' => (o.2 = .true → o' = (.false, .true)) ∧ (o.2 = .false → o'.1 = .true)

instance : DecidableRel accessB := λ _ _ => by unfold accessB; infer_instance

theorem objectiveRel_accessA : ObjectiveRel world accessA := by decide

theorem objectiveRel_accessB : ObjectiveRel world accessB := by decide

/-- The information states of the model: open, or with the objective coordinate given, or
with the discretionary one given. -/
inductive CommonGround
  | open | objectiveGiven | discretionaryGiven
  deriving DecidableEq, Fintype

/-- The outlooks a common ground leaves open. -/
def CommonGround.toSet : CommonGround → Set Outlook
  | .open => Set.univ
  | .objectiveGiven => {o | o.2 = .true}
  | .discretionaryGiven => {o | o.1 = .true}

instance (cg : CommonGround) : DecidablePred (· ∈ cg.toSet) := by
  cases cg <;> simp only [CommonGround.toSet] <;> infer_instance

/-- *Tasty* is strongly discretionary. -/
theorem stronglyDiscretionaryOn_tasty : StronglyDiscretionaryOn world tasty Set.univ := by
  decide

/-- *Opera singer* is objective. -/
theorem objectiveOn_opera : ObjectiveOn world opera Set.univ := by decide

/-- The hybrid (10) is discretionary, cutting the linguist world's refinements. -/
theorem discretionaryOn_sexyLinguist : DiscretionaryOn world sexyLinguist Set.univ := by
  decide

/-- The hybrid is not strongly discretionary: false at every refinement of the non-linguist
world. -/
theorem not_stronglyDiscretionaryOn_sexyLinguist :
    ¬ StronglyDiscretionaryOn world sexyLinguist Set.univ := by
  decide

/-- The hybrid is strongly discretionary once the linguist world is given: *Ebba tycker att
Jonas är en sexig lingvist* (15)–(17) is acceptable only in a context where Jonas is taken
to be a linguist. -/
theorem stronglyDiscretionaryOn_sexyLinguist_objectiveGiven :
    StronglyDiscretionaryOn world sexyLinguist CommonGround.objectiveGiven.toSet := by
  decide

/-- Presupposition placement, (33): a discretionary assertion with an objective
presupposition is strongly discretionary once the presupposition is given. -/
theorem stronglyDiscretionaryOn_terribleDumped_objectiveGiven :
    StronglyDiscretionaryOn world terribleDumped CommonGround.objectiveGiven.toSet := by
  decide

/-- Presupposition placement, (34): an objective assertion with a discretionary
presupposition is strongly discretionary on no information state. -/
theorem not_stronglyDiscretionaryOn_caresNotIdiot (cg : CommonGround) :
    ¬ StronglyDiscretionaryOn world caresNotIdiot cg.toSet := by
  decide +revert

/-- `a` accepts `p` everywhere. -/
theorem accepts_accessA_tasty (o : Outlook) : Accepts accessA tasty o := by decide +revert

/-- `b` accepts `p` exactly in the non-singer world and rejects it exactly in the singer
world. -/
theorem accepts_accessB_tasty_iff (o : Outlook) : Accepts accessB tasty o ↔ o.2 = .false := by
  decide +revert

theorem rejects_accessB_tasty_iff (o : Outlook) : Rejects accessB tasty o ↔ o.2 = .true := by
  decide +revert

/-- The two disagree about `p` exactly in the singer world, `o₁₁` and `o₀₁`. -/
theorem disagreeAt_tasty_iff (o : Outlook) :
    DisagreeAt tasty accessA accessB o ↔ o.2 = .true := by
  decide +revert

/-- Both accept `q` in the singer world; in the other, `a` rejects it and `b` is
unopinionated, so they never disagree about `q`. -/
theorem accepts_accessA_opera_iff (o : Outlook) : Accepts accessA opera o ↔ o.2 = .true := by
  decide +revert

theorem accepts_accessB_opera_iff (o : Outlook) : Accepts accessB opera o ↔ o.2 = .true := by
  decide +revert

theorem rejects_accessA_opera_iff (o : Outlook) : Rejects accessA opera o ↔ o.2 = .false := by
  decide +revert

theorem not_opinionated_accessB_opera (o : Outlook) (h : o.2 = .false) :
    ¬ Opinionated accessB opera o := by
  revert o; decide

theorem not_disagreeAt_opera (o : Outlook) :
    ¬ DisagreeAt opera accessA accessB o ∧ ¬ DisagreeAt opera accessB accessA o := by
  decide +revert

/-- The chili dialogue (3) is faultless: no world makes *tasty* objectively false. -/
theorem not_objectivelyFalseAt_tasty (w : Bool) : ¬ ObjectivelyFalseAt world tasty w :=
  not_objectivelyFalseAt_of_stronglyDiscretionaryOn world tasty Set.univ
    stronglyDiscretionaryOn_tasty ⟨(.true, w), trivial, rfl⟩

/-- The doctor dialogue (6) contrast: asserting *I am an opera singer* in the non-singer
world violates the norm of accuracy. -/
theorem objectivelyFalseAt_opera : ObjectivelyFalseAt world opera .false := by decide

/-- So does asserting the hybrid (10) where John is no linguist, (12). -/
theorem objectivelyFalseAt_sexyLinguist : ObjectivelyFalseAt world sexyLinguist .false := by
  decide

/-- *Tycka* reports of *tasty* are defined everywhere and true for `a`. -/
theorem tycka_tasty (o : Outlook) : tycka world accessA tasty Set.univ o = .true := by
  decide +revert

/-- *Tycka* reports of *opera singer* are undefined. -/
theorem tycka_opera (o : Outlook) : tycka world accessA opera Set.univ o = .indet := by
  decide +revert

end Chili

/-! ### The paper's judgments

The rows of `Data/Examples/Coppock2018.json` with a `complement` feature denote a
proposition of the chili model, their `commonGround` feature an information state, and their
`verb` a subjective attitude verb: *tycka* under the paper's condition (19), *find* and
*consider* under the parallel it offers to Kennedy and Willer. Which predicates are
discretionary is the theory's lexical assumption, as the paper says of *doctor* and *tasty*,
so the rows with a bare taste or factual complement check consistency only; the predictions
are the model theorems above, the hybrid rescued by a common ground ((15)–(17)),
presupposition placement ((33) against (34)) and the split of *find* from *consider* on the
hybrid (37). -/

/-- The model proposition a row's complement denotes. -/
def complements : List (String × Prop3 Chili.Outlook) :=
  [("discretionary", Chili.tasty), ("objective", Chili.opera), ("hybrid", Chili.sexyLinguist),
    ("presupObjective", Chili.terribleDumped), ("presupDiscretionary", Chili.caresNotIdiot)]

/-- The common ground a row names. -/
def commonGrounds : List (String × Chili.CommonGround) :=
  [("open", .open), ("objectiveGiven", .objectiveGiven),
    ("discretionaryGiven", .discretionaryGiven)]

/-- The condition a subjective attitude verb places on its complement: strong
discretionariness, or mere discretionariness. -/
inductive VerbCondition
  | strong | mere
  deriving DecidableEq

/-- The condition as a predicate on a proposition of the chili model relative to a state. -/
def VerbCondition.Holds : VerbCondition → Prop3 Chili.Outlook → Set Chili.Outlook → Prop
  | .strong, p, C => StronglyDiscretionaryOn Chili.world p C
  | .mere, p, C => DiscretionaryOn Chili.world p C

instance (vc : VerbCondition) (p : Prop3 Chili.Outlook) (cg : Chili.CommonGround) :
    Decidable (vc.Holds p cg.toSet) := by
  cases vc <;> simp only [VerbCondition.Holds] <;> infer_instance

/-- *tycka* demands strong discretionariness (19); that *find* demands the same and
*consider* mere discretionariness is the parallel to Kennedy and Willer the paper offers,
leaving the difference between the verbs open. -/
def verbConditions : List (String × VerbCondition) :=
  [("tycka", .strong), ("find", .strong), ("consider", .mere)]

/-- Row consistency: a subjective attitude report is acceptable exactly when its complement
meets the verb's condition relative to the common ground, open unless the row names one. A
complement the model does not read fails the check outright. -/
theorem verb_rows : ∀ row ∈ Examples.all, ∀ vc ∈ row.parse? "verb" verbConditions,
    ∀ c ∈ row.feature? "complement", ∃ p ∈ complements.lookup c,
      ∃ cg ∈ commonGrounds.lookup ((row.feature? "commonGround").getD "open"),
        (row.judgment = .acceptable ↔ vc.Holds p cg.toSet) := by
  decide

end Coppock2018
