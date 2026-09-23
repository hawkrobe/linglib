module

public import Mathlib.Data.Fintype.Sigma
public import Linglib.Semantics.Causation.Morphological

/-!
# Hafeez (2025): Agentivity and causation in Urdu

[hafeez-2025] asks which Urdu causal constructions speakers accept for which causal scenes. The
scenes are the 43 video clips of the Causality Across Languages project (Table 3), and they vary
along three variables: the causer is an intentional human (IHCr), an accidental human (AHCr) or a
natural force (NFCr); the second participant of the chain is a controlling human causee
(ContrHCEAF), a physically or a psychologically impacted human (PhysImpHCEAF, PsychImpHCEAF) or
an inanimate affectee (InanCEAF); and a third participant does or does not mediate the chain
(Mediation). A scene is a `Scene`, and each variable is a `Feature` of it.

The acceptability study (chapter 5) fits one conditional inference tree per response type. Each
leaf of a tree is a conjunction of signed features such as [+IHCr, -Mediation, +InanCEAF], and
the leaf with the highest share of ceiling ratings is the response type's hypothesized semantic
prototype when that share exceeds 50% (Table 18). The seven response types are the lexical
ergative LEX-ERG (ergative causer, transitive verb), the lexical instrumental LEX-INST
(instrumental causer, intransitive verb), the lexical dative LEX-DAT (dative causee or affectee,
infinitive and light verb), the morphological causative verb MCV (the indirect causative *-va*;
verbs with the direct causative *-aa* count as lexical), the adverbial ADV (two clauses joined by
*keyoonkeh* 'because'), the non-sentential cause adjunct NCA (a cause NP with *=par*,
*wajhan=se* or *=se*) and the non-sentential causer adjunct NCrA (a causer NP with
*wajhan=se*).

* `Tree.countP_leaves`: the leaves of any such tree partition the scenes, so every scene falls
  under exactly one leaf.
* `summary_iff_prototype`: the prototypes summarized in Tables 19 and 25 denote the tree leaves,
  LEX-ERG's only on scenes the clips can stage (`Scene.Stageable`), since its summary drops the
  leaf's [-Mediation] (`lexErg_summary_not_prototype`). ADV is the exception: Table 18 prints the
  signs of its tree's InanCEAF split reversed, and the summaries copy the misprint, so they
  name the complement of the prototype (`adv_summary_iff_not_prototype`).
* The agentivity reading of the prototypes in the chapter's conclusion (`lexErg_full`,
  `ncrA_nonagentive`, …) follows from the prototypes and the agentivity degrees of the
  participants.
* `individual_le_prototype`: the production study's preferred scenes (chapter 6, Table 25)
  refine the acceptability prototypes, the dovetailing the abstract reports; the combined
  production model's NCA preference does not (`nca_combined_not_le_prototype`).
* `lexErg_mcv_mediation`: the LEX-ERG prototype is unmediated and the MCV prototype mediated, so
  the Urdu prototypes order the lexical and the morphological causative as [comrie-1989]'s
  compactness generalization demands (`lexErg_mcv_comrieMonotone`).

## Implementation notes

A scene follows the clip-name code of Appendix L, which reproduces the response counts of
Table 18's leaves; the predictor table as printed (Table 4) instead codes clips 11 and 21 with an
inanimate second participant, clip 22 without one, and clip 1 as psychologically impacted.
The ADV tree is transcribed with the InanCEAF signs of section 5.3.5, which puts the 90.8% peak
on [-InanCEAF]; with the signs as Table 18 prints them, its 336-response leaf would be the 15
clips with an inanimate second participant, 180 responses.

The second participant is one variable with four values, so a scene type such as
[-ContrHCEAF, +InanCEAF] and its shorter form [+InanCEAF] are equivalent, which is how Table 18's
LEX-INST leaf and the LEX-INST prototype of Table 19 agree. The scene's mediation is the
substrate's `Causation.Morphological.Mediation`: [+Mediation] is a third participant between
causer and result, the narrow sense of directness the dissertation distinguishes from the broad
one.

## TODO

The percentages of ceiling ratings are not recorded, so each prototype is identified by the node
number of its leaf in Table 18 rather than derived as the maximal leaf above 50%; derive it once
linglib has a format for experimental results. Table 19 prints the peaks of NCA and NCrA swapped
relative to Table 18.

## References

* [hafeez-2025]
* [bohnemeyer-2004]
* [comrie-1989]
-/

@[expose] public section

namespace Hafeez2025

open Causation.Morphological

/-! ### Scenes -/

/-- The causer of a clip. -/
inductive Causer where
  /-- IHCr: acts intentionally and in control. -/
  | intentionalHuman
  /-- AHCr: acts accidentally, without intention or control. -/
  | accidentalHuman
  /-- NFCr: a natural force. -/
  | naturalForce
  deriving DecidableEq, Repr, Fintype

/-- The second participant of the causal chain: a causee when it is an induced agent, an
affectee when it is a patient. -/
inductive CauseeAffectee where
  /-- ContrHCEAF: a human who controls the induced action. -/
  | controlling
  /-- PhysImpHCEAF: a human impacted physically. -/
  | physicallyImpacted
  /-- PsychImpHCEAF: a human impacted psychologically. -/
  | psychologicallyImpacted
  /-- InanCEAF: an inanimate affectee. -/
  | inanimate
  deriving DecidableEq, Repr, Fintype

/-- A causal scene: its causer, its second participant, and whether a third participant
mediates the chain. -/
structure Scene where
  causer : Causer
  causeeAffectee : CauseeAffectee
  mediation : Mediation
  deriving DecidableEq, Repr, Fintype

/-- A scene the clips can stage: a mediated chain's second participant is a human causee, never
an inanimate affectee. Every mediated clip of Table 3 has a human in second position of its
Appendix L name code, and the dissertation notes that in the clips an intentional causer acting
on an inanimate affectee is by necessity unmediated. -/
def Scene.Stageable (s : Scene) : Prop :=
  s.mediation = .indirect → s.causeeAffectee ≠ .inanimate

instance : DecidablePred Scene.Stageable := fun _ ↦ inferInstanceAs (Decidable (_ → _))

/-! ### Features and scene types -/

/-- The binary variables of the analyses (Appendix L). -/
inductive Feature where
  | ihcr | ahcr | nfcr
  | contr | physImp | psychImp | inan
  | mediation
  deriving DecidableEq, Repr

/-- The scenes a feature is true of. -/
def Feature.Holds : Feature → Scene → Prop
  | .ihcr, s => s.causer = .intentionalHuman
  | .ahcr, s => s.causer = .accidentalHuman
  | .nfcr, s => s.causer = .naturalForce
  | .contr, s => s.causeeAffectee = .controlling
  | .physImp, s => s.causeeAffectee = .physicallyImpacted
  | .psychImp, s => s.causeeAffectee = .psychologicallyImpacted
  | .inan, s => s.causeeAffectee = .inanimate
  | .mediation, s => s.mediation = .indirect

instance (f : Feature) : DecidablePred f.Holds := fun _ ↦ by
  cases f <;> unfold Feature.Holds <;> infer_instance

/-- A signed feature, [+F] or [-F]. -/
inductive Literal where
  | pos (f : Feature)
  | neg (f : Feature)
  deriving DecidableEq, Repr

/-- The scenes a signed feature is true of. -/
def Literal.Holds : Literal → Scene → Prop
  | .pos f, s => f.Holds s
  | .neg f, s => ¬f.Holds s

instance (l : Literal) : DecidablePred l.Holds := fun _ ↦ by
  cases l <;> unfold Literal.Holds <;> infer_instance

/-- The opposite sign. -/
def Literal.negate : Literal → Literal
  | .pos f => .neg f
  | .neg f => .pos f

@[simp] theorem Literal.holds_negate (l : Literal) (s : Scene) : l.negate.Holds s ↔ ¬l.Holds s := by
  cases l <;> simp [negate, Holds]

/-- A scene type, a conjunction of signed features. -/
abbrev SceneType := List Literal

/-- The scenes of a scene type. -/
def SceneType.Holds (t : SceneType) (s : Scene) : Prop := ∀ l ∈ t, l.Holds s

instance (t : SceneType) : DecidablePred t.Holds := fun _ ↦ List.decidableBAll _ _

@[simp] theorem SceneType.holds_nil (s : Scene) : SceneType.Holds [] s := by simp [Holds]

@[simp] theorem SceneType.holds_cons (l : Literal) (t : SceneType) (s : Scene) :
    SceneType.Holds (l :: t) s ↔ l.Holds s ∧ t.Holds s := by simp [Holds]

/-! ### Conditional inference trees -/

/-- A binary conditional inference tree: an inner node tests a signed feature, sending the scenes
that pass it left. -/
inductive Tree where
  | leaf
  | node (test : Literal) (pass fail : Tree)

/-- The number of nodes. -/
def Tree.size : Tree → ℕ
  | .leaf => 1
  | .node _ p f => p.size + f.size + 1

/-- The leaves of a tree whose root is node `n`, numbered in preorder as the dissertation's tree
plots number them, each with the scene type of its path. -/
def Tree.leaves : Tree → ℕ → List (ℕ × SceneType)
  | .leaf, n => [(n, [])]
  | .node l p f, n =>
      (p.leaves (n + 1)).map (Prod.map id (l :: ·)) ++
        (f.leaves (n + 1 + p.size)).map (Prod.map id (l.negate :: ·))

/-- The leaves of a tree partition the scenes: each scene falls under exactly one leaf. -/
theorem Tree.countP_leaves (t : Tree) (n : ℕ) (s : Scene) :
    (t.leaves n).countP (fun p ↦ p.2.Holds s) = 1 := by
  induction t generalizing n with
  | leaf => simp [leaves]
  | node l p f ihp ihf =>
    by_cases h : l.Holds s <;>
      simp [leaves, List.countP_append, List.countP_map, Function.comp_def, h, ihp, ihf]

/-! ### Response types -/

/-- The seven response types of the acceptability study. -/
inductive ResponseType where
  | lexErg | lexInst | lexDat | mcv | adv | nca | ncrA
  deriving DecidableEq, Repr, Fintype

namespace ResponseType

open Literal Feature Tree

/-- The response type's conditional inference tree (Table 18). -/
def tree : ResponseType → Tree
  | .lexErg => node (neg ihcr) leaf (node (pos mediation) leaf (node (pos inan) leaf leaf))
  | .lexInst =>
      node (pos ihcr) (node (pos psychImp) leaf leaf)
        (node (neg contr) (node (pos inan) leaf leaf) leaf)
  | .lexDat => node (pos contr) leaf (node (pos nfcr) leaf leaf)
  | .mcv =>
      node (pos mediation) (node (neg ihcr) leaf (node (pos contr) leaf leaf))
        (node (pos contr) leaf leaf)
  | .adv => node (pos inan) (node (pos ihcr) leaf leaf) leaf
  | .nca => node (neg inan) (node (neg nfcr) leaf leaf) leaf
  | .ncrA => node (pos inan) (node (neg ihcr) leaf leaf) (node (pos nfcr) leaf leaf)

/-- The node of the leaf with the peak share of ceiling ratings, when that share exceeds 50%
(Table 18). LEX-DAT peaks at 41.7%, below the threshold. -/
def peak : ResponseType → Option ℕ
  | .lexErg => some 6
  | .lexInst => some 7
  | .lexDat => none
  | .mcv => some 5
  | .adv => some 5
  | .nca => some 3
  | .ncrA => some 6

/-- The hypothesized semantic prototype: the scene type of the peak leaf. -/
def prototype (r : ResponseType) : Option SceneType :=
  r.peak.bind ((r.tree.leaves 1).lookup ·)

/-- The scenes of the response type's prototype. -/
def Prototypical (r : ResponseType) (s : Scene) : Prop := ∃ t ∈ r.prototype, t.Holds s

instance (r : ResponseType) : DecidablePred r.Prototypical := fun s ↦
  decidable_of_iff (∃ t ∈ r.prototype.toList, t.Holds s) (by simp [Prototypical])

/-- The prototype as the summary tables print it (Tables 19 and 25). -/
def summary : ResponseType → Option SceneType
  | .lexErg => some [pos ihcr, pos inan]
  | .lexInst => some [neg ihcr, pos inan]
  | .lexDat => none
  | .mcv => some [pos mediation, pos ihcr, pos contr]
  | .adv => some [pos inan]
  | .nca => some [neg inan, neg nfcr]
  | .ncrA => some [neg inan, pos nfcr]

/-- The scene type the production study's model for the response type alone prefers it for
(Table 25). -/
def individualPreference : ResponseType → Option SceneType
  | .lexErg => some [pos inan, pos ihcr]
  | .nca => some [neg nfcr, pos psychImp]
  | .ncrA => some [neg inan, pos nfcr, pos physImp]
  | _ => none

/-- The scene type the production study's model of all response types together prefers the
response type for (Table 25). -/
def combinedPreference : ResponseType → Option SceneType
  | .lexErg => some [pos inan, pos ihcr]
  | .nca => some [pos psychImp]
  | .ncrA => some [pos nfcr, pos physImp]
  | _ => none

end ResponseType

open ResponseType

/-- Only LEX-DAT has no prototype. -/
theorem prototype_eq_none_iff (r : ResponseType) : r.prototype = none ↔ r = .lexDat := by
  cases r <;> decide

/-- Every prototype is instantiated by a scene the clips can stage, so the statements about
prototypical scenes below are not vacuous. -/
theorem exists_stageable_prototypical (r : ResponseType) (hr : r ≠ .lexDat) :
    ∃ s : Scene, s.Stageable ∧ r.Prototypical s := by
  cases r <;> first | exact absurd rfl hr | decide

/-- The summary tables print the tree leaves: on the scenes the clips can stage, each summary
prototype but ADV's holds of exactly the scenes of its leaf. -/
theorem summary_iff_prototype (r : ResponseType) (hr : r ≠ .adv) (s : Scene) (hs : s.Stageable) :
    (∃ t ∈ r.summary, t.Holds s) ↔ r.Prototypical s := by
  revert s; cases r <;> first | exact absurd rfl hr | decide

/-- Apart from LEX-ERG and ADV, the summaries agree with the leaves on every scene. -/
theorem summary_iff_prototype_of_ne (r : ResponseType) (hr₁ : r ≠ .lexErg) (hr₂ : r ≠ .adv)
    (s : Scene) : (∃ t ∈ r.summary, t.Holds s) ↔ r.Prototypical s := by
  revert s; cases r <;> first | exact absurd rfl hr₁ | exact absurd rfl hr₂ | decide

/-- ADV's printed prototype [+InanCEAF] is the complement of its peak leaf [-InanCEAF]. -/
theorem adv_summary_iff_not_prototype (s : Scene) :
    (∃ t ∈ adv.summary, t.Holds s) ↔ ¬adv.Prototypical s := by
  revert s; decide

/-- LEX-ERG's summary [+IHCr, +InanCEAF] drops its leaf's [-Mediation]: it also holds of a
mediated scene with an inanimate second participant, which the clips never stage. -/
theorem lexErg_summary_not_prototype :
    ∃ s : Scene, ¬s.Stageable ∧ (∃ t ∈ lexErg.summary, t.Holds s) ∧ ¬lexErg.Prototypical s :=
  ⟨⟨.intentionalHuman, .inanimate, .indirect⟩, by decide⟩

/-! ### Agentivity -/

/-- The degrees of agentivity, from intentionality and control, the ability to initiate or
terminate an action in [bohnemeyer-2004]'s sense: full for an intentional actor in control,
marginal for an actor involved accidentally, without intention or control, and induced for a
causee in control of an action it was induced to perform. -/
inductive Degree where
  | full | induced | marginal
  deriving DecidableEq, Repr

/-- A causer's agentivity; a natural force has none. -/
def Causer.degree : Causer → Option Degree
  | .intentionalHuman => some .full
  | .accidentalHuman => some .marginal
  | .naturalForce => none

/-- A second participant's agentivity; an inanimate affectee has none. -/
def CauseeAffectee.degree : CauseeAffectee → Option Degree
  | .controlling => some .induced
  | .physicallyImpacted | .psychologicallyImpacted => some .marginal
  | .inanimate => none

/-- LEX-ERG expresses the highest degree of agentivity: an intentional causer. -/
theorem lexErg_full (s : Scene) (h : lexErg.Prototypical s) : s.causer.degree = some .full := by
  revert s; decide

/-- LEX-INST expresses marginal agentivity or none. -/
theorem lexInst_marginal (s : Scene) (h : lexInst.Prototypical s) :
    s.causer.degree ≠ some .full ∧ s.causeeAffectee.degree = none := by
  revert s; decide

/-- MCV is causation by communication: an intentional causer and a causee in control. -/
theorem mcv_full_induced (s : Scene) (h : mcv.Prototypical s) :
    s.causer.degree = some .full ∧ s.causeeAffectee.degree = some .induced := by
  revert s; decide

/-- NCA wants an agentive causer, fully or marginally, and an agentive second participant,
partially or marginally. -/
theorem nca_agentive (s : Scene) (h : nca.Prototypical s) :
    s.causer.degree ≠ none ∧ s.causeeAffectee.degree ≠ none := by
  revert s; decide

/-- NCrA wants a non-agentive causer and an agentive second participant. -/
theorem ncrA_nonagentive (s : Scene) (h : ncrA.Prototypical s) :
    s.causer.degree = none ∧ s.causeeAffectee.degree ≠ none := by
  revert s; decide

/-! ### Production -/

/-- The production study's preferences refine the acceptability prototypes: every stageable
scene of a response type's individually preferred scene type is prototypical for it. -/
theorem individual_le_prototype (r : ResponseType) (s : Scene) (hs : s.Stageable) :
    (∃ t ∈ r.individualPreference, t.Holds s) → r.Prototypical s := by
  revert s; cases r <;> decide

/-- The combined model prefers NCA for the psychologically impacted second participant, a
preference that reaches past the NCA prototype to natural-force causers, as in the clip of a
woman startled by thunder. -/
theorem nca_combined_not_le_prototype :
    ∃ s : Scene, s.Stageable ∧ (∃ t ∈ nca.combinedPreference, t.Holds s) ∧ ¬nca.Prototypical s :=
  ⟨⟨.naturalForce, .psychologicallyImpacted, .direct⟩, by decide⟩

/-! ### Compactness and directness -/

/-- The LEX-ERG prototype is unmediated and the MCV prototype mediated. -/
theorem lexErg_mcv_mediation (s₁ s₂ : Scene) (h₁ : lexErg.Prototypical s₁)
    (h₂ : mcv.Prototypical s₂) : s₁.mediation < s₂.mediation := by
  revert s₁ s₂; decide

/-- The lexical LEX-ERG and the morphological MCV, located by the mediation of their prototypes,
satisfy [comrie-1989]'s monotonicity strictly. -/
theorem lexErg_mcv_comrieMonotone (s₁ s₂ : Scene) (h₁ : lexErg.Prototypical s₁)
    (h₂ : mcv.Prototypical s₂) :
    CausativeConstruction.ComrieMonotone ⟨.lexical, s₁.mediation⟩ ⟨.morphological, s₂.mediation⟩ :=
  fun _ ↦ (lexErg_mcv_mediation s₁ s₂ h₁ h₂).le

end Hafeez2025
