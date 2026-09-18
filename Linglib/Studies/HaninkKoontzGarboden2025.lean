import Linglib.Semantics.Root.Defs
import Linglib.Semantics.Possession.Relationalizer
import Linglib.Semantics.ArgumentStructure.ChangeOfState
import Linglib.Fragments.Washo.PropertyConcepts
import Linglib.Data.Examples.HaninkKoontzGarboden2025

/-!
# Hanink and Koontz-Garboden (2025): Variation in the Lexical Semantics of Property Concept Roots

This file formalizes [hanink-koontz-garboden-2025]'s argument, from Washo, that property concept
roots vary in meaning within a language, against [menon-pancheva-2014]'s universal
quality-denoting root. Washo property concepts are verbs of three shapes (Table 1): a bare root
inflected like any intransitive, a bound root with the suffix *-iʔ*, and a reduplicated bound
root flanked by *ʔil-* and *-iʔ*, `Washo.Shape`. The paper reads the morphology
at face value: *-iʔ* is the possessive light verb of ordinary possession (31), the existential
closure of Barker's relationalizer at the possessum type, `vHave`, which takes a predicate of
states (34); so a root that needs it denotes a quality, a predicate of states (33), while a bare
root denotes a relation between individuals and states (27). The reduplicated roots denote
relations too, since they alone serve as bare finals of resultative bipartite verbs (38), whose
change-of-state head takes a relation (43a); being bound, they reach *-iʔ* through *ʔil-*, which
returns the range of a relation (57), `nabla`, a Duke-of-York derivation that gives back the
root's own predication when possessing a state is holding it, `vHave_nabla_iff`. One assignment
of types to shapes, `RootType.ofShape`, then derives the morphology of each shape as its shortest
well-typed verbalization, `derivation_minimal`, and the bipartite gap for the suffixed roots
(49), `wellTyped_become_iff`. The change-of-state head is [beavers-koontz-garboden-2020]'s
inchoative operator, and the resultative entails the result state of its theme (46). The
seventy stems of the appendix are the rows of `Washo.propertyConcepts`, on which
[dixon-1982]'s categories predict the shape only for color; the examples are the rows of
`Data.Examples.HaninkKoontzGarboden2025`.

## Implementation notes

Types are the substrate's `Ty` with `.s` for the paper's state sort, and the composability
claims are stated at the type level, since Lean's own typing enforces them in the semantic
definitions. Possession relates a possessor to a possessum of any type, so ordinary possession
(67) and the possession of a state (35) are one operator. The model of causation and change is
the substrate's `ChangeOfStateModel`, whose heads `vBecome` and `vCause` are the paper's (43)
and whose effector stands for the paper's AGENT.

## References

* [hanink-koontz-garboden-2025]
* [menon-pancheva-2014]
* [francez-koontz-garboden-2017]
* [beavers-koontz-garboden-2020]
* [dixon-1982]
* [jacobsen-1980]
-/

namespace HaninkKoontzGarboden2025

open Semantics Semantics.Composition Possession Washo

/-! ### The two root meanings, section 4 -/

/-- A property concept root means either a relation between individuals and states or a
predicate of states alone, a quality. -/
inductive RootType where
  | relation
  | quality
  deriving DecidableEq, Repr

/-- The semantic type of each meaning. -/
def RootType.ty : RootType → Ty
  | .relation => .e ⇒ .s ⇒ .t
  | .quality => .s ⇒ .t

/-- On the analysis bare and prefixed roots denote relations and suffixed roots qualities. -/
def RootType.ofShape : Shape → RootType
  | .bare => .relation
  | .suffixed => .quality
  | .prefixed => .relation

/-- The two meanings are distinguished within Washo, the existence proof against a universal
root meaning. -/
theorem exists_rootType_ne :
    ∃ e₁ ∈ propertyConcepts, ∃ e₂ ∈ propertyConcepts,
      RootType.ofShape e₁.shape ≠ RootType.ofShape e₂.shape :=
  ⟨ihuk, by decide, iyel, by decide, by decide⟩

/-! ### The verbalizing heads and their types -/

/-- The heads that build a verb from a root are zero categorization, which keeps a relation,
the possessive light verb *-iʔ*, which takes a predicate of states, the prefix *ʔil-*, which
takes a relation to a predicate of states, and the change-of-state head of a bipartite verb,
which takes a relation. -/
inductive Head where
  | zero
  | possess
  | attr
  | become
  deriving DecidableEq, Repr

/-- The type a head takes. -/
def Head.input : Head → Ty
  | .zero => .e ⇒ .s ⇒ .t
  | .possess => .s ⇒ .t
  | .attr => .e ⇒ .s ⇒ .t
  | .become => .e ⇒ .s ⇒ .t

/-- The type a head returns is a predicate of individuals and states for the verbalizers, a
predicate of states for *ʔil-*, and a relation to events of change for the bipartite head. -/
def Head.output : Head → Ty
  | .zero => .e ⇒ .s ⇒ .t
  | .possess => .e ⇒ .s ⇒ .t
  | .attr => .s ⇒ .t
  | .become => .e ⇒ .v ⇒ .t

/-- A sequence of heads composes with a type when each takes what the last returns. -/
def WellTyped : Ty → List Head → Prop
  | _, [] => True
  | τ, h :: hs => h.input = τ ∧ WellTyped h.output hs

instance decWellTyped : (τ : Ty) → (hs : List Head) → Decidable (WellTyped τ hs)
  | _, [] => isTrue trivial
  | τ, h :: hs =>
    haveI := decWellTyped h.output hs
    inferInstanceAs (Decidable (h.input = τ ∧ WellTyped h.output hs))

/-- The type a sequence of heads returns. -/
def output (τ : Ty) : List Head → Ty
  | [] => τ
  | h :: hs => output h.output hs

/-- A verbalization of a root is a sequence of at least one head that is well-typed and returns
a stative predicate, with zero categorization open only to a free root. -/
def Verbalizes (sh : Shape) (hs : List Head) : Prop :=
  hs ≠ [] ∧ WellTyped (RootType.ofShape sh).ty hs ∧
    output (RootType.ofShape sh).ty hs = (.e ⇒ .s ⇒ .t) ∧ (Head.zero ∈ hs → sh = .bare)

instance (sh : Shape) (hs : List Head) : Decidable (Verbalizes sh hs) := by
  unfold Verbalizes; infer_instance

/-- The morphology of each shape is the bare root, the root with *-iʔ*, or the root with *ʔil-*
and then *-iʔ*. -/
def derivation : Shape → List Head
  | .bare => [.zero]
  | .suffixed => [.possess]
  | .prefixed => [.attr, .possess]

theorem derivation_verbalizes : ∀ sh, Verbalizes sh (derivation sh) := by decide

/-- *-iʔ* composes directly with a root only if the root is a suffixed one, whose meaning is a
quality. -/
theorem wellTyped_possess_iff (sh : Shape) :
    WellTyped (RootType.ofShape sh).ty [.possess] ↔ sh = .suffixed := by
  cases sh <;> decide

/-- The change-of-state head of a bipartite verb composes with a root iff the root is not a
suffixed one, the gap in the resultative bipartite verbs. -/
theorem wellTyped_become_iff (sh : Shape) :
    WellTyped (RootType.ofShape sh).ty [.become] ↔ sh ≠ .suffixed := by
  cases sh <;> decide

/-- Each shape's morphology is a shortest verbalization of its root. The prefixed roots need
two heads, being bound relations that neither zero categorization nor *-iʔ* alone can take. -/
theorem derivation_minimal (sh : Shape) (hs : List Head) (h : Verbalizes sh hs) :
    (derivation sh).length ≤ hs.length := by
  cases sh
  · exact List.length_pos_of_ne_nil h.1
  · exact List.length_pos_of_ne_nil h.1
  · rcases hs with _ | ⟨h₁, _ | ⟨h₂, t⟩⟩
    · exact absurd rfl h.1
    · cases h₁ <;> simp [Verbalizes, WellTyped, output, Head.input, Head.output,
        RootType.ofShape, RootType.ty] at h
    · show 2 ≤ t.length + 1 + 1
      omega

/-! ### The operators -/

variable {E Y St S : Type*}

/-- The possessive light verb *-iʔ* is the existential closure of Barker's relationalizer. The
possessor `x` stands in `R` to some possessum satisfying `P`, which is ordinary possession when
the possessum is an entity and the possession of a state when it is a quality. -/
def vHave (P : Y → S → Prop) (R : E → Y → S → Prop) : E → S → Prop :=
  Ex (π P R)

theorem vHave_apply (P : Y → S → Prop) (R : E → Y → S → Prop) (x : E) (s : S) :
    vHave P R x s ↔ ∃ y, P y s ∧ R x y s :=
  Iff.rfl

/-- The prefix *ʔil-* takes the range of a relation, the states some individual bears it to. -/
def nabla (P : E → St → Prop) : St → Prop := fun s ↦ ∃ x, P x s

/-- The prefixed root under *-iʔ* is the possession of a state in the relation's range. -/
theorem vHave_nabla_apply (P : E → St → Prop) (R : E → St → S → Prop) (x : E) (s : S) :
    vHave (fun y _ ↦ nabla P y) R x s ↔ ∃ y, (∃ x', P x' y) ∧ R x y s :=
  Iff.rfl

/-- The Duke-of-York derivation of section 5.2: when possessing a state is holding it, the
prefixed root under *ʔil-* and *-iʔ* predicates what the bare relation does (28), the meaning
its bipartite uses show it to have. -/
theorem vHave_nabla_iff (P : E → St → Prop) (R : E → St → S → Prop)
    (h : ∀ x y s, R x y s ↔ P x y) (x : E) (s : S) :
    vHave (fun y _ ↦ nabla P y) R x s ↔ ∃ y, P x y := by
  simp only [vHave_nabla_apply, h]
  exact ⟨fun ⟨y, _, hxy⟩ ↦ ⟨y, hxy⟩, fun ⟨y, hy⟩ ↦ ⟨y, ⟨x, hy⟩, hy⟩⟩

/-! ### Resultative bipartite verbs, section 5.1 -/

variable {Event : Type*} (M : ArgumentStructure.ChangeOfStateModel E St Event)

/-- A resultative bipartite verb, the causative head over the initial's manner and the
change-of-state head over the final's root, entails the result state of its theme, the bare
predication of the final's root. -/
theorem exists_state_of_vCause {P : E → St → Prop} {manner : Event → Prop} {x y : E}
    {v : Event} (h : M.vCause (fun e ↦ manner e ∧ M.vBecome P x e) y v) : ∃ s, P x s :=
  let ⟨_, _, _, _, s, _, hs⟩ := h
  ⟨s, hs⟩

/-! ### The stems of the appendix -/

/-- The semantic root of a stem has one state atom, no core arguments and the type of its
meaning, so every Washo property concept is a property-concept root of the typology of Beavers
and Koontz-Garboden. -/
def toRoot (e : PropertyConcept) : Root :=
  { name := e.stem, entailments := {.state e.gloss}, valency := some ∅,
    denotationType := some (RootType.ofShape e.shape).ty }

theorem toRoot_kinds (e : PropertyConcept) : (toRoot e).kinds = Root.Kinds.propertyConcept := by
  simp [toRoot, Root.kinds, Root.Kinds.propertyConcept, Root.Entailment.kind]

/-- The only category whose members share a shape is color, all of whose stems are prefixed
(appendix). -/
theorem color_prefixed : ∀ e ∈ propertyConcepts, e.category = .color → e.shape = .prefixed := by
  decide

/-- [dixon-1982]'s categories do not predict the shape: the antonyms *MiLe* 'old' and *ešlut’*
'young' differ. -/
theorem category_not_predictive :
    ∃ e₁ ∈ propertyConcepts, ∃ e₂ ∈ propertyConcepts,
      e₁.category = e₂.category ∧ e₁.shape ≠ e₂.shape :=
  ⟨MiLe, by decide, ešlut, by decide, rfl, by decide⟩

end HaninkKoontzGarboden2025
