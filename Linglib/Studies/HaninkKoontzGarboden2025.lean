import Linglib.Semantics.Root.Defs
import Linglib.Semantics.Possession.Relationalizer
import Linglib.Semantics.ArgumentStructure.Verb
import Linglib.Fragments.Washo.PropertyConcepts
import Linglib.Data.Examples.HaninkKoontzGarboden2025

/-!
# Hanink and Koontz-Garboden (2025): Variation in the Lexical Semantics of Property Concept Roots

This file formalizes [hanink-koontz-garboden-2025]'s argument, from Washo, that property concept
roots vary in meaning within a language, against [menon-pancheva-2014]'s universal
quality-denoting root. Washo property concepts are verbs of three shapes (Table 1): a bare root
inflected like any intransitive, a bound root with the suffix *-iʔ*, and a reduplicated bound
root flanked by *ʔil-* and *-iʔ*, `Washo.PropertyConcepts.Shape`. The paper reads the morphology
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
seventy stems of the appendix are the rows of `Washo.PropertyConcepts.all`, on which
[dixon-1982]'s categories predict the shape only for color; the examples are the rows of
`Data.Examples.HaninkKoontzGarboden2025`.

## Implementation notes

Types are the substrate's `Ty` with `.s` for the paper's state sort, and the composability
claims are stated at the type level, since Lean's own typing enforces them in the semantic
definitions. Possession relates a possessor to a possessum of any type, so ordinary possession
(67) and the possession of a state (35) are one operator. The model of causation and change is
the substrate's `Verb.CosModel`, whose effector stands for the paper's AGENT.

## References

* [hanink-koontz-garboden-2025]
* [menon-pancheva-2014]
* [francez-koontz-garboden-2017]
* [beavers-koontz-garboden-2020]
* [dixon-1982]
* [jacobsen-1980]
-/

namespace HaninkKoontzGarboden2025

open Semantics Semantics.Composition Possession Washo.PropertyConcepts

/-! ### The two root meanings, section 4 -/

/-- The meanings a property concept root can have: a relation between individuals and states
(27), or a predicate of states alone, [francez-koontz-garboden-2017]'s quality (33). -/
inductive RootType where
  | relation
  | quality
  deriving DecidableEq, Repr

/-- The semantic type of each meaning. -/
def RootType.ty : RootType → Ty
  | .relation => .e ⇒ .s ⇒ .t
  | .quality => .s ⇒ .t

/-- The analysis (sections 4 and 5): bare and prefixed roots denote relations, suffixed roots
qualities. -/
def RootType.ofShape : Shape → RootType
  | .bare => .relation
  | .suffixed => .quality
  | .prefixed => .relation

/-- The two meanings are distinguished within Washo: the existence proof against a universal
root meaning (section 7). -/
theorem exists_rootType_ne :
    ∃ e₁ ∈ all, ∃ e₂ ∈ all, RootType.ofShape e₁.shape ≠ RootType.ofShape e₂.shape :=
  ⟨ihuk, by decide, iyel, by decide, by decide⟩

/-! ### The verbalizing heads and their types -/

/-- The heads that build a verb from a root: zero categorization, which keeps a relation
(section 4.1); the possessive light verb *-iʔ*, which takes a predicate of states (34); the
prefix *ʔil-*, which takes a relation to a predicate of states (57); and the change-of-state head
of a bipartite verb, which takes a relation (43a). -/
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

/-- The type a head returns: a predicate of individuals and states for the verbalizers, a
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

/-- A verbalization of a root: at least one head, well-typed, returning a stative predicate,
with zero categorization open only to a free root (section 5.2). -/
def Verbalizes (sh : Shape) (hs : List Head) : Prop :=
  hs ≠ [] ∧ WellTyped (RootType.ofShape sh).ty hs ∧
    output (RootType.ofShape sh).ty hs = (.e ⇒ .s ⇒ .t) ∧ (Head.zero ∈ hs → sh = .bare)

instance (sh : Shape) (hs : List Head) : Decidable (Verbalizes sh hs) := by
  unfold Verbalizes; infer_instance

/-- The morphology of each shape (Table 1): the bare root, the root with *-iʔ*, and the root
with *ʔil-* and then *-iʔ*. -/
def derivation : Shape → List Head
  | .bare => [.zero]
  | .suffixed => [.possess]
  | .prefixed => [.attr, .possess]

theorem derivation_verbalizes : ∀ sh, Verbalizes sh (derivation sh) := by decide

/-- (36), (56): *-iʔ* composes directly with a root only if the root is a suffixed one, whose
meaning is a quality. -/
theorem wellTyped_possess_iff (sh : Shape) :
    WellTyped (RootType.ofShape sh).ty [.possess] ↔ sh = .suffixed := by
  cases sh <;> decide

/-- (49): the change-of-state head of a bipartite verb composes with a root iff the root is not a
suffixed one, the gap in the resultative bipartite verbs. -/
theorem wellTyped_become_iff (sh : Shape) :
    WellTyped (RootType.ofShape sh).ty [.become] ↔ sh ≠ .suffixed := by
  cases sh <;> decide

/-- Each shape's morphology is a shortest verbalization of its root: the prefixed roots need
two heads, being bound relations that neither zero categorization nor *-iʔ* alone can take
(section 5.2). -/
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

/-- (34): the possessive light verb *-iʔ*, the existential closure of Barker's relationalizer:
the possessor `x` stands in `R` to some possessum satisfying `P`, ordinary possession when the
possessum is an entity (67) and the possession of a state when it is a quality (35). -/
def vHave (P : Y → S → Prop) (R : E → Y → S → Prop) : E → S → Prop :=
  Ex (π P R)

theorem vHave_apply (P : Y → S → Prop) (R : E → Y → S → Prop) (x : E) (s : S) :
    vHave P R x s ↔ ∃ y, P y s ∧ R x y s :=
  Iff.rfl

/-- (57): the prefix *ʔil-*, the range of a relation: the states some individual bears it to. -/
def nabla (P : E → St → Prop) : St → Prop := λ s => ∃ x, P x s

/-- (60): the prefixed root under *-iʔ*, the possession of a state in the relation's range. -/
theorem vHave_nabla_apply (P : E → St → Prop) (R : E → St → S → Prop) (x : E) (s : S) :
    vHave (λ y _ => nabla P y) R x s ↔ ∃ y, (∃ x', P x' y) ∧ R x y s :=
  Iff.rfl

/-- The Duke-of-York derivation of section 5.2: when possessing a state is holding it, the
prefixed root under *ʔil-* and *-iʔ* predicates what the bare relation does (28), the meaning
its bipartite uses show it to have. -/
theorem vHave_nabla_iff (P : E → St → Prop) (R : E → St → S → Prop)
    (h : ∀ x y s, R x y s ↔ P x y) (x : E) (s : S) :
    vHave (λ y _ => nabla P y) R x s ↔ ∃ y, P x y := by
  simp only [vHave_nabla_apply, h]
  exact ⟨λ ⟨y, _, hxy⟩ => ⟨y, hxy⟩, λ ⟨y, hy⟩ => ⟨y, ⟨x, hy⟩, hy⟩⟩

/-! ### Resultative bipartite verbs, section 5.1 -/

variable {T : Type*} [LinearOrder T] (M : Verb.CosModel E St T)

/-- (43a): the change-of-state head over a relation root, an event of change into a state the
theme bears the relation to. -/
def vBecome (P : E → St → Prop) : E → Event T → Prop :=
  λ x e => ∃ s, M.become s e ∧ P x s

/-- (43b): the causative head, with the initial's manner on the caused event. -/
def vCause (Q : Event T → Prop) : E → Event T → Prop :=
  λ y v => ∃ e, M.effector y v ∧ M.cause v e ∧ Q e

/-- The change-of-state head over a verb's root is [beavers-koontz-garboden-2020]'s inchoative
operator. -/
theorem vBecome_rootState (r : Verb) : vBecome M (M.rootState r) = M.inchoative r := rfl

/-- (46): a resultative bipartite verb entails the result state of its theme, the bare
predication (28) of the final's root. -/
theorem exists_state_of_vCause {P : E → St → Prop} {manner : Event T → Prop} {x y : E}
    {v : Event T} (h : vCause M (λ e => manner e ∧ vBecome M P x e) y v) : ∃ s, P x s :=
  let ⟨_, _, _, _, s, _, hs⟩ := h
  ⟨s, hs⟩

/-! ### The stems of the appendix -/

/-- The semantic root of a stem: one state atom, no core arguments, and the type of its
meaning; every Washo property concept is a property-concept root of
[beavers-koontz-garboden-2020]'s typology. -/
def toRoot (e : Entry) : Root :=
  { name := e.stem, entailments := {.state e.gloss}, valency := some ∅,
    denotationType := some (RootType.ofShape e.shape).ty }

theorem toRoot_kinds (e : Entry) : (toRoot e).kinds = Root.Kinds.propertyConcept := by
  simp [toRoot, Root.kinds, Root.Kinds.propertyConcept, Root.Entailment.kind]

/-- The only category whose members share a shape is color, all of whose stems are prefixed
(appendix). -/
theorem color_prefixed : ∀ e ∈ all, e.category = .color → e.shape = .prefixed := by decide

/-- [dixon-1982]'s categories do not predict the shape: the antonyms *MiLe* 'old' and *ešlut’*
'young' differ. -/
theorem category_not_predictive :
    ∃ e₁ ∈ all, ∃ e₂ ∈ all, e₁.category = e₂.category ∧ e₁.shape ≠ e₂.shape :=
  ⟨MiLe, by decide, ešlut, by decide, rfl, by decide⟩

end HaninkKoontzGarboden2025
