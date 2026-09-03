import Linglib.Semantics.Root.Content
import Linglib.Semantics.Root.Kinds
import Linglib.Semantics.ArgumentStructure.Valency
import Linglib.Semantics.Composition.Ty

/-!
# Verbal roots

A verbal root of [beavers-koontz-garboden-2020] is a bundle of lexical
entailments (§5.2.1), each of one of the four kinds of `Root.Kind`. `Root`
carries a finite set of such atoms, its position with respect to the verbalizing
head `v`, and its within-class content. Its kind signature `Root.kinds` is
the image of the atoms under `Entailment.kind`, and `Root.closedKinds` completes
it under the collocational restrictions (`Root.Kinds.close`). A root composes
with `v` either as its complement, the result position of change-of-state roots
such as √flat and √drown, or adjoined to it as a modifier, the manner position of
√jog and √hand (§4.5.3–4.5.4); position is the second coordinate of the book's
root typology (§5.4.1, (12)), and an adjoined root escapes both the scope of
restitutive *again* (§4.5.4) and the deletion site of verbal VP ellipsis
([kalyakin-2026] §2.2). Participant entailments are the separate linking layer
`ArgumentStructure.EntailmentProfile`. A root may also be annotated with the
coordinates [coon-2019] classifies root classes by, its valency, semantic type,
and whether it combines with transitive Voice.

## Main declarations

* `Root.Entailment` — a labelled state, manner, or result atom, or causation
* `Root.Position` — complement of `v` or adjoined to it
* `Root` — a root's name, atoms, position, content, and annotated
  valency, semantic type, and transitive-Voice licensing
* `Root.kinds` — the kinds of a root's atoms; `Root.closedKinds` closes them
* `Root.changeType` — property-concept or result root, off the closed signature

## References

* [beavers-koontz-garboden-2020]: The Roots of Verbal Meaning.
* [coon-2019]: Building verbs in Chuj.
* [beavers-etal-2021]: States and changes of state.
* [kalyakin-2026]: VP ellipsis and argument structure alternations: Evidence from
  Muira Dargwa complex predicates.
* [spalek-mcnally-2026], [majid-boster-bowerman-2008]: the dimensions of
  `Root.Content`.
-/

namespace Semantics

/-! ### Atoms -/

/-- A lexical entailment of a verbal root, labelled by the state, manner, or result
it names ([beavers-koontz-garboden-2020] §5.4.1). -/
inductive Root.Entailment where
  /-- The root describes the labelled state. -/
  | state (label : String)
  /-- The root describes an action of the labelled manner. -/
  | manner (label : String)
  /-- The root entails a change into the labelled state. -/
  | result (label : String)
  /-- The root entails causation. -/
  | cause
  deriving DecidableEq, Repr

/-- The kind of an atom, forgetting its label. -/
def Root.Entailment.kind : Root.Entailment → Root.Kind
  | .state _ => .state
  | .manner _ => .manner
  | .result _ => .result
  | .cause => .cause

/-! ### Position -/

/-- The position in which a verbal root composes with `v`. -/
inductive Root.Position where
  /-- The complement of `v`, the result position. -/
  | complement
  /-- Adjoined to `v` as a modifier, the manner position. -/
  | adjoined
  deriving DecidableEq, Fintype, Repr

/-! ### Roots -/

/-- A verbal root, with its lexical entailments, position, and content. -/
structure Root where
  /-- The root form, `""` when the root is carried anonymously by a verb whose
  citation form names it. -/
  name : String := ""
  /-- The root's atoms, `∅` where its structural content is unannotated. -/
  entailments : Finset Semantics.Root.Entailment := ∅
  /-- The position in which the root composes with `v`, where annotated. -/
  position : Option Semantics.Root.Position := none
  /-- Within-class content ([spalek-mcnally-2026], [majid-boster-bowerman-2008]); `{}`
  leaves every dimension unconstrained. -/
  content : Semantics.Root.Content := {}
  /-- The core-argument positions the root introduces, where annotated ([coon-2019]). -/
  valency : Option ArgumentStructure.Valency := none
  /-- The root's semantic type, where annotated ([coon-2019] (3)). -/
  denotationType : Option Semantics.Composition.Ty := none
  /-- Whether the root combines with the transitive-forming v ~ Voice head that merges an
  agent, the coordinate separating [coon-2019]'s √TV from its unaccusative √ITV (§3.3). -/
  licensesTransitiveVoice : Bool := false
  deriving DecidableEq

/-- A `Repr` showing the name, atom count, and position, since `Finset` has only an
`unsafe` one. -/
instance : Repr Root := ⟨λ r _ => repr (r.name, r.entailments.card, r.position)⟩

namespace Root

variable (r : Root)

/-- The kind signature of a root, the kinds of its atoms. -/
def kinds : Kinds := r.entailments.image Entailment.kind

variable {r} in
@[simp] theorem mem_kinds {k : Kind} : k ∈ r.kinds ↔ ∃ a ∈ r.entailments, a.kind = k :=
  Finset.mem_image

/-- The kind signature completed under the collocational restrictions
(`Root.Kinds.close`). -/
def closedKinds : Kinds := r.kinds.close

theorem kinds_subset_closedKinds : r.kinds ⊆ r.closedKinds := Kinds.subset_close _

theorem closedKinds_wellFormed : r.closedKinds.WellFormed := Kinds.close_wellFormed _

/-- The change type of a root, read off its closed signature ([beavers-etal-2021]). -/
def changeType : Option ChangeType := r.closedKinds.changeType

end Root

end Semantics
