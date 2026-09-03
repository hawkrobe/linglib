import Linglib.Semantics.ArgumentStructure.Root.Profile
import Linglib.Semantics.ArgumentStructure.Root.Kinds

/-!
# Verbal roots

A verbal root of [beavers-koontz-garboden-2020] is a bundle of lexical
entailments (§5.2.1), each of one of the four kinds of `Root.Kind`. `Root`
carries a finite set of such atoms, its position with respect to the verbalizing
head `v`, and a within-class quality profile. Its kind signature `Root.kinds` is
the image of the atoms under `Entailment.kind`, and `Root.closedKinds` completes
it under the collocational restrictions (`Root.Kinds.close`). A root composes
with `v` either as its complement, the result position of change-of-state roots
such as √flat and √drown, or adjoined to it as a modifier, the manner position of
√jog and √hand (§4.5.3–4.5.4); position is the second coordinate of the book's
root typology (§5.4.1, (12)), and an adjoined root escapes both the scope of
restitutive *again* (§4.5.4) and the deletion site of verbal VP ellipsis
([kalyakin-2026] §2.2). Participant entailments are the separate linking layer
`ArgumentStructure.EntailmentProfile`.

## Main declarations

* `Root.Entailment` — a labelled atom; `Root.Entailment.kind` forgets the label
* `Root.Position` — complement or adjoined to `v`
* `Root` — name, atoms, position, quality profile
* `Root.kinds`, `Root.closedKinds` — the derived and the closed signature

## References

* [beavers-koontz-garboden-2020]: The Roots of Verbal Meaning.
* [kalyakin-2026]: VP ellipsis and argument structure alternations: Evidence from
  Muira Dargwa complex predicates.
* [spalek-mcnally-2026], [majid-boster-bowerman-2008]: the quality dimensions of
  `Root.Profile`.
-/

namespace Verb

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

/-- A verbal root, with its lexical entailments, position, and quality profile. -/
structure Root where
  /-- The root form, `""` when the root is carried anonymously by a verb whose
  citation form names it. -/
  name : String := ""
  /-- The root's atoms, `∅` where its structural content is unannotated. -/
  entailments : Finset Verb.Root.Entailment := ∅
  /-- The position in which the root composes with `v`, where annotated. -/
  position : Option Verb.Root.Position := none
  /-- Within-class graded quality dimensions ([spalek-mcnally-2026],
  [majid-boster-bowerman-2008]); `{}` leaves every dimension unconstrained. -/
  profile : Verb.Root.Profile := {}
  deriving DecidableEq

/-- A `Repr` showing the name, atom count, position, and profile, since `Finset` has
only an `unsafe` one. -/
instance : Repr Root :=
  ⟨λ r _ => repr (r.name, r.entailments.card, r.position, r.profile)⟩

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

end Root

end Verb
