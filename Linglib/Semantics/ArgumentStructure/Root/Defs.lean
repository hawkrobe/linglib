import Linglib.Semantics.ArgumentStructure.Root.Profile
import Linglib.Semantics.ArgumentStructure.Root.Kinds

/-!
# Verbal roots

A verbal root of [beavers-koontz-garboden-2020] is a bundle of lexical
entailments (§5.2.1, after [dowty-1991]): idiosyncratic atoms, each of one of
the four kinds the book's root typology tracks (§5.4.1, (11)) — a state, a
manner, a change into a state, or causation. `Root` carries a finite set of
such atoms and the root's within-class quality profile. Its kind signature
`Root.kinds` is *derived*, the image of the atoms under `Entailment.kind`, and
`Root.closedKinds` adds the kinds the book's collocational restrictions force
(`Root.Kinds.close`); that closure is where the templatic content a root's own
entailments carry with them (a cracked state entails a change, §5.2.1) enters
the signature.

## Main declarations

* `Root.Entailment` — a labelled atom; `Root.Entailment.kind` forgets the label
* `Root` — name, atoms, quality profile
* `Root.kinds`, `Root.closedKinds` — the derived and the closed signature

## References

* [beavers-koontz-garboden-2020]: The Roots of Verbal Meaning.
* [dowty-1991]: Thematic proto-roles and argument selection.
* [bohnemeyer-2004]: Split intransitivity, linking, and lexical representation.
* [spalek-mcnally-2026], [majid-boster-bowerman-2008]: the quality dimensions of
  `Root.Profile`.
-/

namespace Verb

/-! ### Atoms -/

/-- A lexical entailment a root carries, of one of the four kinds of the root
typology of [beavers-koontz-garboden-2020] (§5.4.1, (11)). The label names the
particular state, manner, or result; causation is unlabelled because the
typology records only that there is a cause (the internal vs external cause
distinction of [bohnemeyer-2004] is `EventStructure.InternalExternalCause`).
Participant entailments (volition, sentience, …) are the separate linking layer
`ArgumentStructure.EntailmentProfile`. -/
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

/-- The kind of an atom: forget its label. -/
def Root.Entailment.kind : Root.Entailment → LexKind
  | .state _ => .state
  | .manner _ => .manner
  | .result _ => .result
  | .cause => .cause

/-! ### Roots -/

/-- A verbal root: its form, the lexical entailments it carries, and its
within-class quality profile. -/
structure Root where
  /-- The root form, `""` when the root is carried anonymously by a verb whose
  citation form names it. -/
  name : String := ""
  /-- The root's atoms, `∅` where its structural content is unannotated. -/
  entailments : Finset Verb.Root.Entailment := ∅
  /-- Within-class graded quality dimensions ([spalek-mcnally-2026],
  [majid-boster-bowerman-2008]); `{}` leaves every dimension unconstrained. -/
  profile : Verb.Root.Profile := {}
  deriving DecidableEq

/-- `Finset` has only an `unsafe` `Repr`, so `Root` cannot derive one; this shows
the name, the number of atoms, and the profile. -/
instance : Repr Root := ⟨λ r _ => repr (r.name, r.entailments.card, r.profile)⟩

namespace Root

variable (r : Root)

/-- The kind signature of a root: the kinds of its atoms. -/
def kinds : Kinds := r.entailments.image Entailment.kind

variable {r} in
@[simp] theorem mem_kinds {k : LexKind} : k ∈ r.kinds ↔ ∃ a ∈ r.entailments, a.kind = k :=
  Finset.mem_image

/-- The closed signature: `kinds` completed under the collocational restrictions
of [beavers-koontz-garboden-2020] (`Root.Kinds.close`). -/
def closedKinds : Kinds := r.kinds.close

theorem kinds_le_closedKinds : r.kinds ≤ r.closedKinds := Kinds.le_close _

theorem closedKinds_wellFormed : r.closedKinds.WellFormed := Kinds.close_wellFormed _

end Root

end Verb
