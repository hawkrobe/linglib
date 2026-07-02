import Linglib.Semantics.Verb.Root.OutcomeCardinality
import Linglib.Semantics.Verb.Root.Profile
import Linglib.Semantics.Verb.Root.Signature

/-!
# Atomic Lexical Entailments and Roots

Lexical entailments are the atomic claims a verbal root makes about
the events it describes and the participants in those events.
Following [beavers-koontz-garboden-2020], we treat these as
*structured atoms* rather than as a fixed feature vector: a **root**
is a finite collection of such atoms, and its kind signature
(`Root.Kinds`) is the *derived* set of kinds its atoms realize —
exposing the Bifurcation Thesis of Roots and Manner/Result
Complementarity as testable conjectures rather than architectural
commitments.

## Main declarations

* `LexEntailment` — labeled atoms; `LexEntailment.kind` projects its
  B&K-G kind
* `Root` — a named list of atoms
* `Root.kinds` — the derived signature
* `Root.HasState`/`HasManner`/`HasResult`/`HasCause` — kind membership
-/

namespace Verb

/-! ### Atomic entailments -/

/-- An atomic structural claim a verbal root makes — one of the four
    B&K-G entailment kinds (state, manner, result, cause). The three
    contentful kinds carry a label; `hasCause` is nullary.
    `LexEntailment.kind` projects the kind each realizes.

    Participant/proto-role entailments (volition, sentience, movement,
    affectedness, …) are deliberately *not* modeled here: they are an
    orthogonal, linking-relevant layer carried by
    `ArgumentStructure.EntailmentProfile`. -/
inductive LexEntailment where
  /-- Attributes a static property (state-kind atom). -/
  | hasState     (label : String)
  /-- Specifies the manner in which the action is performed. -/
  | hasManner    (label : String)
  /-- Entails change of state to the labelled result. -/
  | becomesState (label : String)
  /-- Entails a causing event. Nullary because B&K-G's typology is
      neutral about *what* causes — only that there is a cause.
      The cause-type distinction (internal vs external,
      [bohnemeyer-2004]) is carried separately by
      `Semantics.Lexical.EventStructure.InternalExternalCause`. -/
  | hasCause
  deriving DecidableEq, Repr

namespace LexEntailment

/-- The B&K-G kind an atom realizes. Total — every atom has a kind —
    but kept `Option`-valued for the closure API (`Closure.lean`),
    which quantifies over `a.kind = some k`. -/
def kind : LexEntailment → Option LexKind
  | hasState _     => some .state
  | hasManner _    => some .manner
  | becomesState _ => some .result
  | hasCause       => some .cause

end LexEntailment

/-! ### Roots -/

/-- A verbal root: a name and a finite set of atomic entailments it
    imposes.

    The set is the root's *base* entailment set — the atoms asserted
    directly. A closure operation (B&K-G's networks of entailments
    where one atom may entail another) is layered on top in
    `Closure.lean`. -/
structure Root where
  /-- The root form; `""` for an unnamed annotation (e.g. a quality-profile-only
      root carried by a verb whose root form is its citation form). -/
  name : String := ""
  /-- The B&KG structural-entailment atoms; `∅` where the root's structural
      content has not been annotated (its `kinds` is then uninformative,
      and a verb falls back to its class via `Verb.classKinds`). -/
  entailments : Finset LexEntailment := ∅
  /-- The outcome-set cardinality the root encodes ([bhadra-2024]): the axis
      orthogonal to the `kinds` (derived from `entailments`). `none`
      where the root has not been annotated for outcomes. -/
  outcomes : Option OutcomeCardinality := none
  /-- Within-class graded quality dimensions ([spalek-mcnally-2026],
      [majid-boster-bowerman-2008]); `{}` (all unconstrained) by default. -/
  profile : Verb.Root.Profile := {}
  deriving DecidableEq

/-- `Finset` carries no `Repr`, so `Root` cannot `deriving Repr`; we supply
    one by hand so `Verb` can `deriving Repr` over its `root` field. It shows
    `name`, `outcomes`, and `profile` in full plus the `entailments`
    cardinality — the entailment *set* itself has no computable `Repr`
    (`Finset`/`Multiset` would need a `LinearOrder` on the elements to render),
    but this already distinguishes roots that differ in outcomes/profile, which
    the old name-only `Repr` collapsed.

    `BEq`/`LawfulBEq` need no hand-rolled instance: both come from the derived
    `DecidableEq` (line above) via the global `instBEqOfDecidableEq`. -/
instance : Repr Root :=
  ⟨fun r _ => repr (r.name, r.entailments.card, r.outcomes, r.profile)⟩

namespace Root

/-- The derived kind signature of a root: the set of kinds its
    atoms realize. -/
def kinds (r : Root) : Root.Kinds :=
  Finset.univ.filter (fun k => ∃ a ∈ r.entailments, a.kind = some k)

theorem mem_kinds {r : Root} {k : LexKind} :
    k ∈ r.kinds ↔ ∃ a ∈ r.entailments, a.kind = some k := by
  simp only [kinds, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The root entails attribution of some state.
    `abbrev` (not `def`) so `Decidable`/`simp`/`decide` see through to the
    underlying `Finset` membership without per-predicate boilerplate. -/
abbrev HasState (r : Root) : Prop := .state ∈ r.kinds

/-- The root specifies some manner. -/
abbrev HasManner (r : Root) : Prop := .manner ∈ r.kinds

/-- The root entails some change of state (B&K-G "result"). -/
abbrev HasResult (r : Root) : Prop := .result ∈ r.kinds

/-- The root entails causation. -/
abbrev HasCause (r : Root) : Prop := .cause ∈ r.kinds

end Root

end Verb
