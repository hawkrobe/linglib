import Linglib.Semantics.Lexical.Roots.Signature
import Linglib.Semantics.Lexical.Roots.OutcomeCardinality
import Linglib.Semantics.Lexical.Roots.Profile

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

* `LexEntailment` — labeled atoms; `LexEntailment.kind` projects the
  B&K-G kind, if any
* `Root` — a named list of atoms
* `Root.kinds` — the derived signature
* `Root.HasState`/`HasManner`/`HasResult`/`HasCause` — kind membership
-/

namespace Verb

/-! ### Atomic entailments -/

/-- An atomic claim a root can make. The four B&K-G kinds
    (state, manner, result, cause) correspond to the kinds of atoms
    present in a root's entailment set (`LexEntailment.kind`).

    The remaining atoms (volitional, sentient, motion, contact)
    cover Dowty's proto-role components that are independent of the
    state/manner/result/cause cut. -/
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
  /-- The agent acts intentionally. -/
  | volitional
  /-- The agent is sentient. -/
  | sentient
  /-- An entity changes location. -/
  | motion
  /-- Two entities are in physical contact. -/
  | contact
  deriving DecidableEq, Repr

namespace LexEntailment

/-- The B&K-G kind an atom realizes, if any. The proto-role atoms
    (volitional, sentient, motion, contact) carry no kind. -/
def kind : LexEntailment → Option LexKind
  | hasState _     => some .state
  | hasManner _    => some .manner
  | becomesState _ => some .result
  | hasCause       => some .cause
  | _              => none

end LexEntailment

/-! ### Roots -/

/-- A verbal root: a name and a finite set of atomic entailments it
    imposes.

    The set is the root's *base* entailment set — the atoms asserted
    directly. A closure operation (B&K-G's networks of entailments
    where one atom may entail another) is layered on top in
    `Roots/Closure.lean`. -/
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

/-- `Finset` carries neither `Repr` nor `BEq`, so `Root` cannot `deriving` either;
    we supply both by hand so `Verb` can derive `Repr`/`BEq` over its `root` field.
    The `Repr` shows the `name`, `outcomes`, and `profile` fields in full plus the
    `entailments` cardinality — the entailment *set* itself has no computable `Repr`
    (`Finset`/`Multiset` would need a `LinearOrder` on the elements to render), but
    this already distinguishes roots that differ in outcomes/profile, which the old
    name-only `Repr` collapsed. The `BEq` is the lawful `DecidableEq`-backed one. -/
instance : Repr Root :=
  ⟨fun r _ => repr (r.name, r.entailments.card, r.outcomes, r.profile)⟩
instance : BEq Root := ⟨fun a b => decide (a = b)⟩
instance : LawfulBEq Root where
  eq_of_beq h := of_decide_eq_true h
  rfl := decide_eq_true_eq.mpr rfl

namespace Root

/-- The derived kind signature of a root: the set of kinds its
    atoms realize. -/
def kinds (r : Root) : Root.Kinds :=
  Finset.univ.filter (fun k => ∃ a ∈ r.entailments, a.kind = some k)

theorem mem_kinds {r : Root} {k : LexKind} :
    k ∈ r.kinds ↔ ∃ a ∈ r.entailments, a.kind = some k := by
  simp [kinds]

/-- The root entails attribution of some state. -/
def HasState (r : Root) : Prop := .state ∈ r.kinds

/-- The root specifies some manner. -/
def HasManner (r : Root) : Prop := .manner ∈ r.kinds

/-- The root entails some change of state (B&K-G "result"). -/
def HasResult (r : Root) : Prop := .result ∈ r.kinds

/-- The root entails causation. -/
def HasCause (r : Root) : Prop := .cause ∈ r.kinds

instance (r : Root) : Decidable r.HasState :=
  inferInstanceAs (Decidable (_ ∈ _))
instance (r : Root) : Decidable r.HasManner :=
  inferInstanceAs (Decidable (_ ∈ _))
instance (r : Root) : Decidable r.HasResult :=
  inferInstanceAs (Decidable (_ ∈ _))
instance (r : Root) : Decidable r.HasCause :=
  inferInstanceAs (Decidable (_ ∈ _))

end Root

end Verb
