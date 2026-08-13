import Linglib.Semantics.Definiteness.Defs
import Linglib.Semantics.Definiteness.Description
import Linglib.Semantics.Definiteness.Interpret
import Linglib.Semantics.Presupposition.MaximizePresupposition
import Linglib.Semantics.Genericity.MeaningPreservation
import Linglib.Syntax.Category.Determiner.Basic
import Linglib.Fragments.Mandarin.Determiners
import Linglib.Fragments.Cantonese.Determiners

/-!
# Jenks (2018): Articulated Definiteness without Articles

[jenks-2018] argues that Mandarin distinguishes unique definites, realized
as bare nouns via an unblocked Chierchia-style ι type-shift, from anaphoric
definites, realized as Dem-Clf-N with the demonstrative supplying a
Schwarz-style ι^x; an Index! principle, an instance of Maximize
Presupposition, forces the indexed form whenever an index is available,
except for matrix subjects marking continuing topics. The typology (Table 2)
leaves the marked-unique cell unattested. Cells are derived from each
language's `Determiners.inventory`, Index! is built with
`MaximizePresupposition.mpConstraintOf`, and the type-shift claims run
through `MeaningPreservation.selectShift`. Jenks types the ι^x index as a
property (his §4.4 composition with proper names), while the substrate's
`Description.anaphoric` carries a Schwarz-style individual index, so §4.4
is not formalized here. The post-Jenks Shan refutation lives in
`Moroney2021.lean` per chronology discipline.

## References

* [jenks-2018]
-/

namespace Jenks2018

open Semantics.Definiteness
open Semantics.Kinds
open Intensional
open Intensional.Variables

/-! ### The typology and its attested cells (Table 2) -/

/-- The three [jenks-2018] Table 2 attested marking strategies. The fourth
    cell — marked unique — is predicted unattested, with Greenberg's
    grammaticalization path (articles arise from demonstratives, hence in
    anaphoric uses first) as the diachronic explanation. -/
def jenksAttestedStrategies : List DefMarkingStrategy :=
  [.bipartite, .markedAnaphoric, .generallyMarked]

/-- Mandarin's derived strategy is in the attested set. -/
theorem mandarin_attested :
    Mandarin.Determiners.inventory.markingStrategy ∈ jenksAttestedStrategies := by
  rw [Mandarin.Determiners.marking]; decide

/-- Mandarin and Cantonese derive distinct cells — the paper's §6 contrast:
    Cantonese [Clf-N] is a syncretic definite like English *the*, while
    Mandarin marks only anaphoric definites. -/
theorem mandarin_cantonese_distinct_cells :
    Mandarin.Determiners.inventory.markingStrategy ≠
      Cantonese.Determiners.inventory.markingStrategy := by
  rw [Mandarin.Determiners.marking, Cantonese.Determiners.marking]; decide

/-! ### Realization in the Mandarin inventory (§3) -/

/-- Mandarin realizes anaphoric definiteness — the demonstrative
    obligatorily expones familiarity uses as Dem-Clf-N. -/
theorem anaphoric_realized :
    Mandarin.Determiners.inventory.Realizes .anaphoric := by decide

/-- Mandarin realizes the demonstrative kind, the *nà*/*zhè* paradigm, with
    *nà* preferred in simple anaphoric environments. -/
theorem demonstrative_realized :
    Mandarin.Determiners.inventory.Realizes .demonstrative := by decide

/-! ### Bridging and donkey definites (§3.1, §3.3) -/

/-- The bridging split: part-whole bridging projects uniqueness — bare N in
    Mandarin (*chezi … paizhao* 'car … license plate') — while
    producer-product bridging projects familiarity, which only the
    demonstrative expones (*shi … #(na wei) shiren* 'poem … #(that)
    poet'). -/
theorem bridging_split :
    bridgingPresupType .partWhole = .uniqueness ∧
    bridgingPresupType .relational = .familiarity ∧
    ¬ Mandarin.Determiners.inventory.MarksPresup .uniqueness ∧
    Mandarin.Determiners.inventory.MarksPresup .familiarity :=
  ⟨rfl, rfl, by decide, by decide⟩

/-- Donkey definites pattern with discourse anaphora: the donkey use
    projects familiarity, so Mandarin requires Dem-Clf-N in *ruguo*- and
    *dou*-conditionals and in relative-clause donkey configurations
    ((18)–(20); bare conditionals use indeterminate pronouns and involve
    no definite). -/
theorem donkey_requires_demonstrative :
    useTypeToPresupType .donkey = useTypeToPresupType .anaphoric ∧
    Mandarin.Determiners.inventory.MarksPresup .familiarity :=
  ⟨rfl, by decide⟩

/-! ### ι unblocked, ι^x blocked (Blocking Principle (23)) -/

/-- The type-shift context of a Mandarin bare noun: no article blocks ι or
    ∃ ("Don't do covertly what you can do overtly", (23)), while the
    demonstrative paradigm preempts covert ι^x. -/
def mandarinCtx : MeaningPreservation.TypeShiftContext :=
  { number := .neutral
  , downDefined := false
  , iotaBlocked := false
  , iotaAnaphoricBlocked := true
  , existsBlocked := false
  , instantiationAccessible := true }

/-- ι is selected for Mandarin bare nouns while ι^x is unavailable: bare N
    covers unique but not anaphoric definiteness — the `.markedAnaphoric`
    profile at the type-shift layer. -/
theorem iota_unblocked_anaphoric_blocked :
    MeaningPreservation.selectShift mandarinCtx = some .iota ∧
    .iotaAnaphoric ∉ MeaningPreservation.availableShifts mandarinCtx :=
  ⟨rfl, by decide⟩

/-! ### Index! as a Maximize Presupposition instance ((50), §5.2) -/

/-- An Index! candidate: an indexed alternative competes only when an
    index can be supplied by prior mention in discourse. -/
structure IndexCandidate where
  isIndexed : Bool
  indexAvailable : Bool
  deriving DecidableEq, Repr

/-- Index! strength: an indexed candidate gets strength 1 exactly when an
    index can actually be supplied, and bare candidates get 0. -/
def indexStrength (c : IndexCandidate) : Nat :=
  if c.isIndexed && c.indexAvailable then 1 else 0

/-- Index! — "Represent and bind all possible indices" (50) — as the
    substrate's general Maximize Presupposition construction at
    strength 1. -/
def indexConstraint : Constraints.Constraint IndexCandidate :=
  Semantics.Presupposition.MaximizePresupposition.mpConstraintOf
    1 indexStrength

/-- With a discourse antecedent available, the indexed candidate incurs
    strictly fewer Index! violations than the bare one. -/
theorem index_prefers_indexed_when_available :
    indexConstraint { isIndexed := true,  indexAvailable := true } <
    indexConstraint { isIndexed := false, indexAvailable := true } := by
  decide

/-- Without a discourse antecedent Index! is neutral, leaving bare N the
    only option in unique-definite contexts. -/
theorem index_neutral_when_unavailable :
    indexConstraint { isIndexed := true,  indexAvailable := false } =
    indexConstraint { isIndexed := false, indexAvailable := false } := by
  decide

/-! ### The subject-position exception (§5.3) -/

/-- A topic-aware Index! candidate: bare anaphoric subjects mark
    continuing topics, while new (left-dislocated) topics prefer the
    demonstrative. -/
structure TopicCandidate where
  isIndexed : Bool
  indexAvailable : Bool
  isTopic : Bool
  deriving DecidableEq, Repr

/-- Topic-overridden Index! strength: continuing-topic marking gives a
    bare candidate the same strength as an indexed one. -/
def topicAwareIndexStrength (c : TopicCandidate) : Nat :=
  if c.isTopic then 1
  else if c.isIndexed && c.indexAvailable then 1
  else 0

/-- The topic-aware Index! constraint. -/
def topicAwareIndexConstraint :
    Constraints.Constraint TopicCandidate :=
  Semantics.Presupposition.MaximizePresupposition.mpConstraintOf
    1 topicAwareIndexStrength

/-- A bare candidate marked as a continuing topic ties with the indexed
    alternative, restoring the free variation of matrix subjects. -/
theorem subject_topic_overrides_index :
    topicAwareIndexConstraint
      { isIndexed := false, indexAvailable := true, isTopic := true } =
    topicAwareIndexConstraint
      { isIndexed := true,  indexAvailable := true, isTopic := true } := by
  decide

/-- Without topic marking the Index! preference stands. -/
theorem non_topic_keeps_index_preference :
    topicAwareIndexConstraint
      { isIndexed := true,  indexAvailable := true, isTopic := false } <
    topicAwareIndexConstraint
      { isIndexed := false, indexAvailable := true, isTopic := false } := by
  decide

/-! ### The strict demonstrative under situation variation (§4.3) -/

/-- A demonstrative description's referent is fixed by the entity
    assignment at its index, so when the restrictor is situation-invariant
    at that entity the demonstrative cannot covary through the situation
    slot — the strict half of §4.3's contrast ((27)–(30): bare N covaries
    with a quantificational topic, the demonstrative forces the strict
    reading). The covarying half needs the property-typed index noted in
    the module docstring. -/
theorem demonstrative_strict_under_situation_variation {E W : Type}
    (R : DenotGS E W .et) (deictic : Features.Deixis.Feature)
    (sIdx d : Nat) (g : Assignment E) (gs₁ gs₂ : SitAssignment W)
    (hR : R g gs₁ (g d) = R g gs₂ (g d)) :
    interpret (.demonstrative R deictic sIdx d) g gs₁ =
      interpret (.demonstrative R deictic sIdx d) g gs₂ := by
  rw [interpret_demonstrative_eq_anaphoric, interpret_demonstrative_eq_anaphoric,
      interpret_anaphoric, interpret_anaphoric, hR]

end Jenks2018
