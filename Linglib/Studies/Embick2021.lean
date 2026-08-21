import Linglib.Morphology.DistributedMorphology.Locality
import Linglib.Data.Examples.Embick2021

/-!
# The motivation for roots in Distributed Morphology

[embick-2021]: the Two Domains Intuition — that some form–meaning
connections are fixed close to a lexical primitive and others built
compositionally — is explained not by the word but by syntactic locality
around category-free roots. Derived nominals combine the root directly with
n and gerunds nominalize a verbal structure ((8), (9)); agents are licensed
only by a Voice that selects v ((10)), so *growth* has no agentive reading
while *growing* does, and *destruction* gets one only from its encyclopedically
agentive root ((6), (7)). Category-defining heads are cyclic: a head attached
to the categorized root may show root-determined allomorphy and special
interpretation, an outer cyclic head may not ((13), (14)), while an outer
noncyclic head — the tense of *bent*, the aspect of *broken* — remains local
((15)). One cycle bounds both interfaces, each adding its own adjacency.

## Main definitions

* `Head`, `Morpheme`, `cyclic`: the heads of the examples with the
  categorizers cyclic.
* `AgentLicensed`: the Agent-Licensing Assumption (10), Voice selecting v.
* `Row`, `rows`: the nominalizations of (6)–(7) and the inflected verbs of §5.

## Main results

* `agentive_possessor_rows`: the possessor is agentive iff an agent is
  licensed or the root is encyclopedically agentive.
* `derivedNominal_not_agentLicensed`, `gerund_n_not_rootLocal`: a derived
  nominal licenses no agent, and the gerund's n is outer ((9), (14)).
* `inflection_rootLocal`: tense and aspect outside v are local ((15)).
-/

namespace Embick2021

open DistributedMorphology Data.Examples

/-- The heads of the examples. -/
inductive Head where
  | n | v | a | voice | tense | aspect
  deriving DecidableEq, Repr

/-- A head occurrence with its exponent. -/
structure Morpheme where
  head : Head
  exponent : String
  deriving DecidableEq, Repr

/-- The category heads are the cyclic heads. -/
def cyclic (m : Morpheme) : Prop := m.head = .n ∨ m.head = .v ∨ m.head = .a

instance : DecidablePred cyclic := fun _ => inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- **The Agent-Licensing Assumption** ((10)): an agent is introduced by a
Voice that selects v — so only a structure with v below Voice licenses one. -/
def AgentLicensed (s : Spine Morpheme) : Prop :=
  ∃ i : Fin s.heads.length, s.heads[i].head = .voice ∧ ∃ j < i, s.heads[j].head = .v

instance (s : Spine Morpheme) : Decidable (AgentLicensed s) :=
  inferInstanceAs (Decidable (∃ i, _ ∧ ∃ j < i, _))

/-! ### The words -/

/-- Whether the root is encyclopedically agentive (*destroy*) or not (*grow*). -/
inductive RootClass where
  | agentive | nonagentive
  deriving DecidableEq, Repr

/-- Derived nominal, gerund, or inflected verb. -/
inductive Construction where
  | derivedNominal | gerund | inflected
  deriving DecidableEq, Repr

structure Row where
  text : String
  spine : Spine Morpheme
  rootClass : Option RootClass
  construction : Construction
  accepted : Bool
  deriving Repr

def Morpheme.ofLabel (exp : String) : String → Option Morpheme
  | "n" => some ⟨.n, exp⟩
  | "v" => some ⟨.v, exp⟩
  | "a" => some ⟨.a, exp⟩
  | "voice" => some ⟨.voice, exp⟩
  | "T" => some ⟨.tense, exp⟩
  | "aspect" => some ⟨.aspect, exp⟩
  | _ => none

def RootClass.ofLabel : String → Option RootClass
  | "agentive" => some .agentive
  | "nonagentive" => some .nonagentive
  | _ => none

def Construction.ofLabel : String → Option Construction
  | "derivedNominal" => some .derivedNominal
  | "gerund" => some .gerund
  | "inflected" => some .inflected
  | _ => none

/-- The roots of the pool, indexed by first occurrence. -/
def rootNames : List String := (Examples.all.filterMap (·.feature? "root")).eraseDups

def Row.ofExample (ex : LinguisticExample) : Option Row := do
  let root ← ex.feature? "root"
  let heads := [("h1", "h1exp"), ("h2", "h2exp"), ("h3", "h3exp")].filterMap
    fun (k, e) => (ex.feature? k).bind (Morpheme.ofLabel ((ex.feature? e).getD ""))
  let construction ← (ex.feature? "construction").bind Construction.ofLabel
  pure ⟨ex.primaryText, ⟨⟨rootNames.idxOf root⟩, heads⟩,
    (ex.feature? "rootClass").bind RootClass.ofLabel, construction, ex.judgment = .acceptable⟩

theorem row_ofExample_isSome : ∀ ex ∈ Examples.all, (Row.ofExample ex).isSome := by decide

def rows : List Row := Examples.all.filterMap Row.ofExample

/-! ### Nominalizations ((6)–(10)) -/

/-- The possessor reads as an agent iff the structure licenses one or the
root is encyclopedically agentive: *destruction* and both gerunds, not
*growth*. -/
theorem agentive_possessor_rows :
    ∀ r ∈ rows, ∀ c, r.rootClass = some c →
      (r.accepted ↔ (AgentLicensed r.spine ∨ c = .agentive)) := by
  decide

/-- A derived nominal is a root noun: no v, so no agent-licensing Voice. -/
theorem derivedNominal_not_agentLicensed :
    ∀ r ∈ rows, r.construction = .derivedNominal → ¬ AgentLicensed r.spine := by
  decide

/-! ### Inner and outer heads ((13)–(15)) -/

/-- The gerund's n is an outer cyclic head, not local to the root ((9), (14)),
whereas the derived nominal's n is the first ((8), (13)). -/
theorem gerund_n_not_rootLocal :
    ∀ r ∈ rows, ∀ i : Fin r.spine.heads.length, r.spine.heads[i].head = .n →
      (r.spine.RootLocal cyclic i ↔ r.construction = .derivedNominal) := by
  decide

/-- Tense and aspect outside the verbalizer are local to the root ((15)):
*ben-t*, *brok-en*. -/
theorem inflection_rootLocal :
    ∀ r ∈ rows, r.construction = .inflected → ∀ i : Fin r.spine.heads.length,
      r.spine.RootLocal cyclic i := by
  decide

end Embick2021
