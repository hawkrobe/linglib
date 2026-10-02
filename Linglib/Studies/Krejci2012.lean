module

public import Linglib.Semantics.Events.Basic
public import Linglib.Studies.KoontzGarboden2009
public import Linglib.Semantics.Presupposition.Iterative
public import Linglib.Core.Order.UpperLower.Finset
public import Mathlib.Tactic.DeriveFintype

/-!
# Krejci (2012): Causativization as Antireflexivization

This file formalizes Krejci's account of why middle and ingestive verbs (*wash*,
*dress*; *eat*, *learn*) causativize like intransitives in languages that mark causatives
morphologically. The report's survey orders verb classes on a hierarchy of causativizability,
unaccusatives before middles and ingestives before unergatives before simple transitives, on
which no language's causative process skips a tier. Its explanation is that the simple forms
of these verbs are lexically reflexive: their event structure is already causative, with the
causer and the causee coidentified, and the lexical causative (*feed*, *teach*, transitive
*wash* and *dress*) arises by antireflexivization, which delinks the two arguments. This is
the reflexivization analysis of Koontz-Garboden read in the opposite direction of
derivation, so the simple form is that study's `reflexivize` applied to its `causative`.

On a model of *eat*, *feed* and *make eat*, the entailments of the simple form split between
the causer and the causee of the lexical causative but stay with the causee of the
periphrastic causative (`feed_not_makeEat`); denying the simple form while asserting the
lexical causative is consistent on the bieventive representation (`not_eat_and_feed`) and
contradictory under causer addition; the result state supports a restitutive reading of
*again*, with *again* on the result state (`againState`), that the repetitive reading does not
exhaust; and *by itself* is licensed. The hierarchy is a linear order on `Tier`, a causative
process is the set of tiers it reaches, and respecting the hierarchy is a lower-set condition
(`Causative.RespectsHierarchy`), checked on the report's Table 2.8.

## Implementation notes

* The model takes the verb's event to be the change of state and closes the causing event
  existentially, as `KoontzGarboden2009.causative` does; *make eat* adds a second causing
  event with its own effector.
* Of the report's three tests of event-structural complexity only *again* is formalized;
  *re-* and *almost* have the same scopal structure. States are times in the model, a change
  giving rise to the state at its end, so that *again* on the result state has earlier states
  to presuppose.
* The Marathi evidence and the twenty surveyed languages outside Table 2.8 are not
  formalized.

## References

* [krejci-2012]
* [koontz-garboden-2009]
* [chierchia-2004]
* [dowty-1979]
-/

@[expose] public section

namespace Krejci2012

open Event (τ)

open KoontzGarboden2009 ArgumentStructure

/-! ### Antireflexivization -/

section Model

variable {Entity State T E : Type*} [LinearOrder T] [Event.TemporalTrace E T]
  (M : ArgumentStructure.EventStructure.Interpretation Entity State E)
  (manip : Entity → E → Prop) (S : Entity → State → Prop)

/-- In the lexical causative (38a) the causer's manipulation of food brings the causee to the
state of potential digestion. -/
abbrev feed : Entity → Entity → E → Prop := causative M manip S

/-- The simple form (37a) is the lexical causative on its diagonal, where the eater manipulates
the food and comes to digest it. Antireflexivization ((96)–(97)) delinks the two arguments. -/
abbrev eat : Entity → E → Prop := reflexivize (feed M manip S)

/-- The periphrastic causative *make eat* adds a further causing event, with its own effector,
of an eating. -/
def makeEat (z x : Entity) (e : E) : Prop :=
  ∃ w, M.effector z w ∧ M.cause w e ∧ eat M manip S x e

/-- Causativization by causer addition ((94)) is the analysis the report rejects, on which the
simple form is an activity `ingest` with no causing subevent and the causative adds a causer. -/
def causerAddition (ingest : Entity → E → Prop) (y x : Entity) (e : E) : Prop :=
  ∃ w, M.effector y w ∧ M.cause w e ∧ ingest x e

/-- An event precedes another when its run time is before the other's. -/
abbrev Before (e' e : E) : Prop := (τ e').isBefore (τ e)

/-- On the restitutive reading *again* modifies only the result state ((66a)): the state predicate
holds of a state that an earlier state of it preceded, whether or not a change brought that
earlier state about ((65a)). The restitutive reading of a verb is the verb over this
predicate. -/
def againState (ltS : State → State → Prop) (S : Entity → State → Prop) (x : Entity)
    (s : State) : Prop :=
  (Presupposition.again ltS (S x)).holds s

/-- On the repetitive reading *again* modifies the whole predicate ((66b)), so the sentence
presupposes that the whole event happened before. -/
def Repetitive (P : Entity → E → Prop) (x : Entity) (e : E) : Prop :=
  (Presupposition.again Before (P x)).holds e

variable {M manip S} {x y z : Entity} {e : E}

/-- The simple form is the derived inchoative of `KoontzGarboden2009`. -/
theorem eat_eq_anticausative : eat M manip S = anticausative M manip S := rfl

/-- The eater manipulates food ((39a)). -/
theorem exists_manip_of_eat (h : eat M manip S x e) : ∃ w, manip x w ∧ M.cause w e :=
  exists_cause_of_anticausative h

/-- The feeder manipulates food ((45)). -/
theorem exists_manip_of_feed (h : feed M manip S y x e) : ∃ w, manip y w ∧ M.cause w e :=
  let ⟨w, h₁, h₂, _⟩ := h; ⟨w, h₁, h₂⟩

/-- Whoever is fed comes to potential digestion ((44c)). -/
theorem inchoative_of_feed (h : feed M manip S y x e) : M.vBecome S x e :=
  let ⟨_, _, _, h⟩ := h; h

/-- Whoever is made to eat manipulates food ((47a)). -/
theorem exists_manip_of_makeEat (h : makeEat M manip S z x e) :
    ∃ w, manip x w ∧ M.cause w e :=
  let ⟨_, _, _, h⟩ := h; exists_manip_of_eat h

/-- Under causer addition the causative entails the simple form, so denying the one while
asserting the other is contradictory ((95)). -/
theorem ingest_of_causerAddition {ingest : Entity → E → Prop}
    (h : causerAddition M ingest y x e) : ingest x e :=
  let ⟨_, _, _, h⟩ := h; h

/-- Eating licenses *by itself* ((114a)), having a causing subevent whose effector is the
eater, once manipulating food makes one an effector. -/
theorem licensesBySelf_eat (h : ∀ x w, manip x w → M.effector x w) :
    LicensesBySelf M (eat M manip S) :=
  fun _ _ he ↦ let ⟨w, hm, hc⟩ := exists_manip_of_eat he; ⟨w, hc, h _ _ hm⟩

end Model

/-! ### Mary and John -/

/-- The participants. -/
inductive Participant
  | mary
  | john
  deriving DecidableEq

/-- An event running from `s` to `t`. -/
def ev (s t : ℤ) (h : s ≤ t := by decide) : NonemptyInterval ℤ := ⟨(s, t), h⟩

/-- The event running from `s` to `t`. -/
def At (w : NonemptyInterval ℤ) (s t : ℤ) : Prop := (τ w).toProd = (s, t)

def w₀ : NonemptyInterval ℤ := ev 0 1
def e₀ : NonemptyInterval ℤ := ev 1 2
def w₁ : NonemptyInterval ℤ := ev 0 2
def w₂ : NonemptyInterval ℤ := ev 3 4
def e₁ : NonemptyInterval ℤ := ev 4 5

/-- The state of potential digestion holds of John after each meal of the scenarios below, the
states at the times 2 and 5. -/
def digesting (x : Participant) (s : ℤ) : Prop := x = .john ∧ (s = 2 ∨ s = 5)

/-- A model in which the events `causing` lists bring John to potential digestion, with `eff`
the effectors of events. States are times, and a change gives rise to the state at its end. -/
def eating (causing : NonemptyInterval ℤ → NonemptyInterval ℤ → Prop)
    (eff : Participant → NonemptyInterval ℤ → Prop) :
    ArgumentStructure.EventStructure.Interpretation Participant ℤ (NonemptyInterval ℤ) where
  become s e := (∃ w, causing w e) ∧ s = (τ e).toProd.2
  cause := causing
  effector := eff

/-- Mary manipulates the food. -/
def spoonManip (y : Participant) (w : NonemptyInterval ℤ) : Prop := y = .mary ∧ At w 0 1

/-- In spoon feeding ((44a)) Mary's manipulation of the food causes John's change. -/
def spoonFeeding :
    ArgumentStructure.EventStructure.Interpretation Participant ℤ (NonemptyInterval ℤ) :=
  eating (fun w e ↦ At w 0 1 ∧ At e 1 2) spoonManip

/-- John manipulates the food. -/
def supManip (y : Participant) (w : NonemptyInterval ℤ) : Prop := y = .john ∧ At w 0 1

/-- Under supervision ((48)) John's manipulation of the food and Mary's supervising action both
cause John's change. -/
def supervising :
    ArgumentStructure.EventStructure.Interpretation Participant ℤ (NonemptyInterval ℤ) :=
  eating (fun w e ↦ (At w 0 1 ∨ At w 0 2) ∧ At e 1 2)
    (fun y w ↦ (y = .john ∧ At w 0 1) ∨ (y = .mary ∧ At w 0 2))

/-- Mary manipulates the food the first time, John the second. -/
def twoManip (y : Participant) (w : NonemptyInterval ℤ) : Prop :=
  (y = .mary ∧ At w 0 1) ∨ (y = .john ∧ At w 3 4)

/-- In the model of two meals Mary feeds John, and later John eats. -/
def twoMeals :
    ArgumentStructure.EventStructure.Interpretation Participant ℤ (NonemptyInterval ℤ) :=
  eating (fun w e ↦ (At w 0 1 ∧ At e 1 2) ∨ (At w 3 4 ∧ At e 4 5)) twoManip

/-- *I didn't eat pie; you fed pie to me* ((92), (106)) is consistent, since John, fed by Mary,
did not eat, having manipulated no food ((44a)). -/
theorem not_eat_and_feed :
    ¬ eat spoonFeeding spoonManip digesting .john e₀ ∧
      feed spoonFeeding spoonManip digesting .mary .john e₀ :=
  ⟨fun ⟨_, ⟨h, _⟩, _⟩ ↦ Participant.noConfusion h,
    ⟨w₀, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, 2, ⟨⟨w₀, rfl, rfl⟩, rfl⟩, rfl, .inl rfl⟩⟩

/-- Feeding is not making eat, since John, fed, was not made to eat, as whoever is made to eat
manipulates food ((47a)). -/
theorem feed_not_makeEat :
    feed spoonFeeding spoonManip digesting .mary .john e₀ ∧
      ¬ makeEat spoonFeeding spoonManip digesting .mary .john e₀ :=
  ⟨not_eat_and_feed.2, fun ⟨_, _, _, h⟩ ↦ not_eat_and_feed.1 h⟩

/-- Making eat is not feeding ((48)), since Mary made John eat without touching any food. -/
theorem makeEat_not_feed :
    makeEat supervising supManip digesting .mary .john e₀ ∧
      ¬ feed supervising supManip digesting .mary .john e₀ :=
  ⟨⟨w₁, Or.inr ⟨rfl, rfl⟩, ⟨Or.inr rfl, rfl⟩, w₀, ⟨rfl, rfl⟩, ⟨Or.inl rfl, rfl⟩, 2,
      ⟨⟨w₀, Or.inl rfl, rfl⟩, rfl⟩, rfl, .inl rfl⟩,
    fun ⟨_, ⟨h, _⟩, _⟩ ↦ Participant.noConfusion h⟩

/-- Being fed does not license *by itself* ((113d)), since John reaches the state but the
effector of the causing event is Mary. -/
theorem not_licensesBySelf_inchoative :
    ¬ LicensesBySelf spoonFeeding (spoonFeeding.vBecome digesting) := fun h ↦
  let ⟨_, _, hw⟩ := h .john e₀ ⟨2, ⟨⟨w₀, rfl, rfl⟩, rfl⟩, rfl, .inl rfl⟩
  Participant.noConfusion hw.1

/-- *John ate again* said after Mary had fed him, a second causer bringing about the result
state as in the context of (70): the restitutive reading holds, *again* on the state of
potential digestion ((66a)), which John had been in before, and the repetitive reading fails,
since John had not eaten before. -/
theorem restitutive_not_repetitive :
    eat twoMeals twoManip (againState (· < ·) digesting) .john e₁ ∧
      ¬ Repetitive (eat twoMeals twoManip digesting) .john e₁ :=
  ⟨⟨w₂, Or.inr ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩, 5, ⟨⟨w₂, Or.inr ⟨rfl, rfl⟩⟩, rfl⟩,
      ⟨2, by decide, rfl, .inl rfl⟩, rfl, .inr rfl⟩,
    fun ⟨⟨e', hb, w, hm, hc, _⟩, _⟩ ↦ by
      rcases hm with ⟨h, _⟩ | ⟨_, hw⟩
      · exact Participant.noConfusion h
      rcases hc with ⟨h, _⟩ | ⟨_, he⟩
      · exact absurd (hw.symm.trans h) (by decide)
      · have hb' : (τ e').toProd.2 ≤ 4 := hb
        rw [he] at hb'
        exact absurd hb' (by decide)⟩

/-! ### The hierarchy of causativizability -/

/-- The tiers of the hierarchy (22), from the most readily causativized. -/
inductive Tier
  | unaccusative
  | middleIngestive
  | unergative
  | simpleTransitive
  deriving DecidableEq, Fintype, Repr

/-- The position of a tier on the hierarchy. -/
def Tier.rank : Tier → ℕ
  | .unaccusative => 0
  | .middleIngestive => 1
  | .unergative => 2
  | .simpleTransitive => 3

instance : LinearOrder Tier := LinearOrder.lift' Tier.rank (by decide)

/-- A causative process of a language is the set of tiers whose verbs it applies to. -/
structure Causative where
  language : String
  morpheme : String
  reach : Finset Tier

namespace Causative

/-- A process respects the hierarchy when it reaches every tier before a tier it reaches. -/
def RespectsHierarchy (c : Causative) : Prop := IsLowerSet (↑c.reach : Set Tier)

instance : DecidablePred RespectsHierarchy := fun _ ↦ inferInstanceAs (Decidable (IsLowerSet _))

/-- The type of a process, (1) to (4) of Table 2.8, is the last tier it reaches. -/
def type (c : Causative) : WithBot Tier := c.reach.max

/-- A process that respects the hierarchy reaches exactly the tiers up to its type. -/
theorem mem_reach_iff {c : Causative} (h : c.RespectsHierarchy) (t : Tier) :
    t ∈ c.reach ↔ ↑t ≤ c.type :=
  h.mem_iff_le_max

end Causative

/-- The surveyed languages of Table 2.8, three of each type. Malayalam reaches transitives only
with an instrumental causee and is listed with the third type. -/
def table : List Causative :=
  [⟨"Slave", "-h-", {.unaccusative}⟩,
   ⟨"Mapudungun", "-ɨm", {.unaccusative}⟩,
   ⟨"Classical Nahuatl", "-tia", {.unaccusative}⟩,
   ⟨"Cora", "-te", {.unaccusative, .middleIngestive}⟩,
   ⟨"Marathi", "-aw", {.unaccusative, .middleIngestive}⟩,
   ⟨"Amharic", "a-", {.unaccusative, .middleIngestive}⟩,
   ⟨"Ahtna", "-ɬ-", {.unaccusative, .middleIngestive, .unergative}⟩,
   ⟨"Tariana", "-i-ta", {.unaccusative, .middleIngestive, .unergative}⟩,
   ⟨"Malayalam", "-icc", {.unaccusative, .middleIngestive, .unergative}⟩,
   ⟨"Basque", "-arazi", {.unaccusative, .middleIngestive, .unergative, .simpleTransitive}⟩,
   ⟨"Dulong/Rawang", "shv-", {.unaccusative, .middleIngestive, .unergative, .simpleTransitive}⟩,
   ⟨"Koyukon", "-ɬ-", {.unaccusative, .middleIngestive, .unergative, .simpleTransitive}⟩]

/-- No surveyed language skips a tier. -/
theorem table_respectsHierarchy : ∀ c ∈ table, c.RespectsHierarchy := by decide

end Krejci2012
