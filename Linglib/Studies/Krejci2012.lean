import Linglib.Studies.KoontzGarboden2009
import Linglib.Semantics.Presupposition.Iterative
import Linglib.Core.Order.UpperLower.Finset
import Mathlib.Tactic.DeriveFintype

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
*again*, stated on `Presupposition.again`, that the repetitive reading does not exhaust; and
*by itself* is licensed. The
hierarchy is a linear order on `Tier`, a causative process is the set of tiers it reaches,
and respecting the hierarchy is a lower-set condition (`Causative.RespectsHierarchy`),
checked on the report's Table 2.8.

## Implementation notes

* The model takes the verb's event to be the change of state and closes the causing event
  existentially, as `KoontzGarboden2009.causative` does; *make eat* adds a second causing
  event with its own effector.
* Of the report's three tests of event-structural complexity only *again* is formalized;
  *re-* and *almost* have the same scopal structure.
* The Marathi evidence and the twenty surveyed languages outside Table 2.8 are not
  formalized.

## References

* [krejci-2012]
* [koontz-garboden-2009]
* [chierchia-2004]
* [dowty-1979]
-/

namespace Krejci2012

open KoontzGarboden2009 ArgumentStructure

/-! ### Antireflexivization -/

section Model

variable {Entity State T : Type*} [LinearOrder T]
  (M : ArgumentStructure.ChangeOfStateModel Entity State (Event T))
  (manip : Entity → Event T → Prop) (S : Entity → State → Prop)

/-- In the lexical causative (38a) the causer's manipulation of food brings the causee to the
state of potential digestion. -/
abbrev feed : Entity → Entity → Event T → Prop := causative M manip S

/-- The simple form (37a) is the lexical causative on its diagonal, where the eater manipulates
the food and comes to digest it. Antireflexivization ((96)–(97)) delinks the two arguments. -/
abbrev eat : Entity → Event T → Prop := reflexivize (feed M manip S)

/-- The periphrastic causative *make eat* adds a further causing event, with its own effector,
of an eating. -/
def makeEat (z x : Entity) (e : Event T) : Prop :=
  ∃ w, M.effector z w ∧ M.cause w e ∧ eat M manip S x e

/-- Causativization by causer addition ((94)) is the analysis the report rejects, on which the
simple form is an activity `ingest` with no causing subevent and the causative adds a causer. -/
def causerAddition (ingest : Entity → Event T → Prop) (y x : Entity) (e : Event T) : Prop :=
  ∃ w, M.effector y w ∧ M.cause w e ∧ ingest x e

/-- An event precedes another when its run time is before the other's. -/
abbrev Before (e' e : Event T) : Prop := e'.τ.isBefore e.τ

/-- On the restitutive reading *again* modifies the result state, so the sentence presupposes
that the state came about before. -/
def Restitutive (P : Entity → Event T → Prop) (x : Entity) (e : Event T) : Prop :=
  (Presupposition.again Before (M.vBecome S x)).presup e ∧ P x e

/-- On the repetitive reading *again* modifies the whole predicate, so the sentence presupposes
that the whole event happened before. -/
def Repetitive (P : Entity → Event T → Prop) (x : Entity) (e : Event T) : Prop :=
  (Presupposition.again Before (P x)).holds e

variable {M manip S} {x y z : Entity} {e : Event T}

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
theorem ingest_of_causerAddition {ingest : Entity → Event T → Prop}
    (h : causerAddition M ingest y x e) : ingest x e :=
  let ⟨_, _, _, h⟩ := h; h

/-- For a predicate with a result state, the repetitive reading of *again* entails the
restitutive one. -/
theorem restitutive_of_repetitive {P : Entity → Event T → Prop}
    (hP : ∀ x e, P x e → M.vBecome S x e) (h : Repetitive P x e) : Restitutive M S P x e :=
  ⟨Presupposition.again_presup_mono (hP x) e h.1, h.2⟩

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
private def ev (s t : ℤ) (h : s ≤ t := by decide) : Event ℤ := ⟨⟨(s, t), h⟩, .action⟩

/-- The event running from `s` to `t`. -/
private def At (w : Event ℤ) (s t : ℤ) : Prop := w.τ.toProd = (s, t)

private def w₀ : Event ℤ := ev 0 1
private def e₀ : Event ℤ := ev 1 2
private def w₁ : Event ℤ := ev 0 2
private def w₂ : Event ℤ := ev 3 4
private def e₁ : Event ℤ := ev 4 5

/-- The state of potential digestion holds of John. -/
def digesting (x : Participant) (_ : Unit) : Prop := x = .john

/-- A model in which the events `causing` lists bring John to potential digestion, with `eff`
the effectors of events. -/
def eating (causing : Event ℤ → Event ℤ → Prop) (eff : Participant → Event ℤ → Prop) :
    ArgumentStructure.ChangeOfStateModel Participant Unit (Event ℤ) where
  become _ e := ∃ w, causing w e
  cause := causing
  effector := eff

/-- Mary manipulates the food. -/
def spoonManip (y : Participant) (w : Event ℤ) : Prop := y = .mary ∧ At w 0 1

/-- In spoon feeding ((44a)) Mary's manipulation of the food causes John's change. -/
def spoonFeeding :
    ArgumentStructure.ChangeOfStateModel Participant Unit (Event ℤ) :=
  eating (fun w e ↦ At w 0 1 ∧ At e 1 2) spoonManip

/-- John manipulates the food. -/
def supManip (y : Participant) (w : Event ℤ) : Prop := y = .john ∧ At w 0 1

/-- Under supervision ((48)) John's manipulation of the food and Mary's supervising action both
cause John's change. -/
def supervising :
    ArgumentStructure.ChangeOfStateModel Participant Unit (Event ℤ) :=
  eating (fun w e ↦ (At w 0 1 ∨ At w 0 2) ∧ At e 1 2)
    (fun y w ↦ (y = .john ∧ At w 0 1) ∨ (y = .mary ∧ At w 0 2))

/-- Mary manipulates the food the first time, John the second. -/
def twoManip (y : Participant) (w : Event ℤ) : Prop :=
  (y = .mary ∧ At w 0 1) ∨ (y = .john ∧ At w 3 4)

/-- In the model of two meals Mary feeds John, and later John eats. -/
def twoMeals :
    ArgumentStructure.ChangeOfStateModel Participant Unit (Event ℤ) :=
  eating (fun w e ↦ (At w 0 1 ∧ At e 1 2) ∨ (At w 3 4 ∧ At e 4 5)) twoManip

/-- *I didn't eat pie; you fed pie to me* ((92), (106)) is consistent, since John, fed by Mary,
did not eat, having manipulated no food ((44a)). -/
theorem not_eat_and_feed :
    ¬ eat spoonFeeding spoonManip digesting .john e₀ ∧
      feed spoonFeeding spoonManip digesting .mary .john e₀ :=
  ⟨fun ⟨_, ⟨h, _⟩, _⟩ ↦ Participant.noConfusion h,
    ⟨w₀, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, (), ⟨w₀, rfl, rfl⟩, rfl⟩⟩

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
  ⟨⟨w₁, Or.inr ⟨rfl, rfl⟩, ⟨Or.inr rfl, rfl⟩, w₀, ⟨rfl, rfl⟩, ⟨Or.inl rfl, rfl⟩, (),
      ⟨w₀, Or.inl rfl, rfl⟩, rfl⟩,
    fun ⟨_, ⟨h, _⟩, _⟩ ↦ Participant.noConfusion h⟩

/-- Being fed does not license *by itself* ((113d)), since John reaches the state but the
effector of the causing event is Mary. -/
theorem not_licensesBySelf_inchoative :
    ¬ LicensesBySelf spoonFeeding (spoonFeeding.vBecome digesting) := fun h ↦
  let ⟨_, _, hw⟩ := h .john e₀ ⟨(), ⟨w₀, rfl, rfl⟩, rfl⟩
  Participant.noConfusion hw.1

/-- When *John ate again* ((70), (79)) is said after Mary had fed him, the restitutive reading
holds, the state of potential digestion having come about before, and the repetitive reading
fails. -/
theorem restitutive_not_repetitive :
    Restitutive twoMeals digesting (eat twoMeals twoManip digesting) .john e₁ ∧
      ¬ Repetitive (eat twoMeals twoManip digesting) .john e₁ :=
  ⟨⟨⟨e₀, by decide, (), ⟨w₀, Or.inl ⟨rfl, rfl⟩⟩, rfl⟩,
      w₂, Or.inr ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩, (), ⟨w₂, Or.inr ⟨rfl, rfl⟩⟩, rfl⟩,
    fun ⟨⟨e', hb, w, hm, hc, _⟩, _⟩ ↦ by
      rcases hm with ⟨h, _⟩ | ⟨_, hw⟩
      · exact Participant.noConfusion h
      rcases hc with ⟨h, _⟩ | ⟨_, he⟩
      · exact absurd (hw.symm.trans h) (by decide)
      · have hb' : e'.τ.toProd.2 ≤ 4 := hb
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
