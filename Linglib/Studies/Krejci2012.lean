import Linglib.Studies.KoontzGarboden2009
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Core.Order.UpperLower.Finset
import Mathlib.Tactic.DeriveFintype

/-!
# Krejci (2012): Causativization as Antireflexivization

This file formalizes [krejci-2012]'s account of why middle and ingestive verbs (*wash*,
*dress*; *eat*, *learn*) causativize like intransitives in languages that mark causatives
morphologically. The report's survey orders verb classes on a hierarchy of causativizability,
unaccusatives before middles and ingestives before unergatives before simple transitives, on
which no language's causative process skips a tier. Its explanation is that the simple forms
of these verbs are lexically reflexive: their event structure is already causative, with the
causer and the causee coidentified, and the lexical causative (*feed*, *teach*, transitive
*wash* and *dress*) arises by antireflexivization, which delinks the two arguments. This is
the reflexivization analysis of [koontz-garboden-2009] read in the opposite direction of
derivation, so the simple form is that study's `reflexivize` applied to its `causative`.

On a model of *eat*, *feed* and *make eat*, the entailments of the simple form split between
the causer and the causee of the lexical causative but stay with the causee of the
periphrastic causative (`feed_not_makeEat`); denying the simple form while asserting the
lexical causative is consistent on the bieventive representation (`not_eat_and_feed`) and
contradictory under causer addition; the result state supports a restitutive reading of
*again* that the repetitive reading does not exhaust; and *by itself* is licensed. The
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
* [koontz-garboden-2009] — reflexivization, *by itself*, and denial of the simple form
* [chierchia-2004] — *by itself*
* [dowty-1979] — the *again* test
-/

namespace Krejci2012

open KoontzGarboden2009 ArgumentStructure

/-! ### Antireflexivization -/

section Model

variable {Entity State T : Type*} [LinearOrder T] (M : Verb.CosModel Entity State T)
  (manip : Entity → Event T → Prop) (v : Verb)

/-- The lexical causative (38a): the causer's manipulation of food brings the causee to the
state of potential digestion. -/
abbrev feed : Entity → Entity → Event T → Prop := causative M manip v

/-- The simple form (37a) is the lexical causative on its diagonal: the eater manipulates the
food and comes to digest it. Antireflexivization ((96)–(97)) delinks the two arguments. -/
abbrev eat : Entity → Event T → Prop := reflexivize (feed M manip v)

/-- The periphrastic causative *make eat*: a further causing event, with its own effector, of
an eating. -/
def makeEat (z x : Entity) (e : Event T) : Prop :=
  ∃ w, M.effector z w ∧ M.cause w e ∧ eat M manip v x e

/-- Causativization by causer addition ((94)), the analysis the report rejects: the simple
form is an activity `ingest` with no causing subevent, and the causative adds a causer. -/
def causerAddition (ingest : Entity → Event T → Prop) (y x : Entity) (e : Event T) : Prop :=
  ∃ w, M.effector y w ∧ M.cause w e ∧ ingest x e

/-- The restitutive reading of *again*: the result state held before. -/
def Restitutive (P : Entity → Event T → Prop) (x : Entity) (e : Event T) : Prop :=
  P x e ∧ ∃ e', e'.τ.isBefore e.τ ∧ M.inchoative v x e'

/-- The repetitive reading of *again*: the whole event happened before. -/
def Repetitive (P : Entity → Event T → Prop) (x : Entity) (e : Event T) : Prop :=
  P x e ∧ ∃ e', e'.τ.isBefore e.τ ∧ P x e'

variable {M manip v} {x y z : Entity} {e : Event T}

/-- The simple form is the derived inchoative of [koontz-garboden-2009]. -/
theorem eat_eq_anticausative : eat M manip v = anticausative M manip v := rfl

/-- The eater manipulates food ((39a)). -/
theorem exists_manip_of_eat (h : eat M manip v x e) : ∃ w, manip x w ∧ M.cause w e :=
  exists_cause_of_anticausative h

/-- The feeder manipulates food ((45)). -/
theorem exists_manip_of_feed (h : feed M manip v y x e) : ∃ w, manip y w ∧ M.cause w e :=
  let ⟨w, h₁, h₂, _⟩ := h; ⟨w, h₁, h₂⟩

/-- Whoever is fed comes to potential digestion ((44c)). -/
theorem inchoative_of_feed (h : feed M manip v y x e) : M.inchoative v x e :=
  let ⟨_, _, _, h⟩ := h; h

/-- Whoever is made to eat manipulates food ((47a)). -/
theorem exists_manip_of_makeEat (h : makeEat M manip v z x e) :
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
    (hP : ∀ x e, P x e → M.inchoative v x e) (h : Repetitive P x e) : Restitutive M v P x e :=
  let ⟨he, e', hb, he'⟩ := h; ⟨he, e', hb, hP x e' he'⟩

/-- *By itself* ((114a), after [koontz-garboden-2009]): eating has a causing subevent whose
effector is the eater, once manipulating food makes one an effector. -/
theorem licensesBySelf_eat (h : ∀ x w, manip x w → M.effector x w) :
    LicensesBySelf M (eat M manip v) :=
  λ _ _ he => let ⟨w, hm, hc⟩ := exists_manip_of_eat he; ⟨w, hc, h _ _ hm⟩

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

private def eatV : Verb := English.Predicates.Verbal.eat.toVerb

/-- A model in which the events `causing` lists bring John to potential digestion, with `eff`
the effectors of events. -/
def eating (causing : Event ℤ → Event ℤ → Prop) (eff : Participant → Event ℤ → Prop) :
    Verb.CosModel Participant Unit ℤ where
  rootState _ x _ := x = .john
  become _ e := ∃ w, causing w e
  cause := causing
  effector := eff
  manner _ _ := False

/-- Mary manipulates the food. -/
def spoonManip (y : Participant) (w : Event ℤ) : Prop := y = .mary ∧ At w 0 1

/-- Spoon feeding ((44a)): Mary's manipulation of the food causes John's change. -/
def spoonFeeding : Verb.CosModel Participant Unit ℤ :=
  eating (λ w e => At w 0 1 ∧ At e 1 2) spoonManip

/-- John manipulates the food. -/
def supManip (y : Participant) (w : Event ℤ) : Prop := y = .john ∧ At w 0 1

/-- Supervision ((48)): John's manipulation of the food and Mary's supervising action both
cause John's change. -/
def supervising : Verb.CosModel Participant Unit ℤ :=
  eating (λ w e => (At w 0 1 ∨ At w 0 2) ∧ At e 1 2)
    (λ y w => (y = .john ∧ At w 0 1) ∨ (y = .mary ∧ At w 0 2))

/-- Mary manipulates the food the first time, John the second. -/
def twoManip (y : Participant) (w : Event ℤ) : Prop :=
  (y = .mary ∧ At w 0 1) ∨ (y = .john ∧ At w 3 4)

/-- Two meals: Mary feeds John, and later John eats. -/
def twoMeals : Verb.CosModel Participant Unit ℤ :=
  eating (λ w e => (At w 0 1 ∧ At e 1 2) ∨ (At w 3 4 ∧ At e 4 5)) twoManip

/-- *I didn't eat pie; you fed pie to me* ((92), (106)) is consistent: John, fed by Mary, did
not eat, since he manipulated no food ((44a)). -/
theorem not_eat_and_feed :
    ¬ eat spoonFeeding spoonManip eatV .john e₀ ∧
      feed spoonFeeding spoonManip eatV .mary .john e₀ :=
  ⟨λ ⟨_, ⟨h, _⟩, _⟩ => Participant.noConfusion h,
    ⟨w₀, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, (), ⟨w₀, rfl, rfl⟩, rfl⟩⟩

/-- Feeding is not making eat: John, fed, was not made to eat, as whoever is made to eat
manipulates food ((47a)). -/
theorem feed_not_makeEat :
    feed spoonFeeding spoonManip eatV .mary .john e₀ ∧
      ¬ makeEat spoonFeeding spoonManip eatV .mary .john e₀ :=
  ⟨not_eat_and_feed.2, λ ⟨_, _, _, h⟩ => not_eat_and_feed.1 h⟩

/-- Making eat is not feeding ((48)): Mary made John eat without touching any food. -/
theorem makeEat_not_feed :
    makeEat supervising supManip eatV .mary .john e₀ ∧
      ¬ feed supervising supManip eatV .mary .john e₀ :=
  ⟨⟨w₁, Or.inr ⟨rfl, rfl⟩, ⟨Or.inr rfl, rfl⟩, w₀, ⟨rfl, rfl⟩, ⟨Or.inl rfl, rfl⟩, (),
      ⟨w₀, Or.inl rfl, rfl⟩, rfl⟩,
    λ ⟨_, ⟨h, _⟩, _⟩ => Participant.noConfusion h⟩

/-- Being fed does not license *by itself* ((113d)): John reaches the state, but the effector
of the causing event is Mary. -/
theorem not_licensesBySelf_inchoative :
    ¬ LicensesBySelf spoonFeeding (spoonFeeding.inchoative eatV) := λ h =>
  let ⟨_, _, hw⟩ := h .john e₀ ⟨(), ⟨w₀, rfl, rfl⟩, rfl⟩
  Participant.noConfusion hw.1

/-- *John ate again* ((70), (79)) after Mary had fed him: the restitutive reading holds, the
state of potential digestion having held before, and the repetitive reading fails. -/
theorem restitutive_not_repetitive :
    Restitutive twoMeals eatV (eat twoMeals twoManip eatV) .john e₁ ∧
      ¬ Repetitive (eat twoMeals twoManip eatV) .john e₁ :=
  ⟨⟨⟨w₂, Or.inr ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩, (), ⟨w₂, Or.inr ⟨rfl, rfl⟩⟩, rfl⟩,
      e₀, by decide, (), ⟨w₀, Or.inl ⟨rfl, rfl⟩⟩, rfl⟩,
    λ ⟨_, e', hb, w, hm, hc, _⟩ => by
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

/-- A causative process of a language: the tiers whose verbs it applies to. -/
structure Causative where
  language : String
  morpheme : String
  reach : Finset Tier

namespace Causative

/-- The hierarchy: a process reaching a tier reaches every tier before it. -/
def RespectsHierarchy (c : Causative) : Prop := IsLowerSet (↑c.reach : Set Tier)

instance : DecidablePred RespectsHierarchy := λ _ => inferInstanceAs (Decidable (IsLowerSet _))

/-- The type of a process, (1) to (4) of Table 2.8: the last tier it reaches. -/
def type (c : Causative) : WithBot Tier := c.reach.max

/-- A process that respects the hierarchy reaches exactly the tiers up to its type. -/
theorem mem_reach_iff {c : Causative} (h : c.RespectsHierarchy) (t : Tier) :
    t ∈ c.reach ↔ ↑t ≤ c.type := by
  refine ⟨Finset.le_max, λ ht => ?_⟩
  unfold type at ht
  rcases hm : c.reach.max with _ | m <;> rw [hm] at ht
  · exact absurd ht (WithBot.not_coe_le_bot t)
  · exact h (WithBot.coe_le_coe.1 ht) (Finset.mem_of_max hm)

end Causative

/-- Table 2.8: the surveyed languages, three of each type. Malayalam reaches transitives only
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
