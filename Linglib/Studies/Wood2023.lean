import Linglib.Morphology.DistributedMorphology.Allosemy
import Linglib.Morphology.DistributedMorphology.Locality
import Linglib.Fragments.Icelandic.Nominalizations
import Linglib.Data.Examples.Wood2023

/-!
# Wood (2023): Icelandic Nominalizations and Allosemy

This file formalizes [wood-2023]'s account of Icelandic deverbal nominalizations as complex
heads: a root categorized by v and then by n, with no verb phrase and no Voice, whose
ambiguity between complex event, simple event, and referring readings is allosemy of v and n
(`Derivation`). A complex event nominal has eventive v and zero n, so the noun inherits the
verb's meaning; the simple readings have zero v and a contentful n. Borer's Generalization,
that a complex event reading entails a morphologically related verb with that meaning, follows
from two facts: only v introduces the event variable, and n is not in the root's domain, so it
cannot condition root suppletion past v (`borers_generalization`). The nominal's external
argument is introduced by i*, the head that is Voice in the verbal domain, interpreted as an
agent in the context of an eventive nP and as a possessor otherwise (`IStar.alloseme`).

Special meaning is subject to phase locality: a dependency may cross at most one categorizer
(`Local`). A preposition heading the PP complement of a nominal is separated from the root by
v and n, so a preposition that conditions the root's meaning must adjoin to the complex n head
as a prefix, while one with its own meaning heads a PP, and one that does both is doubled
(`nominal_complement_not_local`). The same bound lets n condition an idiosyncratic root meaning
across v (`nominal_n_local`) and forbids it in *-væðing* nominals, where *-væða* is a compound
head attaching to a categorized word, so that two categorizers separate the root from the
outer n (`vaeda_n_not_local`). The prefixes *marg-* and *endur-* are event modifiers: *marg-*
adjoins to v, *endur-* to v or to n, and each needs an event variable at its host, which
licenses *marg-* exactly on nominals whose v is eventive and *endur-* also on simple event and
result nominals but not on simple entities (`Licensed`).

## Implementation notes

Wood's bound for allosemy, one intervening categorizer, is one phase looser than
`Spine.RootLocal`, the bound the book keeps for root suppletion; the study states the strict
one through the substrate. A preposition adjoined to a complex head has no spine position,
since a head does not c-command its own adjunct, so the heads between a preposition and the
root are read off its attachment. The event-modifier account licenses *marg-* on a result
nominal built on eventive v, a case the book does not test.

## References

* [wood-2023]
* [embick-2010]
* [marantz-2013]
* [wood-marantz-2017]
* [myler-2016]
-/

namespace Wood2023

open DistributedMorphology DistributedMorphology.Allosemy Icelandic.Nominalizations

/-! ### The complex head and its readings -/

/-- A head of the complex head: a categorizer with its alloseme. -/
inductive Head where
  | v (a : Verbalizer.Alloseme)
  | n (a : Nominalizer.Alloseme)
  deriving DecidableEq, Repr

/-- Every head of the complex head is a categorizer, hence a phase head. -/
def Head.Cyclic : Head → Prop := λ _ => True

instance : DecidablePred Head.Cyclic := λ _ => inferInstanceAs (Decidable True)

/-- A choice of allosemes for the v and n of a nominalization. -/
structure Derivation where
  v : Verbalizer.Alloseme
  n : Nominalizer.Alloseme
  deriving DecidableEq, Fintype

namespace Derivation

/-- The reading the allosemes yield. -/
def reading (d : Derivation) : Option NominalizationReading := readingFromAllosemes d.v d.n

/-- The heads of the nominalization, innermost first. -/
def heads (d : Derivation) : List Head := [.v d.v, .n d.n]

/-- The complex event derivation: eventive v, zero n. -/
def cen : Derivation := ⟨.eventive, .zero⟩

/-- The simple event derivation: zero v, the simple event alloseme of n. -/
def sen : Derivation := ⟨.zero, .simpleEvent⟩

/-- The simple entity derivation: zero v, the entity alloseme of n. -/
def simpleEntity : Derivation := ⟨.zero, .entity⟩

/-- The result derivation: eventive v, the result alloseme of n. -/
def result : Derivation := ⟨.eventive, .result⟩

theorem reading_cen : cen.reading = some .complexEvent := rfl

theorem reading_sen : sen.reading = some .simpleEvent := rfl

theorem reading_simpleEntity : simpleEntity.reading = some .simpleEntity := rfl

theorem reading_result : result.reading = some .result := rfl

/-- The nP denotes an event when v is eventive and n passes its meaning up unchanged. -/
def Eventive (d : Derivation) : Prop := d.v = .eventive ∧ d.n = .zero

instance : DecidablePred Eventive := λ _ => inferInstanceAs (Decidable (_ ∧ _))

/-- The complex event reading is exactly the eventive nP. -/
theorem eventive_iff (d : Derivation) : d.Eventive ↔ d.reading = some .complexEvent := by
  revert d; decide

end Derivation

/-- Every reading the fragment lists is derived by some choice of allosemes. -/
theorem fragment_readings_derivable :
    ∀ nm ∈ allNoms, ∀ rd ∈ nm.availableReadings,
      ∃ d : Derivation, d.reading = some rd := by
  decide

/-- The reading is not a function of the suffix: the same suffix yields different readings. -/
theorem readings_not_by_suffix :
    opnun.suffix = notkun.suffix ∧ opnun.availableReadings ≠ notkun.availableReadings := by
  decide

/-! ### Spines -/

/-- The verb: the root categorized by eventive v. -/
def verb (r : Root) : Spine Head := ⟨r, [.v .eventive]⟩

/-- The nominalization: the root categorized by v and then by n. -/
def nominal (r : Root) (d : Derivation) : Spine Head := ⟨r, d.heads⟩

/-- A *-væða* verb: the root categorized by n, compounded with the v of *-væða*. -/
def vaedaVerb (r : Root) (a : Nominalizer.Alloseme) : Spine Head := ⟨r, [.n a, .v .eventive]⟩

/-- A *-væðing* nominal: the *-væða* verb categorized by n. -/
def vaedaNominal (r : Root) (a c : Nominalizer.Alloseme) : Spine Head :=
  ⟨r, (vaedaVerb r a).heads ++ [.n c]⟩

/-! ### Borer's Generalization -/

/-- The n of a nominalization is not in the root's domain: category change closes it. -/
theorem nominal_n_not_rootLocal (r : Root) (d : Derivation) :
    ¬ (nominal r d).RootLocal Head.Cyclic ⟨1, Nat.one_lt_two⟩ :=
  Spine.not_rootLocal_of_cyclic_of_cyclic (j := ⟨0, Nat.two_pos⟩)
    (Fin.mk_lt_mk.2 Nat.zero_lt_one) trivial trivial

/-- Borer's Generalization: a complex event nominal contains the eventive v of the verb, and
its n cannot condition suppletion of the root, so the nominal is built on a verb with the
same root exponent and the same meaning. -/
theorem borers_generalization (r : Root) {d : Derivation}
    (h : d.reading = some .complexEvent) :
    d.v = .eventive ∧ ¬ (nominal r d).RootLocal Head.Cyclic ⟨1, Nat.one_lt_two⟩ :=
  ⟨((Derivation.eventive_iff d).2 h).1, nominal_n_not_rootLocal r d⟩

/-! ### The external argument -/

/-- The contentful allosemes of i*, the external-argument head that is Voice in the verbal
domain and Poss in the nominal domain. -/
inductive IStar.Contentful where
  | agent
  | possessor
  deriving DecidableEq, Repr, Fintype

/-- The allosemes of i*. -/
abbrev IStar.Alloseme := Allosemy.Alloseme IStar.Contentful

namespace IStar.Alloseme

@[match_pattern] def agent : IStar.Alloseme := Allosemy.Alloseme.of .agent

@[match_pattern] def possessor : IStar.Alloseme := Allosemy.Alloseme.of .possessor

end IStar.Alloseme

/-- i* is an agent in the context of an eventive complement and a possessor elsewhere. -/
def IStar.vocabulary : List (VocabularyItem Feature IStar.Alloseme) :=
  [⟨complement [.eventive], .agent⟩, [] ⟷ .possessor]

/-- The alloseme of i* selected by its complement's features. -/
def IStar.alloseme (fs : List Feature) : IStar.Alloseme :=
  (subsetPrinciple IStar.vocabulary (complement fs)).getD .possessor

/-- The features an nP presents to i*: its category, and eventivity when it denotes an
event. -/
def Derivation.features (d : Derivation) : List Feature :=
  if d.Eventive then [.cat .n, .eventive] else [.cat .n]

/-- The possessor of a nominal is its agent exactly on the complex event reading. -/
theorem iStar_agent_iff (d : Derivation) :
    IStar.alloseme d.features = .agent ↔ d.reading = some .complexEvent := by
  rw [← Derivation.eventive_iff]
  by_cases h : d.Eventive
  · rw [Derivation.features, ite_eq_left h]; exact iff_of_true (by decide) h
  · rw [Derivation.features, ite_eq_right h]; exact iff_of_false (by decide) h

/-! ### Phase locality of special meaning -/

/-- Wood's phase locality: a dependency conditioning special meaning may cross at most one
categorizer. -/
def Local (between : List Head) : Prop := between.length ≤ 1

/-- Where a preposition attaches to a complex head: adjoined to it, or heading its
complement PP. -/
inductive Attachment where
  | adjunct
  | complement
  deriving DecidableEq, Repr

/-- The heads between a preposition and the root: every head of the complex head when the
preposition heads its complement, all but the outermost when it adjoins to the complex head,
since a head does not c-command its own adjunct. -/
def interveners (s : Spine Head) : Attachment → List Head
  | .complement => s.heads
  | .adjunct => s.heads.dropLast

/-- Adjunction is at least as local as complementation. -/
theorem Local.adjunct_of_complement {s : Spine Head}
    (h : Local (interveners s .complement)) : Local (interveners s .adjunct) := by
  simp only [Local, interveners, List.length_dropLast] at h ⊢; omega

/-- A preposition may condition the root of a verb whether adjoined or in its complement. -/
theorem verb_local (r : Root) (a : Attachment) : Local (interveners (verb r) a) := by
  cases a <;> simp [Local, interveners, verb]

/-- A preposition heading the complement of a nominal cannot condition its root: v and n
intervene. A preposition that conditions the root's meaning must therefore be prefixed. -/
theorem nominal_complement_not_local (r : Root) (d : Derivation) :
    ¬ Local (interveners (nominal r d) .complement) := by
  simp [Local, interveners, nominal, Derivation.heads]

/-- A preposition adjoined to the complex n head may condition the root: only v intervenes. -/
theorem nominal_adjunct_local (r : Root) (d : Derivation) :
    Local (interveners (nominal r d) .adjunct) := by
  simp [Local, interveners, nominal, Derivation.heads]

/-- The n of a nominalization may condition an idiosyncratic meaning of the root across v. -/
theorem nominal_n_local (r : Root) (d : Derivation) : Local ((nominal r d).heads.take 1) := by
  simp [Local, nominal, Derivation.heads]

/-- The outer n of a *-væðing* nominal cannot condition the root: the inner n and v intervene,
so the nominal has no idiosyncratic referring reading. -/
theorem vaeda_n_not_local (r : Root) (a c : Nominalizer.Alloseme) :
    ¬ Local ((vaedaNominal r a c).heads.take 2) := by
  simp [Local, vaedaNominal, vaedaVerb]

/-- A PP complement of a *-væða* verb cannot condition its root: its interpretation is
compositional. -/
theorem vaeda_complement_not_local (r : Root) (a : Nominalizer.Alloseme) :
    ¬ Local (interveners (vaedaVerb r a) .complement) := by
  simp [Local, interveners, vaedaVerb]

/-! ### The prefixes *marg-* and *endur-* -/

/-- The event-modifying prefixes: iterative *marg-* 'many' and *endur-* 're-'. -/
inductive Prefix where
  | marg
  | endur
  deriving DecidableEq, Repr

/-- The heads a prefix adjoins to at the complex head: *marg-* to v, *endur-* to v or n. -/
def Prefix.AdjoinsTo : Prefix → Head → Prop
  | .marg, .v _ => True
  | .marg, .n _ => False
  | .endur, _ => True

/-- Whether a head's alloseme carries an event variable: eventive v, and the simple event and
result allosemes of n. -/
def Head.HasEvent : Head → Prop
  | .v a => a = .eventive
  | .n a => a = .simpleEvent ∨ a = .result

/-- A prefix is licensed on a nominalization when some head it adjoins to there carries an
event variable. -/
def Licensed (p : Prefix) (d : Derivation) : Prop :=
  ∃ h ∈ d.heads, p.AdjoinsTo h ∧ h.HasEvent

/-- *marg-* is licensed exactly when v is eventive. -/
theorem licensed_marg_iff (d : Derivation) : Licensed .marg d ↔ d.v = .eventive := by
  simp [Licensed, Derivation.heads, Prefix.AdjoinsTo, Head.HasEvent]

/-- *endur-* is licensed exactly when v or n carries an event variable. -/
theorem licensed_endur_iff (d : Derivation) :
    Licensed .endur d ↔ d.v = .eventive ∨ d.n = .simpleEvent ∨ d.n = .result := by
  simp [Licensed, Derivation.heads, Prefix.AdjoinsTo, Head.HasEvent]

/-- *marg-* is stricter than *endur-*. -/
theorem Licensed.endur {d : Derivation} (h : Licensed .marg d) : Licensed .endur d :=
  (licensed_endur_iff d).2 (Or.inl ((licensed_marg_iff d).1 h))

/-- *marg-* on *þvottur*: in on the complex event reading, out on the simple event and entity
readings. -/
theorem marg_pvottur :
    Licensed .marg .cen ∧ ¬ Licensed .marg .sen ∧ ¬ Licensed .marg .simpleEntity := by
  simp only [licensed_marg_iff]; decide

/-- *endur-* on *þvottur* and *prentun*: in on the complex event, simple event, and result
readings, out on the entity reading. -/
theorem endur_pvottur_prentun :
    Licensed .endur .cen ∧ Licensed .endur .sen ∧ Licensed .endur .result ∧
      ¬ Licensed .endur .simpleEntity := by
  simp only [licensed_endur_iff]; decide

end Wood2023
