import Linglib.Data.Examples.Tay2024
import Linglib.Fragments.Mandarin.Resultatives
import Linglib.Morphology.Word.Tree
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

/-!
# Tay (2024): Resultative Expressions in Mandarin Chinese

This file formalizes Tay's account of why Mandarin V-V resultatives realize their
arguments more freely than V-*de* resultatives and English resultatives. A V-V resultative is a
synthetic compound built in morphology, V1-∅-V2, so its components are inaccessible to syntactic
operations, chapter 2: a locative can modify V1 of a V-*de* resultative but not of the compound,
(45)–(46), and *repeatedly* has only the whole-event reading on the compound, (41)–(44). The
null affix ∅ introduces a macroevent containing a causing event described by V1 and a caused
event described by V2, inherits every argument of V2, and existentially closes every argument
of V1 (110), `nullAffix`; the variant ∅+C also introduces a causer, the crucial contributory
factor of the macroevent (111), `nullAffixC`. The causer is an argument of the macroevent and not
of V1's event, `nullAffixC_iff`, and V1's arguments are closed, `nullAffix_of`, so no syntactic
requirement relates the arguments of the compound to those of V1: the external argument can be
V1's agent (131)–(132) or its theme (133)–(134), the internal argument need not be V1's agent
(202)–(206), and the sole argument of an unaccusative compound can be V1's agent (219), which is
why Mandarin has subject-oriented resultatives without a reflexive.

What does constrain the external argument is the Onset Condition (141): an event integrated
into the macroevent of a simplex causative is the initial event of its causal chain. Since the
causer is a participant in that initial event, and V1's event is integrated, the causer is a
participant in V1's event, `Macroevent.participant_of_onset`: no pure causers, (146)–(149),
while subject matters are participants, (150)–(151). The macroevent must contain the two
subevents rather than identify or nest them: in *shè-sǐ* 'shoot dead' (107) the shooting and the
dying overlap at the moment of contact only, so their traces are neither equal nor nested,
`shooting_trieventive`. Chapter 8's typology varies three dimensions, whether the null head
merges in morphology, whether the result X can be a verb, and whether a transitive resultative
takes an intransitive X, `ResultativeType`, with Mandarin, English and Japanese as the settled
cases.

## Implementation notes

Predicates take their arguments as tuples `Fin n → D`, so a family of null affixes indexed by
the arities of V1 and V2 is one definition. The causal relation between the macroevent and its
subevents and the participant relation are parameters; the thesis takes the former to be
Lewis's counterfactual causation and leaves its precise characterization open. Temporal traces
are rational intervals. The examples are rows of `Data.Examples.Tay2024` and the compounds
are entries of `Fragments/Mandarin/Resultatives.lean`, which record no orientation: the
apparent subject-oriented transitives *chī-bǎo* (3) and *qí-lèi* (330) are the hybrid
resultatives of chapter 4, whose postverbal phrase is an argument of V2, and that chapter, the
V-*de* construction's syntax (chapter 6), the case against the No Argument Theory (chapter 5),
and the one-causer-per-event condition are not formalized.

## References

* [tay-2024]
-/

namespace Tay2024

open Mandarin Morphology

/-! ### The null affix (chapter 2, section 3.3) -/

section NullAffix

variable {E D : Type*} {m n : ℕ}

/-- The null affix (110) introduces a macroevent `e` containing a causing event `e₁` described by
V1, whose arguments are existentially closed, and a caused event `e₂` described by V2, whose
arguments the compound inherits. -/
def nullAffix (cause : E → E → E → Prop) (R2 : E → (Fin n → D) → Prop)
    (R1 : E → (Fin m → D) → Prop) (e : E) (ys : Fin n → D) : Prop :=
  ∃ e₁ e₂ xs, cause e e₁ e₂ ∧ R2 e₂ ys ∧ R1 e₁ xs

/-- The null affix (111) also introduces `c`, the crucial contributory factor of the macroevent. -/
def nullAffixC (cause : E → E → E → Prop) (ccf : E → D → Prop) (R2 : E → (Fin n → D) → Prop)
    (R1 : E → (Fin m → D) → Prop) (e : E) (c : D) (ys : Fin n → D) : Prop :=
  ∃ e₁ e₂ xs, cause e e₁ e₂ ∧ ccf e c ∧ R2 e₂ ys ∧ R1 e₁ xs

variable (cause : E → E → E → Prop) (ccf : E → D → Prop) (R2 : E → (Fin n → D) → Prop)
  (R1 : E → (Fin m → D) → Prop) {e e₁ e₂ : E} {c : D} {ys : Fin n → D} {xs : Fin m → D}

/-- The causer is an argument of the macroevent alone and enters no relation with the arguments
of V1. -/
theorem nullAffixC_iff :
    nullAffixC cause ccf R2 R1 e c ys ↔ ccf e c ∧ nullAffix cause R2 R1 e ys := by
  simp only [nullAffixC, nullAffix]
  constructor
  · rintro ⟨e₁, e₂, xs, hc, hccf, h2, h1⟩
    exact ⟨hccf, e₁, e₂, xs, hc, h2, h1⟩
  · rintro ⟨hccf, e₁, e₂, xs, hc, h2, h1⟩
    exact ⟨e₁, e₂, xs, hc, hccf, h2, h1⟩

/-- Any arguments of V1 witness the compound, so nothing requires the compound's arguments to be
interpreted as arguments of V1, and nothing forbids it. -/
theorem nullAffix_of (hc : cause e e₁ e₂) (h2 : R2 e₂ ys) (h1 : R1 e₁ xs) :
    nullAffix cause R2 R1 e ys :=
  ⟨e₁, e₂, xs, hc, h2, h1⟩

/-- The external argument of a transitive compound may be any argument of V1 or none of them
(131)–(134): the causer and the closed arguments of V1 are chosen independently. -/
theorem nullAffixC_of (hc : cause e e₁ e₂) (hccf : ccf e c) (h2 : R2 e₂ ys) (h1 : R1 e₁ xs) :
    nullAffixC cause ccf R2 R1 e c ys :=
  ⟨e₁, e₂, xs, hc, hccf, h2, h1⟩

/-- The sole argument of an unaccusative compound may be the agent of V1 (219), so a
subject-oriented resultative needs no reflexive. -/
theorem nullAffix_of_agent {R2 R1 : E → (Fin 1 → D) → Prop} {y : D} (hc : cause e e₁ e₂)
    (h2 : R2 e₂ ![y]) (h1 : R1 e₁ ![y]) : nullAffix cause R2 R1 e ![y] :=
  nullAffix_of cause R2 R1 hc h2 h1

end NullAffix

/-! ### The Onset Condition (chapter 3, section 2.2) -/

section Onset

variable {E D : Type*} (participant : E → D → Prop)

/-- A change-of-state macroevent as a causal chain (136), in causal order, with its crucial
contributory factor, the essential factor in bringing about the result, which is a participant
in the initial event of the chain. -/
structure Macroevent where
  /-- The subevents of the causal chain, in causal order. -/
  chain : List E
  chain_ne : chain ≠ []
  /-- The crucial contributory factor. -/
  ccf : D
  ccf_initial : participant (chain.head chain_ne) ccf

variable {participant}

namespace Macroevent

/-- The Onset Condition (141) says that an event integrated into the macroevent of a simplex
causative is the initial event of its causal chain. -/
def Onset (M : Macroevent participant) (e₁ : E) : Prop := e₁ = M.chain.head M.chain_ne

/-- A pure causer of an event is a crucial contributory factor that is not a participant in it. -/
def PureCauser (M : Macroevent participant) (e₁ : E) : Prop := ¬ participant e₁ M.ccf

/-- There are no pure causers; the event of V1 being integrated, the causer participates in it. -/
theorem participant_of_onset {M : Macroevent participant} {e₁ : E} (h : M.Onset e₁) :
    participant e₁ M.ccf :=
  h ▸ M.ccf_initial

theorem not_pureCauser_of_onset {M : Macroevent participant} {e₁ : E} (h : M.Onset e₁) :
    ¬ M.PureCauser e₁ :=
  fun hp ↦ hp (participant_of_onset h)

end Macroevent

end Onset

/-! ### Trieventive structure (chapter 2, section 3.3) -/

section Traces

variable {E : Type*} (trace : E → Set ℚ)

/-- On the monoeventive analysis (104) V1 and V2 describe one event, so one temporal trace. -/
def Monoeventive (e₁ e₂ : E) : Prop := trace e₁ = trace e₂

/-- On the bieventive analyses (105)–(106) one event is temporally contained in the other. -/
def Bieventive (e₁ e₂ : E) : Prop := trace e₂ ⊆ trace e₁ ∨ trace e₁ ⊆ trace e₂

/-- The events of *shè-sǐ* 'shoot dead' (107). -/
inductive Ev
  | shoot
  | die

/-- In the traces of (108) the shooting ends as the bullet makes contact, when the dying begins. -/
def shooting : Ev → Set ℚ
  | .shoot => Set.Icc 0 1
  | .die => Set.Icc 1 3

/-- The shooting and the dying overlap at a single point, so they are neither one event nor nested,
so only the trieventive macroevent accounts for (107). -/
theorem shooting_trieventive :
    ¬ Monoeventive shooting .shoot .die ∧ ¬ Bieventive shooting .shoot .die ∧
      (shooting .shoot ∩ shooting .die).Nonempty := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_, ⟨1, by simp [shooting]⟩⟩
  · have : (0 : ℚ) ∈ shooting .die := h ▸ (by simp [shooting])
    norm_num [shooting] at this
  · rcases h with h | h
    · have := h (show (3 : ℚ) ∈ shooting .die by norm_num [shooting])
      norm_num [shooting] at this
    · have := h (show (0 : ℚ) ∈ shooting .shoot by norm_num [shooting])
      norm_num [shooting] at this

end Traces

/-! ### The compound in morphology (chapter 2, section 2) -/

/-- The null affix as a morph is a phonologically empty prefix on V2. -/
def nullMorph : Morph := .pref ""

/-- The word V1-∅-V2 (130): ∅ affixed to V2, the result compounded with V1. -/
def vvTree (v1 v2 : Morph) : Word.Tree Morph :=
  .compound (.root v1) (.prefixed nullMorph (.root v2))

@[simp] theorem toList_vvTree (v1 v2 : Morph) : (vvTree v1 v2).toList = [v1, nullMorph, v2] :=
  rfl

/-- The word V1-∅-V2 of a compound of the fragment. -/
def word (c : Resultative) : Word.Tree Morph := vvTree (.root c.v1.form) (.root c.v2.form)

/-- The word differs from the fragment's root compound by the null affix alone. -/
theorem toList_word_erase (c : Resultative) :
    (word c).toList.erase nullMorph = c.tree.toList.map (Morph.root ·.form) := by
  simp [word, nullMorph, Morph.root, Morph.pref, Morph.bound]

/-! ### Typology (chapter 8, section 2) -/

/-- Resultatives vary along three dimensions, whether the null head merges in
morphology, whether the result X can be a verb, and, if so, whether a transitive resultative can
take an intransitive change-of-state verb as X. -/
structure ResultativeType where
  compound : Bool
  verbalX : Bool
  intransitiveX : Bool
  intransitiveX_le : intransitiveX → verbalX

/-- Mandarin V-V resultatives are compounds with a verbal X, and a transitive resultative can
take an intransitive X: *dǎ-pò* (673) with an object, whose result verb `po` is unaccusative. -/
def mandarin : ResultativeType := ⟨true, true, true, fun h ↦ h⟩

/-- English resultatives are not compounds, and X is never a verb (669). -/
def english : ResultativeType := ⟨false, false, false, fun h ↦ h⟩

/-- Japanese V-V resultatives are compounds with verbal X whose transitivity follows V2, so no
intransitive X in a transitive resultative (674)–(675). -/
def japanese : ResultativeType := ⟨true, true, false, fun h ↦ nomatch h⟩

end Tay2024
