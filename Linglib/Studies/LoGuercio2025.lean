import Linglib.Pragmatics.Expressives.Basic
import Linglib.Semantics.Alternatives.Structural
import Linglib.Semantics.Alternatives.Competition
import Linglib.Data.Examples.LoGuercio2025

/-!
# Lo Guercio (2025): Maximize Conventional Implicatures!

This file formalizes the anti-conventional implicatures of [lo-guercio-2025]: scalar
inferences that arise from comparing the conventionally implicated content of formal
alternatives, as scalar implicatures compare at-issue content and antipresuppositions
presuppositional content. Conventionally implied meaning is a restriction on the contexts
of felicitous use, so one sentence has stronger such content than another when its felicity
set is a proper subset of the other's, and the principle Maximize Conventional Implicatures!
forbids a sentence when a formal alternative in the sense of [katzir-2007] and
[fox-katzir-2011], one no more complex than it, has stronger content. All three principles
are instances of the substrate's `Alternatives.violatesMaximize`, of which `violatesMCIs` is
the conventional-implicature instantiation.

The worked case is the epithet. Out of the blue, *John arrived first* carries no inference
that John is no bastard, because *that bastard John arrived first* is not a formal
alternative: the epithet construction is a determiner phrase with three daughters, which no
chain of deletions, contractions, and substitutions from a source of lexical items and
one-daughter phrases can build (`outOfBlue_no_ACI`, through
`Alternatives.Structural.subtree_preservation`). Once *that bastard Pedro* has been
mentioned, its phrase enters the substitution source, the epithet alternative is derived by
substituting it for the subject and then *John* for *Pedro*, the paper's derivation (24)
(`epithet_alternative_priorMention`), and the inference arises (`priorMention_yes_ACI`).

## Implementation notes

The felicity-set semantics of the paper's (12) is `expressiveCI`: a sentence is felicitous
at a world unless it contains the epithet construction and the speaker does not hold the
attitude there. The honorific *don/doña* of the paper's §3.2.1, the Japanese honorifics of
its §3.2.2, the expressive adjectives of its §3.2.4, and the embeddability and oddness
discussion of its §4 are rows of `Data/Examples/LoGuercio2025.json` and prose, not
theorems.

## References

* [lo-guercio-2025]
* [katzir-2007]
* [fox-katzir-2011]
* [gutzmann-2015]
* [kaplan-1999]
-/

namespace LoGuercio2025

open Pragmatics.Expressives
open Alternatives
open Alternatives.Structural
open Syntax

/-! ### The epithet as a structural alternative -/

/-- Vocabulary for the epithet example. -/
inductive EWord where
  | john | pedro | arrived | first | andThen
  | that_ | bastard
  deriving DecidableEq, Repr

instance : BEq EWord := ⟨λ a b => decide (a = b)⟩
instance : LawfulBEq EWord where
  eq_of_beq h := of_decide_eq_true h
  rfl := decide_eq_true rfl

open EWord

/-- The lexical items: terminals only. -/
def epithetLex : List (Tree Cat EWord) :=
  [.terminal .N .john, .terminal .N .pedro,
   .terminal .V .arrived, .terminal .Adv .first,
   .terminal .Conj .andThen,
   .terminal .Det .that_, .terminal .N .bastard]

/-- The predicate *arrived first*. -/
def arrivedFirst : Tree Cat EWord := .node .VP [.terminal .V .arrived, .terminal .Adv .first]

/-- *[DP John] arrived first*, the first conjunct of the paper's (20a) as its (24) parses it. -/
def johnArrived : Tree Cat EWord := .node .S [.node .DP [.terminal .N .john], arrivedFirst]

/-- *[DP that bastard John] arrived first*, the paper's (20b). -/
def bastardJohnArrived : Tree Cat EWord :=
  .node .S [.node .DP [.terminal .Det .that_, .terminal .N .bastard, .terminal .N .john],
    arrivedFirst]

/-- *[DP that bastard Pedro]*, mentioned in the second conjunct of (20a). -/
def bastardPedroDP : Tree Cat EWord :=
  .node .DP [.terminal .Det .that_, .terminal .N .bastard, .terminal .N .pedro]

/-- *[DP that bastard Pedro] arrived first*, the intermediate step of the derivation (24). -/
def bastardPedroArrived : Tree Cat EWord := .node .S [bastardPedroDP, arrivedFirst]

/-- The substitution source after the mention: the lexical items and the contextually
relevant epithet phrase ([fox-katzir-2011]). -/
def priorContextLex : List (Tree Cat EWord) :=
  epithetLex ++ [bastardPedroDP]

/-- The daughters of a tree. -/
def daughters : Tree Cat EWord → List (Tree Cat EWord)
  | .node _ cs => cs
  | _ => []

/-- A determiner phrase with at least two daughters. -/
def WideDP (t : Tree Cat EWord) : Prop := t.cat = .DP ∧ 2 ≤ (daughters t).length

/-- The epithet construction: a determiner phrase *that bastard X*. -/
def IsEpithet : Tree Cat EWord → Prop
  | .node .DP [.terminal .Det .that_, .terminal .N .bastard, _] => True
  | _ => False

instance : DecidablePred WideDP := λ _ => inferInstanceAs (Decidable (_ ∧ _))
instance : DecidablePred IsEpithet := λ t => by unfold IsEpithet; split <;> infer_instance

theorem WideDP.of_isEpithet {t : Tree Cat EWord} (h : IsEpithet t) : WideDP t := by
  unfold IsEpithet at h; split at h
  · exact ⟨rfl, by simp [daughters]⟩
  · exact h.elim

/-- A tree contains the epithet construction. -/
def HasEpithet (φ : Tree Cat EWord) : Prop := ∃ s ∈ φ.subtrees, IsEpithet s

instance : DecidablePred HasEpithet := λ _ => inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- Out of the blue no structural alternative of the bare sentence contains a determiner
phrase with two or more daughters: no source item has one, the sentence has none, and the
operations cannot widen a phrase. -/
theorem no_wideDP_outOfBlue {ψ : Tree Cat EWord}
    (h : ψ ∈ structuralAlternatives epithetLex johnArrived) : ∀ t ∈ ψ.subtrees, ¬ WideDP t :=
  subtree_preservation _ WideDP (by decide)
    (λ _ cs i h ⟨h1, h2⟩ => h ⟨h1, by
      simp only [daughters, List.length_eraseIdx, i.2, if_true] at h2 ⊢; omega⟩)
    (λ _ cs _ _ h ⟨h1, h2⟩ => h ⟨h1, by simpa [daughters, List.length_set] using h2⟩)
    (λ _ _ _ _ _ ⟨_, h2⟩ => by simp [daughters] at h2) (by decide) h

/-- Out of the blue, the epithet sentence is not a structural alternative. -/
theorem epithet_not_alternative_outOfBlue :
    bastardJohnArrived ∉ structuralAlternatives epithetLex johnArrived :=
  λ h => no_wideDP_outOfBlue h (.node .DP [.terminal .Det .that_, .terminal .N .bastard,
    .terminal .N .john]) (by decide) (by decide)

/-- After the mention, the epithet sentence is a structural alternative, by the paper's
derivation (24): the mentioned phrase replaces the subject, then *John* replaces *Pedro*. -/
theorem epithet_alternative_priorMention :
    bastardJohnArrived ∈ structuralAlternatives priorContextLex johnArrived := by
  have step1 : StructOp (substitutionSource priorContextLex johnArrived) johnArrived
      bastardPedroArrived :=
    StructOp.inChild (cs := [Tree.node Cat.DP [Tree.terminal Cat.N john], arrivedFirst])
      ⟨0, by decide⟩
      (StructOp.subst rfl (List.mem_append_left _ (by simp [priorContextLex])))
  have step2 : StructOp (substitutionSource priorContextLex johnArrived) bastardPedroArrived
      bastardJohnArrived :=
    StructOp.inChild (cs := [bastardPedroDP, arrivedFirst]) ⟨0, by decide⟩
      (StructOp.inChild (cs := [Tree.terminal Cat.Det that_, Tree.terminal Cat.N bastard,
          Tree.terminal Cat.N pedro]) ⟨2, by decide⟩
        (StructOp.subst rfl (List.mem_append_left _ (by simp [priorContextLex, epithetLex]))))
  exact Relation.ReflTransGen.head step1 (Relation.ReflTransGen.single step2)

/-! ### Conventionally implicated content as felicity sets -/

/-- Worlds: whether the speaker believes that John is a bastard. -/
abbrev World : Type := Bool

/-- The felicity-set content of the paper's (12): a sentence with the epithet construction is
felicitous only where the speaker holds the attitude; any other sentence is felicitous
everywhere. -/
def expressiveCI (φ : Tree Cat EWord) (w : World) : Prop := HasEpithet φ → w = true

/-- The epithet sentence has stronger content than the bare one: its felicity set is a proper
subset. -/
theorem epithet_ciStronger_than_bare :
    (∀ w, expressiveCI bastardJohnArrived w → expressiveCI johnArrived w) ∧
      ∃ w, expressiveCI johnArrived w ∧ ¬ expressiveCI bastardJohnArrived w :=
  ⟨λ _ _ h => absurd h (by decide), false, λ h => absurd h (by decide),
    λ h => Bool.false_ne_true (h (by decide))⟩

/-! ### The inference -/

/-- Out of the blue the bare sentence does not violate the principle: every formal
alternative is free of the epithet construction, so none has stronger content. -/
theorem outOfBlue_no_ACI :
    ¬ violatesMCIs (World := World) (katzirSource epithetLex) expressiveCI johnArrived
      (λ _ => True) := by
  rintro ⟨φ', hφ', _, ⟨w, _, h_alt⟩, _⟩
  exact h_alt λ ⟨s, hs, hse⟩ => absurd (WideDP.of_isEpithet hse) (no_wideDP_outOfBlue hφ' s hs)

/-- After the mention the bare sentence violates the principle: the epithet sentence is a
formal alternative with stronger content. -/
theorem priorMention_yes_ACI :
    violatesMCIs (World := World) (katzirSource priorContextLex) expressiveCI johnArrived
      (λ _ => True) :=
  ⟨bastardJohnArrived, epithet_alternative_priorMention, epithet_ciStronger_than_bare.1,
    epithet_ciStronger_than_bare.2, trivial⟩

end LoGuercio2025
