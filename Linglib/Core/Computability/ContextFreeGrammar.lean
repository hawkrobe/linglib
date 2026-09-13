/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Computability.ContextFreeGrammar
import Mathlib.Data.Countable.Basic

/-!
# Symbols, rules and derivations of a context-free grammar

Lemmas on mathlib's `Symbol`, `ContextFreeRule` and `ContextFreeGrammar` that the derivation
trees, the closure properties and the weighted grammars share. `[UPSTREAM]` candidate for
`Mathlib/Computability/ContextFreeGrammar.lean`.

## Main definitions

* `Symbol.terminal?`, `Symbol.IsNonterminal`, `Symbol.mapNonterminal`: the terminal at a symbol,
  the nonterminal predicate, and relabelling of nonterminals.
* `ContextFreeRule.NonterminalPos`: the positions of a right-hand side holding a nonterminal.
* `ContextFreeGrammar.RulesWithLHS`: the rules of a grammar with a given left-hand side.

## Main results

* `ContextFreeGrammar.Derives.append_split`: a derivation from a concatenation splits into
  derivations from the two halves.
-/

namespace Symbol

variable {T N N' : Type*}

/-- The terminal at a symbol, if it is one. -/
def terminal? : Symbol T N → Option T
  | .terminal a => some a
  | .nonterminal _ => none

@[simp] theorem terminal?_terminal (a : T) : (terminal a : Symbol T N).terminal? = some a := rfl

@[simp] theorem terminal?_nonterminal (A : N) :
    (nonterminal A : Symbol T N).terminal? = none := rfl

/-- The nonterminal symbols. -/
def IsNonterminal : Symbol T N → Prop
  | terminal _ => False
  | nonterminal _ => True

instance : DecidablePred (IsNonterminal : Symbol T N → Prop)
  | terminal _ => isFalse id
  | nonterminal _ => isTrue trivial

@[simp] theorem isNonterminal_nonterminal (A : N) : (nonterminal A : Symbol T N).IsNonterminal :=
  trivial

@[simp] theorem not_isNonterminal_terminal (a : T) : ¬ (terminal a : Symbol T N).IsNonterminal :=
  id

theorem isNonterminal_iff_terminal?_eq_none (s : Symbol T N) :
    s.IsNonterminal ↔ s.terminal? = none := by
  cases s <;> simp

/-- Relabel the nonterminals of a symbol. -/
def mapNonterminal (f : N → N') : Symbol T N → Symbol T N'
  | .terminal a => .terminal a
  | .nonterminal A => .nonterminal (f A)

@[simp] theorem mapNonterminal_terminal (f : N → N') (a : T) :
    mapNonterminal f (terminal a : Symbol T N) = terminal a := rfl

@[simp] theorem mapNonterminal_nonterminal (f : N → N') (A : N) :
    mapNonterminal f (nonterminal A : Symbol T N) = nonterminal (f A) := rfl

@[simp] theorem terminal?_mapNonterminal (f : N → N') (s : Symbol T N) :
    (s.mapNonterminal f).terminal? = s.terminal? := by cases s <;> rfl

instance [Countable T] [Countable N] : Countable (Symbol T N) :=
  Function.Injective.countable (f := fun s : Symbol T N => match s with
    | .terminal t => Sum.inl t
    | .nonterminal n => Sum.inr n) fun s s' h => by
    cases s <;> cases s' <;> simp_all

end Symbol

namespace ContextFreeRule

variable {T N : Type*}

/-- The positions on the right-hand side of `r` that hold a nonterminal: the slots at which a
derivation from `r` branches. -/
abbrev NonterminalPos (r : ContextFreeRule T N) : Type :=
  {i : Fin r.output.length // r.output[i].IsNonterminal}

/-- A rewrite of a concatenation `u₁ ++ u₂` happens entirely in `u₁` or entirely in `u₂`. -/
theorem Rewrites.append_split {r : ContextFreeRule T N} :
    ∀ {u₁ u₂ v : List (Symbol T N)}, r.Rewrites (u₁ ++ u₂) v →
      (∃ v₁, v = v₁ ++ u₂ ∧ r.Rewrites u₁ v₁) ∨ (∃ v₂, v = u₁ ++ v₂ ∧ r.Rewrites u₂ v₂) := by
  intro u₁ u₂ v hrw
  induction u₁ generalizing v with
  | nil => exact .inr ⟨v, by simp, by simpa using hrw⟩
  | cons x u₁ ih =>
    rw [List.cons_append] at hrw
    cases hrw with
    | head s => exact .inl ⟨r.output ++ u₁, by simp, .head u₁⟩
    | cons x hrw =>
      rcases ih hrw with ⟨v₁, rfl, hrw₁⟩ | ⟨v₂, rfl, hrw₂⟩
      · exact .inl ⟨x :: v₁, by simp, .cons x hrw₁⟩
      · exact .inr ⟨v₂, by simp, hrw₂⟩

end ContextFreeRule

namespace ContextFreeGrammar

variable {T : Type*} {g : ContextFreeGrammar T}

/-- The rules of `g` with left-hand side `a`. -/
abbrev RulesWithLHS (g : ContextFreeGrammar T) [DecidableEq g.NT] (a : g.NT) :=
  {r : ContextFreeRule T g.NT // r ∈ g.rules.filter (·.input = a)}

/-- A production from a concatenation `u₁ ++ u₂` happens entirely in `u₁` or entirely in
`u₂`. -/
theorem Produces.append_split {u₁ u₂ v : List (Symbol T g.NT)} (h : g.Produces (u₁ ++ u₂) v) :
    (∃ v₁, v = v₁ ++ u₂ ∧ g.Produces u₁ v₁) ∨ (∃ v₂, v = u₁ ++ v₂ ∧ g.Produces u₂ v₂) := by
  obtain ⟨r, hr, hrw⟩ := h
  rcases hrw.append_split with ⟨v₁, hv, hrw₁⟩ | ⟨v₂, hv, hrw₂⟩
  · exact .inl ⟨v₁, hv, r, hr, hrw₁⟩
  · exact .inr ⟨v₂, hv, r, hr, hrw₂⟩

/-- A derivation from a concatenation `u₁ ++ u₂` splits into derivations from `u₁` and from
`u₂`. -/
theorem Derives.append_split {u₁ u₂ v : List (Symbol T g.NT)} (h : g.Derives (u₁ ++ u₂) v) :
    ∃ v₁ v₂, v = v₁ ++ v₂ ∧ g.Derives u₁ v₁ ∧ g.Derives u₂ v₂ := by
  induction h with
  | refl => exact ⟨u₁, u₂, rfl, .refl _, .refl _⟩
  | tail _ step ih =>
    obtain ⟨w₁, w₂, rfl, hd₁, hd₂⟩ := ih
    rcases step.append_split with ⟨v₁, hv, hp₁⟩ | ⟨v₂, hv, hp₂⟩
    · exact ⟨v₁, w₂, hv, hd₁.trans_produces hp₁, hd₂⟩
    · exact ⟨w₁, v₂, hv, hd₁, hd₂.trans_produces hp₂⟩

end ContextFreeGrammar
