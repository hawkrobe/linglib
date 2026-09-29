/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Computability.DFA
public import Linglib.Core.Computability.NonRegular.AnBn

/-!
# Regular languages are context-free

Over a finite alphabet every regular language is context-free, and the inclusion is strict. A
finite automaton `M` is simulated by its right-linear grammar, with a nonterminal for each state,
a rule `q → a q'` for each transition from `q` to `q'` on the letter `a`, and a rule `q → ε` for
each accepting state `q`; its sentential forms are a word `w` followed by the state `M.eval w`,
or an accepted word. The language `{aⁿbⁿ}` of two distinct letters is context-free but not
regular.

The alphabet must be finite, because a grammar has finitely many rules and so uses finitely many
letters: over an infinite alphabet the language of all words is regular, by a one-state
automaton, but not context-free.

## Main definitions

* `DFA.toContextFreeGrammar M`: the right-linear grammar of a finite automaton over a finite
  alphabet.

## Main results

* `DFA.language_toContextFreeGrammar`: the grammar of `M` generates the language of `M`.
* `Language.IsRegular.isContextFree`: over a finite alphabet, regular languages are context-free.
* `Language.isContextFree_top_iff`: the language of all words is context-free exactly when the
  alphabet is finite.
* `Language.setOf_isRegular_ssubset_setOf_isContextFree`: over a finite alphabet with two letters,
  the regular languages are a proper subclass of the context-free languages.

## Implementation notes

[UPSTREAM] candidate: `Mathlib/Computability/Chomsky.lean`.

## References

* [J. E. Hopcroft, R. Motwani and J. D. Ullman, *Introduction to Automata Theory, Languages, and
  Computation* (2000)][hopcroft-motwani-ullman-2000]
-/

@[expose] public section

open List Symbol

namespace DFA

variable {α : Type*} {σ : Type} [Fintype α] [Fintype σ] (M : DFA α σ)
  [DecidablePred (· ∈ M.accept)]

/-- The right-linear grammar of `M`: a nonterminal for each state, a rule `q → a (M.step q a)` for
each state `q` and letter `a`, and a rule `q → ε` for each accepting state `q`. -/
def toContextFreeGrammar : ContextFreeGrammar α where
  NT := σ
  initial := M.start
  rules :=
    (Finset.univ.map ⟨fun x : σ × α ↦ ⟨x.1, [terminal x.2, nonterminal (M.step x.1 x.2)]⟩,
      fun x y h ↦ by simp_all [Prod.ext_iff]⟩).disjUnion
    ((Finset.univ.filter (· ∈ M.accept)).map ⟨fun q ↦ ⟨q, []⟩, fun p q h ↦ by simpa using h⟩)
    (by simp only [Finset.disjoint_left, Finset.mem_map]; rintro _ ⟨_, -, rfl⟩ ⟨_, -, h⟩; simp at h)

variable {M}

theorem mem_rules_toContextFreeGrammar {r : ContextFreeRule α σ} :
    r ∈ M.toContextFreeGrammar.rules ↔
      (∃ a, r.output = [terminal a, nonterminal (M.step r.input a)]) ∨
        (r.input ∈ M.accept ∧ r.output = []) := by
  obtain ⟨q, o⟩ := r
  unfold toContextFreeGrammar
  simp [eq_comm]

/-- The grammar of `M` derives every word followed by the state `M` reaches on it. -/
theorem derives_toContextFreeGrammar (w : List α) :
    M.toContextFreeGrammar.Derives [nonterminal M.start]
      (w.map terminal ++ [nonterminal (M.eval w)]) := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w a ih =>
    refine ih.trans_produces (ContextFreeGrammar.produces_map_terminal_append_singleton_iff.2
      ⟨⟨M.eval w, [terminal a, nonterminal (M.step (M.eval w) a)]⟩,
        mem_rules_toContextFreeGrammar.2 (.inl ⟨a, rfl⟩), rfl, ?_⟩)
    simp [eval_append_singleton]

/-- The sentential forms of the grammar of `M` are a word followed by the state `M` reaches on it,
and the words `M` accepts. -/
theorem derives_toContextFreeGrammar_iff {v : List (Symbol α σ)} :
    M.toContextFreeGrammar.Derives [nonterminal M.start] v ↔ ∃ w,
      v = w.map terminal ++ [nonterminal (M.eval w)] ∨
        (v = w.map terminal ∧ M.eval w ∈ M.accept) := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · induction h with
    | refl => exact ⟨[], .inl rfl⟩
    | tail _ hstep ih =>
      obtain ⟨w, rfl | ⟨rfl, -⟩⟩ := ih
      · obtain ⟨r, hr, hq, rfl⟩ :=
          ContextFreeGrammar.produces_map_terminal_append_singleton_iff.1 hstep
        obtain ⟨a, ho⟩ | ⟨hacc, ho⟩ := mem_rules_toContextFreeGrammar.1 hr
        · exact ⟨w ++ [a], .inl (by simp [ho, hq, eval_append_singleton])⟩
        · exact ⟨w, .inr ⟨by simp [ho], hq ▸ hacc⟩⟩
      · exact (ContextFreeGrammar.not_produces_map_terminal hstep).elim
  · rintro ⟨w, rfl | ⟨rfl, hacc⟩⟩
    · exact derives_toContextFreeGrammar w
    · exact (derives_toContextFreeGrammar w).trans_produces
        (ContextFreeGrammar.produces_map_terminal_append_singleton_iff.2
          ⟨⟨M.eval w, []⟩, mem_rules_toContextFreeGrammar.2 (.inr ⟨hacc, rfl⟩), rfl, by simp⟩)

/-- The grammar of `M` generates the language of `M`. -/
theorem language_toContextFreeGrammar : M.toContextFreeGrammar.language = M.accepts := by
  ext w
  change M.toContextFreeGrammar.Derives [nonterminal M.start] _ ↔ _
  rw [derives_toContextFreeGrammar_iff, mem_accepts]
  refine ⟨fun ⟨u, h⟩ ↦ ?_, fun h ↦ ⟨w, .inr ⟨rfl, h⟩⟩⟩
  rcases h with h | ⟨h, hacc⟩
  · simpa using congr(nonterminal (M.eval u) ∈ $h)
  · rwa [map_injective_iff.2 (fun _ _ ↦ terminal.inj) h]

end DFA

namespace Language

variable {α : Type*}

/-- Over a finite alphabet, every regular language is context-free. -/
theorem IsRegular.isContextFree [Finite α] {L : Language α} (h : L.IsRegular) :
    L.IsContextFree := by
  classical
  have := Fintype.ofFinite α
  obtain ⟨σ, _, M, rfl⟩ := h
  exact ⟨M.toContextFreeGrammar, DFA.language_toContextFreeGrammar⟩

/-- The language of all words is context-free exactly when the alphabet is finite: it is regular
over any alphabet, but a grammar has finitely many rules and so uses finitely many letters. -/
theorem isContextFree_top_iff : (⊤ : Language α).IsContextFree ↔ Finite α := by
  refine ⟨fun ⟨g, hg⟩ ↦ ?_, fun _ ↦ IsRegular.isContextFree ?_⟩
  · have hS : (⋃ r ∈ g.rules, terminal ⁻¹' {s : Symbol α g.NT | s ∈ r.output}).Finite :=
      g.rules.finite_toSet.biUnion fun r _ ↦
        r.output.finite_toSet.preimage fun _ _ _ _ ↦ terminal.inj
    refine Set.finite_univ_iff.1 (hS.subset fun a _ ↦ ?_)
    have hd : g.Derives [nonterminal g.initial] [terminal a] :=
      (ContextFreeGrammar.mem_language_iff g [a]).1 (hg ▸ trivial)
    obtain h | ⟨r, hr, ho⟩ := hd.terminal_mem (mem_singleton_self _)
    · simp at h
    · exact Set.mem_iUnion₂.2 ⟨r, hr, ho⟩
  · exact ⟨Unit, inferInstance, ⟨fun _ _ ↦ (), (), Set.univ⟩, top_unique fun _ _ ↦ trivial⟩

/-- Over a finite alphabet with two distinct letters `a` and `b`, the regular languages are a
proper subclass of the context-free languages, as `{aⁿbⁿ}` witnesses. -/
theorem setOf_isRegular_ssubset_setOf_isContextFree [Finite α] [Nontrivial α] :
    {L : Language α | L.IsRegular} ⊂ {L | L.IsContextFree} := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne α
  exact (Set.ssubset_iff_of_subset fun _ ↦ IsRegular.isContextFree).2
    ⟨anbn a b, isContextFree_anbn a b, not_isRegular_anbn hab⟩

end Language
