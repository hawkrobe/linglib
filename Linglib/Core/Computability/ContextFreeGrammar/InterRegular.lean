/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.ContextFreeGrammar
import Linglib.Core.Computability.ContextFreeGrammar.Map
import Mathlib.Computability.DFA

/-!
# Context-free languages are closed under intersection with regular languages

The intersection of a context-free language with a regular language is context-free
([bar-hillel-perles-shamir-1961]). The construction is the triple product: the nonterminals of
the product grammar are the nonterminals of `G` annotated with an entry and an exit state of the
automaton `M`, and a rule of `G` yields one product rule for every way of threading the states
of `M` through its right-hand side. A fresh start symbol rewrites to the start nonterminal of `G`
between the start state and each accepting state of `M`.

## Main definitions

* `ContextFreeGrammar.Annotates`: `Annotates M p l out q` says that the sentential form `l` of
  the product grammar is `out` with its nonterminals annotated so that the states of `M` thread
  from `p` to `q`.
* `ContextFreeGrammar.product`: the product of a grammar with a finite automaton.

## Main results

* `ContextFreeGrammar.product_language`: the product generates the intersection.
* `Language.IsContextFree.inter_isRegular`: closure under intersection with a regular language,
  and its contrapositives `Language.not_isContextFree_of_inter_regular_not` and the proof
  schema `Language.not_isContextFree_via_witness` of [shieber-1985], which first pushes the
  language through a string homomorphism.

## References

* [bar-hillel-perles-shamir-1961]
* [hopcroft-motwani-ullman-2000]
* [shieber-1985]
-/

open scoped Classical

namespace ContextFreeGrammar

variable {T : Type*} {σ : Type} {G : ContextFreeGrammar T} (M : DFA T σ)

/-- The nonterminals of the product grammar: a nonterminal of `G` between an entry and an exit
state of the automaton, or the fresh start symbol `none`. -/
abbrev ProductNT (G : ContextFreeGrammar T) (σ : Type) := Option (σ × G.NT × σ)

/-- `Annotates M p l out q`: the sentential form `l` of the product grammar is `out` with every
nonterminal `A` replaced by some `some (p', A, q')`, the states threading from `p` to `q`: a
terminal advances the automaton, and an annotated nonterminal jumps from its entry state to its
exit state. -/
inductive Annotates : σ → List (Symbol T (ProductNT G σ)) → List (Symbol T G.NT) → σ → Prop
  | nil (p : σ) : Annotates p [] [] p
  | terminal {p q : σ} (a : T) {l : List (Symbol T (ProductNT G σ))} {out : List (Symbol T G.NT)}
      (h : Annotates (M.step p a) l out q) : Annotates p (.terminal a :: l) (.terminal a :: out) q
  | nonterminal {p p' q : σ} (A : G.NT) {l : List (Symbol T (ProductNT G σ))}
      {out : List (Symbol T G.NT)} (h : Annotates p' l out q) :
      Annotates p (.nonterminal (some (p, A, p')) :: l) (.nonterminal A :: out) q

namespace Annotates

variable {M} {p q r : σ} {l l₁ l₂ : List (Symbol T (ProductNT G σ))}
  {out out₁ out₂ : List (Symbol T G.NT)}

theorem append (h₁ : Annotates M p l₁ out₁ q) (h₂ : Annotates M q l₂ out₂ r) :
    Annotates M p (l₁ ++ l₂) (out₁ ++ out₂) r := by
  induction h₁ with
  | nil => exact h₂
  | terminal a _ ih => exact .terminal a (ih h₂)
  | nonterminal A _ ih => exact .nonterminal A (ih h₂)

/-- An annotation of a concatenation splits at the concatenation. -/
theorem split_out (h : Annotates M p l (out₁ ++ out₂) r) :
    ∃ l₁ l₂ q, l = l₁ ++ l₂ ∧ Annotates M p l₁ out₁ q ∧ Annotates M q l₂ out₂ r := by
  induction out₁ generalizing l p with
  | nil => exact ⟨[], l, p, rfl, .nil p, h⟩
  | cons s out₁ ih =>
    cases h with
    | terminal a h =>
      obtain ⟨l₁, l₂, q, rfl, h₁, h₂⟩ := ih h
      exact ⟨_ :: l₁, l₂, q, rfl, .terminal a h₁, h₂⟩
    | nonterminal A h =>
      obtain ⟨l₁, l₂, q, rfl, h₁, h₂⟩ := ih h
      exact ⟨_ :: l₁, l₂, q, rfl, .nonterminal A h₁, h₂⟩

/-- An annotation that is a concatenation annotates a concatenation. -/
theorem split (h : Annotates M p (l₁ ++ l₂) out r) :
    ∃ out₁ out₂ q, out = out₁ ++ out₂ ∧ Annotates M p l₁ out₁ q ∧ Annotates M q l₂ out₂ r := by
  induction l₁ generalizing out p with
  | nil => exact ⟨[], out, p, rfl, .nil p, h⟩
  | cons s l₁ ih =>
    cases h with
    | terminal a h =>
      obtain ⟨out₁, out₂, q, rfl, h₁, h₂⟩ := ih h
      exact ⟨_ :: out₁, out₂, q, rfl, .terminal a h₁, h₂⟩
    | nonterminal A h =>
      obtain ⟨out₁, out₂, q, rfl, h₁, h₂⟩ := ih h
      exact ⟨_ :: out₁, out₂, q, rfl, .nonterminal A h₁, h₂⟩

theorem map_terminal (p : σ) (w : List T) :
    Annotates (G := G) M p (w.map .terminal) (w.map .terminal) (M.evalFrom p w) := by
  induction w generalizing p with
  | nil => exact .nil p
  | cons a w ih => exact .terminal a (ih (M.step p a))

/-- A word annotates only itself, and ends where the automaton ends. -/
theorem eq_of_map_terminal_right {w : List T} (h : Annotates M p l (w.map .terminal) q) :
    l = w.map .terminal ∧ q = M.evalFrom p w := by
  induction w generalizing l p with
  | nil => cases h; exact ⟨rfl, rfl⟩
  | cons a w ih =>
    cases h with
    | terminal _ h => obtain ⟨rfl, rfl⟩ := ih h; exact ⟨rfl, rfl⟩

/-- A word is annotated only by itself, and ends where the automaton ends. -/
theorem eq_of_map_terminal_left {w : List T} (h : Annotates M p (w.map .terminal) out q) :
    out = w.map .terminal ∧ q = M.evalFrom p w := by
  induction w generalizing out p with
  | nil => cases h; exact ⟨rfl, rfl⟩
  | cons a w ih =>
    cases h with
    | terminal _ h => obtain ⟨rfl, rfl⟩ := ih h; exact ⟨rfl, rfl⟩

theorem eq_of_singleton_right {A : G.NT} (h : Annotates M p l [.nonterminal A] q) :
    l = [.nonterminal (some (p, A, q))] := by
  cases h with
  | nonterminal _ h => cases h; rfl

theorem eq_of_singleton_left {p₀ q₀ : σ} {A : G.NT}
    (h : Annotates M p [.nonterminal (some (p₀, A, q₀))] out q) :
    out = [.nonterminal A] ∧ p₀ = p ∧ q₀ = q := by
  cases h with
  | nonterminal _ h => cases h; exact ⟨rfl, rfl, rfl⟩

theorem none_notMem (h : Annotates M p l out q) : Symbol.nonterminal none ∉ l := by
  induction h with
  | nil => simp
  | terminal _ _ ih => simpa using ih
  | nonterminal _ _ ih => simpa using ih

end Annotates

variable [Fintype σ]

/-- The annotations of `out` from state `p`, each with its exit state. -/
noncomputable def annotations :
    σ → List (Symbol T G.NT) → Finset (σ × List (Symbol T (ProductNT G σ)))
  | p, [] => {(p, [])}
  | p, .terminal a :: out => (annotations (M.step p a) out).image fun x => (x.1, .terminal a :: x.2)
  | p, .nonterminal A :: out => Finset.univ.biUnion fun p' =>
      (annotations p' out).image fun x => (x.1, .nonterminal (some (p, A, p')) :: x.2)

theorem mem_annotations {p : σ} {out : List (Symbol T G.NT)}
    {x : σ × List (Symbol T (ProductNT G σ))} :
    x ∈ annotations M p out ↔ Annotates M p x.2 out x.1 := by
  induction out generalizing p x with
  | nil =>
    obtain ⟨q, l⟩ := x
    simp only [annotations, Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩; exact .nil _
    · rintro ⟨⟩; exact ⟨rfl, rfl⟩
  | cons s out ih =>
    obtain ⟨q, l⟩ := x
    cases s with
    | terminal a =>
      simp only [annotations, Finset.mem_image, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨q', l'⟩, h, rfl, rfl⟩; exact .terminal a (ih.mp h)
      · intro h
        cases h with
        | terminal _ h => exact ⟨(q, _), ih.mpr h, rfl, rfl⟩
    | nonterminal A =>
      simp only [annotations, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image,
        Prod.mk.injEq]
      constructor
      · rintro ⟨p', ⟨q', l'⟩, h, rfl, rfl⟩; exact .nonterminal A (ih.mp h)
      · intro h
        cases h with
        | nonterminal _ h => exact ⟨_, (q, _), ih.mpr h, rfl, rfl⟩

/-- The start rule of the product for an accepting state `q`. -/
def startRule (G : ContextFreeGrammar T) (q : σ) : ContextFreeRule T (ProductNT G σ) :=
  ⟨none, [.nonterminal (some (M.start, G.initial, q))]⟩

/-- The rules of the product: a start rule for each accepting state, and each rule of `G` in
every annotation of its right-hand side. -/
noncomputable def productRules (G : ContextFreeGrammar T) :
    Finset (ContextFreeRule T (ProductNT G σ)) :=
  (Finset.univ.filter (· ∈ M.accept)).image (startRule M G) ∪
    G.rules.biUnion fun r => Finset.univ.biUnion fun p =>
      (annotations M p r.output).image fun x => ⟨some (p, r.input, x.1), x.2⟩

theorem mem_productRules {r' : ContextFreeRule T (ProductNT G σ)} :
    r' ∈ productRules M G ↔ (∃ q ∈ M.accept, r' = startRule M G q) ∨
      ∃ r ∈ G.rules, ∃ p q, r'.input = some (p, r.input, q) ∧
        Annotates M p r'.output r.output q := by
  simp only [productRules, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_biUnion, mem_annotations]
  refine or_congr (exists_congr fun q => and_congr_right fun _ => eq_comm)
    (exists_congr fun r => and_congr_right fun _ => ?_)
  constructor
  · rintro ⟨p, ⟨q, l⟩, h, rfl⟩; exact ⟨p, q, rfl, h⟩
  · rintro ⟨p, q, hi, h⟩; exact ⟨p, (q, r'.output), h, by cases r'; cases hi; rfl⟩

theorem startRule_mem_productRules {q : σ} (hq : q ∈ M.accept) :
    startRule M G q ∈ productRules M G :=
  (mem_productRules M).mpr (.inl ⟨q, hq, rfl⟩)

theorem mem_productRules_of_annotates {r : ContextFreeRule T G.NT} (hr : r ∈ G.rules) {p q : σ}
    {l : List (Symbol T (ProductNT G σ))} (h : Annotates M p l r.output q) :
    (⟨some (p, r.input, q), l⟩ : ContextFreeRule T (ProductNT G σ)) ∈ productRules M G :=
  (mem_productRules M).mpr (.inr ⟨r, hr, p, q, rfl, h⟩)

/-- The product of a grammar with a finite automaton: the nonterminals are annotated with entry
and exit states, each rule of `G` appears in every annotation of its right-hand side, and the
fresh start symbol rewrites to the start nonterminal of `G` between the start state and each
accepting state. -/
noncomputable def product (G : ContextFreeGrammar T) (M : DFA T σ) : ContextFreeGrammar T where
  NT := ProductNT G σ
  initial := none
  rules := productRules M G

@[simp] theorem product_initial : (G.product M).initial = (none : ProductNT G σ) := rfl

/-! ### The product generates the intersection -/

variable {M}

/-- A step of the product on an annotated form is a step of `G` on the form it annotates. -/
theorem Produces.of_product {l' t' : List (Symbol T (ProductNT G σ))}
    (step : (G.product M).Produces l' t') {p q : σ} {out : List (Symbol T G.NT)}
    (h : Annotates M p l' out q) : ∃ out', G.Produces out out' ∧ Annotates M p t' out' q := by
  obtain ⟨r', hr', hrw⟩ := step
  obtain ⟨pre, post, rfl, rfl⟩ := hrw.exists_parts
  rcases (mem_productRules M).mp hr' with ⟨q₀, -, rfl⟩ | ⟨r, hr, p₀, q₀, hi, hbody⟩
  · exact absurd (by simp [startRule]) h.none_notMem
  · obtain ⟨out₁, out₃, p₂, rfl, h₁₂, h₃⟩ := h.split
    obtain ⟨out₁, out₂, p₁, rfl, h₁, h₂⟩ := h₁₂.split
    rw [hi] at h₂
    obtain ⟨rfl, rfl, rfl⟩ := h₂.eq_of_singleton_left
    exact ⟨out₁ ++ r.output ++ out₃, ⟨r, hr, ContextFreeRule.rewrites_of_exists_parts r out₁ out₃⟩,
      (h₁.append hbody).append h₃⟩

/-- A derivation of the product from an annotated form is a derivation of `G` from the form it
annotates. -/
theorem Derives.of_product {l' t' : List (Symbol T (ProductNT G σ))}
    (hd : (G.product M).Derives l' t') {p q : σ} {out : List (Symbol T G.NT)}
    (h : Annotates M p l' out q) : ∃ out', G.Derives out out' ∧ Annotates M p t' out' q := by
  induction hd with
  | refl => exact ⟨out, .refl _, h⟩
  | tail _ step ih =>
    obtain ⟨out', hd', h'⟩ := ih
    obtain ⟨out'', hp, h''⟩ := step.of_product h'
    exact ⟨out'', hd'.trans_produces hp, h''⟩

theorem product_language_le : (G.product M).language ≤ G.language ⊓ M.accepts := by
  intro w hw
  rcases ((mem_language_iff _ _).mp hw).eq_or_head with heq | ⟨v, ⟨r', hr', hrw⟩, hrest⟩
  · cases w <;> simp at heq
  · have hin : r'.input = none := by simpa using hrw.nonterminal_input_mem
    obtain ⟨pre, post, hl, rfl⟩ := hrw.exists_parts
    have hpre : pre = [] :=
      List.eq_nil_of_length_eq_zero (by have := congrArg List.length hl; simp at this; omega)
    have hpost : post = [] :=
      List.eq_nil_of_length_eq_zero (by have := congrArg List.length hl; simp at this; omega)
    subst hpre hpost
    simp only [List.nil_append, List.append_nil] at hrest
    rcases (mem_productRules M).mp hr' with ⟨qf, hqf, rfl⟩ | ⟨r, -, p₀, q₀, hi, -⟩
    · obtain ⟨out, hd, h⟩ := hrest.of_product (Annotates.nonterminal (M := M) (p := M.start)
        G.initial (.nil qf))
      obtain ⟨rfl, hq⟩ := h.eq_of_map_terminal_left
      exact ⟨(mem_language_iff _ _).mpr hd, M.mem_accepts.mpr (by rw [DFA.eval, ← hq]; exact hqf)⟩
    · rw [hin] at hi
      simp at hi

/-- Every derivation of `G` of a word is the projection of a derivation of the product from an
annotation of its start, for any entry state. -/
theorem exists_annotates_of_derives {out : List (Symbol T G.NT)} {w : List T}
    (hd : G.Derives out (w.map .terminal)) (p : σ) :
    ∃ l, Annotates M p l out (M.evalFrom p w) ∧ (G.product M).Derives l (w.map .terminal) := by
  induction hd using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨_, .map_terminal p w, .refl _⟩
  | head step _ ih =>
    obtain ⟨l, hl, hd⟩ := ih
    obtain ⟨r, hr, hrw⟩ := step
    obtain ⟨pre, post, rfl, rfl⟩ := hrw.exists_parts
    obtain ⟨l₁, l₃, p₂, rfl, h₁₂, h₃⟩ := hl.split_out
    obtain ⟨l₁, l₂, p₁, rfl, h₁, h₂⟩ := h₁₂.split_out
    exact ⟨l₁ ++ [.nonterminal (some (p₁, r.input, p₂))] ++ l₃,
      (h₁.append (.nonterminal r.input (.nil p₂))).append h₃,
      (Produces.single ⟨_, mem_productRules_of_annotates M hr h₂,
        ContextFreeRule.rewrites_of_exists_parts _ l₁ l₃⟩).trans hd⟩

theorem le_product_language : G.language ⊓ M.accepts ≤ (G.product M).language := by
  rintro w ⟨hG, hM⟩
  obtain ⟨l, hl, hd⟩ :=
    exists_annotates_of_derives (M := M) ((mem_language_iff _ _).mp hG) M.start
  rw [hl.eq_of_singleton_right] at hd
  have hstep : (G.product M).Produces [.nonterminal (G.product M).initial]
      (startRule M G (M.eval w)).output :=
    ⟨startRule M G (M.eval w), startRule_mem_productRules M (M.mem_accepts.mp hM),
      ContextFreeRule.Rewrites.input_output⟩
  exact (mem_language_iff _ _).mpr (hstep.trans_derives hd)

/-- **Bar-Hillel**: the product generates the intersection. -/
theorem product_language (G : ContextFreeGrammar T) (M : DFA T σ) :
    (G.product M).language = G.language ⊓ M.accepts :=
  le_antisymm product_language_le le_product_language

end ContextFreeGrammar

namespace Language.IsContextFree

/-- Context-free languages are closed under intersection with regular languages. -/
theorem inter_isRegular {α : Type*} {L R : Language α} (hL : L.IsContextFree) (hR : R.IsRegular) :
    (L ⊓ R).IsContextFree := by
  obtain ⟨G, rfl⟩ := hL
  obtain ⟨σ, _, M, rfl⟩ := hR
  exact ⟨G.product M, ContextFreeGrammar.product_language G M⟩

/-- If `L ∩ R` is not context-free for a regular `R`, then `L` is not context-free. -/
theorem _root_.Language.not_isContextFree_of_inter_regular_not {α : Type*} {L R : Language α}
    (hR : R.IsRegular) (h : ¬ (L ⊓ R).IsContextFree) : ¬ L.IsContextFree :=
  fun hL => h (hL.inter_isRegular hR)

/-- The proof schema of [shieber-1985]: if the image of `L` under a string homomorphism,
intersected with a regular language, is not context-free, then `L` is not context-free. -/
theorem _root_.Language.not_isContextFree_via_witness {α β : Type*} (f : α → List β)
    (R : Language β) {L : Language α} (hR : R.IsRegular)
    (h : ¬ (Language.stringMap f L ⊓ R).IsContextFree) : ¬ L.IsContextFree :=
  fun hL => h ((hL.stringMap f).inter_isRegular hR)

end Language.IsContextFree
