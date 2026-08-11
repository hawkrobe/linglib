import Linglib.Syntax.CCG.Grammar

/-!
# Stanojević & Steedman 2021: Formal Basis of a Language Universal

Formalisation of the central result of [stanojevic-steedman-2021]: over a *natural
order of dominance* — a chain of first-order categories `X₁|X₂, X₂|X₃, …, Xₙ|Xₙ₊₁`,
each realizable with either slash direction — CCG derives *all and only* the
separable permutations of the canonical linearization. The two excluded
four-element patterns, 2413 and 3142, are exactly the noun-phrase and verb-cluster
orders unattested in the typological record ([stanojevic-steedman-2021] §1, after
Cinque 2005), so the combinatorics of CCG is proposed as the formal basis of the
universal.

The dominance chain is realized as a `Grammar.multimodal` lexicon over atoms `ℕ`
(word `i` carries both `Xᵢ/Xᵢ₊₁` and `Xᵢ\Xᵢ₊₁`; the paper's order-free `|` is this
two-entry realization), and separable permutations are defined by the separating-tree
characterization of Bose, Buss & Lubiw (the paper's (17)) as an inductive predicate:
a singleton, or a split into contiguous parts in original (`pos`) or inverted
(`neg`) order.

## Main statements

- `derives_of_sepPerm` — completeness (the paper's Lemma 1–Lemma 3 / Theorem 2):
  every separable permutation of a span is derivable, at both slashings of the
  span category.
- `sepPerm_of_derives` — soundness (Theorem 1): everything derivable over the NOD
  grammar is a span category over a separable permutation. Application and
  second-order composition provably never fire over a first-order chain.
- `derives_iff_sepPerm` — the universal: derivability at a span category is
  separability.

## Implementation notes

The Schröder-number count (Theorem 3) and the 22-of-24 four-element instance with
its typological grounding are not yet formalised; they need a decidability
instance for `SepPerm`.
-/

namespace StanojevicSteedman2021

open CCG

/-- The word token of position `i` in the dominance chain. -/
def tok (i : ℕ) : String := toString i

/-- The forward realization of chain position `i`: `Xᵢ/Xᵢ₊₁`. -/
def fwd (i : ℕ) : Cat ℕ := .rslash (.atom i) .dot (.atom (i + 1))

/-- The backward realization of chain position `i`: `Xᵢ\Xᵢ₊₁`. -/
def bwd (i : ℕ) : Cat ℕ := .lslash (.atom i) .dot (.atom (i + 1))

/-- The natural-order-of-dominance lexicon over `n` words: each position carries both
slash realizations of its chain category — the paper's order-free `|`. -/
def nodLexicon (n : ℕ) : List (String × Cat ℕ) :=
  (List.range n).flatMap fun i => [(tok (i + 1), fwd (i + 1)), (tok (i + 1), bwd (i + 1))]

/-- The NOD grammar: the multimodal (universal-rule) grammar over the chain lexicon.
The start atom plays no role in the span-level claims. -/
def nodGrammar (n : ℕ) : Grammar ℕ := .multimodal (nodLexicon n) 1

theorem mem_nodLexicon {n m : ℕ} (h1 : 1 ≤ m) (hn : m ≤ n) :
    (tok m, fwd m) ∈ nodLexicon n ∧ (tok m, bwd m) ∈ nodLexicon n := by
  have : m - 1 ∈ List.range n := List.mem_range.mpr (by omega)
  constructor <;> [refine List.mem_flatMap.mpr ⟨m - 1, this, ?_⟩;
    refine List.mem_flatMap.mpr ⟨m - 1, this, ?_⟩] <;>
    simp [show m - 1 + 1 = m from by omega]

/-- Separable permutations of the span `i…j`, by the separating-tree
characterization ([stanojevic-steedman-2021] (17)): a singleton, or a split of the
span into two contiguous parts, concatenated in original (`pos`) or inverted
(`neg`) order. -/
inductive SepPerm : ℕ → ℕ → List ℕ → Prop where
  /-- A single word is a separable permutation of its own span. -/
  | single (i : ℕ) : SepPerm i i [i]
  /-- Contiguous parts in canonical order. -/
  | pos {i j k : ℕ} {u v : List ℕ} :
      SepPerm i j u → SepPerm (j + 1) k v → SepPerm i k (u ++ v)
  /-- Contiguous parts in inverted order. -/
  | neg {i j k : ℕ} {u v : List ℕ} :
      SepPerm i j u → SepPerm (j + 1) k v → SepPerm i k (v ++ u)

theorem SepPerm.le {i j : ℕ} {l : List ℕ} (h : SepPerm i j l) : i ≤ j := by
  induction h with
  | single => omega
  | pos _ _ ih1 ih2 => omega
  | neg _ _ ih1 ih2 => omega

/-! ### Completeness

Every separable permutation of the span `i…j` is derivable at both slashings of the
span category `Xᵢ|Xⱼ₊₁` — the paper's Lemmas 1–3 in one induction: `pos` splits
combine by (possibly crossing) forward composition, `neg` splits by backward
composition, and the strengthened both-slashes hypothesis feeds the harmonic and
crossing cases alike. -/

theorem derives_of_sepPerm {n i j : ℕ} {l : List ℕ} (h1 : 1 ≤ i) (hn : j ≤ n)
    (h : SepPerm i j l) :
    (nodGrammar n).Derives (.rslash (.atom i) .dot (.atom (j + 1))) (l.map tok) ∧
    (nodGrammar n).Derives (.lslash (.atom i) .dot (.atom (j + 1))) (l.map tok) := by
  induction h with
  | single m =>
    obtain ⟨hf, hb⟩ := mem_nodLexicon h1 hn
    exact ⟨.lex hf, .lex hb⟩
  | @pos i j k u v hu hv ihu ihv =>
    obtain ⟨huf, hub⟩ := ihu h1 (by have := hv.le; omega)
    obtain ⟨hvf, hvb⟩ := ihv (by omega) hn
    refine ⟨?_, ?_⟩ <;> rw [List.map_append]
    · exact .fc 1 huf hvf (Or.inl rfl) (by simp [Cat.generalizedForwardComp])
    · exact .fc 1 huf hvb (Or.inl rfl) (by simp [Cat.generalizedForwardComp])
  | @neg i j k u v hu hv ihu ihv =>
    obtain ⟨huf, hub⟩ := ihu h1 (by have := hv.le; omega)
    obtain ⟨hvf, hvb⟩ := ihv (by omega) hn
    refine ⟨?_, ?_⟩ <;> rw [List.map_append]
    · exact .bc 1 hvf hub (Or.inl rfl) (by simp [Cat.generalizedBackwardComp])
    · exact .bc 1 hvb hub (Or.inl rfl) (by simp [Cat.generalizedBackwardComp])


/-! ### Soundness

The rule induction: everything derivable over the NOD grammar is a span category
`Xᵢ|Xⱼ₊₁` over a separable permutation of `i…j`. All derivable categories are
first-order, so application (which would need an atomic secondary) and second-order
composition (which would need a second-order secondary) provably never fire. -/

theorem sepPerm_of_derives {n : ℕ} {c : Cat ℕ} {w : List String}
    (h : (nodGrammar n).Derives c w) :
    ∃ i j l, 1 ≤ i ∧ j ≤ n ∧ SepPerm i j l ∧ w = l.map tok ∧
      (c = .rslash (.atom i) .dot (.atom (j + 1)) ∨
       c = .lslash (.atom i) .dot (.atom (j + 1))) := by
  induction h with
  | @lex w' c' hmem =>
    obtain ⟨m, hm, hentry⟩ := List.mem_flatMap.mp hmem
    have hm' := List.mem_range.mp hm
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hentry
    rcases hentry with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨m + 1, m + 1, [m + 1], by omega, by omega, .single _, rfl, Or.inl rfl⟩
    · exact ⟨m + 1, m + 1, [m + 1], by omega, by omega, .single _, rfl, Or.inr rfl⟩
  | @fc nn a b c u v _ _ hgate hc iha ihb =>
    obtain ⟨i, j, l, hi, hj, hsep, rfl, hcat⟩ := iha
    obtain ⟨i', j', l', hi', hj', hsep', rfl, hcat'⟩ := ihb
    rcases hcat with rfl | rfl
    · rcases nn with _ | _ | _ | nn
      · rcases hcat' with rfl | rfl <;> simp [Cat.generalizedForwardComp] at hc
      · rcases hcat' with rfl | rfl <;>
          simp only [Cat.generalizedForwardComp, Option.map_eq_some_iff] at hc
        · obtain ⟨x, hx, rfl⟩ := hc
          rw [Option.ite_none_right_eq_some, Option.some.injEq] at hx
          obtain ⟨hij, rfl⟩ := hx
          obtain rfl : i' = j + 1 := by
            injection hij with hij; omega
          exact ⟨i, j', l ++ l', hi, hj', .pos hsep hsep', by simp, Or.inl rfl⟩
        · obtain ⟨x, hx, rfl⟩ := hc
          rw [Option.ite_none_right_eq_some, Option.some.injEq] at hx
          obtain ⟨hij, rfl⟩ := hx
          obtain rfl : i' = j + 1 := by
            injection hij with hij; omega
          exact ⟨i, j', l ++ l', hi, hj', .pos hsep hsep', by simp, Or.inr rfl⟩
      · rcases hcat' with rfl | rfl <;> exact hgate.elim
      · exact hgate.elim
    · simp at hc
  | @bc nn a b c u v _ _ hgate hc iha ihb =>
    obtain ⟨i, j, l, hi, hj, hsep, rfl, hcat⟩ := iha
    obtain ⟨i', j', l', hi', hj', hsep', rfl, hcat'⟩ := ihb
    rcases hcat' with rfl | rfl
    · simp at hc
    · rcases nn with _ | _ | _ | nn
      · rcases hcat with rfl | rfl <;> simp [Cat.generalizedBackwardComp] at hc
      · rcases hcat with rfl | rfl <;>
          simp only [Cat.generalizedBackwardComp, Option.map_eq_some_iff] at hc
        · obtain ⟨x, hx, rfl⟩ := hc
          rw [Option.ite_none_right_eq_some, Option.some.injEq] at hx
          obtain ⟨hij, rfl⟩ := hx
          obtain rfl : i = j' + 1 := by injection hij with hij; omega
          exact ⟨i', j, l ++ l', hi', hj, .neg hsep' hsep, by simp, Or.inl rfl⟩
        · obtain ⟨x, hx, rfl⟩ := hc
          rw [Option.ite_none_right_eq_some, Option.some.injEq] at hx
          obtain ⟨hij, rfl⟩ := hx
          obtain rfl : i = j' + 1 := by injection hij with hij; omega
          exact ⟨i', j, l ++ l', hi', hj, .neg hsep' hsep, by simp, Or.inr rfl⟩
      · rcases hcat with rfl | rfl <;> exact hgate.elim
      · exact hgate.elim

/-! ### The universal -/

/-- **CCG derives exactly the separable permutations** ([stanojevic-steedman-2021],
Theorems 1 and 2), at the forward slashing of the span category. -/
theorem derives_fwd_iff {n i j : ℕ} {w : List String} (h1 : 1 ≤ i) (hn : j ≤ n) :
    (nodGrammar n).Derives (.rslash (.atom i) .dot (.atom (j + 1))) w ↔
      ∃ l, SepPerm i j l ∧ w = l.map tok := by
  constructor
  · intro h
    obtain ⟨i', j', l, _, _, hsep, rfl, hcat⟩ := sepPerm_of_derives h
    rcases hcat with hcat | hcat
    · obtain ⟨h1, h2⟩ : i' = i ∧ j' = j := by
        injection hcat with hx _ hy
        injection hx with hx; injection hy with hy
        omega
      subst h1; subst h2
      exact ⟨l, hsep, rfl⟩
    · exact absurd hcat (by simp)
  · rintro ⟨l, hsep, rfl⟩
    exact (derives_of_sepPerm h1 hn hsep).1

/-- The mirror of `derives_fwd_iff`, at the backward slashing. -/
theorem derives_bwd_iff {n i j : ℕ} {w : List String} (h1 : 1 ≤ i) (hn : j ≤ n) :
    (nodGrammar n).Derives (.lslash (.atom i) .dot (.atom (j + 1))) w ↔
      ∃ l, SepPerm i j l ∧ w = l.map tok := by
  constructor
  · intro h
    obtain ⟨i', j', l, _, _, hsep, rfl, hcat⟩ := sepPerm_of_derives h
    rcases hcat with hcat | hcat
    · exact absurd hcat (by simp)
    · obtain ⟨h1, h2⟩ : i' = i ∧ j' = j := by
        injection hcat with hx _ hy
        injection hx with hx; injection hy with hy
        omega
      subst h1; subst h2
      exact ⟨l, hsep, rfl⟩
  · rintro ⟨l, hsep, rfl⟩
    exact (derives_of_sepPerm h1 hn hsep).2

end StanojevicSteedman2021
