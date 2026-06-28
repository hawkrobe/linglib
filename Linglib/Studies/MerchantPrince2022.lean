import Linglib.Phonology.OptimalityTheory.Grammar

/-!
# Merchant & Prince (2022): tableaux to grammars

[merchant-prince-2022]'s *Mother of All Tableaux* studies the large-scale structure
of an OT typology: the partition of `Ord(S.Con)` into **grammars**, the invariant
**MOAT** that every violation tableau yielding the typology instantiates, and its
geometry. This file lands the foundational wire — the bridge from the Concrete-OT
**tableau** engine (`OptimalityTheory.Tableau`, the `LexMinProblem` the Studies
already build) to the abstract **`Grammar`** hub (`OptimalityTheory.Grammar`,
[merchant-riggle-2016]).

A row `w` of a tableau, asserted optimal, generates the ERC set of its winner-loser
comparisons against the other candidates (`rowERCSet`); the **grammar of that row**
(`rowGrammar`) is `Grammar.ofERCSet` of those conditions. Its legs are exactly the
rankings under which `w` wins (`mem_rowGrammar_legs_iff_lex`) — this is the semantic
anchor connecting the abstract hub back to lexicographic optimality
([prince-smolensky-1993]).

This is the first real consumer of the `Grammar` hub. The MOAT superstructure —
`Typology` as the partition of these row-grammars (one row per grammar, by "One
Tableau Suffices"), the border-point pair, the EPO, and the MOAT itself — builds on
this bridge and is left to follow-on work.

## Main definitions

* `rowERCSet` — the winner-loser ERCs of a tableau row against the other candidates.
* `rowGrammar` — the `Grammar` of a tableau row (the tableau → hub bridge).

## Main results

* `mem_rowGrammar_legs_iff_lex` — a row's grammar collects exactly the rankings
  under which its profile lexicographically dominates every competitor's.

## References

* [merchant-prince-2022]
* [merchant-riggle-2016]
* [prince-smolensky-1993]
-/

namespace MerchantPrince2022

open OptimalityTheory

variable {C : Type*} [DecidableEq C] {n : ℕ}

/-- The ERC set of a tableau row `w`: `w`'s winner-loser ERCs against every *other*
candidate. These are the ranking conditions a leg must satisfy for `w` to be the
optimum ([prince-2002]). (Noncomputable: it enumerates the competitor `Finset` via
`Finset.toList`; only the *set* of conditions matters, and consistency/membership
stay decidable.) -/
noncomputable def rowERCSet (t : Tableau C n) (w : C) : ERCSet n :=
  (t.candidates.erase w).toList.map (tableauERC t w)

/-- The **grammar of a tableau row** — the bridge from the Concrete-OT tableau
engine to the abstract `Grammar` hub ([merchant-prince-2022]; [merchant-riggle-2016]).
`h` is the consistency of the row's conditions, i.e. that `w` is a genuine,
non-harmonically-bounded optimum. -/
noncomputable def rowGrammar (t : Tableau C n) (w : C)
    (h : ERCSet.consistent (rowERCSet t w)) : Grammar n :=
  Grammar.ofERCSet (rowERCSet t w) h

@[simp] theorem mem_rowGrammar_legs {t : Tableau C n} {w : C}
    {h : ERCSet.consistent (rowERCSet t w)} {r : Ranking n} :
    r ∈ (rowGrammar t w h).legs ↔ ERCSet.satisfiedBy r (rowERCSet t w) := by
  simp only [rowGrammar, Grammar.legs_ofERCSet, ERCSet.mem_linearExtensions]

/-- **The semantic anchor.** A row's grammar collects exactly the rankings under
which `w`'s violation profile, read in the ranking's priority order, lexicographically
dominates every competitor's — i.e. the rankings that select `w` as optimum
([prince-smolensky-1993]). This connects the abstract `Grammar` hub back to the
tableau's lexicographic evaluation. -/
theorem mem_rowGrammar_legs_iff_lex {t : Tableau C n} {w : C}
    {h : ERCSet.consistent (rowERCSet t w)} {r : Ranking n} :
    r ∈ (rowGrammar t w h).legs ↔
      ∀ l ∈ t.candidates.erase w,
        toLex (fun p => t.profile w (r p)) ≤ toLex (fun p => t.profile l (r p)) := by
  rw [mem_rowGrammar_legs]
  unfold ERCSet.satisfiedBy rowERCSet
  constructor
  · intro hsat l hl
    exact (tableauERC_satisfiedBy_iff t r w l).mp
      (hsat _ (List.mem_map.mpr ⟨l, Finset.mem_toList.mpr hl, rfl⟩))
  · intro hlex α hα
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hα
    exact (tableauERC_satisfiedBy_iff t r w l).mpr (hlex l (Finset.mem_toList.mp hl))

end MerchantPrince2022
