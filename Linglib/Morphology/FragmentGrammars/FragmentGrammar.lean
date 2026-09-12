import Linglib.Morphology.FragmentGrammars.AdaptorGrammar

/-!
# Fragment grammars

This file defines fragment grammars, the model of [odonnell-2015]: an adaptor grammar in which
every nonterminal on the right-hand side of every rule carries a Pólya urn over the two outcomes
`recurse` and `halt`, together with the corpus probability of §3.1.8 given the latent table and
halt-count assignments.

Expanding a rule `r`, a fragment grammar decides at each right-hand-side nonterminal `B` whether
to expand `B` productively or to halt and leave `B` an open slot of the fragment being stored.
The decision is a biased coin whose weight `ν_{r,B}` has a beta prior with pseudo-counts
`ψ_{r,B}`; integrating out `ν_{r,B}` turns the decisions taken at that slot into a two-colour
Pólya urn, which is the representation the book computes with. Recursing everywhere recovers the
Dirichlet–multinomial PCFG (`DMPCFG`), and deciding once per nonterminal rather than once per slot
recovers the adaptor grammar (`AdaptorGrammar`); a fragment grammar stores partial trees with
arbitrary open slots.

## Main definitions

* `FragmentGrammar G`: an `AdaptorGrammar G` with an urn `halt r i : PolyaUrn Decision` at each
  nonterminal position `i` of each rule `r`.
* `FragmentGrammar.HaltCounts G`: the latent count `Z` of recurse and halt decisions per slot.
* `FragmentGrammar.corpusProbGivenStorage D Y Z`: the corpus probability of §3.1.8 given tables
  `Y` and halt counts `Z`, the adaptor-grammar factor times one `PolyaUrn.seqProb` per slot.
* `FragmentGrammar.posterior D Z`: the conjugate update by a corpus and its halt counts.

## Implementation notes

`Z` is latent for the same reason `Y` is: marginalising over `(Y, Z)` is the inference problem
of §3.2. The book writes the halt count at slot `B` of rule `r` as `x_r - z_{r,B}`, so a `Z`
consistent with the corpus has `Z r i .recurse + Z r i .halt` equal to the corpus count of `r`;
as for `TableAssignment`, that consistency is a hypothesis of the caller.

## References

* [odonnell-2015] §2.3.6, §3.1.8.
-/

namespace Morphology.FragmentGrammars

open ProbabilityTheory

/-- The outcome of the lazy coin at a nonterminal slot: `recurse` expands the slot productively,
`halt` leaves it open in the stored fragment. -/
inductive FragmentGrammar.Decision
  | recurse
  | halt
  deriving DecidableEq, Fintype, Inhabited

/-- A fragment grammar over `G`: an adaptor grammar with, at each nonterminal position of each
rule, a Pólya urn over `recurse`/`halt` decisions whose pseudo-counts are the beta parameters
`ψ_{r,B}` of [odonnell-2015]. -/
@[ext]
structure FragmentGrammar {T : Type} [DecidableEq T] (G : ContextFreeGrammar T)
    [DecidableEq G.NT] extends AdaptorGrammar G where
  /-- The urn over `recurse`/`halt` decisions at nonterminal position `i` of rule `r`. -/
  halt : (r : ContextFreeRule T G.NT) → r.NonterminalPos → PolyaUrn FragmentGrammar.Decision

namespace FragmentGrammar

variable {T : Type} [DecidableEq T] {G : ContextFreeGrammar T} [DecidableEq G.NT]

/-- The latent variable `Z` of §3.1.8: at each nonterminal position of each rule, the number of
`recurse` and of `halt` decisions taken there across the corpus. -/
abbrev HaltCounts (G : ContextFreeGrammar T) : Type :=
  (r : ContextFreeRule T G.NT) → r.NonterminalPos → Decision → ℕ

variable (M : FragmentGrammar G)

/-- The corpus probability of §3.1.8 given a table assignment `Y` and halt counts `Z`: the
adaptor-grammar factor `AdaptorGrammar.corpusProbGivenTables` times, at each nonterminal slot,
the urn likelihood `B(ψ + z↻, ψ' + z⊥) / B(ψ, ψ')` of the decisions taken there. -/
noncomputable def corpusProbGivenStorage (D : Multiset (DerivationTree T G.NT))
    (Y : AdaptorGrammar.TableAssignment G) (Z : HaltCounts G) : ℝ :=
  M.corpusProbGivenTables D Y * ∏ r ∈ G.rules, ∏ i, (M.halt r i).seqProb (Z r i)

theorem corpusProbGivenStorage_nonneg (D : Multiset (DerivationTree T G.NT))
    (Y : AdaptorGrammar.TableAssignment G) (Z : HaltCounts G) :
    0 ≤ M.corpusProbGivenStorage D Y Z :=
  mul_nonneg (M.corpusProbGivenTables_nonneg D Y) <| Finset.prod_nonneg λ r _ =>
    Finset.prod_nonneg λ i _ => ((M.halt r i).seqProb_pos _).le

/-- The empty corpus with empty tables and no decisions has probability `1`. -/
@[simp]
theorem corpusProbGivenStorage_empty :
    M.corpusProbGivenStorage 0 (AdaptorGrammar.emptyTables G) 0 = 1 := by
  simp only [corpusProbGivenStorage, AdaptorGrammar.corpusProbGivenTables_empty, one_mul]
  exact Finset.prod_eq_one λ r _ => Finset.prod_eq_one λ i _ => (M.halt r i).seqProb_zero

/-- The conjugate update by a corpus `D` and its halt counts `Z`: the adaptor-grammar component
absorbs the rule counts of `D`, and the urn at each slot absorbs the decisions taken there. -/
noncomputable def posterior (D : Multiset (DerivationTree T G.NT)) (Z : HaltCounts G) :
    FragmentGrammar G where
  toAdaptorGrammar := M.toAdaptorGrammar.posterior D
  halt r i := (M.halt r i).posterior (Z r i)

@[simp]
theorem posterior_zero : M.posterior 0 0 = M := by
  ext1 <;> simp [posterior]

theorem posterior_add (D₁ D₂ : Multiset (DerivationTree T G.NT)) (Z₁ Z₂ : HaltCounts G) :
    M.posterior (D₁ + D₂) (Z₁ + Z₂) = (M.posterior D₁ Z₁).posterior D₂ Z₂ := by
  ext1 <;> simp [posterior, AdaptorGrammar.posterior_add, PolyaUrn.posterior_add]

end FragmentGrammar

end Morphology.FragmentGrammars
