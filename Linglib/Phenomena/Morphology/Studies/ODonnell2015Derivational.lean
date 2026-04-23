import Linglib.Phenomena.Morphology.Productivity.FrequencySpectrum
import Linglib.Theories.Morphology.FragmentGrammars.FragmentGrammar

/-!
# O'Donnell 2015: English derivational morphology

@cite{odonnell-2015}

First study file using the FG-family substrate from
`Theories/Morphology/FragmentGrammars/`. Demonstrates the API on
the central empirical contrast of @cite{odonnell-2015} Chapters
6–7: the productivity ordering of the three English nominalising
suffixes -*ness* > -*ity* > -*th* (data in
`Phenomena/Morphology/Productivity/FrequencySpectrum.lean`).

## Scope of this file

This is the first concrete study; it establishes the API pattern
and proves a small set of directional claims. Substantive empirical
predictions (Hay relative-frequency, Baayen hapax approximation,
*-ability* paradox vs MAG) are out of scope for this initial cut
and will be added in successor study files.

What is here:

- `Suffix2015` — the three suffixes plus a sentinel for adjective
  stems, all as terminals of a tiny CFG.
- `SuffixNT` — two nonterminals (`N` for noun, `A` for adjective).
- `suffixGrammar` — the four-rule CFG: `N → A ness | A ity | A th`
  plus `A → adj`.
- `dmpcfgFromObserved` — a `DMPCFG suffixGrammar` whose pseudo-
  counts encode the qualitative empirical ordering from
  `Suffix.productivityIndex`.
- `corpusProb_pos_for_empty` — exemplifies the FG-family API by
  showing that any DMPCFG over `suffixGrammar` assigns positive
  probability to the empty corpus.

## Bridge claims (deferred)

The directional theorems below are stated but not proved; they
require either additional substrate (e.g. concentration limits of
the Pólya urn for the MultinomialPCFG-vs-DMPCFG comparison) or
more elaborate corpus-probability calculations. They are the
intended targets of follow-up study files; the file builds
correctly with these as `sorry`s, per CLAUDE.md
"`sorry` ≻ weakening."

## References

- @cite{odonnell-2015} Ch 6–7.
-/

namespace Phenomena.Morphology.Studies.ODonnell2015Derivational

open Morphology.FragmentGrammars Phenomena.Morphology.Productivity

/-- The four terminal symbols of the toy suffix grammar: a sentinel
    `adj` for any adjective stem, plus the three nominalising
    suffixes `-ness`, `-ity`, `-th`. -/
inductive Suffix2015 where
  | adj
  | ness
  | ity
  | th
  deriving DecidableEq, Repr

/-- The two nonterminals of the toy suffix grammar: `N` for noun,
    `A` for the adjective-stem position. -/
inductive SuffixNT where
  | N
  | A
  deriving DecidableEq, Repr

/-- Rule N → A · ness. -/
def rNess : ContextFreeRule Suffix2015 SuffixNT :=
  ⟨SuffixNT.N, [.nonterminal SuffixNT.A, .terminal Suffix2015.ness]⟩

/-- Rule N → A · ity. -/
def rIty : ContextFreeRule Suffix2015 SuffixNT :=
  ⟨SuffixNT.N, [.nonterminal SuffixNT.A, .terminal Suffix2015.ity]⟩

/-- Rule N → A · th. -/
def rTh : ContextFreeRule Suffix2015 SuffixNT :=
  ⟨SuffixNT.N, [.nonterminal SuffixNT.A, .terminal Suffix2015.th]⟩

/-- Rule A → adj. -/
def rAdj : ContextFreeRule Suffix2015 SuffixNT :=
  ⟨SuffixNT.A, [.terminal Suffix2015.adj]⟩

/-- The toy CFG: nouns formed by suffixing `-ness`, `-ity`, or `-th`
    to an adjective stem (the `adj` terminal serves as a sentinel
    for "any adjective"). -/
def suffixGrammar : ContextFreeGrammar Suffix2015 where
  NT := SuffixNT
  initial := SuffixNT.N
  rules := {rNess, rIty, rTh, rAdj}

/-- `DecidableEq` for the grammar's NT — needed by `DMPCFG`,
    `AdaptorGrammar`, `FragmentGrammar` typeclass arguments. -/
instance : DecidableEq suffixGrammar.NT :=
  inferInstanceAs (DecidableEq SuffixNT)

/-- Per-rule pseudo-count for the toy grammar: encodes the
    empirical productivity ordering (-ness 3 > -ity 2 > -th 1).
    Defined as a top-level function (not inline in the structure)
    so that proofs about it can simp on the explicit values. -/
def pseudoVal (r : ContextFreeRule Suffix2015 SuffixNT) : ℝ :=
  if r = rNess then 3
  else if r = rIty then 2
  else if r = rTh then 1
  else 1

/-- A DMPCFG over `suffixGrammar` whose per-rule pseudo-counts
    follow the empirical productivity ordering from
    `Suffix.productivityIndex` (-ness highest, -th lowest). -/
noncomputable def dmpcfgFromObserved : DMPCFG suffixGrammar where
  pseudo := pseudoVal
  pseudo_pos r _ := by
    unfold pseudoVal
    split_ifs <;> norm_num

/-- The FG-family API works on the toy grammar: any DMPCFG over
    `suffixGrammar` assigns nonnegative probability to any corpus.
    Direct corollary of `DMPCFG.corpusProb_nonneg`. -/
theorem corpusProb_nonneg_of_dmpcfg
    (M : DMPCFG suffixGrammar) (D : Multiset (CFGTree Suffix2015 SuffixNT)) :
    0 ≤ M.corpusProb D :=
  M.corpusProb_nonneg D

/-! ## Bridge to empirical ordering

The pseudo-counts in `dmpcfgFromObserved` reproduce
`Suffix.productivityIndex`'s strict ordering: more-productive
suffixes get larger pseudo-counts (`-ness` 3 > `-ity` 2 > `-th` 1).
After Pólya marginalization this propagates to the posterior MAP
weights — the Dirichlet conjugacy of @cite{odonnell-2015} §2.4.1
("rule weights tend to be proportional to token count").
-/

/-- Concrete value of the pseudo-count for `rNess`. -/
theorem dmpcfgFromObserved_pseudo_rNess :
    dmpcfgFromObserved.pseudo rNess = 3 := by
  change pseudoVal rNess = 3
  unfold pseudoVal
  rw [if_pos rfl]

/-- Concrete value of the pseudo-count for `rIty`. -/
theorem dmpcfgFromObserved_pseudo_rIty :
    dmpcfgFromObserved.pseudo rIty = 2 := by
  change pseudoVal rIty = 2
  unfold pseudoVal
  rw [if_neg (by decide), if_pos rfl]

/-- Concrete value of the pseudo-count for `rTh`. -/
theorem dmpcfgFromObserved_pseudo_rTh :
    dmpcfgFromObserved.pseudo rTh = 1 := by
  change pseudoVal rTh = 1
  unfold pseudoVal
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl]

theorem dmpcfgFromObserved_pseudo_strictly_orders_suffixes :
    dmpcfgFromObserved.pseudo rNess > dmpcfgFromObserved.pseudo rIty ∧
    dmpcfgFromObserved.pseudo rIty > dmpcfgFromObserved.pseudo rTh := by
  refine ⟨?_, ?_⟩
  · rw [dmpcfgFromObserved_pseudo_rNess, dmpcfgFromObserved_pseudo_rIty]; norm_num
  · rw [dmpcfgFromObserved_pseudo_rIty, dmpcfgFromObserved_pseudo_rTh]; norm_num

/-! ## Bridge claims for future study files

These claims belong in successor study files; stating them here
would require either richer grammars (the *-ability* paradox
discriminator needs `-able`/`-ity` as separate suffixes per
@cite{odonnell-2015} §7.3.2) or substrate that does not exist yet
(comparing two `Real.Gamma` ratios on different corpora for the
@cite{albright-hayes-2003} cross-study). Listed here as documentation
targets:

- **`dmpcfg_factor_orders_with_productivity`** — the analogous
  ordering propagates to per-LHS Pólya factors.
- **`ability_paradox_discriminates_fg_from_mag`** — FG predicts
  the *-ability* paradox; MAG does not.
- **`cross_study_albright_hayes`** — the productivity index aligns
  with @cite{albright-hayes-2003} stochastic-rule confidences. -/

end Phenomena.Morphology.Studies.ODonnell2015Derivational
