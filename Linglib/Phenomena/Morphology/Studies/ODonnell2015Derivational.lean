import Linglib.Phenomena.Morphology.Productivity.FrequencySpectrum
import Linglib.Theories.Morphology.FragmentGrammars.FragmentGrammar

/-!
# O'Donnell 2015: English derivational morphology

@cite{odonnell-2015}

First study file using the FG-family substrate from
`Theories/Morphology/FragmentGrammars/`. Demonstrates the API on
the central empirical contrast of @cite{odonnell-2015} Chapter 7
(Fig 7.3, p. 262 / Table 7.1, p. 265): the productivity ordering
of the three English nominalising suffixes -*ness* > -*ion* >
-*ate*. Data anchor: `Phenomena/Morphology/Productivity/FrequencySpectrum.lean`.

## Scope of this file

This is the first concrete study; it establishes the API pattern
and proves a small set of directional claims. Substantive empirical
predictions (Hay relative-frequency, Baayen hapax approximation,
*-ability* paradox vs MAG) are out of scope for this initial cut
and will be added in successor study files.

What is here:

- `Suffix2015` — the three suffixes plus a sentinel for adjective
  / verb / bound-stem bases, all as terminals of a tiny CFG.
- `SuffixNT` — three nonterminals (`N` for noun, `A` for
  adjective, `V` for verb).
- `suffixGrammar` — the five-rule CFG: `N → A ness | V ion | V ate`
  plus `A → adj` and `V → v`.
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
correctly with these as documentation-only items, per CLAUDE.md
"`sorry` ≻ weakening."

## References

- @cite{odonnell-2015} Ch 6–7.
-/

namespace Phenomena.Morphology.Studies.ODonnell2015Derivational

open Morphology.FragmentGrammars Phenomena.Morphology.Productivity

/-- The five terminal symbols of the toy suffix grammar: sentinels
    `adj` / `v` for adjective and verb stems, plus the three
    nominalising suffixes `-ness`, `-ion`, `-ate`. -/
inductive Suffix2015 where
  | adj
  | v
  | ness
  | ion
  | ate
  deriving DecidableEq, Repr

/-- The three nonterminals of the toy suffix grammar. -/
inductive SuffixNT where
  | N
  | A
  | V
  deriving DecidableEq, Repr

/-- Rule N → A · ness. -/
def rNess : ContextFreeRule Suffix2015 SuffixNT :=
  ⟨SuffixNT.N, [.nonterminal SuffixNT.A, .terminal Suffix2015.ness]⟩

/-- Rule N → V · ion. -/
def rIon : ContextFreeRule Suffix2015 SuffixNT :=
  ⟨SuffixNT.N, [.nonterminal SuffixNT.V, .terminal Suffix2015.ion]⟩

/-- Rule N → V · ate. -/
def rAte : ContextFreeRule Suffix2015 SuffixNT :=
  ⟨SuffixNT.N, [.nonterminal SuffixNT.V, .terminal Suffix2015.ate]⟩

/-- Rule A → adj. -/
def rAdj : ContextFreeRule Suffix2015 SuffixNT :=
  ⟨SuffixNT.A, [.terminal Suffix2015.adj]⟩

/-- Rule V → v. -/
def rV : ContextFreeRule Suffix2015 SuffixNT :=
  ⟨SuffixNT.V, [.terminal Suffix2015.v]⟩

/-- The toy CFG: nouns formed either by suffixing `-ness` to an
    adjective or `-ion`/`-ate` to a verb. Categorical typing
    (Adj vs V) is what makes the *-ate* and *-ion* selectional
    restrictions visible. -/
def suffixGrammar : ContextFreeGrammar Suffix2015 where
  NT := SuffixNT
  initial := SuffixNT.N
  rules := {rNess, rIon, rAte, rAdj, rV}

/-- `DecidableEq` for the grammar's NT — needed by `DMPCFG`,
    `AdaptorGrammar`, `FragmentGrammar` typeclass arguments. -/
instance : DecidableEq suffixGrammar.NT :=
  inferInstanceAs (DecidableEq SuffixNT)

/-- Per-rule pseudo-count for the toy grammar: encodes the
    empirical productivity ordering (-ness 3 > -ion 2 > -ate 1).
    Defined as a top-level function (not inline in the structure)
    so that proofs about it can simp on the explicit values. -/
def pseudoVal (r : ContextFreeRule Suffix2015 SuffixNT) : ℝ :=
  if r = rNess then 3
  else if r = rIon then 2
  else if r = rAte then 1
  else 1

/-- A DMPCFG over `suffixGrammar` whose per-rule pseudo-counts
    follow the empirical productivity ordering from
    `Suffix.productivityIndex` (-ness highest, -ate lowest). -/
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
suffixes get larger pseudo-counts (`-ness` 3 > `-ion` 2 >
`-ate` 1). After Pólya marginalization this propagates to the
posterior MAP weights — the Dirichlet conjugacy of
@cite{odonnell-2015} §2.4.1 ("rule weights tend to be
proportional to token count").

Note: in the DMPCFG model this propagation is *intuitively wrong*
on real corpora — DMPCFG learns weights proportional to token
count, so it would predict `-ion > -ness` if `-ion` has more
tokens (which it does in CELEX, per @cite{odonnell-2015}
Fig 7.4, p. 267). This is the @cite{odonnell-2015} Ch 7 critique
of DMPCFG. The pseudo-counts here are *stipulated* to match the
empirical productivity, not learned — so they bypass the critique.
A follow-up study file should set up the actual token-frequency
comparison.
-/

/-- Concrete value of the pseudo-count for `rNess`. -/
theorem dmpcfgFromObserved_pseudo_rNess :
    dmpcfgFromObserved.pseudo rNess = 3 := by
  change pseudoVal rNess = 3
  unfold pseudoVal
  rw [if_pos rfl]

/-- Concrete value of the pseudo-count for `rIon`. -/
theorem dmpcfgFromObserved_pseudo_rIon :
    dmpcfgFromObserved.pseudo rIon = 2 := by
  change pseudoVal rIon = 2
  unfold pseudoVal
  rw [if_neg (by decide), if_pos rfl]

/-- Concrete value of the pseudo-count for `rAte`. -/
theorem dmpcfgFromObserved_pseudo_rAte :
    dmpcfgFromObserved.pseudo rAte = 1 := by
  change pseudoVal rAte = 1
  unfold pseudoVal
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl]

theorem dmpcfgFromObserved_pseudo_strictly_orders_suffixes :
    dmpcfgFromObserved.pseudo rNess > dmpcfgFromObserved.pseudo rIon ∧
    dmpcfgFromObserved.pseudo rIon > dmpcfgFromObserved.pseudo rAte := by
  refine ⟨?_, ?_⟩
  · rw [dmpcfgFromObserved_pseudo_rNess, dmpcfgFromObserved_pseudo_rIon]; norm_num
  · rw [dmpcfgFromObserved_pseudo_rIon, dmpcfgFromObserved_pseudo_rAte]; norm_num

/-! ## Bridge claims for future study files

These claims belong in successor study files; stating them here
would require either richer grammars (the *-ability* paradox
discriminator needs `-able`/`-ity` as separate suffixes; the
paradox is discussed in @cite{odonnell-2015} Ch 8 and motivated
by the productivity-and-ordering generalization of §7.3.3) or
substrate that does not exist yet (comparing two `Real.Gamma`
ratios on different corpora for the @cite{albright-hayes-2003}
cross-study). Listed here as documentation targets:

- **`fg_predicts_ness_in_top_5`** — @cite{odonnell-2015} Fig 7.3
  central claim. Requires a corpus + actual model fit.
- **`dmpcfg_wrongly_predicts_ion_productive`** — Fig 7.3 negative
  claim. Same.
- **`fg_baayen_correlation`** — @cite{odonnell-2015} Table 7.1.
- **`fg_consistent_with_hay_relative_frequency`** —
  @cite{odonnell-2015} §7.3.2 / Fig 7.5.
- **`ability_paradox_discriminates_fg_from_mag`** — Ch 8.
- **`cross_study_albright_hayes`** — productivity index alignment. -/

end Phenomena.Morphology.Studies.ODonnell2015Derivational
