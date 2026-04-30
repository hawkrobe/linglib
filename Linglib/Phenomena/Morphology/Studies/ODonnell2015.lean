import Linglib.Phenomena.Morphology.Productivity.FrequencySpectrum
import Linglib.Theories.Morphology.FragmentGrammars.FragmentGrammar

/-!
# O'Donnell 2015: English derivational morphology

@cite{odonnell-2015}

First study file using the FG-family substrate from
`Theories/Morphology/FragmentGrammars/`. Demonstrates the API on
the central empirical contrast of @cite{odonnell-2015} Chapter 7
(Fig 7.3, p. 262 / Table 7.1, p. 265): the productivity contrast
between the highly productive English nominaliser *-ness* and the
unproductive *-ion* and *-ate*. Data anchor:
`Phenomena/Morphology/Productivity/FrequencySpectrum.lean`.

## Empirical content

The book's Chapter 7 load-bearing claim is qualitative:
**`-ness:Adj>N` is productive; `-ion:V>N` and `-ate:BND>V` are not.**
On Fig 7.3 (p. 262), only the FG model places `-ness` in its top-5
productive suffixes; DMPCFG, MAG, DOP1 and ENDOP all wrongly elevate
`-ion`, and three of those also wrongly elevate `-ate`. The data
file `FrequencySpectrum.lean` encodes a strict ordering
`ness > ion > ate` via `Suffix.productivityIndex`; the
`ion > ate` half is a tie-break (both are unproductive on novel
forms but `-ate` is structurally more restricted), not part of
@cite{odonnell-2015}'s central contrast.

Note that `-ate` is **not** a nominaliser — it is a verb-forming
suffix that selects bound stems (e.g. *segregate* from bound
*segregat-*). The toy grammar below reflects this: `rAte` produces
`V`, not `N`, with a `BND` (bound-stem) nonterminal as its argument.
The three suffixes are grouped here by being the central derivational
contrast of @cite{odonnell-2015} Ch 7, not by sharing an output category.

## DMPCFG critique (Ch 7)

The DMPCFG model bases its productivity inferences on the token
frequency of suffixes (@cite{odonnell-2015} Ch 7, p. 268). Per
@cite{odonnell-2015} Fig 7.4 (p. 267), `-ion` has roughly an order
of magnitude more CELEX tokens than `-ness`, so a learned DMPCFG
posterior places `-ion` above `-ness` in productivity — exactly the
failure mode @cite{odonnell-2015} uses to discriminate FG from
DMPCFG. The pseudo-counts in `dmpcfgFromObserved` are *stipulated*
to track the empirical productivity (via `productivityIndex`),
not learned from a corpus. Two PMF-form theorems below
(`…_prior_lt` and `…_lt_of_count_gap`) make the prior + flip
dichotomy Lean-checkable.

## References

- @cite{odonnell-2015} Ch 6–7.
-/

namespace Phenomena.Morphology.Studies.ODonnell2015

open Morphology.FragmentGrammars Phenomena.Morphology.Productivity

/-! ## Toy CFG -/

/-- The six terminal symbols of the toy derivational grammar:
    sentinels `adj`/`v`/`bnd` for adjective, verb and bound-stem
    bases, plus the three derivational suffixes `-ness`, `-ion`,
    `-ate`. -/
inductive Sym where
  | adj
  | v
  | bnd
  | ness
  | ion
  | ate
  deriving DecidableEq, Repr

/-- The four nonterminals of the toy derivational grammar.
    `BND` represents a bound stem — the selectional restriction
    of `-ate` (cf. *segregat-*, *demonstrat-*). -/
inductive SuffixNT where
  | N
  | A
  | V
  | BND
  deriving DecidableEq, Repr

/-- Rule N → A · ness. -/
def rNess : ContextFreeRule Sym SuffixNT :=
  ⟨SuffixNT.N, [.nonterminal SuffixNT.A, .terminal Sym.ness]⟩

/-- Rule N → V · ion. -/
def rIon : ContextFreeRule Sym SuffixNT :=
  ⟨SuffixNT.N, [.nonterminal SuffixNT.V, .terminal Sym.ion]⟩

/-- Rule V → BND · ate. Reflects @cite{odonnell-2015}'s `-ate:BND>V`
    classification (p. 261): `-ate` is a verb-forming suffix that
    selects bound stems, not a noun-forming suffix. -/
def rAte : ContextFreeRule Sym SuffixNT :=
  ⟨SuffixNT.V, [.nonterminal SuffixNT.BND, .terminal Sym.ate]⟩

/-- Rule A → adj. -/
def rAdj : ContextFreeRule Sym SuffixNT :=
  ⟨SuffixNT.A, [.terminal Sym.adj]⟩

/-- Rule V → v. -/
def rV : ContextFreeRule Sym SuffixNT :=
  ⟨SuffixNT.V, [.terminal Sym.v]⟩

/-- Rule BND → bnd. -/
def rBnd : ContextFreeRule Sym SuffixNT :=
  ⟨SuffixNT.BND, [.terminal Sym.bnd]⟩

/-- The toy CFG: nominalisation via `-ness` (from adjective) or
    `-ion` (from verb), verb formation via `-ate` (from bound stem). -/
def suffixGrammar : ContextFreeGrammar Sym where
  NT := SuffixNT
  initial := SuffixNT.N
  rules := {rNess, rIon, rAte, rAdj, rV, rBnd}

/-- `DecidableEq` for the grammar's `NT` projection — needed by
    `DMPCFG`'s typeclass arguments. Not synthesised automatically
    because `suffixGrammar.NT` is a structure projection that the
    typeclass solver does not reduce to `SuffixNT`. -/
instance : DecidableEq suffixGrammar.NT :=
  inferInstanceAs (DecidableEq SuffixNT)

/-! ## Bridge from data layer + DMPCFG instance -/

/-- Bridge from `Productivity.Suffix` to the rules of this grammar.
    Free-standing, not `Suffix.toRule` — dot notation would resolve
    to `Productivity.Suffix.toRule`. -/
def suffixToRule : Suffix → ContextFreeRule Sym SuffixNT
  | .ness => rNess
  | .ion  => rIon
  | .ate  => rAte

/-- Per-rule pseudo-count for the toy grammar. The three
    productivity-bearing rules get `productivityIndex + 1` (so
    `ness ↦ 3`, `ion ↦ 2`, `ate ↦ 1`), inheriting both the strict
    ordering and any future revision of `Suffix.productivityIndex`.
    The three structural selectional rules get a neutral `1`. -/
def pseudoVal (r : ContextFreeRule Sym SuffixNT) : ℝ :=
  if r = rNess then ((Suffix.ness.productivityIndex : ℕ) : ℝ) + 1
  else if r = rIon then ((Suffix.ion.productivityIndex : ℕ) : ℝ) + 1
  else if r = rAte then ((Suffix.ate.productivityIndex : ℕ) : ℝ) + 1
  else if r = rAdj then 1
  else if r = rV then 1
  else if r = rBnd then 1
  else 1

/-- A `DMPCFG` over `suffixGrammar` whose per-rule pseudo-counts are
    derived from `Suffix.productivityIndex` (the data layer's
    qualitative productivity ranking). The connection is structural:
    if the data file revises `productivityIndex`, the pseudo-counts
    here change in lockstep. -/
def dmpcfgFromObserved : DMPCFG suffixGrammar where
  pseudo := pseudoVal
  pseudo_pos r _ := by
    unfold pseudoVal
    split_ifs <;> positivity

/-! ## Plumbing: named N-bucket witnesses + parametric pseudoVal lemma -/

/-- `rNess` as an inhabitant of the N-LHS subtype. Named once so
    consumers don't repeat `⟨rNess, by decide⟩` at every call. -/
private def nNess : DMPCFG.RulesWithLHS (G := suffixGrammar) SuffixNT.N :=
  ⟨rNess, by decide⟩

/-- `rIon` as an inhabitant of the N-LHS subtype. -/
private def nIon : DMPCFG.RulesWithLHS (G := suffixGrammar) SuffixNT.N :=
  ⟨rIon, by decide⟩

/-- The N-LHS bucket of `suffixGrammar` is nonempty (`rNess` ∈ it).
    Required for `mapWeightPMF` and `mapWeight_sum_eq_one_of_lhs`. -/
instance n_bucket_nonempty :
    Nonempty (DMPCFG.RulesWithLHS (G := suffixGrammar) SuffixNT.N) :=
  ⟨nNess⟩

/-- Parametric pseudo-count formula for productivity-bearing rules:
    `pseudoVal (suffixToRule s) = productivityIndex s + 1`. -/
private lemma pseudoVal_suffixToRule (s : Suffix) :
    pseudoVal (suffixToRule s) = ((s.productivityIndex : ℕ) : ℝ) + 1 := by
  cases s <;> rfl

@[simp] private lemma pseudoVal_rNess : pseudoVal rNess = 3 := by
  show pseudoVal (suffixToRule .ness) = 3
  rw [pseudoVal_suffixToRule]; norm_num [Suffix.productivityIndex]

@[simp] private lemma pseudoVal_rIon : pseudoVal rIon = 2 := by
  show pseudoVal (suffixToRule .ion) = 2
  rw [pseudoVal_suffixToRule]; norm_num [Suffix.productivityIndex]

@[simp] private lemma pseudoVal_rAte : pseudoVal rAte = 1 := by
  show pseudoVal (suffixToRule .ate) = 1
  rw [pseudoVal_suffixToRule]; norm_num [Suffix.productivityIndex]

/-! ## Theorems -/

/-- The FG-family API exemplified on the toy grammar: any `DMPCFG`
    over `suffixGrammar` assigns probability 1 — and hence positive
    probability — to the empty corpus. Direct corollary of
    `DMPCFG.corpusProb_zero`. -/
theorem corpusProb_pos_for_empty (M : DMPCFG suffixGrammar) :
    0 < M.corpusProb 0 := by
  rw [DMPCFG.corpusProb_zero]; exact zero_lt_one

/-- Structural drift sentry: a stronger productivity ranking in the
    data layer (`Phenomena/Morphology/Productivity/FrequencySpectrum`)
    implies a larger DMPCFG pseudo-count for the corresponding rule.
    Propagates `moreProductiveThan` through `pseudoVal`, so this
    breaks if `Suffix.productivityIndex` is revised in a way that
    contradicts the rule-level encoding. -/
theorem dmpcfgFromObserved_pseudo_respects_productivity
    {a b : Suffix} (h : moreProductiveThan a b) :
    dmpcfgFromObserved.pseudo (suffixToRule a) >
        dmpcfgFromObserved.pseudo (suffixToRule b) := by
  show pseudoVal (suffixToRule a) > pseudoVal (suffixToRule b)
  rw [pseudoVal_suffixToRule, pseudoVal_suffixToRule]
  have : (a.productivityIndex : ℝ) > (b.productivityIndex : ℝ) := by
    exact_mod_cast h
  linarith

/-- The central failure mode @cite{odonnell-2015} Ch 7 documents
    (p. 268; Fig 7.4 p. 267 supplies the CELEX evidence). DMPCFG
    posterior MAP weights track `pseudo + count`, so any corpus
    where `rIon` derivations exceed `rNess` derivations by more than
    1 makes DMPCFG's PMF rank `rIon` above `rNess` — directly
    contradicting `moreProductiveThan ness ion`. The `+1` threshold
    reflects the pseudo-count gap (`pseudoVal rNess − pseudoVal rIon
    = 3 − 2 = 1`); once corpus counts overcome the prior gap,
    frequency dominates.

    O'Donnell's CELEX numbers in Fig 7.4 (`-ion`: ~162k tokens vs
    `-ness`: ~16k tokens) leave the gap an order of magnitude larger
    than +1, so the conclusion holds for realistic data; the
    hypothesis is the abstract minimum that suffices. -/
theorem dmpcfgFromObserved_mapWeightPMF_lt_of_count_gap
    (D : Multiset (CFGTree Sym SuffixNT))
    (h : DMPCFG.corpusRuleCount (G := suffixGrammar) rNess D + 1 <
         DMPCFG.corpusRuleCount (G := suffixGrammar) rIon D) :
    dmpcfgFromObserved.mapWeightPMF D nNess <
        dmpcfgFromObserved.mapWeightPMF D nIon := by
  rw [DMPCFG.mapWeightPMF_lt_iff]
  show pseudoVal rNess +
        (DMPCFG.corpusRuleCount (G := suffixGrammar) rNess D : ℝ) <
      pseudoVal rIon +
        (DMPCFG.corpusRuleCount (G := suffixGrammar) rIon D : ℝ)
  rw [pseudoVal_rNess, pseudoVal_rIon]
  have h' : (DMPCFG.corpusRuleCount (G := suffixGrammar) rNess D : ℝ) + 1 <
            (DMPCFG.corpusRuleCount (G := suffixGrammar) rIon D : ℝ) := by
    exact_mod_cast h
  linarith

/-- Prior PMF (empty corpus): DMPCFG correctly orders the N-rules of
    `suffixGrammar`. With no data, the posterior IS the prior (per
    `mapWeight_zero`), and the prior IS the per-LHS-normalised
    pseudo-counts. Since `pseudoVal rNess > pseudoVal rIon` by
    construction, the PMF mass at `rNess` exceeds that at `rIon`.

    The *first half* of the @cite{odonnell-2015} Ch 7 critique of
    DMPCFG: it does not start wrong. The model's failure mode is
    data-driven, not prior-driven. -/
theorem dmpcfgFromObserved_mapWeightPMF_prior_lt :
    dmpcfgFromObserved.mapWeightPMF 0 nIon <
      dmpcfgFromObserved.mapWeightPMF 0 nNess := by
  rw [DMPCFG.mapWeightPMF_lt_iff]
  show pseudoVal rIon + (DMPCFG.corpusRuleCount (G := suffixGrammar) rIon 0 : ℝ) <
       pseudoVal rNess + (DMPCFG.corpusRuleCount (G := suffixGrammar) rNess 0 : ℝ)
  rw [DMPCFG.corpusRuleCount_zero, DMPCFG.corpusRuleCount_zero,
      pseudoVal_rIon, pseudoVal_rNess]
  norm_num

/-- The full @cite{odonnell-2015} Ch 7 critique of DMPCFG, in one
    theorem. Two facts that look contradictory but aren't:

    - Without data (empty corpus), DMPCFG's PMF over the N-rules
      ranks `rNess` above `rIon` — matching the data-layer
      `productivityIndex`.
    - Given a corpus with sufficiently many `rIon` derivations
      (more than `rNess` by more than the pseudo-count gap of 1),
      the PMF flips and ranks `rIon` above `rNess` — contradicting
      the empirical productivity ordering @cite{odonnell-2015}
      reports for English.

    Per Ch 7 (Fig 7.4 p. 267), DMPCFG is built with the right prior
    but bases its posterior on `pseudo + count`, so when CELEX-scale
    token frequencies hit the model the data overwhelms the prior
    and the posterior ranking flips. The fix the book proposes —
    Fragment Grammars — gives a different posterior structure that
    doesn't collapse productivity into raw frequency. -/
theorem dmpcfgFromObserved_mapWeightPMF_prior_and_posterior_disagree
    (D : Multiset (CFGTree Sym SuffixNT))
    (h : DMPCFG.corpusRuleCount (G := suffixGrammar) rNess D + 1 <
         DMPCFG.corpusRuleCount (G := suffixGrammar) rIon D) :
    -- Prior: ness > ion at empty corpus
    (dmpcfgFromObserved.mapWeightPMF 0 nIon <
      dmpcfgFromObserved.mapWeightPMF 0 nNess) ∧
    -- Posterior: ion > ness once data dominates
    (dmpcfgFromObserved.mapWeightPMF D nNess <
      dmpcfgFromObserved.mapWeightPMF D nIon) :=
  ⟨dmpcfgFromObserved_mapWeightPMF_prior_lt,
   dmpcfgFromObserved_mapWeightPMF_lt_of_count_gap D h⟩

end Phenomena.Morphology.Studies.ODonnell2015

/-
TODO(theorem) — bridge claims for future study files. Each is
followed by the substrate gap that currently blocks stating it
as a Lean theorem.

- `fg_predicts_ness_in_top_5` — @cite{odonnell-2015} Fig 7.3 central
  claim. Needs a "top-K productivity ranking" primitive over
  `FragmentGrammar` posteriors (substrate has `corpusProbGivenStorage`
  but no MAP-extraction lemma).
- `fg_baayen_correlation` — @cite{odonnell-2015} Table 7.1. Needs a
  Baayen P-measure (hapax/N) substrate; `grep hapax Theories/`
  returns no matches.
- `fg_consistent_with_hay_relative_frequency` — @cite{odonnell-2015}
  §7.3.2 (p. 269). Needs a relative-frequency comparator primitive
  (Hay 2001 / Hay & Baayen 2002).
- `ability_paradox_discriminates_fg_from_mag` — @cite{odonnell-2015}
  Ch 8. "MAG" is `AdaptorGrammar` (already formalised in
  `FragmentGrammars/AdaptorGrammar.lean`); needs a richer toy grammar
  with `-able`/`-ity` rules and a stored `-ability` fragment.
- `cross_study_albright_hayes` — productivity index alignment. Needs
  a `suffixToAHRule` shim into `Phenomena/Morphology/Studies/AlbrightHayes2003.lean`'s
  `StochasticRule` substrate, then a `pseudo`-vs-`rawConfidence`
  comparison theorem.
-/
