import Linglib.Morphology.FragmentGrammars.FragmentGrammar
import Linglib.Morphology.Exponence.Rule

/-!
# O'Donnell 2015: English derivational morphology

[odonnell-2015]

First study file using the FG-family substrate from
`Morphology/FragmentGrammars/`. Demonstrates the API on
the central empirical contrast of [odonnell-2015] Chapter 7
(Fig 7.3, p. 262): the productivity contrast between the highly
productive English nominaliser *-ness* and the unproductive *-ion*
and *-ate*.

## Empirical content

The book's Chapter 7 load-bearing claim is qualitative:
**`-ness:Adj>N` is productive; `-ion:V>N` and `-ate:BND>V` are not.**
On Fig 7.3 (p. 262), only the FG model places `-ness` in its top-5
productive suffixes; all four competing models (DMPCFG, MAG, DOP1,
ENDOP) rank `-ion` first or second, and three of those (DMPCFG, DOP1,
ENDOP) also wrongly elevate `-ate` (pp. 261–263). Table 7.1 (p. 265)
adds that only FG correlates strongly with Baayen's hapax-based
productivity estimators. `Suffix.productivityIndex` encodes a strict
ordering `ness > ion > ate`; the `ion > ate` half is a tie-break
(both are unproductive on novel forms but `-ate` is structurally more
restricted), not part of [odonnell-2015]'s central contrast.

Note that `-ate` is **not** a nominaliser — it is a verb-forming
suffix that selects bound stems (e.g. *segregate* from bound
*segregat-*). The toy grammar below reflects this: `rAte` produces
`V`, not `N`, with a `BND` (bound-stem) nonterminal as its argument.
The three suffixes are grouped here by being the central derivational
contrast of [odonnell-2015] Ch 7, not by sharing an output category.

## DMPCFG critique (Ch 7)

The DMPCFG model bases its productivity inferences on the token
frequency of suffixes ([odonnell-2015] Ch 7, p. 268). Per
[odonnell-2015] Fig 7.4 (p. 267), `-ion` has roughly an order
of magnitude more CELEX tokens than `-ness`, so a learned DMPCFG
posterior places `-ion` above `-ness` in productivity — exactly the
failure mode [odonnell-2015] uses to discriminate FG from
DMPCFG. The pseudo-counts in `dmpcfgFromObserved` are *stipulated*
to track the empirical productivity (via `productivityIndex`),
not learned from a corpus. Two PMF-form theorems below
(`…_prior_lt` and `…_lt_of_count_gap`) make the prior + flip
dichotomy Lean-checkable.

## References

- [odonnell-2015] Ch 6–7.
-/

namespace ODonnell2015

open Morphology.FragmentGrammars

/-! ## The three suffixes

[odonnell-2015] Chapter 7's central productivity contrast (pp. 261–263).
The terms "productive" and "unproductive" are pre-theoretic descriptions
consistent with the literature the book reviews; the data below commits
to nothing about *why* one suffix is productive and another is not. -/

/-- The three English derivational suffixes of the Chapter 7 contrast.

- *-ness* (Adj>N): "perhaps the most commonly-discussed productive
  suffix in English" (p. 261); *pine-scented* → *pine-scentedness*.
- *-ion* (V>N): high type and token frequency but unproductive on novel
  verbs — the competing models' "obviously absurd prediction" is that it
  attaches to arbitrary verbs, producing \**meetion* "a MEETING event"
  (pp. 261–262).
- *-ate* (BND>V): a verb-forming suffix "restricted, by its categorial
  definition, from attaching to anything besides bound stems" (p. 263),
  e.g. *segregate* from bound *segregat-*. -/
inductive Suffix where
  | ness
  | ion
  | ate
  deriving DecidableEq, Repr

/-- A pre-theoretic *productivity index* for the three suffixes — higher
is more productive. Coding `ness > ion > ate` reproduces the ordering
implied by [odonnell-2015] Chapter 7 (Fig 7.3 and the §7.3.1.1
discussion). The `ion > ate` direction is a tie-break: both are
unproductive on novel forms, but `ate` is structurally more restricted
(bound stems only), so we rank it strictly lower. -/
def Suffix.productivityIndex : Suffix → Nat
  | .ness => 2
  | .ion  => 1
  | .ate  => 0

/-- The pre-theoretic strict ordering on the three suffixes by
productivity. Any theory of productivity that purports to account for
the [odonnell-2015] Chapter 7 data must reproduce this ordering;
failure to do so falsifies the theory against the data (this is exactly
the discriminator deployed against DMPCFG / MAG / DOP1 / ENDOP in
Fig 7.3, all of which place *-ion* in their top 5). -/
def moreProductiveThan (a b : Suffix) : Prop :=
  a.productivityIndex > b.productivityIndex

instance : DecidableRel moreProductiveThan := fun a b =>
  inferInstanceAs (Decidable (a.productivityIndex > b.productivityIndex))

/-! ## Frequency-spectrum statistics (Fig 7.4, pp. 267–268)

The book's distributional evidence: *-ness* has the "large number of
rare events" (LNRE) shape characteristic of a productive process — a
spectrum "sharply peaked at low-frequency forms"; *-ion*'s spectrum has
few hapaxes and spreads its mass through higher frequency ranges
(cf. §1.2.6 and Fig 1.1 on unproductive *-ity*/*-th*). Fig 7.4 reports
spectra for *-ness* and *-ion* only; the book gives no spectrum for
*-ate*, whose unproductivity is categorial (bound stems only). -/

/-- Corpus statistics for a suffix in the Chapter 7 training corpus
(CELEX-derived): word types, word tokens, hapax legomena. -/
structure SpectrumStats where
  wordTypes  : Nat
  wordTokens : Nat
  hapaxes    : Nat
  deriving DecidableEq, Repr

/-- *-ness*: 1024 word types, 15,568 tokens, 350 hapaxes
([odonnell-2015] pp. 267–268). LNRE-shaped: hapax-rich, spectrum
peaked at frequency 1 (Fig 7.4, left). -/
def nessStats : SpectrumStats := ⟨1024, 15568, 350⟩

/-- *-ion*: 1117 word types, 162,573 tokens, 83 hapaxes
([odonnell-2015] pp. 267–268). Not LNRE-shaped: hapax-poor, mass
spread toward higher frequencies (Fig 7.4, right). -/
def ionStats : SpectrumStats := ⟨1117, 162573, 83⟩

/-- *-ness* is hapax-richer than *-ion* (350/1024 vs 83/1117) — the
distributional fingerprint of productivity that Baayen's hapax-based
estimators measure and that the FG model exploits (p. 268). Stated by
cross-multiplication to stay in `Nat`. -/
theorem ness_hapax_richer :
    nessStats.hapaxes * ionStats.wordTypes >
      ionStats.hapaxes * nessStats.wordTypes := by decide

/-- *-ness* has the higher type–token ratio (1024/15,568 vs
1117/162,573): *-ion*'s distribution is dominated by reuse of
high-frequency existing words, not novel coinage. -/
theorem ness_higher_type_token_ratio :
    nessStats.wordTypes * ionStats.wordTokens >
      ionStats.wordTypes * nessStats.wordTokens := by decide

/-- *-ion* has more than an order of magnitude more tokens than
*-ness* — the token-frequency gap that misleads DMPCFG, which "bases
productivity inferences purely on the token frequency of suffixes"
(p. 268). -/
theorem ion_token_frequency_dominates :
    ionStats.wordTokens > 10 * nessStats.wordTokens := by decide

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

/-- Rule V → BND · ate. Reflects [odonnell-2015]'s `-ate:BND>V`
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

/-- Bridge from `Suffix` to the rules of this grammar. -/
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
    derived from `Suffix.productivityIndex` (the qualitative productivity
    ranking). The connection is structural: revising `productivityIndex`
    changes the pseudo-counts here in lockstep. -/
def dmpcfgFromObserved : DMPCFG suffixGrammar where
  pseudo := pseudoVal
  pseudo_pos r _ := by
    unfold pseudoVal
    split_ifs <;> positivity

/-! ## Plumbing: named N-bucket witnesses + parametric pseudoVal lemma -/

/-- `rNess` as an inhabitant of the N-LHS subtype. Named once so
    consumers don't repeat `⟨rNess, by decide⟩` at every call. -/
private def nNess : suffixGrammar.RulesWithLHS SuffixNT.N :=
  ⟨rNess, by decide⟩

/-- `rIon` as an inhabitant of the N-LHS subtype. -/
private def nIon : suffixGrammar.RulesWithLHS SuffixNT.N :=
  ⟨rIon, by decide⟩

/-- The N-LHS bucket of `suffixGrammar` is nonempty (`rNess` ∈ it).
    Required for `mapWeightPMF` and `mapWeight_sum_eq_one_of_lhs`. -/
instance n_bucket_nonempty :
    Nonempty (suffixGrammar.RulesWithLHS SuffixNT.N) :=
  ⟨nNess⟩

/-- All four LHS buckets of `suffixGrammar` are nonempty: every
    nonterminal in this toy grammar has at least one rule expanding
    it (N has rNess + rIon, A has rAdj, V has rAte + rV, BND has rBnd).

    Required to construct `dmpcfgFromObserved.posteriorMAP D`
    as a full `MultinomialPCFG suffixGrammar` (the structure carries
    the typeclass `[∀ a, Nonempty (G.RulesWithLHS a)]` because
    PMFs over empty supports don't exist). -/
instance suffixGrammar_buckets_nonempty :
    ∀ a : suffixGrammar.NT, Nonempty (suffixGrammar.RulesWithLHS a) := by
  intro a
  match a with
  | SuffixNT.N => exact ⟨nNess⟩
  | SuffixNT.A => exact ⟨⟨rAdj, by decide⟩⟩
  | SuffixNT.V => exact ⟨⟨rV, by decide⟩⟩
  | SuffixNT.BND => exact ⟨⟨rBnd, by decide⟩⟩

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

/-- Structural drift sentry: a stronger productivity ranking
    (`moreProductiveThan`) implies a larger DMPCFG pseudo-count for the
    corresponding rule. Propagates `moreProductiveThan` through
    `pseudoVal`, so this breaks if `Suffix.productivityIndex` is revised
    in a way that contradicts the rule-level encoding. -/
theorem dmpcfgFromObserved_pseudo_respects_productivity
    {a b : Suffix} (h : moreProductiveThan a b) :
    dmpcfgFromObserved.pseudo (suffixToRule a) >
        dmpcfgFromObserved.pseudo (suffixToRule b) := by
  show pseudoVal (suffixToRule a) > pseudoVal (suffixToRule b)
  rw [pseudoVal_suffixToRule, pseudoVal_suffixToRule]
  have : (a.productivityIndex : ℝ) > (b.productivityIndex : ℝ) := by
    exact_mod_cast h
  linarith

/-- The central failure mode [odonnell-2015] Ch 7 documents
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
    (h : CFGTree.corpusRuleCount (N := SuffixNT) rNess D + 1 <
         CFGTree.corpusRuleCount (N := SuffixNT) rIon D) :
    dmpcfgFromObserved.mapWeightPMF D nNess <
        dmpcfgFromObserved.mapWeightPMF D nIon := by
  rw [DMPCFG.mapWeightPMF_lt_iff]
  show pseudoVal rNess +
        (CFGTree.corpusRuleCount (N := SuffixNT) rNess D : ℝ) <
      pseudoVal rIon +
        (CFGTree.corpusRuleCount (N := SuffixNT) rIon D : ℝ)
  rw [pseudoVal_rNess, pseudoVal_rIon]
  have h' : (CFGTree.corpusRuleCount (N := SuffixNT) rNess D : ℝ) + 1 <
            (CFGTree.corpusRuleCount (N := SuffixNT) rIon D : ℝ) := by
    exact_mod_cast h
  linarith

/-- Prior PMF (empty corpus): DMPCFG correctly orders the N-rules of
    `suffixGrammar`. With no data, the posterior IS the prior (per
    `mapWeight_zero`), and the prior IS the per-LHS-normalised
    pseudo-counts. Since `pseudoVal rNess > pseudoVal rIon` by
    construction, the PMF mass at `rNess` exceeds that at `rIon`.

    The *first half* of the [odonnell-2015] Ch 7 critique of
    DMPCFG: it does not start wrong. The model's failure mode is
    data-driven, not prior-driven. -/
theorem dmpcfgFromObserved_mapWeightPMF_prior_lt :
    dmpcfgFromObserved.mapWeightPMF 0 nIon <
      dmpcfgFromObserved.mapWeightPMF 0 nNess := by
  rw [DMPCFG.mapWeightPMF_lt_iff]
  show pseudoVal rIon + (CFGTree.corpusRuleCount (N := SuffixNT) rIon 0 : ℝ) <
       pseudoVal rNess + (CFGTree.corpusRuleCount (N := SuffixNT) rNess 0 : ℝ)
  rw [CFGTree.corpusRuleCount_zero, CFGTree.corpusRuleCount_zero,
      pseudoVal_rIon, pseudoVal_rNess]
  norm_num

/-- **Bridge demo.** The same prior comparison stated as a fact about
    `dmpcfgFromObserved.posteriorMAP 0` — a `MultinomialPCFG suffixGrammar`
    derived from the DMPCFG via the conjugate-prior collapse.

    This is the proof-of-life that the `DMPCFG → MultinomialPCFG`
    bridge cashes out: any DMPCFG-side PMF fact translates straight
    to a MultinomialPCFG-side fact about the posterior MAP, via
    `posteriorMAP_rulePMF`. Future cross-paper consumers (Albright-Hayes,
    Bybee, dual-route) can target `MultinomialPCFG` and have their
    theorems automatically apply to DMPCFG-derived posteriors. -/
theorem dmpcfgFromObserved_posteriorMAP_prior_lt :
    (dmpcfgFromObserved.posteriorMAP 0).rulePMF SuffixNT.N nIon <
      (dmpcfgFromObserved.posteriorMAP 0).rulePMF SuffixNT.N nNess :=
  dmpcfgFromObserved_mapWeightPMF_prior_lt

/-- The full [odonnell-2015] Ch 7 critique of DMPCFG, in one
    theorem. Two facts that look contradictory but aren't:

    - Without data (empty corpus), DMPCFG's PMF over the N-rules
      ranks `rNess` above `rIon` — matching the data-layer
      `productivityIndex`.
    - Given a corpus with sufficiently many `rIon` derivations
      (more than `rNess` by more than the pseudo-count gap of 1),
      the PMF flips and ranks `rIon` above `rNess` — contradicting
      the empirical productivity ordering [odonnell-2015]
      reports for English.

    Per Ch 7 (Fig 7.4 p. 267), DMPCFG is built with the right prior
    but bases its posterior on `pseudo + count`, so when CELEX-scale
    token frequencies hit the model the data overwhelms the prior
    and the posterior ranking flips. The fix the book proposes —
    Fragment Grammars — gives a different posterior structure that
    doesn't collapse productivity into raw frequency. -/
theorem dmpcfgFromObserved_mapWeightPMF_prior_and_posterior_disagree
    (D : Multiset (CFGTree Sym SuffixNT))
    (h : CFGTree.corpusRuleCount (N := SuffixNT) rNess D + 1 <
         CFGTree.corpusRuleCount (N := SuffixNT) rIon D) :
    -- Prior: ness > ion at empty corpus
    (dmpcfgFromObserved.mapWeightPMF 0 nIon <
      dmpcfgFromObserved.mapWeightPMF 0 nNess) ∧
    -- Posterior: ion > ness once data dominates
    (dmpcfgFromObserved.mapWeightPMF D nNess <
      dmpcfgFromObserved.mapWeightPMF D nIon) :=
  ⟨dmpcfgFromObserved_mapWeightPMF_prior_lt,
   dmpcfgFromObserved_mapWeightPMF_lt_of_count_gap D h⟩

/-! ### The Probabilistic Elsewhere Condition (§5.5.3)

[odonnell-2015] §5.5.3 (pp. 189–191) derives the Elsewhere Condition —
"also known as Pāṇini's principle, pre-emption, the subset principle,
or the blocking principle" — from probabilistic inference alone: rules
define distributions over the forms they generate, so a rule whose
support properly includes another's "must assign lower probability to
each of those forms, on average" (conservation of belief), and
conditioning preserves the preference. The book quotes
[kiparsky-1973]'s formulation — prefer `r₂` when
`Inputs(r₂) ⊂ Inputs(r₁)` — which is the specificity order of
`Morphology.Exponence.Rule` (applicability-set inclusion).

Formalized in the uniform-generation case, where the preference is
pointwise rather than on average: nested supports give the narrower
rule a strictly higher generation probability at every shared form
(`genProb_lt_of_ssubset`), and a likelihood-maximal rule among a
vocabulary's generators is an Elsewhere winner
(`maxGenProb_isElsewhereWinner`) — no nesting or comparability
assumption needed, because card-minimality forces `⊆`-minimality. -/

section ProbabilisticElsewhere

open Morphology.Exponence

variable {Ctx F : Type*} [DecidableEq Ctx]

/-- Uniform generation probability over a finite support — the uniform
case of [odonnell-2015] §5.5.3's rules-as-distributions. -/
def genProb (s : Finset Ctx) (c : Ctx) : ℚ :=
  if c ∈ s then (s.card : ℚ)⁻¹ else 0

/-- The pointwise probabilistic Elsewhere Condition: at every shared
form, a properly narrower rule assigns strictly higher probability. -/
theorem genProb_lt_of_ssubset {s₁ s₂ : Finset Ctx} (h : s₂ ⊂ s₁)
    {c : Ctx} (hc : c ∈ s₂) : genProb s₁ c < genProb s₂ c := by
  have hc₁ : c ∈ s₁ := h.1 hc
  have h₂ : (0 : ℚ) < s₂.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨c, hc⟩
  have hlt : (s₂.card : ℚ) < s₁.card := by
    exact_mod_cast Finset.card_lt_card h
  simp only [genProb, if_pos hc, if_pos hc₁]
  gcongr

/-- A finitely supported rule: an exponent with a finite set of forms
it can generate. -/
structure FinRule (Ctx F : Type*) where
  /-- The exponent. -/
  exponent : F
  /-- The forms the rule generates. -/
  supp : Finset Ctx

/-- View a finitely supported rule in the shared exponence core:
applicability is support membership. -/
def FinRule.toRule (r : FinRule Ctx F) : Rule Ctx F :=
  ⟨r.exponent, (· ∈ r.supp)⟩

/-- **Elsewhere selection is maximum-likelihood inference**
([odonnell-2015] §5.5.3): a rule maximizing uniform generation
probability at `c` among a vocabulary's generators is an Elsewhere
winner of the corresponding vocabulary. -/
theorem maxGenProb_isElsewhereWinner {v : List (FinRule Ctx F)} {c : Ctx}
    {r : FinRule Ctx F} (hrv : r ∈ v) (hrc : c ∈ r.supp)
    (hmax : ∀ s ∈ v, c ∈ s.supp → genProb s.supp c ≤ genProb r.supp c) :
    IsElsewhereWinner (v.map FinRule.toRule) c r.toRule := by
  refine ⟨⟨List.mem_map_of_mem hrv, hrc⟩, ?_⟩
  rintro t ⟨ht, htc⟩ hle
  obtain ⟨s, hsv, rfl⟩ := List.mem_map.mp ht
  have htc' : c ∈ s.supp := htc
  have hsub : s.supp ⊆ r.supp := fun x hx => Rule.le_iff.mp hle hx
  have hcard : r.supp.card ≤ s.supp.card := by
    have hp := hmax s hsv htc'
    simp only [genProb] at hp
    rw [if_pos htc', if_pos hrc] at hp
    have hs₀ : (0 : ℚ) < s.supp.card := by
      exact_mod_cast Finset.card_pos.mpr ⟨c, htc'⟩
    have hr₀ : (0 : ℚ) < r.supp.card := by
      exact_mod_cast Finset.card_pos.mpr ⟨c, hrc⟩
    exact_mod_cast (inv_le_inv₀ hs₀ hr₀).mp hp
  have heq : s.supp = r.supp := Finset.eq_of_subset_of_card_le hsub hcard
  exact Rule.le_iff.mpr fun x hx => show x ∈ s.supp from heq ▸ hx

end ProbabilisticElsewhere

end ODonnell2015

/-
TODO(theorem) — bridge claims for future study files. Each is
followed by the substrate gap that currently blocks stating it
as a Lean theorem.

- `fg_predicts_ness_in_top_5` — [odonnell-2015] Fig 7.3 central
  claim. Needs a "top-K productivity ranking" primitive over
  `FragmentGrammar` posteriors (substrate has `corpusProbGivenStorage`
  but no MAP-extraction lemma).
- `fg_baayen_correlation` — [odonnell-2015] Table 7.1. Needs a
  Baayen P-measure (hapax/N) substrate; `grep hapax Theories/`
  returns no matches.
- `fg_consistent_with_hay_relative_frequency` — [odonnell-2015]
  §7.3.2 (p. 269). Needs a relative-frequency comparator primitive
  (Hay 2001 / Hay & Baayen 2002).
- `ability_paradox_discriminates_fg_from_mag` — [odonnell-2015]
  Ch 8. "MAG" is `AdaptorGrammar` (already formalised in
  `FragmentGrammars/AdaptorGrammar.lean`); needs a richer toy grammar
  with `-able`/`-ity` rules and a stored `-ability` fragment.
- `cross_study_albright_hayes` — productivity index alignment. Needs
  a `suffixToAHRule` shim into `Studies/AlbrightHayes2003.lean`'s
  `StochasticRule` substrate, then a `pseudo`-vs-`rawConfidence`
  comparison theorem.
-/
