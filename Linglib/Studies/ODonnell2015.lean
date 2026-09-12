import Linglib.Core.Computability.ContextFreeGrammar.Dirichlet
import Linglib.Core.Probability.PitmanYor
import Linglib.Morphology.Exponence.Select
import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno

/-!
# O'Donnell (2015): Productivity and Reuse in Language

This file formalizes the central empirical contrast of the seventh chapter of
[odonnell-2015] on English derivational morphology: the nominalizer *-ness* is productive
while *-ion* and the verb-forming *-ate* are not, and of the competing models only the
fragment grammar recovers this, the Dirichlet-multinomial probabilistic context-free
grammar ranking the token-frequent *-ion* first. The three suffixes carry a productivity
ordering (`Suffix.productivityIndex`, `moreProductiveThan`) grounded in the hapax-based
statistics of Baayen that the book correlates with its models (`ness_hapax_richer`,
`ness_higher_type_token_ratio`, `ion_token_frequency_dominates`), the book's adaptor and
fragment grammars are built over the Dirichlet PCFG of `DirichletPCFG` (`AdaptorGrammar`,
`FragmentGrammar`), the suffixes are rules of a toy grammar (`suffixGrammar`), and a Dirichlet
prior whose pseudo-counts track the empirical productivity is exhibited (`suffixPrior`,
`suffixPrior_pseudo_respects_productivity`).

## Implementation notes

The *-ate* rule produces verbs from bound stems, so the three suffixes are grouped by the
book's contrast rather than by output category; the ordering of *-ion* above *-ate* is a
tie-break between two unproductive suffixes, not part of the book's claim. The
pseudo-counts are stipulated to track productivity, not learned from a corpus, which is the
book's point against the token-frequency model.

## References

* [odonnell-2015]
* [kiparsky-1973]
* [pitman-2006]
-/

namespace ODonnell2015

open ProbabilityTheory

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
the discriminator deployed against the Dirichlet PCFG, MAG, DOP1 and ENDOP in
Fig 7.3, all of which place *-ion* in their top 5). -/
def moreProductiveThan (a b : Suffix) : Prop :=
  a.productivityIndex > b.productivityIndex

instance : DecidableRel moreProductiveThan := λ a b =>
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
*-ness* — the token-frequency gap that misleads the Dirichlet PCFG, which "bases
productivity inferences purely on the token frequency of suffixes"
(p. 268). -/
theorem ion_token_frequency_dominates :
    ionStats.wordTokens > 10 * nessStats.wordTokens := by decide

/-! ## Adaptor and fragment grammars (§3.1.7, §3.1.8)

An adaptor grammar in the book's maximum-a-posteriori variant is a Dirichlet PCFG with a
Pitman–Yor process at each nonterminal memoising the subtrees computed there. The corpus
probability is stated given the latent table assignment `Y`, per nonterminal a set partition of
the uses of that nonterminal by the table they sat at, since marginalising over `Y` is the
inference problem of §3.2. `TableAssignment` uses mathlib's `OrderedFinpartition`, whose
`extendEquiv` is the seating-plan bijection of [pitman-2006]; `pypFactor` depends only on the
block sizes. -/

/-- The book's adaptor grammar over `G`: a Dirichlet PCFG with a Pitman–Yor process memoising
the subtrees rooted at each nonterminal. -/
@[ext]
structure AdaptorGrammar {T : Type} [DecidableEq T] (G : ContextFreeGrammar T)
    [DecidableEq G.NT] extends DirichletPCFG G where
  /-- The Pitman–Yor process memoising expansions of each nonterminal. -/
  pyp : G.NT → PitmanYor

namespace AdaptorGrammar

variable {T : Type} [DecidableEq T] {G : ContextFreeGrammar T} [DecidableEq G.NT]

/-- The latent table assignment `Y`: for each nonterminal, a set partition of its uses in the
corpus by the table they sat at. Consistency with the corpus is the caller's hypothesis. -/
abbrev TableAssignment (G : ContextFreeGrammar T) : Type :=
  G.NT → Σ n, OrderedFinpartition n

variable (M : AdaptorGrammar G)

/-- The Pitman–Yor probability of the table assignment at nonterminal `a`. -/
noncomputable def pypFactor (a : G.NT) (Y : TableAssignment G) : ℝ :=
  (M.pyp a).partitionProb (Y a).snd.toNatPartition

/-- The corpus probability given a table assignment: at each nonterminal the grammar expands,
the Dirichlet PCFG factor times the Pitman–Yor factor. -/
noncomputable def corpusProbGivenTables (D : Multiset (RoseTree (Symbol T G.NT)))
    (Y : TableAssignment G) : ℝ :=
  ∏ a ∈ G.rules.image (·.input), M.toDirichletPCFG.lhsFactor a D * M.pypFactor a Y

theorem corpusProbGivenTables_nonneg (D : Multiset (RoseTree (Symbol T G.NT)))
    (Y : TableAssignment G) : 0 ≤ M.corpusProbGivenTables D Y :=
  Finset.prod_nonneg λ a ha => mul_nonneg (M.toDirichletPCFG.lhsFactor_pos ha D).le
    ((M.pyp a).partitionProb_nonneg _)

/-- The table assignment with no customers at any nonterminal. -/
def emptyTables (G : ContextFreeGrammar T) : TableAssignment G :=
  λ _ => ⟨0, default⟩

@[simp]
theorem pypFactor_emptyTables (a : G.NT) : M.pypFactor a (emptyTables G) = 1 := by
  show (M.pyp a).partitionProb (default : OrderedFinpartition 0).toNatPartition = 1
  rw [Subsingleton.elim (default : OrderedFinpartition 0).toNatPartition default]
  simp [PitmanYor.partitionProb, default, Nat.Partition.indiscrete]

@[simp]
theorem corpusProbGivenTables_empty : M.corpusProbGivenTables 0 (emptyTables G) = 1 :=
  Finset.prod_eq_one λ a ha =>
    have := DirichletPCFG.nonempty_rulesWithLHS_of_mem_image ha
    by simp

/-- The conjugate update of the Dirichlet component by a corpus; the Pitman–Yor
hyperparameters are unchanged. -/
noncomputable def posterior (D : Multiset (RoseTree (Symbol T G.NT))) : AdaptorGrammar G :=
  { M with toDirichletPCFG := M.toDirichletPCFG.posterior D }

@[simp]
theorem posterior_zero : M.posterior 0 = M := by
  ext1 <;> simp [posterior]

theorem posterior_add (D₁ D₂ : Multiset (RoseTree (Symbol T G.NT))) :
    M.posterior (D₁ + D₂) = (M.posterior D₁).posterior D₂ := by
  ext1 <;> simp [posterior, DirichletPCFG.posterior_add]

end AdaptorGrammar

/-! Expanding a rule `r`, a fragment grammar decides at each right-hand-side nonterminal `B`
whether to expand `B` productively or to halt and leave `B` an open slot of the fragment being
stored. The decision is a biased coin whose weight has a beta prior with pseudo-counts
`ψ_{r,B}`; integrating the weight out turns the decisions at that slot into a two-colour Pólya
urn, which is the representation the book computes with. The halt count `Z` is latent like
`Y`; the book writes the halt count at a slot of `r` as `x_r - z_{r,B}`, so a `Z` consistent with
the corpus has `Z r i .recurse + Z r i .halt` equal to the corpus count of `r`. -/

/-- The outcome of the lazy coin at a nonterminal slot: `recurse` expands the slot productively,
`halt` leaves it open in the stored fragment. -/
inductive FragmentGrammar.Decision
  | recurse
  | halt
  deriving DecidableEq, Fintype, Inhabited

/-- A fragment grammar over `G`: an adaptor grammar with, at each nonterminal position of each
rule, a Pólya urn over `recurse`/`halt` decisions whose pseudo-counts are the beta parameters
`ψ_{r,B}`. -/
@[ext]
structure FragmentGrammar {T : Type} [DecidableEq T] (G : ContextFreeGrammar T)
    [DecidableEq G.NT] extends AdaptorGrammar G where
  /-- The urn over `recurse`/`halt` decisions at nonterminal position `i` of rule `r`. -/
  halt : (r : ContextFreeRule T G.NT) → r.NonterminalPos → PolyaUrn FragmentGrammar.Decision

namespace FragmentGrammar

variable {T : Type} [DecidableEq T] {G : ContextFreeGrammar T} [DecidableEq G.NT]

/-- The latent variable `Z`: at each nonterminal position of each rule, the number of
`recurse` and of `halt` decisions taken there across the corpus. -/
abbrev HaltCounts (G : ContextFreeGrammar T) : Type :=
  (r : ContextFreeRule T G.NT) → r.NonterminalPos → Decision → ℕ

variable (M : FragmentGrammar G)

/-- The corpus probability given a table assignment `Y` and halt counts `Z`: the
adaptor-grammar factor times, at each nonterminal slot, the urn likelihood of the decisions
taken there. -/
noncomputable def corpusProbGivenStorage (D : Multiset (RoseTree (Symbol T G.NT)))
    (Y : AdaptorGrammar.TableAssignment G) (Z : HaltCounts G) : ℝ :=
  M.corpusProbGivenTables D Y * ∏ r ∈ G.rules, ∏ i, (M.halt r i).seqProb (Z r i)

theorem corpusProbGivenStorage_nonneg (D : Multiset (RoseTree (Symbol T G.NT)))
    (Y : AdaptorGrammar.TableAssignment G) (Z : HaltCounts G) :
    0 ≤ M.corpusProbGivenStorage D Y Z :=
  mul_nonneg (M.corpusProbGivenTables_nonneg D Y) <| Finset.prod_nonneg λ r _ =>
    Finset.prod_nonneg λ i _ => ((M.halt r i).seqProb_pos _).le

@[simp]
theorem corpusProbGivenStorage_empty :
    M.corpusProbGivenStorage 0 (AdaptorGrammar.emptyTables G) 0 = 1 := by
  simp only [corpusProbGivenStorage, AdaptorGrammar.corpusProbGivenTables_empty, one_mul]
  exact Finset.prod_eq_one λ r _ => Finset.prod_eq_one λ i _ => (M.halt r i).seqProb_zero

/-- The conjugate update by a corpus `D` and its halt counts `Z`: the adaptor-grammar component
absorbs the rule counts of `D`, and the urn at each slot absorbs the decisions taken there. -/
noncomputable def posterior (D : Multiset (RoseTree (Symbol T G.NT))) (Z : HaltCounts G) :
    FragmentGrammar G where
  toAdaptorGrammar := M.toAdaptorGrammar.posterior D
  halt r i := (M.halt r i).posterior (Z r i)

@[simp]
theorem posterior_zero : M.posterior 0 0 = M := by
  ext1 <;> simp [posterior]

theorem posterior_add (D₁ D₂ : Multiset (RoseTree (Symbol T G.NT))) (Z₁ Z₂ : HaltCounts G) :
    M.posterior (D₁ + D₂) (Z₁ + Z₂) = (M.posterior D₁ Z₁).posterior D₂ Z₂ := by
  ext1 <;> simp [posterior, AdaptorGrammar.posterior_add, PolyaUrn.posterior_add]

end FragmentGrammar

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
    `DirichletPCFG`'s typeclass arguments. Not synthesised automatically
    because `suffixGrammar.NT` is a structure projection that the
    typeclass solver does not reduce to `SuffixNT`. -/
instance : DecidableEq suffixGrammar.NT :=
  inferInstanceAs (DecidableEq SuffixNT)

/-! ## The Dirichlet prior over the toy grammar -/

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

/-- The Dirichlet prior over `suffixGrammar` whose pseudo-counts derive from
    `Suffix.productivityIndex`, so revising the ranking changes the prior in
    lockstep. -/
def suffixPrior : DirichletPCFG suffixGrammar where
  pseudo := pseudoVal
  pseudo_pos r _ := by
    unfold pseudoVal
    split_ifs <;> positivity

/-- Parametric pseudo-count formula for productivity-bearing rules:
    `pseudoVal (suffixToRule s) = productivityIndex s + 1`. -/
private lemma pseudoVal_suffixToRule (s : Suffix) :
    pseudoVal (suffixToRule s) = ((s.productivityIndex : ℕ) : ℝ) + 1 := by
  cases s <;> rfl

private lemma pseudoVal_rNess : pseudoVal rNess = 3 := by
  show pseudoVal (suffixToRule .ness) = 3
  rw [pseudoVal_suffixToRule]; norm_num [Suffix.productivityIndex]

private lemma pseudoVal_rIon : pseudoVal rIon = 2 := by
  show pseudoVal (suffixToRule .ion) = 2
  rw [pseudoVal_suffixToRule]; norm_num [Suffix.productivityIndex]

/-! ## Theorems -/

/-- Any Dirichlet PCFG over `suffixGrammar` assigns probability `1`, hence positive
    probability, to the empty corpus. -/
theorem corpusProb_pos_for_empty (M : DirichletPCFG suffixGrammar) : 0 < M.corpusProb 0 := by
  rw [DirichletPCFG.corpusProb_zero]; exact zero_lt_one

/-- A stronger productivity ranking (`moreProductiveThan`) implies a larger pseudo-count for
    the corresponding rule, so a revision of `Suffix.productivityIndex` that contradicts the
    rule-level encoding breaks here. -/
theorem suffixPrior_pseudo_respects_productivity
    {a b : Suffix} (h : moreProductiveThan a b) :
    suffixPrior.pseudo (suffixToRule a) > suffixPrior.pseudo (suffixToRule b) := by
  show pseudoVal (suffixToRule a) > pseudoVal (suffixToRule b)
  rw [pseudoVal_suffixToRule, pseudoVal_suffixToRule]
  have : (a.productivityIndex : ℝ) > (b.productivityIndex : ℝ) := by exact_mod_cast h
  linarith

/-- The failure mode of the Dirichlet PCFG the book documents in Chapter 7 (p. 268, with the
    CELEX evidence of Fig 7.4 on p. 267): its posterior predictive tracks pseudo-count plus
    corpus count, so any corpus in which `rIon` derivations exceed `rNess` derivations by more
    than the pseudo-count gap of `1` ranks `rIon` above `rNess`, against
    `moreProductiveThan ness ion`. The CELEX token gap is an order of magnitude larger than the
    hypothesis requires. -/
theorem suffixPrior_predictive_lt_of_count_gap (D : Multiset (RoseTree (Symbol Sym SuffixNT)))
    (h : RoseTree.corpusRuleCount (N := SuffixNT) rNess D + 1 <
         RoseTree.corpusRuleCount (N := SuffixNT) rIon D) :
    suffixPrior.predictive rNess D < suffixPrior.predictive rIon D := by
  refine (suffixPrior.predictive_lt_iff_of_same_lhs (r := rNess) (r' := rIon) (by decide) rfl).2 ?_
  have h' : (RoseTree.corpusRuleCount (N := SuffixNT) rNess D : ℝ) + 1 <
      RoseTree.corpusRuleCount (N := SuffixNT) rIon D := by exact_mod_cast h
  show pseudoVal rNess + _ < pseudoVal rIon + _
  rw [pseudoVal_rNess, pseudoVal_rIon]
  linarith

/-- With no data the Dirichlet PCFG orders the nominalising rules correctly: the prior
    predictive is the normalised pseudo-count, and `pseudoVal rNess > pseudoVal rIon`. The
    model's failure is data-driven, not prior-driven. -/
theorem suffixPrior_predictive_prior_lt :
    suffixPrior.predictive rIon 0 < suffixPrior.predictive rNess 0 := by
  refine (suffixPrior.predictive_lt_iff_of_same_lhs (r := rIon) (r' := rNess) (by decide) rfl).2 ?_
  show pseudoVal rIon + _ < pseudoVal rNess + _
  rw [pseudoVal_rIon, pseudoVal_rNess, RoseTree.corpusRuleCount_zero,
    RoseTree.corpusRuleCount_zero]
  norm_num

/-- The same prior comparison as a fact about the predictive PCFG, the point estimate the
    Dirichlet prior induces. -/
theorem suffixPrior_predictivePCFG_prior_lt :
    (suffixPrior.predictivePCFG 0).weight rIon < (suffixPrior.predictivePCFG 0).weight rNess := by
  rw [DirichletPCFG.predictivePCFG_weight _ (by decide),
    DirichletPCFG.predictivePCFG_weight _ (by decide),
    ENNReal.ofReal_lt_ofReal_iff (suffixPrior.predictive_pos (by decide) 0)]
  exact suffixPrior_predictive_prior_lt

/-- The Chapter 7 critique of the Dirichlet PCFG in one theorem: right without data, wrong once
    `-ion` tokens dominate. The fix the book proposes, the fragment grammar, gives a posterior
    that does not collapse productivity into raw frequency. -/
theorem suffixPrior_prior_and_posterior_disagree (D : Multiset (RoseTree (Symbol Sym SuffixNT)))
    (h : RoseTree.corpusRuleCount (N := SuffixNT) rNess D + 1 <
         RoseTree.corpusRuleCount (N := SuffixNT) rIon D) :
    suffixPrior.predictive rIon 0 < suffixPrior.predictive rNess 0 ∧
      suffixPrior.predictive rNess D < suffixPrior.predictive rIon D :=
  ⟨suffixPrior_predictive_prior_lt, suffixPrior_predictive_lt_of_count_gap D h⟩

/-! ### The Probabilistic Elsewhere Condition (§5.5.3)

[odonnell-2015] §5.5.3 (pp. 189–191) derives the Elsewhere Condition —
"also known as Pāṇini's principle, pre-emption, the subset principle,
or the blocking principle" — from probabilistic inference alone: rules
define distributions over the forms they generate, so a rule whose
support properly includes another's "must assign lower probability to
each of those forms, on average" (conservation of belief), and
conditioning preserves the preference. The book quotes
[kiparsky-1973]'s formulation — prefer `r₂` when
`Inputs(r₂) ⊂ Inputs(r₁)` — which is `Morphology.Exponence.Rule`'s
specificity order (applicability-set inclusion, `Exponence.toPreorder`).

Formalized in the uniform-generation case, where the preference is
pointwise rather than on average: nested supports give the narrower
rule a strictly higher generation probability at every shared form
(`genProb_lt_of_ssubset`), and a likelihood-maximal rule among a
vocabulary's generators is an Elsewhere winner
(`maxGenProb_isElsewhereWinner`) — no nesting or comparability
assumption needed, because card-minimality forces `⊆`-minimality. Since
higher probability is smaller support (`genProb_le_iff_card_le`), this is
the size principle as a specificity score in the shared core:
`selectByCard_isElsewhereWinner` runs `Exponence.selectBy` on the
dualized support cardinality, discharging the core's conditional
soundness law via `Finset.eq_of_subset_of_card_le`. -/

section ProbabilisticElsewhere

open Morphology Morphology.Exponence

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

/-- Uniform generation probability ranks supports by cardinality at a
shared form: a rule assigns at least as much probability iff its support
is no larger. The monotone bridge from maximum-likelihood selection to
the support-cardinality specificity score — maximizing probability *is*
minimizing support cardinality. -/
theorem genProb_le_iff_card_le {s₁ s₂ : Finset Ctx} {c : Ctx}
    (h₁ : c ∈ s₁) (h₂ : c ∈ s₂) :
    genProb s₁ c ≤ genProb s₂ c ↔ s₂.card ≤ s₁.card := by
  have hs₁ : (0 : ℚ) < s₁.card := by exact_mod_cast Finset.card_pos.mpr ⟨c, h₁⟩
  have hs₂ : (0 : ℚ) < s₂.card := by exact_mod_cast Finset.card_pos.mpr ⟨c, h₂⟩
  simp only [genProb, if_pos h₁, if_pos h₂]
  rw [inv_le_inv₀ hs₁ hs₂]
  exact_mod_cast Iff.rfl

/-- A finitely supported rule: an exponent with a finite set of forms
it can generate. -/
structure FinRule (Ctx F : Type*) where
  /-- The exponent. -/
  exponent : F
  /-- The forms the rule generates. -/
  supp : Finset Ctx

/-- A finitely supported rule exposes the shared exponence core interface
(`Morphology.Exponence.Rule`): applicability is support membership. -/
instance : Exponence.Rule (FinRule Ctx F) Ctx F :=
  ⟨FinRule.exponent, λ r c => c ∈ r.supp⟩

instance : Preorder (FinRule Ctx F) := Exponence.toPreorder

instance : DecidableRel (Exponence.Applies : FinRule Ctx F → Ctx → Prop) :=
  λ r c => inferInstanceAs (Decidable (c ∈ r.supp))

omit [DecidableEq Ctx] in
/-- Dualized support cardinality is strictly antitone in specificity: a
strictly broader finitely supported rule has strictly larger support
(card `≤` does not imply support `⊆`, so the score is not an order
embedding — strict antitonicity is exactly what the `Finset`-support
engine retains). -/
private theorem finRule_card_strictAnti :
    StrictAnti (λ r : FinRule Ctx F => OrderDual.toDual r.supp.card) := by
  intro s r hlt
  have hsub : s.supp ⊆ r.supp := λ x hx => hlt.le hx
  have hns : ¬ r.supp ⊆ s.supp := λ hsub' => not_le_of_gt hlt λ x hx => hsub' hx
  exact OrderDual.toDual_lt_toDual.mpr
    (Finset.card_lt_card (lt_of_le_not_ge hsub hns))

/-- **The size principle as a specificity score** ([odonnell-2015]
§5.5.3): selecting the finitely supported rule of least support
cardinality — dualized so smaller supports win the `argmax` — through
the shared core's `Exponence.selectBy` yields an Elsewhere winner.
Minimizing support cardinality *is* maximizing uniform generation
probability (`genProb_le_iff_card_le`), so this is Elsewhere selection as
maximum-likelihood inference, on record as a score. -/
theorem selectByCard_isElsewhereWinner {v : List (FinRule Ctx F)} {c : Ctx}
    {r : FinRule Ctx F}
    (h : selectBy (λ s => OrderDual.toDual s.supp.card) v c = some r) :
    IsElsewhereWinner v c r :=
  selectBy_isElsewhereWinner (finRule_card_strictAnti.strictAntiOn _) h

/-- **Elsewhere selection is maximum-likelihood inference**
([odonnell-2015] §5.5.3): a rule maximizing uniform generation
probability at `c` among a vocabulary's generators is an Elsewhere
winner of the corresponding vocabulary. Maximizing probability is
minimizing support cardinality (`genProb_le_iff_card_le`), whence
card-minimality forces `⊆`-minimality — the same reasoning
`selectByCard_isElsewhereWinner` routes through the core's score. -/
theorem maxGenProb_isElsewhereWinner {v : List (FinRule Ctx F)} {c : Ctx}
    {r : FinRule Ctx F} (hrv : r ∈ v) (hrc : c ∈ r.supp)
    (hmax : ∀ s ∈ v, c ∈ s.supp → genProb s.supp c ≤ genProb r.supp c) :
    IsElsewhereWinner v c r := by
  refine ⟨⟨hrv, hrc⟩, ?_⟩
  rintro s ⟨hsv, htc⟩ hle
  have htc' : c ∈ s.supp := htc
  have hsub : s.supp ⊆ r.supp := λ x hx => hle hx
  have hcard : r.supp.card ≤ s.supp.card :=
    (genProb_le_iff_card_le htc' hrc).mp (hmax s hsv htc')
  have heq : s.supp = r.supp := Finset.eq_of_subset_of_card_le hsub hcard
  exact λ x hx => show x ∈ s.supp from heq ▸ hx

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
  Ch 8. "MAG" is `AdaptorGrammar` above; needs a richer toy grammar
  with `-able`/`-ity` rules and a stored `-ability` fragment.
- `cross_study_albright_hayes` — productivity index alignment. Needs
  a `suffixToAHRule` shim into `Studies/AlbrightHayes2003.lean`'s
  `StochasticRule` substrate, then a `pseudo`-vs-`rawConfidence`
  comparison theorem.
-/
