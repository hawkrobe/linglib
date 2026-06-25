import Linglib.Morphology.DM.Impoverishment
import Linglib.Morphology.DM.VocabularyInsertion
import Linglib.Fragments.Taos.Agreement
import Linglib.Fragments.Basque.Postsyntax

/-!
# Middleton (2026) — Ordering of Impoverishment Rules in Taos and Basque
[middleton-2026] [arregi-nevins-2012] [halle-marantz-1993]
[harbour-2014] [harbour-2016] [kontak-kunkel-1987]
[watkins-1984] [harbour-middleton-2026]

This file formalises the architectural argument of [middleton-2026].
Working within Distributed Morphology ([halle-marantz-1993]),
[arregi-nevins-2012] propose a strict modular postsyntax in
which paradigmatic Impoverishment applies *as a block* before
syntagmatic Impoverishment, and Metathesis follows all
Impoverishment. Middleton shows from Taos verbal agreement that the
second claim survives but the first does not (§§4.2.1–§4.2.5);
the Basque half of the paper (§3.1) re-establishes the second
claim — metathesis after impoverishment — using a different
language and different rule shapes (whole-terminal deletion +
adjacent-terminal swap).

## Scope

The full Taos paradigm involves dozens of Vocabulary Insertion rules
and a large family of impoverishment / metathesis rules. We do not
re-derive the entire paradigm. What lives here:

* This file gives one **schematic** pair of rules
  `paraAtomicRule` / `synMinimalRule` that exhibits the divergence
  predicted by the paper at a real-shaped Taos witness neighborhood.
  The conditioning features (`[+author]`, `[+atomic]`, `[+minimal]`)
  are drawn from the Harbour decomposition the paper uses, but the
  rules themselves are not literal transcriptions of paper rules —
  they are minimal witnesses to the para-vs-syn ordering interaction
  in [middleton-2026] §4.2.1–§4.2.4.
* The general claim — that `runStrict` is strictly less expressive
  than `runInterleaved` whenever a syntagmatic rule needs to feed a
  paradigmatic one — is `runStrict_forces_paraSyn_order` /
  `runInterleaved_admits_synPara`; instantiated on the witness below.
* A small VI set demonstrates how the postsyntactic output feeds
  Vocabulary Insertion (Subset Principle, [halle-marantz-1993]),
  again schematically.
* The Basque half of the paper requires *whole terminal* deletion
  (Participant Dissimilation, rule 16) and *adjacent terminal* swap
  (Ergative Metathesis, rule 13) — operations the focus-level Taos
  sections cannot express. The framework lift — `MorphPhrase`,
  `TermImpovRule`, `TermMetaRule` with their applicators — is
  inlined at the end of the file; the bundles live in
  `Fragments/Basque/Postsyntax.lean`; the rules and the Ondarru
  `s-endu-n` (17a) divergence witness are stated here.

What is **not** modeled:

* The full Taos paradigm and the literal rule statements of
  [middleton-2026] (rule numbers and conditioning environments
  vary across the four §4.2 cases).
* Harbour's Reciprocal Containment constraints on feature bundles.
* Real Taos VI competition — only enough VIs to demonstrate the
  pipeline.
-/

namespace Middleton2026

open Minimalist Morphology.DM.Impoverishment Morphology.DM.VI
     Taos.Agreement Basque.Postsyntax

/-! ### Metathesis Rule

`MetathesisRule` parallels `ImpoverishmentRule`: keyed on a `Neighborhood`,
carries a decidable condition. The structural change is to swap two
distinguished feature *types* in the focus bundle — the rule names a pair
of feature types and exchanges the positions of the first occurrences of
each. The directionality matches [arregi-nevins-2012]'s
`[[X] ⟩ ⟨ [Y]] / Z` notation: "swap X and Y in environment Z."
-/

structure MetathesisRule where
  condition : Neighborhood → Prop
  decCond : DecidablePred condition
  swapFst : FeatureVal
  swapSnd : FeatureVal

instance (rule : MetathesisRule) (n : Neighborhood) :
    Decidable (rule.condition n) := rule.decCond n

/-- Build a metathesis rule from a Boolean condition over the focus
    bundle (paradigmatic-style — the most common case in the Taos rules
    of [middleton-2026], where the condition refers only to the
    feature inventory of the same node being reordered). -/
def focusRule (focusCheck : FeatureBundle → Bool)
    (swapFst swapSnd : FeatureVal) : MetathesisRule where
  condition n := focusCheck n.focus = true
  decCond n := inferInstanceAs (Decidable (focusCheck n.focus = true))
  swapFst := swapFst
  swapSnd := swapSnd

/-- Index of the first feature in `l` whose type matches `fv`. -/
def indexOfType (l : List GramFeature) (fv : FeatureVal) : Option Nat :=
  l.findIdx? (λ f => f.featureType.sameType fv)

/-- Swap the elements at positions `i` and `j` in a list. Out-of-bounds
    indices leave the list unchanged. -/
def swapAt {α : Type _} (l : List α) (i j : Nat) : List α :=
  match l[i]?, l[j]? with
  | some xi, some xj => (l.set i xj).set j xi
  | _, _ => l

/-- Reorder the focus exponents by swapping the first occurrences of
    `swapFst` and `swapSnd` (their *linear positions* in the terminal's
    exponent string). Metathesis is inherently an operation on linear
    order, so it acts on the ordered `toGramFeatures` view. -/
def swapInBundle (fb : FeatureBundle) (swapFst swapSnd : FeatureVal) :
    List GramFeature :=
  let l := FeatureBundle.toGramFeatures fb
  match indexOfType l swapFst, indexOfType l swapSnd with
  | some i, some j => swapAt l i j
  | _, _ => l

/-- Apply a metathesis rule at a neighborhood, returning the resulting
    *bundle*. When the condition holds, swap the positions of `swapFst`
    and `swapSnd` in the focus exponent string.

    NB: the canonical `FeatureBundle` is a total assignment keyed by feature
    *dimension*, hence order-insensitive; folding the swapped exponent list
    back via `ofGramFeatures` therefore launders the reordering away. The
    bundle-level result is thus a no-op whenever the swapped types differ,
    which is correct for the *pipeline* below (`runStrict`/`runInterleaved`
    only ever carry an empty metathesis chain). The empirically contentful,
    order-sensitive focus-level metathesis of [middleton-2026] is stated on
    the exponent-string view directly (`derivIM`/`derivMI`). -/
def applyMetathesis (rule : MetathesisRule) (n : Neighborhood) :
    FeatureBundle :=
  if rule.condition n then
    FeatureBundle.ofGramFeatures (swapInBundle n.focus rule.swapFst rule.swapSnd)
  else n.focus

/-- Apply a sequence of metathesis rules left-to-right. Each rule sees
    the focus as updated by prior rules; surrounding context is held
    fixed (one cycle of metathesis). Specializes `runChain`. -/
def applyMetathesisChain (rules : List MetathesisRule) (n : Neighborhood) :
    FeatureBundle :=
  runChain applyMetathesis rules n

/-- `applyMetathesisChain` distributes over list concatenation. -/
theorem applyMetathesisChain_append (rs₁ rs₂ : List MetathesisRule)
    (n : Neighborhood) :
    applyMetathesisChain (rs₁ ++ rs₂) n =
      applyMetathesisChain rs₂
        { n with focus := applyMetathesisChain rs₁ n } :=
  runChain_append _ _ _ _

/-- Convenience: apply a rule to a bare focus bundle with no context. -/
def MetathesisRule.applyToBundle (rule : MetathesisRule)
    (fb : FeatureBundle) : FeatureBundle :=
  applyMetathesis rule (Neighborhood.ofBundle fb)

/-! ### Strict vs Interleaved Postsyntactic Pipelines

Two architectures for the postsyntactic component:

* **`runStrict` ([arregi-nevins-2012], Fig. 1).** Postsyntax is a
  strict modular pipeline: paradigmatic Impoverishment → syntagmatic
  Impoverishment → Metathesis → VI. Within Feature Markedness,
  paradigmatic rules apply *as a block* before any syntagmatic rule.

* **`runInterleaved` ([middleton-2026]).** Impoverishment rules
  apply in whatever order the analysis demands — paradigmatic and
  syntagmatic may interleave. Metathesis still follows all
  impoverishment (this ordering is preserved).

The two pipelines coincide on inputs whose impoverishment list is in
para-then-syn order (`runStrict_eq_interleaved_paraSyn`). They diverge
when a syntagmatic rule must precede a paradigmatic one
([middleton-2026] §4.2.1–§4.2.4) *or* when a paradigmatic rule
must precede a syntagmatic one and one cannot guarantee the strict
block ordering ([middleton-2026] §4.2.5).
-/

/-- The Arregi & Nevins postsyntax (their Fig. 1, simplified to the two
    contested layers): paradigmatic Impoverishment, then syntagmatic
    Impoverishment, then Metathesis. Exponence Conversion and
    Morphological Concord are abstracted away — their internal ordering
    is not at issue in [middleton-2026]. -/
structure ModularPostsyntax where
  paradigmatic : List ImpoverishmentRule
  syntagmatic  : List ImpoverishmentRule
  metathesis   : List MetathesisRule

/-- A&N's strict pipeline: para-block, then syn-block, then metathesis. -/
def runStrict (M : ModularPostsyntax) (n : Neighborhood) : FeatureBundle :=
  let afterPara := applyImpoverishmentChain M.paradigmatic n
  let afterSyn  := applyImpoverishmentChain M.syntagmatic { n with focus := afterPara }
  applyMetathesisChain M.metathesis { n with focus := afterSyn }

/-- Middleton's interleaved postsyntax: a single impoverishment list
    (whose entries may be paradigmatic or syntagmatic in any order),
    then metathesis. -/
structure InterleavedPostsyntax where
  impoverishment : List ImpoverishmentRule
  metathesis     : List MetathesisRule

def runInterleaved (M : InterleavedPostsyntax) (n : Neighborhood) :
    FeatureBundle :=
  let afterImp := applyImpoverishmentChain M.impoverishment n
  applyMetathesisChain M.metathesis { n with focus := afterImp }

/-- Promote a strict pipeline to an interleaved one in para-then-syn
    order. The two then compute the same output. -/
def ModularPostsyntax.toInterleaved (M : ModularPostsyntax) :
    InterleavedPostsyntax where
  impoverishment := M.paradigmatic ++ M.syntagmatic
  metathesis     := M.metathesis

/-- The strict pipeline is exactly the interleaved pipeline run on the
    paradigmatic-then-syntagmatic concatenation. Hence `runStrict` is
    strictly *less expressive* than `runInterleaved`: anything strict
    can derive, interleaved can derive too (with the same rules). -/
theorem runStrict_eq_interleaved_paraSyn
    (M : ModularPostsyntax) (n : Neighborhood) :
    runStrict M n = runInterleaved M.toInterleaved n := by
  simp only [runStrict, runInterleaved, ModularPostsyntax.toInterleaved,
             applyImpoverishmentChain_append]

/-- A two-rule strict pipeline (one paradigmatic, one syntagmatic, no
    metathesis) reduces to applying `[p, s]` in order. -/
@[simp] theorem runStrict_singleton (p s : ImpoverishmentRule)
    (n : Neighborhood) :
    runStrict ⟨[p], [s], []⟩ n = applyImpoverishmentChain [p, s] n := by
  simp only [runStrict, applyImpoverishmentChain, runChain,
             applyMetathesisChain, List.foldl_nil, List.foldl_cons]

/-- An interleaved pipeline with no metathesis reduces to the
    impoverishment chain. -/
@[simp] theorem runInterleaved_no_metathesis (rs : List ImpoverishmentRule)
    (n : Neighborhood) :
    runInterleaved ⟨rs, []⟩ n = applyImpoverishmentChain rs n := by
  simp only [runInterleaved, applyMetathesisChain, runChain, List.foldl_nil]

/-- **The structural inadequacy of `runStrict`.** Whenever a paradigmatic
    rule `p` and a syntagmatic rule `s` produce different outputs depending
    on whether they fire in `[s, p]` or `[p, s]` order at some neighborhood
    `n`, the strict pipeline ⟨[p], [s], []⟩ is *forced* to yield the
    `[p, s]` answer — the `[s, p]` derivation is unreachable.

    This is the formal counterpart of [middleton-2026]'s argument
    that A&N's modular ordering cannot derive Taos: the four cases in
    §4.2.1–§4.2.4 require precisely the syn-before-para derivation that
    `runStrict` excludes by construction. -/
theorem runStrict_forces_paraSyn_order
    (p s : ImpoverishmentRule) (n : Neighborhood) :
    runStrict ⟨[p], [s], []⟩ n = applyImpoverishmentChain [p, s] n :=
  runStrict_singleton p s n

/-- The interleaved pipeline can deliver the syn-first derivation that
    `runStrict` cannot. -/
theorem runInterleaved_admits_synPara
    (p s : ImpoverishmentRule) (n : Neighborhood) :
    runInterleaved ⟨[s, p], []⟩ n = applyImpoverishmentChain [s, p] n :=
  runInterleaved_no_metathesis _ _

/-- **Inadequacy theorem.** If `[p, s]` and `[s, p]` give different focuses
    at `n`, then the strict pipeline ⟨[p], [s], []⟩ cannot match the
    interleaved pipeline ⟨[s, p], []⟩ at `n`. -/
theorem runStrict_neq_runInterleaved_of_diverges
    (p s : ImpoverishmentRule) (n : Neighborhood)
    (h : applyImpoverishmentChain [p, s] n ≠ applyImpoverishmentChain [s, p] n) :
    runStrict ⟨[p], [s], []⟩ n ≠ runInterleaved ⟨[s, p], []⟩ n := by
  rw [runStrict_singleton, runInterleaved_no_metathesis]
  exact h

/-- A two-step pipeline that runs impoverishment then metathesis at a
    neighborhood (the order both A&N and Middleton endorse). -/
def runImpovThenMeta (rs : List ImpoverishmentRule) (ms : List MetathesisRule)
    (n : Neighborhood) : FeatureBundle :=
  applyMetathesisChain ms { n with focus := applyImpoverishmentChain rs n }

/-- The reversed two-step pipeline: metathesis first, then impoverishment
    (the order both A&N and Middleton reject — supported by Basque in §3.1
    and by Taos in §3.2 of [middleton-2026]). -/
def runMetaThenImpov (rs : List ImpoverishmentRule) (ms : List MetathesisRule)
    (n : Neighborhood) : FeatureBundle :=
  applyImpoverishmentChain rs { n with focus := applyMetathesisChain ms n }

/-- **Metathesis-after-impoverishment is non-trivial.** If a single
    impoverishment rule `r` and a single metathesis rule `m` produce
    different focuses depending on order at `n`, then `runImpovThenMeta`
    and `runMetaThenImpov` differ — i.e., the architectural choice has
    empirical content. -/
theorem runImpov_neq_runMeta_of_diverges
    (r : ImpoverishmentRule) (m : MetathesisRule) (n : Neighborhood)
    (h : applyMetathesisChain [m] { n with focus := applyImpoverishment r n } ≠
         applyImpoverishment r { n with focus := applyMetathesis m n }) :
    runImpovThenMeta [r] [m] n ≠ runMetaThenImpov [r] [m] n := by
  intro heq
  apply h
  simp only [runImpovThenMeta, runMetaThenImpov, applyImpoverishmentChain,
             runChain, List.foldl_cons, List.foldl_nil] at heq
  exact heq

/-! ### Two Schematic Rules in Distinct Phases -/

/-- A **paradigmatic** rule: deletes `[+atomic]` whenever the focus
    contains both `[+author]` and `[+minimal]`. The condition refers
    only to the focus, so the rule is paradigmatic by construction
    (`paradigmatic_isParadigmatic`).

    This is a minimal stand-in for the paradigmatic rules involved in
    [middleton-2026] §4.2.1–§4.2.4 — it is not a transcription of
    any specific paper rule. -/
def paraAtomicRule : ImpoverishmentRule :=
  paradigmatic
    (λ fb =>
      (FeatureBundle.toGramFeatures fb).any (λ f => f.featureType.sameType (fAuthor true)) &&
      (FeatureBundle.toGramFeatures fb).any (λ f => f.featureType.sameType (fMinimal true)))
    (fAtomic true)

theorem paraAtomicRule_isParadigmatic : Paradigmatic paraAtomicRule :=
  paradigmatic_isParadigmatic _ _

/-- A **syntagmatic** rule: deletes `[+minimal]` when the focus
    contains `[+atomic]` *and* there is at least one bundle of
    object-context to the right (the schematic `[O 3i]` condition,
    weakened to bare presence — sufficient for the bleeding/feeding
    interaction the paper diagnoses). The dependence on `rightCtx`
    is what makes the rule syntagmatic, and `synMinimalRule_isSyntagmatic`
    proves it. -/
def synMinimalRule : ImpoverishmentRule where
  condition n :=
    ((FeatureBundle.toGramFeatures n.focus).any (λ f => f.featureType.sameType (fAtomic true)) = true)
    ∧ (n.rightCtx.length > 0)
  decCond _ := inferInstance
  target := fMinimal true

/-- The two rules are genuinely in distinct phases: `synMinimalRule`
    actually depends on its right-context (it is *not* paradigmatic).
    Witness: two neighborhoods that share a focus but differ on
    `rightCtx`. -/
theorem synMinimalRule_isSyntagmatic : Syntagmatic synMinimalRule := by
  intro hPara
  let fb : FeatureBundle :=
    .ofGramFeatures [.valued (fAtomic true), .valued (fMinimal true)]
  let n₁ : Neighborhood :=
    { focus := fb, leftCtx := [], rightCtx := [argBundle person3 numSg] }
  let n₂ : Neighborhood := { focus := fb, leftCtx := [], rightCtx := [] }
  have hfoc : n₁.focus = n₂.focus := rfl
  have h := hPara n₁ n₂ hfoc
  have h₁ : synMinimalRule.condition n₁ := by decide
  have h₂ : ¬ synMinimalRule.condition n₂ := by decide
  exact h₂ (h.mp h₁)

/-! ### A Real-Shaped Taos Witness -/

/-- Witness focus: a 1s-style bundle `[+author, +atomic, +minimal]`
    (suppressing `[+participant]`, which is irrelevant to either rule). -/
def witnessFocus : FeatureBundle :=
  .ofGramFeatures
    [.valued (fAuthor true),
     .valued (fAtomic true),
     .valued (fMinimal true)]

/-- Witness neighborhood: the 1s-style focus, with a real 3s
    bundle to the right standing in for the Taos object slot
    that conditions `synMinimalRule`. -/
def witness : Neighborhood :=
  { focus := witnessFocus,
    leftCtx := [],
    rightCtx := [argBundle person3 numSg] }

/-- Run para-then-syn (the order A&N's strict pipeline forces). -/
def stripParaSyn : FeatureBundle :=
  applyImpoverishmentChain [paraAtomicRule, synMinimalRule] witness

/-- Run syn-then-para (the order Middleton's interleaved pipeline can
    choose). -/
def stripSynPara : FeatureBundle :=
  applyImpoverishmentChain [synMinimalRule, paraAtomicRule] witness

/-! ### The Two Orderings Yield Different Outputs -/

/-- Para-then-syn (= A&N): `paraAtomicRule` deletes `[+atomic]` first;
    `synMinimalRule` then can't fire (no `[+atomic]` left in focus).
    The `[+minimal]` survives. -/
theorem stripParaSyn_eq :
    stripParaSyn =
      .ofGramFeatures [.valued (fAuthor true), .valued (fMinimal true)] := by
  decide

/-- Syn-then-para (= Middleton): `synMinimalRule` fires first (focus
    has `[+atomic]`, rightCtx non-empty), deleting `[+minimal]`;
    `paraAtomicRule` then can't fire (no `[+minimal]` left in focus).
    The `[+atomic]` survives instead. -/
theorem stripSynPara_eq :
    stripSynPara =
      .ofGramFeatures [.valued (fAuthor true), .valued (fAtomic true)] := by
  decide

/-- The two orders produce different feature bundles at this
    neighborhood. -/
theorem orderings_diverge : stripParaSyn ≠ stripSynPara := by
  rw [stripParaSyn_eq, stripSynPara_eq]
  decide

/-! ### A&N's Strict Pipeline Cannot Reach the Syn-First Output -/

/-- The schematic A&N postsyntax that contains exactly `paraAtomicRule`
    in the paradigmatic phase and `synMinimalRule` in the syntagmatic
    phase, with no metathesis. -/
def arregiNevinsPostsyntax : ModularPostsyntax :=
  { paradigmatic := [paraAtomicRule]
    syntagmatic  := [synMinimalRule]
    metathesis   := [] }

/-- The schematic Middleton interleaved postsyntax, with the
    syntagmatic rule scheduled first — the order required by the
    §4.2.1–§4.2.4 Taos cases. -/
def middletonPostsyntax : InterleavedPostsyntax :=
  { impoverishment := [synMinimalRule, paraAtomicRule]
    metathesis     := [] }

/-- A&N's pipeline computes the para-first answer at the witness. -/
theorem arregiNevins_witness :
    runStrict arregiNevinsPostsyntax witness =
      .ofGramFeatures [.valued (fAuthor true), .valued (fMinimal true)] := by
  show runStrict { paradigmatic := [paraAtomicRule]
                   syntagmatic := [synMinimalRule]
                   metathesis := [] } witness = _
  rw [runStrict_forces_paraSyn_order paraAtomicRule synMinimalRule witness]
  exact stripParaSyn_eq

/-- Middleton's pipeline computes the (different) syn-first answer. -/
theorem middleton_witness :
    runInterleaved middletonPostsyntax witness =
      .ofGramFeatures [.valued (fAuthor true), .valued (fAtomic true)] := by
  show runInterleaved { impoverishment := [synMinimalRule, paraAtomicRule]
                        metathesis := [] } witness = _
  rw [runInterleaved_admits_synPara paraAtomicRule synMinimalRule witness]
  exact stripSynPara_eq

/-- **Architectural inadequacy of `runStrict` for Taos.** At the
    witness neighborhood, the strict A&N pipeline and Middleton's
    interleaved one return different feature bundles. Hence no
    `ModularPostsyntax` built from `paraAtomicRule` (paradigmatic) and
    `synMinimalRule` (syntagmatic) — and no extension that adds
    further rules to the same phases — can yield the syn-first output
    that Taos requires in [middleton-2026] §4.2.1–§4.2.4. -/
theorem arregiNevins_neq_middleton_at_witness :
    runStrict arregiNevinsPostsyntax witness ≠
      runInterleaved middletonPostsyntax witness := by
  rw [arregiNevins_witness, middleton_witness]
  decide

/-! ### Metathesis Still Follows Impoverishment (the Uphold) -/

/-- A metathesis rule that swaps `[+author]` with `[+atomic]` when the
    focus contains all three of `[+author]`, `[+atomic]`, `[+minimal]`.
    Schematic of [middleton-2026]'s metathesis rules: a metathesis
    triggered in the presence of a particular number feature. The
    dependence on `[+minimal]` is what couples this rule to
    `synMinimalRule` (which deletes `[+minimal]`), so that the IM/MI
    orders diverge — the empirically motivated witness of "metathesis
    after impoverishment, not before." -/
def authorAtomicMetathesis : MetathesisRule :=
  focusRule
    (λ fb =>
      (FeatureBundle.toGramFeatures fb).any (λ f => f.featureType.sameType (fAuthor true)) &&
      (FeatureBundle.toGramFeatures fb).any (λ f => f.featureType.sameType (fAtomic true)) &&
      (FeatureBundle.toGramFeatures fb).any (λ f => f.featureType.sameType (fMinimal true)))
    (fAuthor true)
    (fAtomic true)

/-! Metathesis reorders the *exponent string* of a terminal; the canonical
`FeatureBundle` (a dimension-keyed total assignment) is order-insensitive
and cannot witness that reordering. The order-sensitive content of
[middleton-2026]'s "metathesis must follow impoverishment" claim is
therefore stated on the ordered exponent view `List GramFeature`. (The
whole-terminal Basque half below, where order lives at the *phrase* level
in `List FeatureBundle`, is unaffected and witnesses the same claim with a
different rule shape.) -/

/-- Apply a metathesis rule to an ordered exponent string: when the rule's
    condition holds at the corresponding bundle, swap the first occurrences
    of `swapFst` and `swapSnd` in the list; otherwise leave it unchanged. -/
def applyMetathesisExp (rule : MetathesisRule) (l : List GramFeature) :
    List GramFeature :=
  if rule.condition (Neighborhood.ofBundle (.ofGramFeatures l)) then
    match indexOfType l rule.swapFst, indexOfType l rule.swapSnd with
    | some i, some j => swapAt l i j
    | _, _ => l
  else l

/-- Apply an impoverishment rule to an ordered exponent string in the
    witness context: when the rule fires, drop every exponent of the
    target's dimension, preserving the order of the survivors. -/
def applyImpovExp (rule : ImpoverishmentRule) (l : List GramFeature) :
    List GramFeature :=
  if rule.condition { witness with focus := .ofGramFeatures l } then
    l.filter (λ f => ! f.featureType.sameType rule.target)
  else l

/-- Witness exponent string: `[+author, +atomic, +minimal]`, the ordered
    view of `witnessFocus`. -/
def witnessExp : List GramFeature :=
  FeatureBundle.toGramFeatures witnessFocus

/-- Impoverishment-then-metathesis (Middleton's and A&N's shared
    order), on the exponent string. -/
def derivIM : List GramFeature :=
  applyMetathesisExp authorAtomicMetathesis (applyImpovExp synMinimalRule witnessExp)

/-- Metathesis-then-impoverishment (the order both authors reject), on the
    exponent string. -/
def derivMI : List GramFeature :=
  applyImpovExp synMinimalRule (applyMetathesisExp authorAtomicMetathesis witnessExp)

/-- The two orders of impoverishment vs. metathesis genuinely diverge
    at the witness, witnessing the architectural fact that metathesis
    must follow impoverishment. In `derivIM`, `synMinimalRule` first
    deletes `[+minimal]`, bleeding the metathesis condition, so the
    exponents stay in `[+author, +atomic]` order; in `derivMI`,
    metathesis fires first and swaps them to `[+atomic, +author]` before
    `[+minimal]` is deleted. -/
theorem impov_before_meta_diverges_from_meta_before_impov :
    derivIM ≠ derivMI := by
  decide

/-! ### Postsyntax Feeds Vocabulary Insertion -/

/-- The post-postsyntactic focus bundle from A&N's strict pipeline at
    the witness — extracted as a top-level def so it is the input to
    Vocabulary Insertion below. -/
def arregiNevinsOutput : FeatureBundle :=
  runStrict arregiNevinsPostsyntax witness

/-- The post-postsyntactic focus bundle from Middleton's interleaved
    pipeline at the witness. -/
def middletonOutput : FeatureBundle :=
  runInterleaved middletonPostsyntax witness

/-- A small schematic Vocabulary Item set keyed on `FeatureVal`. The
    Subset Principle ([halle-marantz-1993]) selects the longest
    matching entry. We use `Morpheme.surface` for the exponents to
    keep the connection to the Taos morpheme inventory in the
    Fragment. -/
def viSet : List (FeatureVI FeatureVal String) :=
  [ -- specific: 1st-person + minimal (surfaces with `n` per [middleton-2026] rule 21)
    ⟨[fAuthor true, fMinimal true], Morpheme.n.surface⟩
  , -- specific: 1st-person + atomic
    ⟨[fAuthor true, fAtomic true], Morpheme.o.surface⟩
  , -- elsewhere: empty feature spec, matches anything
    ⟨[], Morpheme.ô.surface⟩ ]

/-- A&N's output feeds VI as `[+author, +minimal]`; the Subset
    Principle selects the `[+author, +minimal]` entry over the
    elsewhere `ô`. Surface form: `n`. -/
theorem arregiNevinsOutput_inserts_n :
    subsetPrinciple viSet
        ((FeatureBundle.toGramFeatures arregiNevinsOutput).map GramFeature.featureType) =
      some Morpheme.n.surface := by
  decide

/-- Middleton's output feeds VI as `[+author, +atomic]`; the Subset
    Principle selects the `[+author, +atomic]` entry. Surface form:
    `o`. The two architectures predict *different surface forms* at
    the same input — the empirical bite of the architectural
    divergence. -/
theorem middletonOutput_inserts_o :
    subsetPrinciple viSet
        ((FeatureBundle.toGramFeatures middletonOutput).map GramFeature.featureType) =
      some Morpheme.o.surface := by
  decide

/-- The architectural divergence shows up at the level of surface
    exponents, not just feature bundles: the same input neighborhood
    yields different morphemes under the two pipelines. -/
theorem arregiNevins_vs_middleton_surface :
    subsetPrinciple viSet
        ((FeatureBundle.toGramFeatures arregiNevinsOutput).map GramFeature.featureType) ≠
      subsetPrinciple viSet
        ((FeatureBundle.toGramFeatures middletonOutput).map GramFeature.featureType) := by
  rw [arregiNevinsOutput_inserts_n, middletonOutput_inserts_o]
  decide

/-! ### Basque — Whole-Terminal Postsyntax (Middleton §3.1)

The Basque half of the paper operates on whole terminals, not features
within a terminal. We lift the focus-level `Neighborhood`-based machinery
of `Impoverishment.lean` / `Metathesis.lean` to phrase-level scans, then
state Participant Dissimilation, Ergative Metathesis, and the Ondarru
divergence witness.

Embick & Noyer 2001 call rules of `TermMetaRule`'s shape "Local
Dislocation". `TermMetaRule` is the `FeatureBundle`-typed
instantiation with the applicator. -/

/-- A Basque morphological phrase: a linear sequence of terminal
    `FeatureBundle`s, head-leftmost in linear (post-linearisation)
    order. -/
abbrev MorphPhrase := List FeatureBundle

/-- A **terminal-level Impoverishment** rule: deletes a whole terminal
    when its `Neighborhood` (focus = the candidate terminal,
    `leftCtx`/`rightCtx` = its phrase-mates) satisfies `condition`.
    Parallel to the focus-level `ImpoverishmentRule` whose target is a
    feature within one terminal; here the target is the terminal
    itself. Motivating case: Basque Participant Dissimilation,
    [middleton-2026] (16). -/
structure TermImpovRule where
  condition : Neighborhood → Prop
  decCond : DecidablePred condition

instance (rule : TermImpovRule) (n : Neighborhood) :
    Decidable (rule.condition n) := rule.decCond n

/-- Build a `TermImpovRule` from a Boolean predicate over the
    neighborhood. -/
private def termImpov (cond : Neighborhood → Bool) : TermImpovRule where
  condition n := cond n = true
  decCond _ := inferInstanceAs (Decidable (cond _ = true))

/-- Apply a `TermImpovRule`, scanning the phrase left-to-right. The
    first terminal whose neighborhood satisfies the rule is dropped;
    if no terminal matches, the phrase is returned unchanged. -/
def applyTermImpov (rule : TermImpovRule) (phrase : MorphPhrase) :
    MorphPhrase :=
  let rec go (left rest : List FeatureBundle) : List FeatureBundle :=
    match rest with
    | [] => left
    | t :: rest' =>
      let n : Neighborhood :=
        { focus := t, leftCtx := left, rightCtx := rest' }
      if rule.condition n then left ++ rest'
      else go (left ++ [t]) rest'
  go [] phrase

/-- A **terminal-level Metathesis** rule: swaps two adjacent terminals
    when the condition holds at their joint context. By convention `t1`
    is the immediate left of `t2`. Motivating case: Basque Ergative
    Metathesis, [middleton-2026] (13). -/
structure TermMetaRule where
  condition : List FeatureBundle → FeatureBundle → FeatureBundle →
              List FeatureBundle → Prop
  decCond : ∀ left t1 t2 right, Decidable (condition left t1 t2 right)

instance (rule : TermMetaRule) (left t1 t2 right) :
    Decidable (rule.condition left t1 t2 right) :=
  rule.decCond left t1 t2 right

/-- Build a `TermMetaRule` from a Boolean predicate. -/
private def termMeta
    (cond : List FeatureBundle → FeatureBundle → FeatureBundle →
            List FeatureBundle → Bool) :
    TermMetaRule where
  condition left t1 t2 right := cond left t1 t2 right = true
  decCond _ _ _ _ :=
    inferInstanceAs (Decidable (cond _ _ _ _ = true))

/-- Apply a `TermMetaRule`, scanning the phrase left-to-right. Swap the
    first adjacent pair whose joint context satisfies the condition. -/
def applyTermMeta (rule : TermMetaRule) (phrase : MorphPhrase) :
    MorphPhrase :=
  let rec go (left rest : List FeatureBundle) : List FeatureBundle :=
    match rest with
    | [] => left
    | [t] => left ++ [t]
    | t1 :: t2 :: rest' =>
      if rule.condition left t1 t2 rest' then
        left ++ (t2 :: t1 :: rest')
      else
        go (left ++ [t1]) (t2 :: rest')
  go [] phrase

/-- Run impoverishment first, then metathesis — the endorsed pipeline
    of both [arregi-nevins-2012] and [middleton-2026]. -/
def runPhraseImpovThenMeta
    (impovs : List TermImpovRule) (metas : List TermMetaRule)
    (phrase : MorphPhrase) : MorphPhrase :=
  metas.foldl (λ p r => applyTermMeta r p)
    (impovs.foldl (λ p r => applyTermImpov r p) phrase)

/-- Run metathesis first, then impoverishment — the order both authors
    reject; the Basque Ondarru `*s-endu-s-n` form [middleton-2026]
    (17b) is the diagnostic witness. -/
def runPhraseMetaThenImpov
    (impovs : List TermImpovRule) (metas : List TermMetaRule)
    (phrase : MorphPhrase) : MorphPhrase :=
  impovs.foldl (λ p r => applyTermImpov r p)
    (metas.foldl (λ p r => applyTermMeta r p) phrase)

/-- **Participant Dissimilation** ([middleton-2026] (16),
    [arregi-nevins-2012] §4.6). Delete a 1p absolutive clitic
    (`[CL +participant +author]`) when there is a participant ergative
    clitic somewhere to the right in the same auxiliary. The rule
    operates at the terminal level — it deletes a whole bundle, not a
    feature within one. -/
def participantDissimilation : TermImpovRule :=
  termImpov (λ n =>
    isAbsParticipantAuthor n.focus &&
    n.rightCtx.any isErgParticipant)

/-- **Ergative Metathesis** ([middleton-2026] (13),
    [arregi-nevins-2012] §3.2). Swap T with an immediately
    following ergative clitic when T is leftmost in the auxiliary.
    The leftmost requirement (`left.isEmpty`) is what lets
    Participant Dissimilation *feed* Ergative Metathesis: only
    after PD deletes the absolutive clitic does T become leftmost. -/
def ergativeMetathesis : TermMetaRule :=
  termMeta (λ left t1 t2 _ =>
    left.isEmpty && isT t1 && isErgClitic t2)

/-- The Ondarru witness phrase from [middleton-2026] (17a):
    `s-endu-n` `[1pABS, T:past, 2sERG]`. The complementizer is
    suppressed — it does not participate in either rule. -/
def basqueWitnessPhrase : MorphPhrase :=
  [abs1pAuthor, tPast, erg2s]

/-- **PD-then-Meta surface form (the grammatical s-endu-n order).**
    PD deletes the absolutive 1p, leaving `[T, ERG]`; with T now
    leftmost, Ergative Metathesis swaps to `[ERG, T]` — the order
    that surfaces as `s-endu-n`. -/
theorem basqueImpovThenMeta_eq :
    runPhraseImpovThenMeta [participantDissimilation] [ergativeMetathesis]
        basqueWitnessPhrase
      = [erg2s, tPast] := by decide

/-- **Meta-then-PD surface form (the rejected *17b order).**
    Ergative Metathesis cannot fire at the input — T is not
    leftmost (the absolutive clitic precedes it). PD then deletes
    the absolutive clitic, but it is too late to feed metathesis;
    the result is the T-leftmost order `[T, ERG]`, the form
    [middleton-2026] marks ungrammatical (would require
    L-Support repair `*d-endu-s-n`). -/
theorem basqueMetaThenImpov_eq :
    runPhraseMetaThenImpov [participantDissimilation] [ergativeMetathesis]
        basqueWitnessPhrase
      = [tPast, erg2s] := by decide

/-- **The two phrase-level pipelines diverge on the Ondarru witness.**
    This is the Basque counterpart to
    `arregiNevins_neq_middleton_at_witness`; together they are the two
    empirical legs of [middleton-2026]'s claim that metathesis must
    follow impoverishment. -/
theorem basque_orderings_diverge :
    runPhraseImpovThenMeta [participantDissimilation] [ergativeMetathesis]
        basqueWitnessPhrase
      ≠ runPhraseMetaThenImpov [participantDissimilation] [ergativeMetathesis]
        basqueWitnessPhrase := by
  rw [basqueImpovThenMeta_eq, basqueMetaThenImpov_eq]
  decide

end Middleton2026
