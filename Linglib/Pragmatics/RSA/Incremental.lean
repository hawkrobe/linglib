import Linglib.Core.Probability.Choice.RationalAction

/-!
# IncrementalSemantics — Cohn-Gordon's bundle for word-by-word RSA
[cohn-gordon-goodman-potts-2019]

A scene-specific incremental RSA model factors into three pieces:

- `wordApplies : U → W → Bool` — word-level Boolean truth
- `completeUtterances : List (List U)` — closed set of full utterances
- `worlds : List W` — referents to normalize over

From these three pieces every other ingredient — utterance-level truth,
extension-based incremental semantics ⟦pfx⟧(r), the chain-rule speaker,
the literal-listener categorical L0^UTT, and the study-level chain — is
*derived* rather than re-stipulated per study.

This consolidates what was previously triplicated across CommonGround's Figure 1
scene, the [sedivy-2007] reference-game scene, and the
[rubio-fernandez-2016] display: each becomes a single
`IncrementalSemantics` value; studies derive their exact-ℚ chains from it.

## The deep theorem (§2.4)

`l0Utt_ge_inv_card` proves Cohn-Gordon's *weakly-informative* bound
generically over the bundle: any complete utterance true of `r ∈ worlds`
yields a literal-listener posterior of at least `1 / worlds.length` for
`r`. The bound follows from filter-monotonicity (numerator ≥ 1 since `r`
is in the filter; total ≤ `worlds.length` since filtering can only
shrink). Concrete scenes inherit the bound by instantiating the bundle.
-/

namespace RSA

/-- Bundle of scene-specific data for an incremental RSA model.

The three fields jointly determine the entire model:
`incrementalSem` derives the extension-based meaning function
([cohn-gordon-goodman-potts-2019] §2.2) and `l0Utt` projects
the literal listener over complete utterances; studies build their
No-Brevity chains (`s1Score = L0`, α = 1, no cost) from these. -/
structure IncrementalSemantics (U W : Type) [DecidableEq U] where
  /-- Word-level Boolean truth: does word `u` apply to world `w`? -/
  wordApplies : U → W → Bool
  /-- Closed set of complete utterances available in the scene. -/
  completeUtterances : List (List U)
  /-- Referents to normalize over (e.g. the visual display). -/
  worlds : List W

namespace IncrementalSemantics

variable {U W : Type} [DecidableEq U]

/-- Utterance-level Boolean semantics: conjunction of word applicability. -/
def uttSem (sem : IncrementalSemantics U W) (utt : List U) (r : W) : Bool :=
  utt.all (fun w => sem.wordApplies w r)

/-- Number of complete utterances extending `pfx` that are true of `r`. -/
def trueExtCount (sem : IncrementalSemantics U W) (pfx : List U) (r : W) : ℕ :=
  (sem.completeUtterances.filter
    (fun u => pfx.isPrefixOf u && sem.uttSem u r)).length

/-- Number of complete utterances extending `pfx` that are true of at
    least one referent in `sem.worlds`. -/
def viableExtCount (sem : IncrementalSemantics U W) (pfx : List U) : ℕ :=
  (sem.completeUtterances.filter
    (fun u => pfx.isPrefixOf u && sem.worlds.any (fun r => sem.uttSem u r))).length

/-- Extension-based incremental semantics
    ([cohn-gordon-goodman-potts-2019] §2.2):

      ⟦pfx⟧(r) = trueExtCount(pfx, r) / viableExtCount(pfx) -/
noncomputable def incrementalSem (sem : IncrementalSemantics U W)
    (pfx : List U) (r : W) : ℝ :=
  (sem.trueExtCount pfx r : ℝ) / (sem.viableExtCount pfx : ℝ)

theorem incrementalSem_nonneg (sem : IncrementalSemantics U W)
    (pfx : List U) (r : W) : 0 ≤ sem.incrementalSem pfx r :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- Literal listener over **complete** utterances:
    L0^UTT(r | utt) = ⟦utt⟧(r) / Σ_{r'} ⟦utt⟧(r').
    For complete utt with no proper extensions, ⟦utt⟧ collapses to
    Boolean truth, so this is uniform-prior Bayes over `worlds`. -/
noncomputable def l0Utt (sem : IncrementalSemantics U W)
    (utt : List U) (r : W) : ℝ :=
  if ((sem.worlds.filter (fun r' => sem.uttSem utt r')).length : ℝ) = 0 then 0
  else (if sem.uttSem utt r = true then (1 : ℝ) else 0) /
       ((sem.worlds.filter (fun r' => sem.uttSem utt r')).length : ℝ)

theorem l0Utt_nonneg (sem : IncrementalSemantics U W)
    (utt : List U) (r : W) : 0 ≤ sem.l0Utt utt r := by
  unfold l0Utt
  split_ifs with h h'
  · exact le_refl (0 : ℝ)
  · positivity
  · positivity

/-- **Cohn-Gordon §2.4 weakly-informative bound** (generic).

    For *any* complete utterance `utt` that is true of `r` (with
    `r ∈ worlds`), the literal listener assigns posterior at least
    `1 / worlds.length` to `r`. The proof is purely combinatorial:
    the numerator is 1 (since `utt` is true of `r`), and the total
    counts referents satisfying `utt`, which is at most `worlds.length`
    and at least 1 (since `r` is in the filter).

    Cohn-Gordon use this bound to certify that greedy unrolling — even
    without a global view of the utterance space — never produces an
    utterance arbitrarily worse than uniform. Studies that build a
    greedy unroller for a specific scene need only prove that the
    output is in `completeUtterances` and is true of the target;
    the bound then follows. -/
theorem l0Utt_ge_inv_card (sem : IncrementalSemantics U W)
    (utt : List U) (r : W)
    (hr : r ∈ sem.worlds) (htrue : sem.uttSem utt r = true) :
    sem.l0Utt utt r ≥ 1 / (sem.worlds.length : ℝ) := by
  have hmem : r ∈ sem.worlds.filter (fun r' => sem.uttSem utt r') :=
    List.mem_filter.mpr ⟨hr, htrue⟩
  have hn_pos : 0 < (sem.worlds.filter (fun r' => sem.uttSem utt r')).length :=
    List.length_pos_of_mem hmem
  have hn_le : (sem.worlds.filter (fun r' => sem.uttSem utt r')).length ≤
      sem.worlds.length :=
    List.length_filter_le _ _
  have hnR_pos : (0 : ℝ) <
      ((sem.worlds.filter (fun r' => sem.uttSem utt r')).length : ℝ) := by
    exact_mod_cast hn_pos
  have hnR_ne : ((sem.worlds.filter (fun r' => sem.uttSem utt r')).length : ℝ) ≠ 0 :=
    ne_of_gt hnR_pos
  unfold l0Utt
  rw [if_neg hnR_ne, if_pos htrue, ge_iff_le]
  apply one_div_le_one_div_of_le hnR_pos
  exact_mod_cast hn_le

end IncrementalSemantics

end RSA
