/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Probability.Entropy
import Mathlib.Data.List.Infix
import Linglib.Processing.Expectation.LanguageModel

/-!
# Levy (2008): expectation-based syntactic comprehension

[levy-2008] (Cognition 106, 1126–1177) derives a resource-allocation theory of
processing difficulty: a comprehender maintains a probability distribution over
the complete structures consistent with the input so far, and the difficulty of
a word is the relative entropy of the updated distribution with respect to the
old one. The paper's central result (its eq. (4)) is that this difficulty is
exactly the word's surprisal — [hale-2001]'s theory — for *any* generative
process over structures, making surprisal a *causal bottleneck* (§2.3): the
structural representations affect predicted difficulty only through the
conditional word probabilities they determine.

## Main definitions

* `consistent` — the structures whose complete string extends a prefix (𝒯ᵢ).
* `posterior` — the comprehender's distribution given a prefix: the prior
  conditioned on consistency (eq. (3)).
* `nextProb` — the induced conditional word probability.

## Main results

* `posterior_incremental` — incremental update equals direct conditioning
  (eqs. (5)–(8)), via `PMF.filter_filter`.
* `klDiv_posterior_eq_surprisal` — eq. (4): the relative entropy of the update
  equals the surprisal of the word, via `PMF.klDiv_filter_self`.
* `klDiv_posterior_eq_lm_surprisal` — the difficulty read through any
  `LangModel` matching the process's conditional word probabilities.
* `bottleneck` — §2.3: processes agreeing on conditional word probabilities
  incur identical update difficulty, whatever their structures.

## Implementation notes

Structures form a `Fintype` (the paper allows "normally infinite" 𝒯; the
substrate's discrete-sum KL reduction is `Fintype`-gated — lift when it is).
The prior `P` is fixed throughout, matching the paper's caveat that the
equivalence holds only when extra-sentential context does not change while the
word is processed.
-/

namespace Levy2008

open Processing.LanguageModel
open scoped ENNReal

variable {T W : Type*}

/-- The complete structures whose string extends the prefix `ws` — the paper's
    𝒯ᵢ, "the set of complete structures with prefix `w₁…ᵢ`". -/
def consistent (str : T → List W) (ws : List W) : Set T := {t | ws <+: str t}

/-- Longer prefixes select fewer structures. -/
theorem consistent_anti (str : T → List W) {ws ws' : List W} (h : ws <+: ws') :
    consistent str ws' ⊆ consistent str ws :=
  fun _ ht => h.trans ht

/-- `P(w₁…ᵢ)`: the total mass of structures consistent with a prefix — the
    paper's secondary reading of `P` as a distribution over strings. -/
noncomputable def prefixMass (P : PMF T) (str : T → List W) (ws : List W) : ℝ≥0∞ :=
  ∑' t, (consistent str ws).indicator P t

/-- `Pᵢ` (eq. (3)): the comprehender's distribution over complete structures
    given the prefix — the prior conditioned on consistency. -/
noncomputable def posterior (P : PMF T) (str : T → List W) (ws : List W)
    (h : ∃ t ∈ consistent str ws, t ∈ P.support) : PMF T :=
  P.filter (consistent str ws) h

/-- `Pᵢ(w)`: the conditional probability of the next word induced by the
    generative process. -/
noncomputable def nextProb (P : PMF T) (str : T → List W) (ws : List W) (w : W) : ℝ≥0∞ :=
  prefixMass P str (ws ++ [w]) / prefixMass P str ws

variable (P : PMF T) (str : T → List W) (ws : List W) (w : W)

/-- Incremental update equals direct conditioning (eqs. (5)–(8)): filtering the
    current posterior by consistency with the extended prefix is conditioning
    the prior on the extended prefix directly. -/
theorem posterior_incremental
    (hws : ∃ t ∈ consistent str ws, t ∈ P.support)
    (hnext : ∃ t ∈ consistent str (ws ++ [w]), t ∈ P.support) :
    (posterior P str ws hws).filter (consistent str (ws ++ [w]))
      (hnext.imp fun _ ht =>
        ⟨ht.1, (PMF.mem_support_filter_iff hws).mpr
          ⟨consistent_anti str (List.prefix_append ws [w]) ht.1, ht.2⟩⟩) =
    posterior P str (ws ++ [w]) hnext :=
  PMF.filter_filter P (consistent_anti str (List.prefix_append ws [w])) hws hnext _

variable [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]

/-- **Eq. (4)**: the relative entropy of the updated distribution over
    structures with respect to the pre-update distribution is the surprisal of
    the word that triggered the update. -/
theorem klDiv_posterior_eq_surprisal
    (hws : ∃ t ∈ consistent str ws, t ∈ P.support)
    (hnext : ∃ t ∈ consistent str (ws ++ [w]), t ∈ P.support) :
    (posterior P str (ws ++ [w]) hnext).klDiv (posterior P str ws hws)
      = ENNReal.ofReal (-Real.log (nextProb P str ws w).toReal) := by
  rw [← posterior_incremental P str ws w hws hnext, PMF.klDiv_filter_self]
  simp only [posterior]
  rw [PMF.tsum_indicator_filter_of_subset P
    (consistent_anti str (List.prefix_append ws [w])) hws]
  rfl

/-- The update difficulty read through any language model that matches the
    process's conditional word probabilities is that model's surprisal. -/
theorem klDiv_posterior_eq_lm_surprisal (lm : LangModel W)
    (hlm : lm.nextProb ws w = nextProb P str ws w)
    (hws : ∃ t ∈ consistent str ws, t ∈ P.support)
    (hnext : ∃ t ∈ consistent str (ws ++ [w]), t ∈ P.support) :
    (posterior P str (ws ++ [w]) hnext).klDiv (posterior P str ws hws)
      = ENNReal.ofReal (lm.surprisal ws w) := by
  rw [klDiv_posterior_eq_surprisal, LangModel.surprisal, hlm]

/-- **Causal bottleneck** (§2.3, Fig. 1b): two generative processes assigning
    the same conditional word probability incur the same update difficulty,
    regardless of their structural representations. -/
theorem bottleneck {T' : Type*} [Fintype T'] [MeasurableSpace T']
    [MeasurableSingletonClass T'] (P' : PMF T') (str' : T' → List W)
    (hagree : nextProb P str ws w = nextProb P' str' ws w)
    (hws : ∃ t ∈ consistent str ws, t ∈ P.support)
    (hnext : ∃ t ∈ consistent str (ws ++ [w]), t ∈ P.support)
    (hws' : ∃ t ∈ consistent str' ws, t ∈ P'.support)
    (hnext' : ∃ t ∈ consistent str' (ws ++ [w]), t ∈ P'.support) :
    (posterior P str (ws ++ [w]) hnext).klDiv (posterior P str ws hws)
      = (posterior P' str' (ws ++ [w]) hnext').klDiv (posterior P' str' ws hws') := by
  rw [klDiv_posterior_eq_surprisal, klDiv_posterior_eq_surprisal, hagree]

end Levy2008
