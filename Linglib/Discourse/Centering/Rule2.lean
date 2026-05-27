import Linglib.Discourse.Centering.Basic
import Linglib.Discourse.Centering.Transition
/-!
# Centering Theory — Rule 2 (Transition Preference)
@cite{grosz-joshi-weinstein-1995} @cite{brennan-friedman-pollard-1987}
@cite{strube-1998} @cite{poesio-stevenson-eugenio-hitzeman-2004}
Two Rule 2 variants in this file: GJW 95 sequence ranking (CON-CON >
RET-RET > SHIFT-SHIFT) via `pairRank`, and Strube 1998's cheap/expensive
distinction via `isCheap`. The BFP 87 4-way variant lives in
`Studies/PoesioEtAl2004.lean`.
-/
set_option autoImplicit false
namespace Discourse.Centering
variable {E R : Type*}
/-! ### Rule 2 (GJW 1995): sequences of transitions -/
/-- Rule 2 (GJW 95): sequence preference by sum-of-ranks. -/
def pairRank (t₁ t₂ : Transition) : Nat := t₁.rank + t₂.rank
theorem rule2_continuations_preferred_over_retentions :
    pairRank .continuation .continuation > pairRank .retaining .retaining := by decide
theorem rule2_retentions_preferred_over_shifts :
    pairRank .retaining .retaining > pairRank .shifting .shifting := by decide
theorem rule2_continuations_preferred_over_shifts :
    pairRank .continuation .continuation > pairRank .shifting .shifting := by decide
/-! ### Rule 2 (Strube 1998): cheap vs expensive -/
/-- A transition is *cheap* (@cite{strube-1998}) if `CB(U_n) = CP(U_{n-1})`:
    the previous utterance's preferred center predicts the current CB. -/
def isCheap [DecidableEq E] [CfRankerOf E R] {U : Type*} [Realizes U E]
    (prev : Utterance E R) (cur : U) (prevCp : Option E) : Prop :=
  cb prev cur = prevCp ∧ (cb prev cur).isSome
instance isCheap.decidable [DecidableEq E] [CfRankerOf E R] {U : Type*}
    [Realizes U E] (prev : Utterance E R) (cur : U) (prevCp : Option E) :
    Decidable (isCheap prev cur prevCp) :=
  inferInstanceAs (Decidable (cb prev cur = prevCp ∧ (cb prev cur).isSome))
/-- Strube 1998 Rule 2 preference: cheap > expensive. -/
def Rule2Strube1998Preferred [DecidableEq E] [CfRankerOf E R] {U : Type*}
    [Realizes U E]
    (prev : Utterance E R) (cur : U) (prevCp : Option E) : Prop :=
  isCheap prev cur prevCp
end Discourse.Centering
