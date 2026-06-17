import Linglib.Semantics.Questions.Basic
import Linglib.Core.Logic.Modal.Inquisitive

/-!
# Ciardelli 2022 — InqML denotation into `Question`

[ciardelli-2022] [ciardelli-groenendijk-roelofsen-2018]

Formulas of inquisitive modal logic ([ciardelli-2022] Ch. 8) denote
inquisitive contents. `Question.ofInqML M φ` packages the supporting
teams of `φ` — viewed as information states via the canonical
`Finset W → Set W` coercion — into a `Question W`; the downward-closure
and empty-state obligations discharge directly from InqML's persistence
(`isLowerSet_support`) and empty-team (`support_empty`) lemmas.

The denotation is a lattice/Heyting homomorphism: it carries InqML's
`conj`/`inqDisj`/`impl`/`bot` to the `Question` algebra's
`⊓`/`⊔`/`⇨`/`⊥` (`ofInqML_conj` … `ofInqML_bot`). These are stated here
but not yet proved (`sorry`); the crux is transporting the Finset/Set
coercion through the operations. They land once a downstream study needs
them.

## Main declarations

* `Question.ofInqML` — the InqML denotation map.
* `Question.mem_ofInqML` — its membership characterization.
* `Question.ofInqML_conj` / `_inqDisj` / `_impl` / `_bot` — the
  homomorphism laws (currently `sorry`).
-/

namespace Question

open Core.Logic.Modal (KripkeModel)
open Core.Logic.Modal.Inquisitive

variable {W : Type*} [DecidableEq W] [Fintype W] {Atom : Type*}

/-- The image of a lower family of teams under the `Finset W → Set W`
    coercion is again lower (`Fintype W`: every state is the coercion of
    its `toFinset`). The reusable bridge any downward-closed team logic
    needs to denote its support into `Question`. -/
private theorem isLowerSet_image_coe {s : Set (Finset W)} (hs : IsLowerSet s) :
    IsLowerSet ((fun t : Finset W => (↑t : Set W)) '' s) := by
  rintro a b hba ⟨t, ht, rfl⟩
  exact ⟨(Set.toFinite b).toFinset,
    hs (fun w hw => hba ((Set.Finite.mem_toFinset _).mp hw)) ht, by simp⟩

/-- The inquisitive content denoted by an InqML formula at a Kripke
    model. A state `s : Set W` lies in the denotation iff some supporting
    team `t : Finset W` coerces to `s`.

    Built via `Question.ofLowerSet`: the two `Question` obligations are
    exactly InqML's empty-team property (`support_empty`) and persistence
    (`isLowerSet_support`), bridged across the `Finset → Set` coercion. -/
def ofInqML (M : KripkeModel W Atom) (φ : Formula Atom) : Question W :=
  ofLowerSet ((fun t : Finset W => (↑t : Set W)) '' { t : Finset W | support M φ t })
    ⟨∅, support_empty M φ, by simp⟩ (isLowerSet_image_coe (isLowerSet_support M φ))

/-- Membership in the InqML denotation: a state `s : Set W` lies in the
    `Question` iff some supporting team `t : Finset W` coerces to `s`. -/
@[simp] theorem mem_ofInqML (M : KripkeModel W Atom) (φ : Formula Atom) (s : Set W) :
    s ∈ (ofInqML M φ).props ↔ ∃ t : Finset W, ↑t = s ∧ support M φ t := by
  simp only [ofInqML, props_ofLowerSet, Set.mem_image, Set.mem_setOf_eq, and_comm]

/-- `ofInqML` carries InqML conjunction to the lattice meet `⊓`.
    `support (.conj φ ψ)` is the pointwise `And`, so the supporting-team
    set is an intersection, and the injective `Finset → Set` coercion
    preserves it. -/
theorem ofInqML_conj (M : KripkeModel W Atom) (φ ψ : Formula Atom) :
    ofInqML M (.conj φ ψ) = ofInqML M φ ⊓ ofInqML M ψ := by
  -- TODO: unfold `support_conj` to `support φ ∧ support ψ`; `Set.image`
  -- of an intersection under the injective coercion is the intersection
  -- of images (`Set.InjOn.image_inter`), matching `inf_eq_conj`.
  sorry

/-- `ofInqML` carries InqML disjunction to the lattice join `⊔`.
    `support (.inqDisj φ ψ)` is the pointwise `Or`, and `Set.image`
    distributes over union unconditionally. -/
theorem ofInqML_inqDisj (M : KripkeModel W Atom) (φ ψ : Formula Atom) :
    ofInqML M (.inqDisj φ ψ) = ofInqML M φ ⊔ ofInqML M ψ := by
  -- TODO: `support_inqDisj` is `support φ ∨ support ψ`; `Set.image_union`
  -- gives the join, matching `sup_eq_inqDisj`.
  sorry

/-- `ofInqML` carries InqML implication to the Heyting arrow `⇨`.
    `support (.impl φ ψ) t` is `∀ u ⊆ t, support φ u → support ψ u`. -/
theorem ofInqML_impl (M : KripkeModel W Atom) (φ ψ : Formula Atom) :
    ofInqML M (.impl φ ψ) = ofInqML M φ ⇨ ofInqML M ψ := by
  -- TODO: the crux. Characterize `Question`'s Heyting `⇨` pointwise as
  -- `{s | ∀ r ⊆ s, r ∈ P.props → r ∈ Q.props}`, then bridge the Finset
  -- subteam quantifier to the Set substate quantifier via `Fintype W`
  -- (every `r ⊆ ↑t` is `↑u` for a unique `u ⊆ t`).
  sorry

/-- `ofInqML` carries InqML `⊥` to the lattice bottom `⊥`.
    `support .bot t` holds iff `t = ∅`, so the denotation is `{∅}`. -/
theorem ofInqML_bot (M : KripkeModel W Atom) :
    ofInqML M (Atom := Atom) .bot = ⊥ := by
  -- TODO: `support_bot t ↔ t = ∅`; the image of `{∅}` is `{∅} = bot.props`
  -- (`bot_eq`).
  sorry

end Question
