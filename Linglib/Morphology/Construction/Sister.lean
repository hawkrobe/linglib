/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Morphology.Construction.Schema
import Linglib.Morphology.Paradigm.Function

/-!
# Sister schemas

Two schemas with coindexed variables are *sisters* ([jackendoff-audring-2020]
§4.8; [booij-2010]'s second-order schemas, notated with `≈`): the linked
variables must be filled alike across a paired instantiation (`Sister.Pairs`).
The binary case formalized here is the canonical instance of their "two or more
schemas" relation; the n-ary generalization is out of scope. The link is a bare
relation on the two variable spaces — deliberately minimal substrate; J&A's
stronger "the very same variable" reads as partial matching, which the link
relation does not commit to.

Sisterhood is nondirectional by construction: `Sister.swap` transposes the pair,
and `pairs_swap` shows paired instantiation is preserved. This is where the
nondirectionality lives — on the packaging, not on any one realization.

Rules of referral in Paradigm Function Morphology recast as a variety of sister
schemas ([jackendoff-audring-2020], crediting [blevins-2016]): a referred cell
realizes exactly as its referent's exponence-only evaluation
(`Morphology.PFM.evalBlockForm_referral`), so the two cells share realization —
the realization-sharing a sister link expresses. The equation itself is
directional (it evaluates the referral); the direction-of-referral problem
[blevins-2016] raises is dissolved by reading the shared realization as a
symmetric sister link, which is J&A's conceptual claim, carried by `swap`.

## Main declarations

- `Morphology.PFM.mem_expoFragment_expo` — members of a block's exponence
  fragment carry exponence payloads
- `Morphology.PFM.evalBlockForm_referral` — a referred cell realizes as its
  referent's exponence-only evaluation
- `Sister` — two schemas with a variable link
- `Sister.Pairs` — paired instantiation sharing fillers at linked variables
- `Sister.swap`, `Sister.pairs_swap` — nondirectionality of the sister relation
-/

namespace Morphology.PFM

open Morphology.Exponence

variable {L Z P : Type*}

/-- Every member of a block's exponence fragment carries an exponence payload. -/
theorem mem_expoFragment_expo {b : Block L Z P} {r : Rule L P (Action Z P)}
    (h : r ∈ expoFragment b) : ∃ f, r.payload = Action.expo f := by
  simp only [expoFragment, List.mem_filter] at h
  obtain ⟨-, h2⟩ := h
  cases hp : r.payload with
  | expo f => exact ⟨f, rfl⟩
  | referral g => rw [hp] at h2; simp at h2

section Referral
variable [PartialOrder P] [DecidableEq L] [DecidableLE P]

/-- A referred cell realizes exactly as its referent's exponence-only evaluation:
when the narrowest rule at `(w, σ)` is a referral to `retarget`, evaluating the
block equals evaluating its exponence fragment at the retargeted cell. The two
cells share realization — the sister link recast from [blevins-2016]'s rules of
referral. -/
theorem evalBlockForm_referral {Lindex : Z → L} {b : Block L Z P} {w : Z} {σ : P}
    {r : Rule L P (Action Z P)} {retarget : P → P}
    (hr : selectMinimal b (Lindex w, σ) = some r)
    (hpay : r.payload = Action.referral retarget) :
    evalBlockForm Lindex b (w, σ)
      = evalBlockForm Lindex (expoFragment b) (w, retarget σ) := by
  cases hs : selectMinimal (expoFragment b) (Lindex w, retarget σ) with
  | none => simp only [evalBlockForm, hr, hpay, hs]
  | some s =>
    obtain ⟨g, hg⟩ := mem_expoFragment_expo (selectMinimal_mem hs)
    simp only [evalBlockForm, hr, hpay, hs, hg]

end Referral

end Morphology.PFM

namespace Morphology.Construction

variable {V₁ V₂ α : Type*}

/-- Two schemas with coindexed variables: `link v₁ v₂` marks a variable of `fst`
as the same as a variable of `snd`. -/
structure Sister (V₁ V₂ α : Type*) [PartialOrder α] where
  /-- The first schema. -/
  fst : Schema V₁ α
  /-- The second schema. -/
  snd : Schema V₂ α
  /-- The variable coindices. -/
  link : V₁ → V₂ → Prop

namespace Sister

variable [PartialOrder α]

/-- A paired instantiation: each schema is instantiated, and linked variables are
filled alike. -/
def Pairs (S : Sister V₁ V₂ α) (w₁ : V₁ → α) (w₂ : V₂ → α) : Prop :=
  S.fst.Instantiates w₁ ∧ S.snd.Instantiates w₂ ∧
    ∀ ⦃v₁ v₂⦄, S.link v₁ v₂ → w₁ v₁ = w₂ v₂

/-- The transposed sister: swap the two schemas and the link. -/
def swap (S : Sister V₁ V₂ α) : Sister V₂ V₁ α where
  fst := S.snd
  snd := S.fst
  link v₂ v₁ := S.link v₁ v₂

/-- Sisterhood is nondirectional: transposing preserves paired instantiation. -/
theorem pairs_swap {S : Sister V₁ V₂ α} {w₁ : V₁ → α} {w₂ : V₂ → α} :
    S.swap.Pairs w₂ w₁ ↔ S.Pairs w₁ w₂ := by
  constructor
  · rintro ⟨h₂, h₁, hlink⟩
    exact ⟨h₁, h₂, fun _ _ hl => (hlink hl).symm⟩
  · rintro ⟨h₁, h₂, hlink⟩
    exact ⟨h₂, h₁, fun _ _ hl => (hlink hl).symm⟩

end Sister

end Morphology.Construction
