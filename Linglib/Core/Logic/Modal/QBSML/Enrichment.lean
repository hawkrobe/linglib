import Linglib.Core.Logic.Modal.QBSML.Defs

/-!
# Pragmatic enrichment for QBSML

[aloni-vanormondt-2023] [aloni-2022]

The first-order extension of BSML's pragmatic enrichment function `[·]⁺`
([aloni-2022] Definition 6), adding quantifier cases. Per
[aloni-vanormondt-2023] Definition 4.13, `[·]⁺` recursively inserts
`NE` conjuncts into every clause of an NE-free formula:

    [Pt₁...tₙ]⁺  =  Pt₁...tₙ ∧ NE
    [¬φ]⁺        =  ¬[φ]⁺ ∧ NE
    [φ ∧ ψ]⁺     =  ([φ]⁺ ∧ [ψ]⁺) ∧ NE
    [φ ∨ ψ]⁺     =  ([φ]⁺ ∨ [ψ]⁺) ∧ NE
    [◇φ]⁺        =  ◇[φ]⁺ ∧ NE
    [∃xφ]⁺       =  ∃x[φ]⁺ ∧ NE
    [∀xφ]⁺       =  ∀x[φ]⁺ ∧ NE

(`□` is derived as `¬◇¬`, so it carries no separate enrichment clause here.)

The intuition ([aloni-2022]'s "neglect-zero" hypothesis): conversational
participants systematically ignore empty configurations when interpreting,
so each clause must witness a non-empty state. Combined with split
disjunction, this derives ignorance, distribution, free choice, and the
behaviour-under-negation pattern — the QBSML free-choice facts of
`Core/Logic/Modal/QBSML/FreeChoice.lean`.

## Main declarations

* `QBSMLFormula.enrich` — the enrichment function `[·]⁺`.
* `enriched_support_implies_nonempty` — a state supporting an enriched
  formula is non-empty (the `NE` conjunct guards every clause).
* `antiSupport_strip_ne`, `antiSupport_conj_ne_iff` — anti-support of
  `φ ∧ NE` reduces to anti-support of `φ`; the workhorse of the free-choice
  derivations.
* `enrichment_strengthens_support`, `enrichment_strengthens_antiSupport` —
  [aloni-2022] Fact 1 extended to QBSML: on the NE-free fragment, the
  enriched form entails the original, bilaterally.
* `support_enrich_nec_iff` — support of the enriched derived `□` unfolds to
  pointwise enriched support at the accessible lifts, plus non-emptiness.

## Implementation notes

`enrich` is total on `QBSMLFormula` for definitional convenience, but `[·]⁺`
is defined only on the NE-free fragment in both papers, so the `.ne` case is
a filler convention. The construction is structurally identical to BSML's
`Core/Logic/Modal/BSML/Enrichment.lean` but operates on `QBSMLFormula Var Const Pred`
(quantifiers, predicate atoms) rather than `BSMLFormula Atom`. The two are
kept parallel rather than unified: a shared "team-semantic formula language
with an `NE` constructor" abstraction awaits a third instance, per the family
roadmap in `Core/Logic/Team/Algebra.lean`.
-/

namespace Core.Logic.Modal.QBSML

variable {Var Const Pred : Type*}

/-! ### The enrichment function -/

/-- Pragmatic enrichment `[·]⁺` for QBSML formulas ([aloni-vanormondt-2023]
    Definition 4.13). Recursively conjoins `NE` to every clause. -/
def QBSMLFormula.enrich : QBSMLFormula Var Const Pred → QBSMLFormula Var Const Pred
  | .pred P x   => .conj (.pred P x) .ne
  | .predc P c  => .conj (.predc P c) .ne
  | .ne         => .ne  -- totality filler; enrichment is defined only on the NE-free fragment
  | .neg φ      => .conj (.neg φ.enrich) .ne
  | .conj φ ψ   => .conj (.conj φ.enrich ψ.enrich) .ne
  | .disj φ ψ   => .conj (.disj φ.enrich ψ.enrich) .ne
  | .poss φ     => .conj (.poss φ.enrich) .ne
  | .exi x φ    => .conj (.exi x φ.enrich) .ne
  | .univ x φ   => .conj (.univ x φ.enrich) .ne

/-! ### Enriched support forces non-emptiness -/

variable {W Domain : Type*}
variable [DecidableEq W]
variable [DecidableEq Var] [Fintype Var] [DecidableEq Domain] [Fintype Domain]

/-- A QBSML state supporting an enriched formula must be non-empty. The NE
    conjunct guards every clause of `enrich φ`, forcing the witnessing state
    to satisfy `Nonempty`. -/
theorem enriched_support_implies_nonempty (M : QBSMLModel W Domain Const Pred)
    (φ : QBSMLFormula Var Const Pred) (s : Finset (Index W Var Domain))
    (h : support M φ.enrich s) : s.Nonempty := by
  cases φ with
  | ne => exact h
  | _  => exact h.2

/-! ### Stripping NE from anti-support -/

/-- Anti-support of `φ ∧ NE` implies anti-support of `φ`. The split partitions
    the state as `t₁ ∪ t₂` with `antiSupport NE t₂` forcing `t₂ = ∅`, hence
    `t₁ = s`. The QBSML analogue of `BSML/Enrichment`'s `antiSupport_strip_ne`;
    the workhorse of the free-choice derivations in
    `Studies/AloniVanOrmondt2023.lean`. -/
theorem antiSupport_strip_ne (M : QBSMLModel W Domain Const Pred)
    (φ : QBSMLFormula Var Const Pred) (s : Finset (Index W Var Domain))
    (h : antiSupport M (.conj φ .ne) s) :
    antiSupport M φ s := by
  obtain ⟨t₁, t₂, hunion, h₁, h₂⟩ := h
  -- h₂ : t₂ = ∅, so t₁ = s
  subst h₂
  have heq : t₁ = s := (Finset.union_empty t₁).symm.trans hunion
  subst heq; exact h₁

/-- Anti-support of `φ` implies anti-support of `φ ∧ NE` via the trivial
    split `(s, ∅)`. The reverse direction of `antiSupport_strip_ne`. -/
theorem antiSupport_conj_ne_of_antiSupport (M : QBSMLModel W Domain Const Pred)
    (φ : QBSMLFormula Var Const Pred) (s : Finset (Index W Var Domain))
    (h : antiSupport M φ s) :
    antiSupport M (.conj φ .ne) s :=
  ⟨s, ∅, Core.Logic.Team.splitsAs_self_empty s, h, rfl⟩

/-- Anti-support of `φ ∧ NE` ↔ anti-support of `φ`. -/
theorem antiSupport_conj_ne_iff (M : QBSMLModel W Domain Const Pred)
    (φ : QBSMLFormula Var Const Pred) (s : Finset (Index W Var Domain)) :
    antiSupport M (.conj φ .ne) s ↔ antiSupport M φ s :=
  ⟨antiSupport_strip_ne M φ s, antiSupport_conj_ne_of_antiSupport M φ s⟩

/-! ### Enrichment strengthens (joint bilateral induction) -/

/-- Both directions of "enrichment strengthens" ([aloni-2022] Fact 1
    extended to QBSML). For NE-free `φ`:
    - `support M (enrich φ) s → support M φ s`
    - `antiSupport M (enrich φ) s → antiSupport M φ s`

    Joint bilateral induction over the NE-free derivation. The negation case
    interleaves the two directions (support of `¬ψ` is anti-support of `ψ`).
    All quantifier cases use `antiSupport_strip_ne` to peel the `NE`
    conjunct, then `extendUniversal` / `extendFunctional` to apply the IH
    on the extended state. -/
private theorem enrichment_strengthens_both (M : QBSMLModel W Domain Const Pred)
    {φ : QBSMLFormula Var Const Pred} (hNE : φ.IsNEFree) :
    (∀ s : Finset (Index W Var Domain), support M φ.enrich s → support M φ s) ∧
    (∀ s : Finset (Index W Var Domain),
        antiSupport M φ.enrich s → antiSupport M φ s) := by
  induction hNE with
  | pred P x =>
    refine ⟨?_, ?_⟩
    · intro s h; exact h.1
    · intro s h; exact antiSupport_strip_ne M (.pred P x) s h
  | predc P c =>
    refine ⟨?_, ?_⟩
    · intro s h; exact h.1
    · intro s h; exact antiSupport_strip_ne M (.predc P c) s h
  | @neg ψ _ ih =>
    obtain ⟨ih_s, ih_a⟩ := ih
    refine ⟨?_, ?_⟩
    · -- support (¬ψ).enrich s = support ((¬ψ.enrich) ∧ NE) s = antiSupport ψ.enrich s ∧ NE
      intro s h
      show antiSupport M ψ s
      exact ih_a s h.1
    · -- antiSupport (¬ψ).enrich s; strip the outer NE; reduces to support ψ.enrich s
      intro s h
      have h' := antiSupport_strip_ne M (.neg ψ.enrich) s h
      show support M ψ s
      exact ih_s s h'
  | @conj ψ₁ ψ₂ _ _ ih₁ ih₂ =>
    obtain ⟨ih₁_s, ih₁_a⟩ := ih₁
    obtain ⟨ih₂_s, ih₂_a⟩ := ih₂
    refine ⟨?_, ?_⟩
    · intro s h; exact ⟨ih₁_s s h.1.1, ih₂_s s h.1.2⟩
    · intro s h
      have h' := antiSupport_strip_ne M (.conj ψ₁.enrich ψ₂.enrich) s h
      obtain ⟨t₁, t₂, hunion, h₁, h₂⟩ := h'
      exact ⟨t₁, t₂, hunion, ih₁_a t₁ h₁, ih₂_a t₂ h₂⟩
  | @disj ψ₁ ψ₂ _ _ ih₁ ih₂ =>
    obtain ⟨ih₁_s, ih₁_a⟩ := ih₁
    obtain ⟨ih₂_s, ih₂_a⟩ := ih₂
    refine ⟨?_, ?_⟩
    · intro s h
      obtain ⟨t₁, t₂, hunion, h₁, h₂⟩ := h.1
      exact ⟨t₁, t₂, hunion, ih₁_s t₁ h₁, ih₂_s t₂ h₂⟩
    · intro s h
      have h' := antiSupport_strip_ne M (.disj ψ₁.enrich ψ₂.enrich) s h
      exact ⟨ih₁_a s h'.1, ih₂_a s h'.2⟩
  | @poss ψ _ ih =>
    obtain ⟨ih_s, ih_a⟩ := ih
    refine ⟨?_, ?_⟩
    · intro s h i hi
      obtain ⟨X, hX, hne, hsupp⟩ := h.1 i hi
      exact ⟨X, hX, hne, ih_s _ hsupp⟩
    · intro s h
      have h' := antiSupport_strip_ne M (.poss ψ.enrich) s h
      exact fun i hi => ih_a _ (h' i hi)
  | @exi x ψ _ ih =>
    obtain ⟨ih_s, ih_a⟩ := ih
    refine ⟨?_, ?_⟩
    · -- support (.exi x ψ).enrich s = (∃ h, ... support ψ.enrich (s.extendFunctional x h)) ∧ NE
      intro s h
      obtain ⟨h_fn, hne, hsupp⟩ := h.1
      exact ⟨h_fn, hne, ih_s _ hsupp⟩
    · -- antiSupport (.exi x ψ).enrich s; strip NE; reduces to antiSupport ψ.enrich (s.extendUniversal x)
      intro s h
      have h' := antiSupport_strip_ne M (.exi x ψ.enrich) s h
      show antiSupport M ψ (State.extendUniversal s x)
      exact ih_a _ h'
  | @univ x ψ _ ih =>
    obtain ⟨ih_s, ih_a⟩ := ih
    refine ⟨?_, ?_⟩
    · -- support (.univ x ψ).enrich s = support ψ.enrich (s.extendUniversal x) ∧ NE
      intro s h
      show support M ψ (State.extendUniversal s x)
      exact ih_s _ h.1
    · -- antiSupport (.univ x ψ).enrich s; strip NE; reduces to functional
      intro s h
      have h' := antiSupport_strip_ne M (.univ x ψ.enrich) s h
      obtain ⟨h_fn, hne, hsupp⟩ := h'
      exact ⟨h_fn, hne, ih_a _ hsupp⟩

/-- **Enrichment strengthens (support direction)** — [aloni-2022] Fact 1
    extended to QBSML. For NE-free `φ`, supporting the enriched form implies
    supporting the original. -/
theorem enrichment_strengthens_support (M : QBSMLModel W Domain Const Pred)
    (φ : QBSMLFormula Var Const Pred) (s : Finset (Index W Var Domain))
    (hNE : φ.IsNEFree)
    (h : support M φ.enrich s) :
    support M φ s :=
  (enrichment_strengthens_both M hNE).1 s h

/-- **Enrichment strengthens (anti-support direction)**. -/
theorem enrichment_strengthens_antiSupport (M : QBSMLModel W Domain Const Pred)
    (φ : QBSMLFormula Var Const Pred) (s : Finset (Index W Var Domain))
    (hNE : φ.IsNEFree)
    (h : antiSupport M φ.enrich s) :
    antiSupport M φ s :=
  (enrichment_strengthens_both M hNE).2 s h

/-! ### The enriched derived `□` -/

/-- Support of the enriched derived `□` is pointwise enriched support at
    the full accessible lifts, plus non-emptiness: the two NE-strips that
    peel `[□φ]⁺ = [¬◇¬φ]⁺` down to `[φ]⁺` at each `R(wᵢ)[gᵢ]`, packaged
    once for the `□`-free-choice derivations
    (`Core/Logic/Modal/QBSML/FreeChoice.lean`). -/
theorem support_enrich_nec_iff (M : QBSMLModel W Domain Const Pred)
    (φ : QBSMLFormula Var Const Pred) (s : Finset (Index W Var Domain)) :
    support M φ.nec.enrich s ↔
      (∀ i ∈ s, support M φ.enrich
        (State.modalLift (M.access i.world) i.assign)) ∧ s.Nonempty := by
  constructor
  · intro h
    have h' : antiSupport M (.poss (QBSMLFormula.neg φ).enrich) s :=
      antiSupport_strip_ne M _ s h.1
    exact ⟨fun i hi => antiSupport_strip_ne M _ _ (h' i hi), h.2⟩
  · intro h
    exact ⟨antiSupport_conj_ne_of_antiSupport M _ s fun i hi =>
      antiSupport_conj_ne_of_antiSupport M _ _ (h.1 i hi), h.2⟩

end Core.Logic.Modal.QBSML
