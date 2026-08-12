import Linglib.Logic.Team.BSML.Defs

/-!
# BSML Classical Validities

Aloni's bilateral state-based modal logic ([aloni-2022]) preserves several
classical validities despite its non-classical bilateral semantics, and exhibits
one non-classical defect: replacement under negation can fail. This module
proves the key equivalences and the replacement-failure counterexample.

## Main declarations

* `box_diamond_duality_support` / `box_diamond_duality_antiSupport`:
  `□φ` and `¬◇¬φ` are bilaterally equivalent (definitional — `□` is an
  abbreviation).
* `deMorgan_conj_support` / `deMorgan_disj_support` (+ anti-support and
  full-equivalence counterparts): De Morgan laws hold bilaterally.
* `dne_equivalent`: double negation elimination as a bilateral equivalence.
* `disjoint_support_antiSupport`: the engine fact — anti-support of `φ` and
  support of `φ` cannot share any world. Proved by structural induction.
* `negation_incompatibility`: if `s` supports `¬φ` and `t` supports `φ`, then
  `s` and `t` are disjoint as finsets.
* `replacement_failure_counterexample`: a concrete `KripkeModel` witnessing
  `φ ≡ ψ ⇏ ¬φ ≡ ¬ψ`. The pair is `p ∧ ¬p` versus `¬NE`, both supported only
  by `∅`; their negations diverge there.

## Implementation notes

The bilateral validities (De Morgan, DNE, box-diamond) all close by `Iff.rfl`
because the substrate (`BSML.Defs.eval`) is wired so that, e.g.,
`eval M true (.neg (.conj φ ψ))` and `eval M true (.disj (.neg φ) (.neg ψ))`
are the same clause up to one polarity flip. The proofs are documentary —
the content is in `Defs.lean`, where the design of `eval` enforces these.

The negation-incompatibility result is one-directional only: support of `¬φ`
implies incompatibility with every supporter of `φ`, but the converse fails
in BSML ([aloni-2022] gives a counterexample using `¬((p ∧ NE) ∨ q)`).
The framing "negation as incompatibility" should not be read as a definitional
identification.

## Todo

* Engage with [aloni-anttila-yang-2024], which axiomatizes BSML and
  proves the soundness/completeness results these validities sit underneath.
* Extract the bilateral validities to a `Bilateral.Validities`
  module — they depend only on the `IsBilateral` polarity-flip structure
  (already wired via `BSML.isBilateral` in `Defs.lean`).
-/

namespace BSML

open ModalLogic (KripkeModel)

variable {W : Type*} [DecidableEq W] {Atom : Type*}

/-! ### Box-diamond duality -/

/-- Box-diamond duality (support): definitionally equal since `□ := ¬◇¬`. -/
theorem box_diamond_duality_support (M : KripkeModel W Atom)
    (φ : Formula Atom) (t : Finset W) :
    support M φ.nec t ↔ support M (.neg (.poss (.neg φ))) t := Iff.rfl

/-- Box-diamond duality (anti-support): definitionally equal. -/
theorem box_diamond_duality_antiSupport (M : KripkeModel W Atom)
    (φ : Formula Atom) (t : Finset W) :
    antiSupport M φ.nec t ↔ antiSupport M (.neg (.poss (.neg φ))) t := Iff.rfl

/-! ### De Morgan laws -/

/-- De Morgan for conjunction (support): `¬(φ ∧ ψ) ≡ ¬φ ∨ ¬ψ`.
    Both sides reduce to the same SPLIT existential. -/
theorem deMorgan_conj_support (M : KripkeModel W Atom)
    (φ ψ : Formula Atom) (t : Finset W) :
    support M (.neg (.conj φ ψ)) t ↔
    support M (.disj (.neg φ) (.neg ψ)) t := Iff.rfl

/-- De Morgan for conjunction (anti-support). -/
theorem deMorgan_conj_antiSupport (M : KripkeModel W Atom)
    (φ ψ : Formula Atom) (t : Finset W) :
    antiSupport M (.neg (.conj φ ψ)) t ↔
    antiSupport M (.disj (.neg φ) (.neg ψ)) t := Iff.rfl

/-- De Morgan for disjunction (support): `¬(φ ∨ ψ) ≡ ¬φ ∧ ¬ψ`. -/
theorem deMorgan_disj_support (M : KripkeModel W Atom)
    (φ ψ : Formula Atom) (t : Finset W) :
    support M (.neg (.disj φ ψ)) t ↔
    support M (.conj (.neg φ) (.neg ψ)) t := Iff.rfl

/-- De Morgan for disjunction (anti-support). -/
theorem deMorgan_disj_antiSupport (M : KripkeModel W Atom)
    (φ ψ : Formula Atom) (t : Finset W) :
    antiSupport M (.neg (.disj φ ψ)) t ↔
    antiSupport M (.conj (.neg φ) (.neg ψ)) t := Iff.rfl

/-! ### Bilateral equivalence statements -/

/-- DNE is a full bilateral equivalence. -/
theorem dne_equivalent (φ : Formula Atom) :
    equivalent (W := W) (.neg (.neg φ)) φ :=
  fun _ _ => ⟨Iff.rfl, Iff.rfl⟩

/-- Box-diamond duality is a full bilateral equivalence. -/
theorem box_diamond_equivalent (φ : Formula Atom) :
    equivalent (W := W) φ.nec (.neg (.poss (.neg φ))) :=
  fun _ _ => ⟨Iff.rfl, Iff.rfl⟩

/-- De Morgan for conjunction is a full bilateral equivalence. -/
theorem deMorgan_conj_equivalent (φ ψ : Formula Atom) :
    equivalent (W := W) (.neg (.conj φ ψ)) (.disj (.neg φ) (.neg ψ)) :=
  fun _ _ => ⟨Iff.rfl, Iff.rfl⟩

/-- De Morgan for disjunction is a full bilateral equivalence. -/
theorem deMorgan_disj_equivalent (φ ψ : Formula Atom) :
    equivalent (W := W) (.neg (.disj φ ψ)) (.conj (.neg φ) (.neg ψ)) :=
  fun _ _ => ⟨Iff.rfl, Iff.rfl⟩

/-! ### Negation and incompatibility -/

/-- Pointwise form of the disjointness fact, with explicit team variables so
    the inductive hypothesis can apply across arbitrary `s`, `t`. -/
private theorem notMem_of_antiSupport_of_support
    (M : KripkeModel W Atom) (φ : Formula Atom) :
    ∀ (s t : Finset W), antiSupport M φ s → support M φ t →
      ∀ w, w ∈ s → w ∉ t := by
  induction φ with
  | atom p =>
    intro s t hs ht w hsw htw
    exact Bool.false_ne_true ((hs w hsw).symm.trans (ht w htw))
  | ne =>
    intro s _ hs _ w hsw _
    exact Finset.notMem_empty w (hs ▸ hsw)
  | neg ψ ih =>
    intro s t hs ht w hsw htw
    exact ih t s ht hs w htw hsw
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    intro s t hs ht w hsw htw
    obtain ⟨s₁, s₂, hunion, h₁, h₂⟩ := hs
    rcases Finset.mem_union.mp (hunion ▸ hsw) with h | h
    · exact ih₁ s₁ t h₁ ht.1 w h htw
    · exact ih₂ s₂ t h₂ ht.2 w h htw
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    intro s t hs ht w hsw htw
    obtain ⟨t₁, t₂, hunion, h₁, h₂⟩ := ht
    rcases Finset.mem_union.mp (hunion ▸ htw) with h | h
    · exact ih₁ s t₁ hs.1 h₁ w hsw h
    · exact ih₂ s t₂ hs.2 h₂ w hsw h
  | poss ψ ih =>
    intro s t hs ht w hsw htw
    obtain ⟨s', hs'_sub, hs'_ne, hs'_supp⟩ := ht w htw
    obtain ⟨v, hv_s'⟩ := hs'_ne
    exact ih (M.access w) s' (hs w hsw) hs'_supp v
      (hs'_sub (Finset.mem_coe.mpr hv_s')) hv_s'

/-- Anti-support and support of the same `φ` are disjoint teams: if `s`
    anti-supports `φ` and `t` supports `φ`, no world lies in both. -/
theorem disjoint_support_antiSupport (M : KripkeModel W Atom)
    (φ : Formula Atom) {s t : Finset W}
    (hs : antiSupport M φ s) (ht : support M φ t) : Disjoint s t :=
  Finset.disjoint_left.mpr (notMem_of_antiSupport_of_support M φ s t hs ht)

/-- Negation and incompatibility: if `s` supports `¬φ` and `t` supports `φ`,
    then `s` and `t` are disjoint as finsets.

    One-directional only — the converse fails in BSML; see [aloni-2022]. -/
theorem negation_incompatibility (M : KripkeModel W Atom)
    (φ : Formula Atom) {s t : Finset W}
    (hs : support M (.neg φ) s) (ht : support M φ t) : Disjoint s t :=
  disjoint_support_antiSupport M φ hs ht

/-! ### Failure of replacement under negation -/

/-- Failure of replacement under negation: `φ ≡ ψ ⇏ ¬φ ≡ ¬ψ`.

    Counterexample ([aloni-2022]): `⊥₁ = p ∧ ¬p` and `⊥₂ = ¬NE` are
    bilaterally equivalent (both supported only by `∅`), but `¬⊥₁` and `¬⊥₂`
    diverge: `¬(p ∧ ¬p)` is supported by every team (including `∅`) via the
    trivial split `∅ ∪ ∅`, while `¬¬NE = NE` requires a non-empty team. -/
theorem replacement_failure_counterexample :
    ∃ (W : Type) (_ : DecidableEq W) (_ : Fintype W)
      (M : KripkeModel W String) (t : Finset W),
      (support M (.conj (.atom "p") (.neg (.atom "p"))) t ↔
       support M (.neg .ne) t) ∧
      ¬(support M (.neg (.conj (.atom "p") (.neg (.atom "p")))) t ↔
        support M (.neg (.neg .ne)) t) := by
  refine ⟨Bool, inferInstance, inferInstance,
    ⟨λ _ => Finset.univ, λ _ _ => true⟩, ∅, ?_, ?_⟩
  · exact ⟨fun _ => rfl,
           fun _ => ⟨fun w hw => absurd hw (Finset.notMem_empty w),
                     fun w hw => absurd hw (Finset.notMem_empty w)⟩⟩
  · intro h
    have hne : (∅ : Finset Bool).Nonempty := h.mp
      ⟨∅, ∅, by simp,
       fun w hw => absurd hw (Finset.notMem_empty w),
       fun w hw => absurd hw (Finset.notMem_empty w)⟩
    exact Finset.not_nonempty_empty hne

end BSML
