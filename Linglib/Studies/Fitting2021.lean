import Linglib.Core.Order.Bilattice.Basic
import Linglib.Core.Data.Trivalent

/-!
# Fitting (2021): The strict/tolerant idea and bilattices

This file formalizes [fitting-2021]'s generalization of the strict/tolerant logic `ST` of
[cobreros-etal-2012] from three values to any logical bilattice: an interlaced bilattice with
negation and conflation together with a prime bifilter of designated values
([arieli-avron-1996]). Over its exact values `−a = a` and anticonsistent values `−a ≤ₖ a` live
two logics (Definition 8.7.1): `ST⟨B, F⟩` reads premises strictly and conclusions tolerantly
over anticonsistent valuations, `C⟨B, F⟩` reads both strictly over exact valuations. They
validate the same sequents (Proposition 8.7.2, `stValid_iff_cValid`), yet cut is locally valid
only in the second (Proposition 8.7.3, `cut_not_local_stValid`).

The examples come from products `L ⊙ L` of De Morgan algebras: the exact values of `L ⊙ L` are
`L` (Proposition 8.8.3, `exactIso`), `D × L` is a prime bifilter for every prime filter `D`
(Lemma 8.9.2, `PrimeFilter.prod`), and `C⟨L ⊙ L, D × L⟩` is the logic `⟨L, D⟩` itself
(Proposition 8.9.3, `cValid_prod_iff`). Hence every logical De Morgan algebra has a
strict/tolerant counterpart with the same consequence relation (Proposition 8.10.1,
`stValid_prod_iff`): classical logic from `Bool`, `K3` and `LP` from `Trivalent`, and `FDE`
from `FOUR` (Examples 8.10.2–8.10.5).

## Implementation notes

* Formulas have conjunction, disjunction and negation only (Definition 8.6.1); prime bifilters and
  prime filters carry the nonemptiness and properness that §8.2 requires of designated sets.
* Lemma 8.8.2, the general interlaced-bilattice route to Proposition 8.8.3, is not formalized;
  the proposition is proved in coordinates for the product.
* Locators use the chapter's numbering, `8.n` for the preprint's `§n`.

## References

* [fitting-2021]
* [cobreros-etal-2012]
* [arieli-avron-1996]
* [arieli-avron-1998]
* [belnap-1977]
* [priest-1979]
-/

open Bilattice Product

namespace Fitting2021

variable {B α : Type*}

/-! ### Formulas and valuations (§8.6) -/

/-- Formulas over propositional letters ([fitting-2021] Def 8.6.1): conjunction, disjunction,
negation, no implication. -/
inductive Fml (α : Type*) where
  | atom (p : α)
  | and (φ ψ : Fml α)
  | or (φ ψ : Fml α)
  | not (φ : Fml α)

section Eval

variable [Lattice B] [Lattice (Know B)] [Negation B]

/-- The extension of a valuation to formulas ([fitting-2021] Def 8.6.2). -/
def Fml.eval (v : α → B) : Fml α → B
  | atom p => v p
  | and φ ψ => φ.eval v ⊓ ψ.eval v
  | or φ ψ => φ.eval v ⊔ ψ.eval v
  | not φ => neg (φ.eval v)

variable [Conflation B] [NegConfComm B]

/-- Exact valuations evaluate to exact values ([fitting-2021] Prop 8.6.3). -/
theorem eval_isExact {v : α → B} (hv : ∀ p, IsExact (v p)) :
    ∀ φ : Fml α, IsExact (φ.eval v)
  | .atom p => hv p
  | .and φ ψ => (eval_isExact hv φ).inf (eval_isExact hv ψ)
  | .or φ ψ => (eval_isExact hv φ).sup (eval_isExact hv ψ)
  | .not φ => (eval_isExact hv φ).neg

variable [Interlaced B]

/-- Anticonsistent valuations evaluate to anticonsistent values ([fitting-2021] Prop 8.6.3). -/
theorem eval_isAnticonsistent {v : α → B} (hv : ∀ p, IsAnticonsistent (v p)) :
    ∀ φ : Fml α, IsAnticonsistent (φ.eval v)
  | .atom p => hv p
  | .and φ ψ => (eval_isAnticonsistent hv φ).inf (eval_isAnticonsistent hv ψ)
  | .or φ ψ => (eval_isAnticonsistent hv φ).sup (eval_isAnticonsistent hv ψ)
  | .not φ => (eval_isAnticonsistent hv φ).neg

omit [Conflation B] [NegConfComm B] in
/-- Evaluation is knowledge-monotone in the valuation ([fitting-2021] Prop 8.6.4). -/
theorem eval_kLE_eval {v w : α → B} (h : ∀ p, v p ≤ₖ w p) :
    ∀ φ : Fml α, φ.eval v ≤ₖ φ.eval w
  | .atom p => h p
  | .and φ ψ => by
    calc φ.eval v ⊓ ψ.eval v
        ≤ₖ φ.eval w ⊓ ψ.eval v := Interlaced.inf_kmono (eval_kLE_eval h φ) _
      _ = ψ.eval v ⊓ φ.eval w := inf_comm ..
      _ ≤ₖ ψ.eval w ⊓ φ.eval w := Interlaced.inf_kmono (eval_kLE_eval h ψ) _
      _ = φ.eval w ⊓ ψ.eval w := inf_comm ..
  | .or φ ψ => by
    calc φ.eval v ⊔ ψ.eval v
        ≤ₖ φ.eval w ⊔ ψ.eval v := Interlaced.sup_kmono (eval_kLE_eval h φ) _
      _ = ψ.eval v ⊔ φ.eval w := sup_comm ..
      _ ≤ₖ ψ.eval w ⊔ φ.eval w := Interlaced.sup_kmono (eval_kLE_eval h ψ) _
      _ = φ.eval w ⊔ ψ.eval w := sup_comm ..
  | .not φ => neg_kLE_neg (eval_kLE_eval h φ)

end Eval

/-! ### Prime bifilters ([fitting-2021] Def 8.6.5, after [arieli-avron-1998]) -/

section Bifilter

variable [Lattice B] [Lattice (Know B)]

/-- A prime bifilter: a proper nonempty subset that is a prime filter for both the truth and the
knowledge lattice operations ([fitting-2021] Def 8.6.5), generalizing the designated values
`{t, ⊤}` of `FOUR` ([arieli-avron-1996], [arieli-avron-1998]). -/
structure PrimeBifilter (B : Type*) [Lattice B] [Lattice (Know B)] where
  /-- The designated values. -/
  carrier : Set B
  nonempty : carrier.Nonempty
  ne_univ : carrier ≠ Set.univ
  inf_mem_iff {a b : B} : a ⊓ b ∈ carrier ↔ a ∈ carrier ∧ b ∈ carrier
  kInf_mem_iff {a b : B} : (a ⊗ b : B) ∈ carrier ↔ a ∈ carrier ∧ b ∈ carrier
  sup_mem_iff {a b : B} : a ⊔ b ∈ carrier ↔ a ∈ carrier ∨ b ∈ carrier
  kSup_mem_iff {a b : B} : (a ⊕ b : B) ∈ carrier ↔ a ∈ carrier ∨ b ∈ carrier

instance : Membership B (PrimeBifilter B) := ⟨λ F a => a ∈ F.carrier⟩

/-- Prime bifilters are upward closed in the knowledge order ([fitting-2021] Prop 8.6.6). -/
theorem PrimeBifilter.mem_of_kLE (F : PrimeBifilter B) {a b : B} (ha : a ∈ F) (h : a ≤ₖ b) :
    b ∈ F := by
  have hab : (a ⊕ b : B) = b :=
    toKnow.injective (by simpa only [toKnow_kSup] using sup_eq_right.mpr h)
  exact hab ▸ F.kSup_mem_iff.mpr (Or.inl ha)

/-- Prime bifilters are upward closed in the truth order ([fitting-2021] Prop 8.6.6). -/
theorem PrimeBifilter.mem_of_le (F : PrimeBifilter B) {a b : B} (ha : a ∈ F) (h : a ≤ b) :
    b ∈ F :=
  sup_eq_right.mpr h ▸ F.sup_mem_iff.mpr (Or.inl ha)

end Bifilter

/-! ### The strict/tolerant and classical logics of a logical bilattice (§8.7) -/

section Logics

variable [Lattice B] [Lattice (Know B)] [Negation B] [Conflation B]

/-- Strictly designated: designated and exact ([fitting-2021] Def 8.7.1). -/
def StrictlyDesignated (F : PrimeBifilter B) (a : B) : Prop := a ∈ F ∧ IsExact a

/-- Tolerantly designated: designated and anticonsistent ([fitting-2021] Def 8.7.1). -/
def TolerantlyDesignated (F : PrimeBifilter B) (a : B) : Prop := a ∈ F ∧ IsAnticonsistent a

/-- A valuation satisfies a sequent strict-to-tolerantly: if every premise is strictly
designated, some conclusion is tolerantly designated. -/
def STSatisfies (F : PrimeBifilter B) (v : α → B) (Γ Δ : List (Fml α)) : Prop :=
  (∀ φ ∈ Γ, StrictlyDesignated F (φ.eval v)) → ∃ ψ ∈ Δ, TolerantlyDesignated F (ψ.eval v)

/-- A valuation satisfies a sequent strictly on both sides. -/
def CSatisfies (F : PrimeBifilter B) (v : α → B) (Γ Δ : List (Fml α)) : Prop :=
  (∀ φ ∈ Γ, StrictlyDesignated F (φ.eval v)) → ∃ ψ ∈ Δ, StrictlyDesignated F (ψ.eval v)

/-- `ST⟨B, F⟩` validity ([fitting-2021] Def 8.7.1): over valuations into the anticonsistent
values, strict premises entail a tolerant conclusion. -/
def STValid (F : PrimeBifilter B) (Γ Δ : List (Fml α)) : Prop :=
  ∀ v : α → B, (∀ p, IsAnticonsistent (v p)) → STSatisfies F v Γ Δ

/-- `C⟨B, F⟩` validity ([fitting-2021] Def 8.7.1): over valuations into the exact values, strict
premises entail a strict conclusion. -/
def CValid (F : PrimeBifilter B) (Γ Δ : List (Fml α)) : Prop :=
  ∀ v : α → B, (∀ p, IsExact (v p)) → CSatisfies F v Γ Δ

instance {F : PrimeBifilter B} [DecidablePred (· ∈ F)] [DecidablePred (IsExact (B := B))]
    (a : B) : Decidable (StrictlyDesignated F a) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance {F : PrimeBifilter B} [DecidablePred (· ∈ F)]
    [DecidablePred (IsAnticonsistent (B := B))] (a : B) : Decidable (TolerantlyDesignated F a) :=
  inferInstanceAs (Decidable (_ ∧ _))

variable [Interlaced B] [NegConfComm B]

/-- [fitting-2021] Prop 8.7.2: the strict/tolerant and classical logics of a logical bilattice
validate exactly the same sequents. Right-to-left replaces the chapter's contraposition: given an
anticonsistent valuation, choose an exact valuation knowledge-below it, win there classically,
and transport the witness up along knowledge-monotonicity and bifilter closure. -/
theorem stValid_iff_cValid (F : PrimeBifilter B) (Γ Δ : List (Fml α)) :
    STValid F Γ Δ ↔ CValid F Γ Δ := by
  constructor
  · intro hST v hv hΓ
    obtain ⟨ψ, hψΔ, hψF, _⟩ := hST v (λ p => (hv p).isAnticonsistent) hΓ
    exact ⟨ψ, hψΔ, hψF, eval_isExact hv ψ⟩
  · intro hC v hv hΓ
    choose v' hexact hle using λ p => (hv p).exists_exact_kLE
    have hmono : ∀ φ : Fml α, φ.eval v' ≤ₖ φ.eval v := eval_kLE_eval hle
    have hΓ' : ∀ φ ∈ Γ, StrictlyDesignated F (φ.eval v') := λ φ hφ => by
      have hx := hΓ φ hφ
      have heq : φ.eval v' = φ.eval v := (eval_isExact hexact φ).eq_of_kLE hx.2 (hmono φ)
      rw [heq]; exact hx
    obtain ⟨ψ, hψΔ, hψF, _⟩ := hC v' hexact hΓ'
    exact ⟨ψ, hψΔ, F.mem_of_kLE hψF (hmono ψ), eval_isAnticonsistent hv ψ⟩

omit [Interlaced B] [NegConfComm B] in
/-- Cut is locally valid in `C⟨B, F⟩` ([fitting-2021] Prop 8.7.3): a valuation satisfying both
premises of a cut instance satisfies its conclusion. -/
theorem cut_cSatisfies (F : PrimeBifilter B) {Γ Δ : List (Fml α)} {A : Fml α} {v : α → B}
    (h₁ : CSatisfies F v (A :: Γ) Δ) (h₂ : CSatisfies F v Γ (A :: Δ)) : CSatisfies F v Γ Δ := by
  intro hΓ
  obtain ⟨ψ, hψ, hd⟩ := h₂ hΓ
  rcases List.mem_cons.mp hψ with rfl | hψΔ
  · exact h₁ λ φ hφ => by
      rcases List.mem_cons.mp hφ with rfl | h
      exacts [hd, hΓ _ h]
  · exact ⟨ψ, hψΔ, hd⟩

variable [BoundedOrder (Know B)]

omit [Interlaced B] [NegConfComm B] in
/-- [fitting-2021] Prop 8.7.3, the `ST` half: the cut scheme fails locally in `ST⟨B, F⟩` when the
knowledge order is nontrivial. The countermodel sends a letter to the knowledge top — designated
and anticonsistent but not exact — so both cut premises hold while the empty conclusion fails. -/
theorem cut_not_local_stValid (F : PrimeBifilter B) (p : α) (hbt : (⊥ : Know B) ≠ ⊤) :
    ¬ ∀ v : α → B, (∀ q, IsAnticonsistent (v q)) →
      STSatisfies F v [.atom p] [] → STSatisfies F v [] [.atom p] →
      STSatisfies F v ([] : List (Fml α)) [] := by
  intro h
  set kT : B := ofKnow (⊤ : Know B) with hkT
  have hle_top : ∀ x : B, x ≤ₖ kT := λ x => by
    rw [hkT, kLE_def, toKnow_ofKnow]; exact le_top
  have hanti : IsAnticonsistent kT := hle_top _
  have hnexact : ¬ IsExact kT := by
    intro hex
    have h1 := conf_kLE_conf (hle_top (conf (ofKnow (⊥ : Know B))))
    rw [conf_conf, show conf kT = kT from hex] at h1
    rw [hkT, kLE_def, toKnow_ofKnow, toKnow_ofKnow] at h1
    exact hbt (le_antisymm h1 bot_le).symm
  have hmem : kT ∈ F := by
    obtain ⟨a, ha⟩ := F.nonempty
    exact F.mem_of_kLE ha (hle_top a)
  have hfinal := h (λ _ => kT) (λ _ => hanti)
    (λ hΓ => absurd (hΓ _ (List.Mem.head _)).2 hnexact)
    (λ _ => ⟨.atom p, List.Mem.head _, hmem, hanti⟩)
  obtain ⟨ψ, hψ, -⟩ := hfinal (λ φ hφ => nomatch hφ)
  exact nomatch hψ

end Logics

/-! ### Products of De Morgan algebras (§§8.8–8.9) -/

section DeMorgan

variable {L : Type*} [LatticeWithInvolution L]

/-- [fitting-2021] Prop 8.8.3: the exact members of `L ⊙ L` are the pairs `⟨a, aᶜ⟩`, and under
the truth order they are `L`. -/
def exactIso : {x : L ⊙ L // IsExact x} ≃o L where
  toFun x := x.1.pro
  invFun a := ⟨mk a aᶜ, (Evidential.isExact_iff _).2 rfl⟩
  left_inv x := Subtype.ext (Product.ext rfl ((Evidential.isExact_iff _).1 x.2).symm)
  right_inv _ := rfl
  map_rel_iff' {x y} := by
    show x.1.pro ≤ y.1.pro ↔ x ≤ y
    rw [← Subtype.coe_le_coe, le_def, (Evidential.isExact_iff _).1 x.2,
      (Evidential.isExact_iff _).1 y.2, LatticeWithInvolution.compl_le_compl_iff_le, and_self]

/-- A prime filter of `L` ([fitting-2021] Def 8.9.1): the designated values of a logical De Morgan
algebra `⟨L, D⟩`, nonempty and proper as §8.2 requires. -/
structure PrimeFilter (L : Type*) [Lattice L] where
  /-- The designated values. -/
  carrier : Set L
  nonempty : carrier.Nonempty
  ne_univ : carrier ≠ Set.univ
  inf_mem_iff {a b : L} : a ⊓ b ∈ carrier ↔ a ∈ carrier ∧ b ∈ carrier
  sup_mem_iff {a b : L} : a ⊔ b ∈ carrier ↔ a ∈ carrier ∨ b ∈ carrier

instance : Membership L (PrimeFilter L) := ⟨λ D a => a ∈ D.carrier⟩

/-- [fitting-2021] Lemma 8.9.2: `D × L` is a prime bifilter of `L ⊙ L`. -/
def PrimeFilter.prod (D : PrimeFilter L) : PrimeBifilter (L ⊙ L) where
  carrier := {x | x.pro ∈ D}
  nonempty := let ⟨a, ha⟩ := D.nonempty; ⟨Product.mk a ⊥, ha⟩
  ne_univ h := D.ne_univ (Set.eq_univ_of_forall λ a =>
    (show Product.mk a ⊥ ∈ {x : L ⊙ L | x.pro ∈ D} from h ▸ Set.mem_univ _))
  inf_mem_iff := D.inf_mem_iff
  kInf_mem_iff := D.inf_mem_iff
  sup_mem_iff := D.sup_mem_iff
  kSup_mem_iff := D.sup_mem_iff

theorem PrimeFilter.mem_prod_iff (D : PrimeFilter L) (x : L ⊙ L) : x ∈ D.prod ↔ x.pro ∈ D :=
  Iff.rfl

instance (D : PrimeFilter L) [DecidablePred (· ∈ D)] : DecidablePred (· ∈ D.prod) :=
  λ x => inferInstanceAs (Decidable (x.pro ∈ D))

/-- In `D × L` the strictly designated values are the exact pairs `⟨a, aᶜ⟩` with `a ∈ D`. -/
theorem strictlyDesignated_prod_iff (D : PrimeFilter L) (x : L ⊙ L) :
    StrictlyDesignated D.prod x ↔ x.pro ∈ D ∧ x.con = x.proᶜ :=
  and_congr Iff.rfl (Evidential.isExact_iff x)

/-- In `D × L` the tolerantly designated values are the anticonsistent pairs with `a ∈ D`. -/
theorem tolerantlyDesignated_prod_iff (D : PrimeFilter L) (x : L ⊙ L) :
    TolerantlyDesignated D.prod x ↔ x.pro ∈ D ∧ x.proᶜ ≤ x.con :=
  and_congr Iff.rfl (Evidential.isAnticonsistent_iff x)

/-- The logic `⟨L, D⟩`: formulas evaluated in `L` by meet, join and the De Morgan complement. -/
def Fml.evalL (v : α → L) : Fml α → L
  | atom p => v p
  | and φ ψ => φ.evalL v ⊓ ψ.evalL v
  | or φ ψ => φ.evalL v ⊔ ψ.evalL v
  | not φ => (φ.evalL v)ᶜ

/-- Validity in the logic `⟨L, D⟩` (§8.2): designated premises entail a designated conclusion. -/
def LValid (D : PrimeFilter L) (Γ Δ : List (Fml α)) : Prop :=
  ∀ v : α → L, (∀ φ ∈ Γ, φ.evalL v ∈ D) → ∃ ψ ∈ Δ, ψ.evalL v ∈ D

/-- The exact valuation of `L ⊙ L` a valuation in `L` determines, `p ↦ ⟨v p, (v p)ᶜ⟩`. -/
def exactVal (v : α → L) (p : α) : L ⊙ L := mk (v p) (v p)ᶜ

theorem exactVal_isExact (v : α → L) (p : α) : IsExact (exactVal v p) :=
  (Evidential.isExact_iff _).2 rfl

/-- Exact valuations are exactly the `exactVal`s. -/
theorem eq_exactVal_of_isExact {v : α → L ⊙ L} (hv : ∀ p, IsExact (v p)) :
    v = exactVal λ p => (v p).pro :=
  funext λ p => Product.ext rfl ((Evidential.isExact_iff _).1 (hv p))

/-- Evaluation in `L ⊙ L` along an exact valuation is evaluation in `L`. -/
theorem eval_exactVal (v : α → L) : ∀ φ : Fml α, φ.eval (exactVal v) = mk (φ.evalL v) (φ.evalL v)ᶜ
  | .atom _ => rfl
  | .and φ ψ => by
    rw [Fml.eval, Fml.evalL, eval_exactVal v φ, eval_exactVal v ψ, mk_inf_mk,
      LatticeWithInvolution.compl_inf]
  | .or φ ψ => by
    rw [Fml.eval, Fml.evalL, eval_exactVal v φ, eval_exactVal v ψ, mk_sup_mk,
      LatticeWithInvolution.compl_sup]
  | .not φ => by
    rw [Fml.eval, Fml.evalL, eval_exactVal v φ, neg_mk', LatticeWithInvolution.compl_compl]

/-- [fitting-2021] Prop 8.9.3: `C⟨L ⊙ L, D × L⟩` is the logic `⟨L, D⟩` — the two validate the same
sequents, the exact values of the product corresponding to `L` and `(D × L) ∩ E` to `D`. -/
theorem cValid_prod_iff (D : PrimeFilter L) (Γ Δ : List (Fml α)) :
    CValid D.prod Γ Δ ↔ LValid D Γ Δ := by
  constructor
  · intro h v hΓ
    obtain ⟨ψ, hψ, hD, -⟩ := h (exactVal v) (exactVal_isExact v) λ φ hφ =>
      ⟨by rw [PrimeFilter.mem_prod_iff, eval_exactVal, pro_mk]; exact hΓ φ hφ,
        eval_isExact (exactVal_isExact v) φ⟩
    rw [PrimeFilter.mem_prod_iff, eval_exactVal, pro_mk] at hD
    exact ⟨ψ, hψ, hD⟩
  · intro h v hv hΓ
    rw [eq_exactVal_of_isExact hv] at hΓ ⊢
    obtain ⟨ψ, hψ, hD⟩ := h (λ p => (v p).pro) λ φ hφ => by
      have := (hΓ φ hφ).1
      rwa [PrimeFilter.mem_prod_iff, eval_exactVal, pro_mk] at this
    exact ⟨ψ, hψ, by rw [PrimeFilter.mem_prod_iff, eval_exactVal, pro_mk]; exact hD,
      eval_isExact (exactVal_isExact _) ψ⟩

/-! ### Generating strict/tolerant examples (§8.10) -/

/-- [fitting-2021] Prop 8.10.1: the strict/tolerant counterpart `ST⟨L ⊙ L, D × L⟩` of a logical
De Morgan algebra `⟨L, D⟩` has the same consequence relation. -/
theorem stValid_prod_iff (D : PrimeFilter L) (Γ Δ : List (Fml α)) :
    STValid D.prod Γ Δ ↔ LValid D Γ Δ :=
  (stValid_iff_cValid _ _ _).trans (cValid_prod_iff D Γ Δ)

/-- [fitting-2021] Prop 8.10.1: and it differs at the metaconsequence level — cut fails locally in
the counterpart. -/
theorem cut_not_local_prod [Nontrivial L] (D : PrimeFilter L) (p : α) :
    ¬ ∀ v : α → L ⊙ L, (∀ q, IsAnticonsistent (v q)) →
      STSatisfies D.prod v [.atom p] [] → STSatisfies D.prod v [] [.atom p] →
      STSatisfies D.prod v ([] : List (Fml α)) [] :=
  cut_not_local_stValid D.prod p λ h =>
    bot_ne_top (congrArg (λ k : Know (L ⊙ L) => (ofKnow k).pro) h)

end DeMorgan

/-! ### Examples 8.10.2–8.10.5: classical logic, `K3`, `LP` and `FDE` -/

section Examples

/-- Classical logic as a logical De Morgan algebra: `Bool` with `{true}` designated. -/
def classicalFilter : PrimeFilter Bool where
  carrier := {b | b = true}
  nonempty := ⟨true, rfl⟩
  ne_univ h := absurd (h ▸ Set.mem_univ false) (by decide)
  inf_mem_iff {a b} := by revert a b; decide
  sup_mem_iff {a b} := by revert a b; decide

instance : DecidablePred (· ∈ classicalFilter) := λ b => inferInstanceAs (Decidable (b = true))

/-- The designated values `{t, ⊤}` of `FOUR` ([fitting-2021] Example 8.7.4) are `{true} × Bool`
([fitting-2021] Example 8.10.2). -/
abbrev fourBifilter : PrimeBifilter FOUR := classicalFilter.prod

theorem mem_fourBifilter_iff : ∀ x : FOUR, x ∈ fourBifilter ↔ x = FOUR.T ∨ x = FOUR.I := by
  decide

/-- `FOUR`'s exact values are the classical `{F, T}` ([fitting-2021] Example 8.7.4). -/
theorem four_isExact_iff : ∀ x : FOUR, IsExact x ↔ x = FOUR.F ∨ x = FOUR.T := by decide

/-- `FOUR`'s anticonsistent values are `{F, T, I}`, the value space of `LP`
([fitting-2021] Example 8.7.4). -/
theorem four_isAnticonsistent_iff :
    ∀ x : FOUR, IsAnticonsistent x ↔ x = FOUR.F ∨ x = FOUR.T ∨ x = FOUR.I := by
  decide

/-- The original collapse ([cobreros-etal-2012], via [fitting-2021] Example 8.7.4): `ST` and
classical logic validate the same sequents. -/
theorem four_stValid_iff_cValid {α : Type*} (Γ Δ : List (Fml α)) :
    STValid fourBifilter Γ Δ ↔ CValid fourBifilter Γ Δ :=
  stValid_iff_cValid fourBifilter Γ Δ

/-- And cut fails locally in `ST` over `FOUR`. -/
theorem four_cut_not_local {α : Type*} (p : α) :
    ¬ ∀ v : α → FOUR, (∀ q, IsAnticonsistent (v q)) →
      STSatisfies fourBifilter v [.atom p] [] → STSatisfies fourBifilter v [] [.atom p] →
      STSatisfies fourBifilter v ([] : List (Fml α)) [] :=
  cut_not_local_prod classicalFilter p

/-- `K3`, Kleene's strong three-valued logic: `Trivalent` with `{true}` designated
([fitting-2021] Example 8.10.3). -/
def k3Filter : PrimeFilter Trivalent where
  carrier := {a | a = .true}
  nonempty := ⟨.true, rfl⟩
  ne_univ h := absurd (h ▸ Set.mem_univ Trivalent.false) (by decide)
  inf_mem_iff {a b} := by revert a b; decide
  sup_mem_iff {a b} := by revert a b; decide

instance : DecidablePred (· ∈ k3Filter) := λ a => inferInstanceAs (Decidable (a = .true))

/-- `LP`, Priest's logic of paradox ([priest-1979]): the same values with `{½, 1}` designated
([fitting-2021] Example 8.10.4). -/
def lpFilter : PrimeFilter Trivalent where
  carrier := {a | a ≠ .false}
  nonempty := ⟨.true, by decide⟩
  ne_univ h := absurd (h ▸ Set.mem_univ Trivalent.false) (by decide)
  inf_mem_iff {a b} := by revert a b; decide
  sup_mem_iff {a b} := by revert a b; decide

instance : DecidablePred (· ∈ lpFilter) := λ a => inferInstanceAs (Decidable (a ≠ .false))

/-- The bilattice `NINE = Trivalent ⊙ Trivalent` of Figure 4 ([fitting-2021] Example 8.10.3). -/
abbrev NINE := Trivalent ⊙ Trivalent

/-- `NINE`'s exact values are `{f, d⊤, t}` ([fitting-2021] §8.5). -/
theorem nine_isExact_iff : ∀ x : NINE,
    IsExact x ↔ x = mk .false .true ∨ x = mk .indet .indet ∨ x = mk .true .false := by
  decide

/-- `NINE`'s consistent values are the exact ones with `{df, ⊥, dt}` ([fitting-2021] §8.5). -/
theorem nine_isConsistent_iff : ∀ x : NINE, IsConsistent x ↔ IsExact x ∨
    x = mk .false .indet ∨ x = mk .false .false ∨ x = mk .indet .false := by
  decide

/-- `NINE`'s anticonsistent values are the exact ones with `{of, ⊤, ot}`
([fitting-2021] §8.5). -/
theorem nine_isAnticonsistent_iff : ∀ x : NINE, IsAnticonsistent x ↔ IsExact x ∨
    x = mk .indet .true ∨ x = mk .true .true ∨ x = mk .true .indet := by
  decide

/-- The two prime bifilters of `NINE` ([fitting-2021] Examples 8.7.5 and 8.10.4): `{t, ot, ⊤}`
from `K3` and the six-element `{dt, t, d⊤, ot, of, ⊤}` from `LP`. -/
theorem nine_bifilters : (∀ x : NINE, x ∈ k3Filter.prod ↔
      x = mk .true .false ∨ x = mk .true .indet ∨ x = mk .true .true) ∧
    ∀ x : NINE, x ∈ lpFilter.prod ↔ x = mk .indet .false ∨ x = mk .true .false ∨
      x = mk .indet .indet ∨ x = mk .true .indet ∨ x = mk .indet .true ∨ x = mk .true .true := by
  decide

/-- With `K3` the strictly designated values reduce to `{t}`, so `C⟨NINE, {1} × K3⟩` is `K3`
([fitting-2021] Example 8.7.5). -/
theorem k3_strict_iff : ∀ x : NINE, StrictlyDesignated k3Filter.prod x ↔ x = mk .true .false := by
  decide

/-- With `LP` the strictly designated values are `{d⊤, t}` and the tolerantly designated ones
`{t, d⊤, ot, of, ⊤}` ([fitting-2021] Example 8.10.4). -/
theorem lp_designated : (∀ x : NINE, StrictlyDesignated lpFilter.prod x ↔
      x = mk .indet .indet ∨ x = mk .true .false) ∧
    ∀ x : NINE, TolerantlyDesignated lpFilter.prod x ↔ x = mk .true .false ∨
      x = mk .indet .indet ∨ x = mk .true .indet ∨ x = mk .indet .true ∨ x = mk .true .true := by
  decide

/-- `P, ¬P ⇒ Q` fails in strict/tolerant `LP` as in `LP`: `v(P) = d⊤`, `v(Q) = f`
([fitting-2021] Example 8.10.4). -/
theorem lp_explosion_fails :
    ¬ STValid lpFilter.prod [.atom true, .not (.atom true)] [.atom false] := λ h =>
  absurd (h (λ b => if b then mk .indet .indet else mk .false .true) (by decide) (by decide))
    (by decide)

/-- `FDE` as a logical De Morgan algebra: `FOUR` under the truth order with `{t, ⊤}` designated
([fitting-2021] Example 8.10.5). -/
def fdeFilter : PrimeFilter FOUR where
  carrier := {x | x = FOUR.T ∨ x = FOUR.I}
  nonempty := ⟨FOUR.T, Or.inl rfl⟩
  ne_univ h := absurd (h ▸ Set.mem_univ FOUR.U) (by decide)
  inf_mem_iff {a b} := by revert a b; decide
  sup_mem_iff {a b} := by revert a b; decide

instance : DecidablePred (· ∈ fdeFilter) :=
  λ x => inferInstanceAs (Decidable (x = FOUR.T ∨ x = FOUR.I))

/-- The bilattice `SIXTEEN = FOUR ⊙ FOUR` of Figure 6 ([fitting-2021] Example 8.10.5). -/
abbrev SIXTEEN := FOUR ⊙ FOUR


/-- `FDE`'s strict/tolerant counterpart validates exactly the sequents of `FDE`
([fitting-2021] Example 8.10.5). -/
theorem fde_stValid_iff {α : Type*} (Γ Δ : List (Fml α)) :
    STValid fdeFilter.prod Γ Δ ↔ LValid fdeFilter Γ Δ :=
  stValid_prod_iff fdeFilter Γ Δ

/-- Not every value is exact, consistent or anticonsistent: `⟨⊥, ⊤⟩` and `⟨⊤, ⊥⟩` of `SIXTEEN` are
none ([fitting-2021] §8.5, Example 8.10.5). -/
theorem sixteen_neither :
    ¬ IsConsistent (mk FOUR.U FOUR.I : SIXTEEN) ∧
      ¬ IsAnticonsistent (mk FOUR.U FOUR.I : SIXTEEN) ∧
      ¬ IsConsistent (mk FOUR.I FOUR.U : SIXTEEN) ∧
      ¬ IsAnticonsistent (mk FOUR.I FOUR.U : SIXTEEN) := by
  simp only [Evidential.isConsistent_iff, Evidential.isAnticonsistent_iff]
  decide

end Examples

end Fitting2021
