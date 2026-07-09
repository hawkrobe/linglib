import Linglib.Core.Logic.Bilattice.Basic

/-!
# Fitting 2021: strict/tolerant logics from logical bilattices
[fitting-2021]

[fitting-2021] generalizes the strict/tolerant phenomenon of
[cobreros-etal-2012] — `ST` has exactly classical logic's
consequence relation yet differs at the metaconsequence level — from three
truth values to any *logical bilattice*: an interlaced bilattice with negation
and conflation together with a prime bifilter `F` of designated values (the
designated-value theory of [arieli-avron-1996], [arieli-avron-1998]). From
such a pair, two logics arise ([fitting-2021] Def 8.7.1): `ST⟨B,F⟩` runs
valuations over the *anticonsistent* values with strict (exact designated)
premises and tolerant (anticonsistent designated) conclusions; `C⟨B,F⟩` — the
classical-like logic — runs valuations over the *exact* values.

The chapter's central results, formalized here over the
`Core.Logic.Bilattice` substrate:

* **`stValid_iff_cValid`** ([fitting-2021] Prop 8.7.2): `ST⟨B,F⟩` and
  `C⟨B,F⟩` validate exactly the same sequents. (Both directions are proved
  directly: right-to-left builds an exact valuation knowledge-below the given
  anticonsistent one by the interpolation lemma and transports along
  knowledge-monotonicity, rather than contraposing as in the chapter.)
* **`cut_cSatisfies` / `cut_not_local_stValid`** ([fitting-2021] Prop 8.7.3):
  the cut scheme is locally valid in `C⟨B,F⟩` but fails in `ST⟨B,F⟩` — the
  two logics differ at the metaconsequence level. The countermodel sends a
  letter to the knowledge top: designated and anticonsistent but not exact.
* **the `FOUR` instance** ([fitting-2021] Example 8.7.4): `FOUR`'s exact
  values are `{F, T}`, its anticonsistent values `{F, T, I}`, and `{T, I}` is
  a prime bifilter; the resulting pair is the original
  [cobreros-etal-2012] `ST` alongside classical logic, so the
  collapse and the cut failure specialize to the classic case.

The §8.8–8.10 extension — every non-distributive logical De Morgan algebra
generates a strict/tolerant counterpart via the product `L ⊙ L` — remains
TODO; its bilattice ingredients (`Product`, the diagonal `Negation` instance,
factor recovery) are already in the substrate.
-/

open Bilattice

namespace Fitting2021

variable {B α : Type*}

/-- Formulas over propositional letters ([fitting-2021] Def 8.6.1):
conjunction, disjunction, negation — no implication. -/
inductive Fml (α : Type*) where
  | atom (p : α)
  | and (φ ψ : Fml α)
  | or (φ ψ : Fml α)
  | not (φ : Fml α)

section Eval

variable [Lattice B] [Lattice (Know B)] [Negation B]

/-- Valuation extension ([fitting-2021] Def 8.6.2). -/
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

/-- Anticonsistent valuations evaluate to anticonsistent values
([fitting-2021] Prop 8.6.3). -/
theorem eval_isAnticonsistent {v : α → B} (hv : ∀ p, IsAnticonsistent (v p)) :
    ∀ φ : Fml α, IsAnticonsistent (φ.eval v)
  | .atom p => hv p
  | .and φ ψ => (eval_isAnticonsistent hv φ).inf (eval_isAnticonsistent hv ψ)
  | .or φ ψ => (eval_isAnticonsistent hv φ).sup (eval_isAnticonsistent hv ψ)
  | .not φ => (eval_isAnticonsistent hv φ).neg

omit [Conflation B] [NegConfComm B] in
/-- Evaluation is knowledge-monotone in the valuation
([fitting-2021] Prop 8.6.4). -/
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

/-- A prime bifilter: a proper nonempty subset that is a prime filter for both
the truth and the knowledge lattice operations ([fitting-2021] Def 8.6.5,
generalizing the designated values `{t, ⊤}` of `FOUR` per
[arieli-avron-1996], [arieli-avron-1998]). -/
structure PrimeBifilter (B : Type*) [Lattice B] [Lattice (Know B)] where
  /-- The designated values. -/
  carrier : Set B
  nonempty : carrier.Nonempty
  ne_univ : carrier ≠ Set.univ
  inf_mem_iff {a b : B} : a ⊓ b ∈ carrier ↔ a ∈ carrier ∧ b ∈ carrier
  kInf_mem_iff {a b : B} : (a ⊗ b : B) ∈ carrier ↔ a ∈ carrier ∧ b ∈ carrier
  sup_mem_iff {a b : B} : a ⊔ b ∈ carrier ↔ a ∈ carrier ∨ b ∈ carrier
  kSup_mem_iff {a b : B} : (a ⊕ b : B) ∈ carrier ↔ a ∈ carrier ∨ b ∈ carrier

instance : Membership B (PrimeBifilter B) := ⟨fun F a => a ∈ F.carrier⟩

/-- Prime bifilters are upward closed in the knowledge order
([fitting-2021] Prop 8.6.6). -/
theorem PrimeBifilter.mem_of_kLE (F : PrimeBifilter B) {a b : B} (ha : a ∈ F)
    (h : a ≤ₖ b) : b ∈ F := by
  have hab : (a ⊕ b : B) = b :=
    toKnow.injective (by simpa only [toKnow_kSup] using sup_eq_right.mpr h)
  exact hab ▸ F.kSup_mem_iff.mpr (Or.inl ha)

/-- Prime bifilters are upward closed in the truth order
([fitting-2021] Prop 8.6.6). -/
theorem PrimeBifilter.mem_of_le (F : PrimeBifilter B) {a b : B} (ha : a ∈ F)
    (h : a ≤ b) : b ∈ F :=
  sup_eq_right.mpr h ▸ F.sup_mem_iff.mpr (Or.inl ha)

end Bifilter

/-! ### The strict/tolerant and classical logics of a logical bilattice -/

section Logics

variable [Lattice B] [Lattice (Know B)] [Negation B] [Conflation B]

/-- Strictly designated: designated and exact ([fitting-2021] Def 8.7.1). -/
def StrictlyDesignated (F : PrimeBifilter B) (a : B) : Prop := a ∈ F ∧ IsExact a

/-- Tolerantly designated: designated and anticonsistent
([fitting-2021] Def 8.7.1). -/
def TolerantlyDesignated (F : PrimeBifilter B) (a : B) : Prop :=
  a ∈ F ∧ IsAnticonsistent a

/-- A valuation satisfies a sequent strict-to-tolerantly: if every premise is
strictly designated, some conclusion is tolerantly designated. -/
def STSatisfies (F : PrimeBifilter B) (v : α → B) (Γ Δ : List (Fml α)) : Prop :=
  (∀ φ ∈ Γ, StrictlyDesignated F (φ.eval v)) →
    ∃ ψ ∈ Δ, TolerantlyDesignated F (ψ.eval v)

/-- A valuation satisfies a sequent strictly on both sides. -/
def CSatisfies (F : PrimeBifilter B) (v : α → B) (Γ Δ : List (Fml α)) : Prop :=
  (∀ φ ∈ Γ, StrictlyDesignated F (φ.eval v)) →
    ∃ ψ ∈ Δ, StrictlyDesignated F (ψ.eval v)

/-- `ST⟨B,F⟩` validity ([fitting-2021] Def 8.7.1): over valuations into the
anticonsistent values, strict premises entail a tolerant conclusion. -/
def STValid (F : PrimeBifilter B) (Γ Δ : List (Fml α)) : Prop :=
  ∀ v : α → B, (∀ p, IsAnticonsistent (v p)) → STSatisfies F v Γ Δ

/-- `C⟨B,F⟩` validity ([fitting-2021] Def 8.7.1): over valuations into the
exact values, strict premises entail a strict conclusion. -/
def CValid (F : PrimeBifilter B) (Γ Δ : List (Fml α)) : Prop :=
  ∀ v : α → B, (∀ p, IsExact (v p)) → CSatisfies F v Γ Δ

variable [Interlaced B] [NegConfComm B]

/-- **[fitting-2021] Prop 8.7.2**: the strict/tolerant and classical logics of
a logical bilattice validate exactly the same sequents. Right-to-left replaces
the chapter's contraposition: given an anticonsistent valuation, choose an
exact valuation knowledge-below it (interpolation), win there classically, and
transport the witness up along knowledge-monotonicity and bifilter closure. -/
theorem stValid_iff_cValid (F : PrimeBifilter B) (Γ Δ : List (Fml α)) :
    STValid F Γ Δ ↔ CValid F Γ Δ := by
  constructor
  · intro hST v hv hΓ
    obtain ⟨ψ, hψΔ, hψF, _⟩ := hST v (fun p => (hv p).isAnticonsistent) hΓ
    exact ⟨ψ, hψΔ, hψF, eval_isExact hv ψ⟩
  · intro hC v hv hΓ
    choose v' hexact hle using fun p => (hv p).exists_exact_kLE
    have hmono : ∀ φ : Fml α, φ.eval v' ≤ₖ φ.eval v := eval_kLE_eval hle
    have hΓ' : ∀ φ ∈ Γ, StrictlyDesignated F (φ.eval v') := fun φ hφ => by
      have hx := hΓ φ hφ
      have heq : φ.eval v' = φ.eval v :=
        (eval_isExact hexact φ).eq_of_kLE hx.2 (hmono φ)
      rw [heq]; exact hx
    obtain ⟨ψ, hψΔ, hψF, _⟩ := hC v' hexact hΓ'
    exact ⟨ψ, hψΔ, F.mem_of_kLE hψF (hmono ψ), eval_isAnticonsistent hv ψ⟩

omit [Interlaced B] [NegConfComm B] in
/-- Cut is locally valid in `C⟨B,F⟩` ([fitting-2021] Prop 8.7.3): any
valuation satisfying both premises of a cut instance satisfies its
conclusion. -/
theorem cut_cSatisfies (F : PrimeBifilter B) {Γ Δ : List (Fml α)} {A : Fml α}
    {v : α → B} (h₁ : CSatisfies F v (A :: Γ) Δ) (h₂ : CSatisfies F v Γ (A :: Δ)) :
    CSatisfies F v Γ Δ := by
  intro hΓ
  obtain ⟨ψ, hψ, hd⟩ := h₂ hΓ
  rcases List.mem_cons.mp hψ with rfl | hψΔ
  · exact h₁ fun φ hφ => by
      rcases List.mem_cons.mp hφ with rfl | h
      exacts [hd, hΓ _ h]
  · exact ⟨ψ, hψΔ, hd⟩

variable [BoundedOrder (Know B)]

omit [Interlaced B] [NegConfComm B] in
/-- **[fitting-2021] Prop 8.7.3, `ST` half**: the cut scheme fails locally in
`ST⟨B,F⟩` (for a nontrivial knowledge order). The countermodel sends a letter
to the knowledge top — designated and anticonsistent, but not exact — so both
cut premises hold while the empty conclusion fails. -/
theorem cut_not_local_stValid (F : PrimeBifilter B) (p : α)
    (hbt : (⊥ : Know B) ≠ ⊤) :
    ¬ ∀ v : α → B, (∀ q, IsAnticonsistent (v q)) →
      STSatisfies F v [.atom p] [] → STSatisfies F v [] [.atom p] →
      STSatisfies F v ([] : List (Fml α)) [] := by
  intro h
  set kT : B := ofKnow (⊤ : Know B) with hkT
  have hle_top : ∀ x : B, x ≤ₖ kT := fun x => by
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
  have hfinal := h (fun _ => kT) (fun _ => hanti)
    (fun hΓ => absurd (hΓ _ (List.Mem.head _)).2 hnexact)
    (fun _ => ⟨.atom p, List.Mem.head _, hmem, hanti⟩)
  obtain ⟨ψ, hψ, -⟩ := hfinal (fun φ hφ => nomatch hφ)
  exact nomatch hψ

end Logics

/-! ### The `FOUR` instance ([fitting-2021] Example 8.7.4)

Belnap's `FOUR` with the designated values `{t, ⊤}` is the paradigm logical
bilattice: its exact values are the classical `{F, T}`, its anticonsistent
values `{F, T, I}` (Priest's LP space), and the resulting logic pair is the
original strict/tolerant logic of [cobreros-etal-2012] alongside classical
logic. -/

section FOURInstance

private theorem four_conf_conf : ∀ a : FOUR, FOUR.conf (FOUR.conf a) = a := by decide
private theorem four_conf_le : ∀ a b : FOUR, a ≤ b → FOUR.conf a ≤ FOUR.conf b := by
  decide
private theorem four_conf_kLE : ∀ a b : FOUR, a ≤ₖ b → FOUR.conf b ≤ₖ FOUR.conf a := by
  decide

/-- Boolean-complement conflation makes `FOUR` a bilattice with conflation. -/
instance : Conflation FOUR where
  conf := FOUR.conf
  conf_conf := four_conf_conf
  conf_le_conf {a b} h := four_conf_le a b h
  conf_kLE_conf {a b} h := four_conf_kLE a b h

/-- Negation and conflation commute on `FOUR`. -/
instance : NegConfComm FOUR where
  neg_conf := by decide

/-- `FOUR`'s exact values are the classical `{F, T}`
([fitting-2021] Example 8.7.4). -/
theorem four_isExact_iff : ∀ x : FOUR, IsExact x ↔ x = FOUR.F ∨ x = FOUR.T := by
  decide

/-- `FOUR`'s anticonsistent values are `{F, T, I}` — Priest's LP value space
([fitting-2021] Example 8.7.4). -/
theorem four_isAnticonsistent_iff :
    ∀ x : FOUR, IsAnticonsistent x ↔ x = FOUR.F ∨ x = FOUR.T ∨ x = FOUR.I := by
  decide

private theorem four_bif_inf : ∀ a b : FOUR,
    (a ⊓ b = FOUR.T ∨ a ⊓ b = FOUR.I) ↔
      ((a = FOUR.T ∨ a = FOUR.I) ∧ (b = FOUR.T ∨ b = FOUR.I)) := by decide
private theorem four_bif_kInf : ∀ a b : FOUR,
    ((a ⊗ b : FOUR) = FOUR.T ∨ (a ⊗ b : FOUR) = FOUR.I) ↔
      ((a = FOUR.T ∨ a = FOUR.I) ∧ (b = FOUR.T ∨ b = FOUR.I)) := by decide
private theorem four_bif_sup : ∀ a b : FOUR,
    (a ⊔ b = FOUR.T ∨ a ⊔ b = FOUR.I) ↔
      ((a = FOUR.T ∨ a = FOUR.I) ∨ (b = FOUR.T ∨ b = FOUR.I)) := by decide
private theorem four_bif_kSup : ∀ a b : FOUR,
    ((a ⊕ b : FOUR) = FOUR.T ∨ (a ⊕ b : FOUR) = FOUR.I) ↔
      ((a = FOUR.T ∨ a = FOUR.I) ∨ (b = FOUR.T ∨ b = FOUR.I)) := by decide

/-- The designated values `{t, ⊤}` of `FOUR` form a prime bifilter
([fitting-2021] Example 8.7.4; the designated-value choice of
[arieli-avron-1996]). -/
def fourBifilter : PrimeBifilter FOUR where
  carrier := {x | x = FOUR.T ∨ x = FOUR.I}
  nonempty := ⟨FOUR.T, Or.inl rfl⟩
  ne_univ h := by
    have : FOUR.U ∈ ({x | x = FOUR.T ∨ x = FOUR.I} : Set FOUR) :=
      h ▸ Set.mem_univ FOUR.U
    exact absurd this (by decide)
  inf_mem_iff {a b} := four_bif_inf a b
  kInf_mem_iff {a b} := four_bif_kInf a b
  sup_mem_iff {a b} := four_bif_sup a b
  kSup_mem_iff {a b} := four_bif_kSup a b

/-- The original strict/tolerant collapse ([cobreros-etal-2012], via
[fitting-2021] Example 8.7.4): over `FOUR` with designated `{t, ⊤}`, `ST` and
classical logic validate exactly the same sequents. -/
theorem four_stValid_iff_cValid {α : Type*} (Γ Δ : List (Fml α)) :
    STValid fourBifilter Γ Δ ↔ CValid fourBifilter Γ Δ :=
  stValid_iff_cValid fourBifilter Γ Δ

/-- And the pair separates at the metaconsequence level: cut fails locally in
`ST` over `FOUR`. -/
theorem four_cut_not_local {α : Type*} (p : α) :
    ¬ ∀ v : α → FOUR, (∀ q, IsAnticonsistent (v q)) →
      STSatisfies fourBifilter v [.atom p] [] →
      STSatisfies fourBifilter v [] [.atom p] →
      STSatisfies fourBifilter v ([] : List (Fml α)) [] :=
  cut_not_local_stValid fourBifilter p (by decide)

end FOURInstance

end Fitting2021
