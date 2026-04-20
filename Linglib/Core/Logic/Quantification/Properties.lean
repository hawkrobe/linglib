import Linglib.Core.Logic.Quantification.Defs

/-!
# Generalized Quantifier Properties — Theorems
@cite{barwise-cooper-1981} @cite{keenan-stavi-1986} @cite{peters-westerstahl-2006} @cite{van-benthem-1984} @cite{van-benthem-1986} @cite{icard-2012}

Theorems about GQ properties: duality, conservativity/symmetry/strength,
left monotonicity and smoothness, Boolean closure, type ⟨1⟩ theorems,
van Benthem characterization, and entailment-signature bridge.
-/

namespace Core.Quantification

variable {α : Type*}

-- ============================================================================
-- §4 Duality Theorems
-- ============================================================================

/-- Outer negation reverses scope monotonicity: mon↑ → mon↓. B&C Theorem C9. -/
theorem outerNeg_up_to_down (q : GQ α)
    (h : ScopeUpwardMono q) : ScopeDownwardMono (outerNeg q) := by
  intro R S S' hSS' hNeg hQS
  exact hNeg (h R S S' hSS' hQS)

/-- Outer negation reverses scope monotonicity: mon↓ → mon↑. B&C Theorem C9. -/
theorem outerNeg_down_to_up (q : GQ α)
    (h : ScopeDownwardMono q) : ScopeUpwardMono (outerNeg q) := by
  intro R S S' hSS' hNeg hQS'
  exact hNeg (h R S S' hSS' hQS')

/-- Inner negation reverses scope monotonicity: mon↑ → mon↓ (B&C §4.11). -/
theorem innerNeg_up_to_down (q : GQ α)
    (h : ScopeUpwardMono q) : ScopeDownwardMono (innerNeg q) := by
  intro R S S' hSS' hInner
  exact h R (fun x => ¬ S' x) (fun x => ¬ S x) (fun x hNS' hSx => hNS' (hSS' x hSx)) hInner

/-- Inner negation reverses scope monotonicity: mon↓ → mon↑ (B&C §4.11). -/
theorem innerNeg_down_to_up (q : GQ α)
    (h : ScopeDownwardMono q) : ScopeUpwardMono (innerNeg q) := by
  intro R S S' hSS' hInner
  exact h R (fun x => ¬ S' x) (fun x => ¬ S x) (fun x hNS' hSx => hNS' (hSS' x hSx)) hInner

/-- Outer negation reverses restrictor monotonicity: mon↑ → mon↓. -/
theorem outerNeg_restrictorUp_to_down (q : GQ α)
    (h : RestrictorUpwardMono q) : RestrictorDownwardMono (outerNeg q) := by
  intro R R' S hRR' hNeg hQR
  exact hNeg (h R R' S hRR' hQR)

/-- Outer negation reverses restrictor monotonicity: mon↓ → mon↑. -/
theorem outerNeg_restrictorDown_to_up (q : GQ α)
    (h : RestrictorDownwardMono q) : RestrictorUpwardMono (outerNeg q) := by
  intro R R' S hRR' hNeg hQR'
  exact hNeg (h R R' S hRR' hQR')

/-- Outer negation is involutive: ~~Q = Q. (Uses propositional extensionality.) -/
theorem outerNeg_involution (q : GQ α) : outerNeg (outerNeg q) = q := by
  funext R S; simp [outerNeg]

/-- Inner negation is involutive: Q~~ = Q. (Uses propositional extensionality.) -/
theorem innerNeg_involution (q : GQ α) : innerNeg (innerNeg q) = q := by
  funext R S; simp [innerNeg]

/-- Dual is involutive: Q̌̌ = Q. -/
theorem dualQ_involution (q : GQ α) : dualQ (dualQ q) = q := by
  funext R S; simp [dualQ, outerNeg, innerNeg]

-- §2.4 QuantityInvariant closure --

/-- Outer negation preserves QuantityInvariant: if Q is bijection-invariant,
    so is ~Q. -/
theorem quantityInvariant_outerNeg (q : GQ α)
    (h : QuantityInvariant q) : QuantityInvariant (outerNeg q) := by
  intro A B A' B' f hBij hA hB
  simp only [outerNeg, not_iff_not]
  exact h A B A' B' f hBij hA hB

/-- Inner negation preserves QuantityInvariant: if Q is bijection-invariant,
    so is Q~. -/
theorem quantityInvariant_innerNeg (q : GQ α)
    (h : QuantityInvariant q) : QuantityInvariant (innerNeg q) := by
  intro A B A' B' f hBij hA hB
  simp only [innerNeg]
  exact h A (fun x => ¬ B x) A' (fun x => ¬ B' x) f hBij hA
    (fun x => not_congr (hB x))

/-- Dual preserves QuantityInvariant. -/
theorem quantityInvariant_dualQ (q : GQ α)
    (h : QuantityInvariant q) : QuantityInvariant (dualQ q) :=
  quantityInvariant_outerNeg _ (quantityInvariant_innerNeg _ h)

/-- Meet preserves QuantityInvariant. -/
theorem quantityInvariant_gqMeet (f g : GQ α)
    (hf : QuantityInvariant f) (hg : QuantityInvariant g) :
    QuantityInvariant (gqMeet f g) := by
  intro A B A' B' σ hBij hA hB
  simp only [gqMeet]
  exact and_congr (hf A B A' B' σ hBij hA hB) (hg A B A' B' σ hBij hA hB)

/-- Conservative + intersection condition → symmetric (B&C Theorem C5).
    Proof: by conservativity Q(A,B) = Q(A, A∩B) and Q(B,A) = Q(B, B∩A);
    both have the same restrictor∩scope = A∩B, so intersection condition
    equates them. -/
theorem intersection_conservative_symmetric (q : GQ α)
    (hCons : Conservative q) (hInt : IntersectionCondition q) :
    QSymmetric q := by
  intro R S
  rw [hCons R S, hCons S R]
  apply hInt
  intro x
  exact ⟨fun ⟨_, hR, hS⟩ => ⟨hS, hS, hR⟩, fun ⟨_, hS, hR⟩ => ⟨hR, hR, hS⟩⟩

/-- Scope-downward monotonicity is equivalent to scope-upward monotonicity
    of the inner negation (co-property characterization, P&W §3.2.4). -/
theorem co_property_mono (q : GQ α) :
    ScopeDownwardMono q ↔ ScopeUpwardMono (innerNeg q) := by
  constructor
  · exact innerNeg_down_to_up q
  · intro h
    have h' := innerNeg_up_to_down (innerNeg q) h
    rw [innerNeg_involution] at h'
    exact h'

-- ============================================================================
-- §5 Conservativity, Symmetry, and Strength
-- ============================================================================

/-- Under conservativity, symmetric ↔ intersective (P&W Ch.6 Fact 1).
    This is the single most important bridge theorem — it explains why
    weak determiners allow there-insertion. -/
theorem conserv_symm_iff_int (q : GQ α) (hCons : Conservative q) :
    QSymmetric q ↔ IntersectionCondition q := by
  constructor
  · intro hSym R S R' S' hEq
    have step_RS : q R S ↔ q (fun x => R x ∧ S x) (fun x => R x ∧ S x) := by
      calc q R S
          ↔ q R (fun x => R x ∧ S x) := hCons R S
        _ ↔ q (fun x => R x ∧ S x) R := hSym R (fun x => R x ∧ S x)
        _ ↔ q (fun x => R x ∧ S x) (fun x => (R x ∧ S x) ∧ R x) :=
            hCons (fun x => R x ∧ S x) R
        _ ↔ q (fun x => R x ∧ S x) (fun x => R x ∧ S x) := by
            congr! 2 with x; tauto
    have step_R'S' : q R' S' ↔ q (fun x => R' x ∧ S' x) (fun x => R' x ∧ S' x) := by
      calc q R' S'
          ↔ q R' (fun x => R' x ∧ S' x) := hCons R' S'
        _ ↔ q (fun x => R' x ∧ S' x) R' := hSym R' (fun x => R' x ∧ S' x)
        _ ↔ q (fun x => R' x ∧ S' x) (fun x => (R' x ∧ S' x) ∧ R' x) :=
            hCons (fun x => R' x ∧ S' x) R'
        _ ↔ q (fun x => R' x ∧ S' x) (fun x => R' x ∧ S' x) := by
            congr! 2 with x; tauto
    rw [step_RS, step_R'S']
    have hFun : (fun x => R x ∧ S x) = (fun x => R' x ∧ S' x) :=
      funext fun x => propext (hEq x)
    rw [hFun]
  · exact intersection_conservative_symmetric q hCons

/-- Non-trivial symmetric quantifiers are not positive strong (P&W Ch.6 Fact 7). -/
theorem symm_not_positive_strong (q : GQ α) (hCons : Conservative q)
    (hSym : QSymmetric q)
    (hNontrivF : ∃ R S, ¬ q R S) :
    ¬ PositiveStrong q := by
  intro hPos
  obtain ⟨R', S', hF⟩ := hNontrivF
  have hInt := (conserv_symm_iff_int q hCons).mp hSym
  have hSame : q (fun x => R' x ∧ S' x) (fun x => R' x ∧ S' x) ↔ q R' S' := by
    apply hInt; intro x; tauto
  exact hF (hSame.mp (hPos _))

/-- Conservativity of a GQ is equivalent to its restricted quantifiers
    living on their restrictors (P&W §3.2.2). -/
theorem conservative_iff_livesOn (q : GQ α) :
    Conservative q ↔ ∀ A, LivesOn (restrict q A) A := by
  unfold Conservative LivesOn restrict
  exact ⟨fun h A B => h A B, fun h R S => h R S⟩

/-- Every `GQ α` satisfies Extension: the representation is universe-free. -/
theorem extension_trivial (q : GQ α) : Extension q := trivial

/-- @cite{van-benthem-1984}: Under Extension (free for GQ α), Conservativity
    is equivalent to LivesOn — the restricted quantifier depends only on
    elements of its restrictor. -/
theorem vanBenthem_cons_ext (q : GQ α) :
    Extension q → (Conservative q ↔ ∀ A, LivesOn (restrict q A) A) :=
  fun _ => conservative_iff_livesOn q

-- ============================================================================
-- §5b Basic Left Monotonicity and Smoothness (@cite{peters-westerstahl-2006} §5.5-5.6)
-- ============================================================================

/-- Persistence → ↑_SE Mon. -/
theorem restrictorUpMono_to_upSE (q : GQ α)
    (h : RestrictorUpwardMono q) : UpSEMon q :=
  fun R S R' hSub _ hQ => h R R' S hSub hQ

/-- Persistence → ↑_SW Mon. -/
theorem restrictorUpMono_to_upSW (q : GQ α)
    (h : RestrictorUpwardMono q) : UpSWMon q :=
  fun R S R' hSub _ hQ => h R R' S hSub hQ

/-- ↑_SW Mon ∧ ↑_SE Mon → Persistence (@cite{peters-westerstahl-2006} Prop 6). -/
theorem upSW_upSE_to_restrictorUpMono (q : GQ α)
    (hSW : UpSWMon q) (hSE : UpSEMon q) : RestrictorUpwardMono q := by
  intro R R' S hSub hQ
  classical
  let R'' : α → Prop := fun x => R x ∨ (R' x ∧ ¬ S x)
  have step1 : q R'' S := by
    apply hSW R S R'' (fun x hRx => Or.inl hRx) ?_ hQ
    intro x hR''x hSx
    rcases hR''x with h | h
    · exact h
    · exact absurd hSx h.2
  apply hSE R'' S R' (fun x hR''x => ?_) (fun x hR'x hNS => ?_) step1
  · rcases hR''x with h | h
    · exact hSub x h
    · exact h.1
  · exact Or.inr ⟨hR'x, hNS⟩

/-- Persistence ↔ ↑_SW Mon ∧ ↑_SE Mon (@cite{peters-westerstahl-2006} Prop 6). -/
theorem persistent_iff_upSW_and_upSE (q : GQ α) :
    RestrictorUpwardMono q ↔ UpSWMon q ∧ UpSEMon q :=
  ⟨fun h => ⟨restrictorUpMono_to_upSW q h, restrictorUpMono_to_upSE q h⟩,
   fun ⟨hSW, hSE⟩ => upSW_upSE_to_restrictorUpMono q hSW hSE⟩

/-- Anti-persistence → ↓_NW Mon. -/
theorem restrictorDownMono_to_downNW (q : GQ α)
    (h : RestrictorDownwardMono q) : DownNWMon q :=
  fun R S R' hSub _ hQ => h R' R S hSub hQ

/-- Anti-persistence → ↓_NE Mon. -/
theorem restrictorDownMono_to_downNE (q : GQ α)
    (h : RestrictorDownwardMono q) : DownNEMon q :=
  fun R S R' hSub _ hQ => h R' R S hSub hQ

/-- ↓_NW Mon ∧ ↓_NE Mon → Anti-persistence. -/
theorem downNW_downNE_to_restrictorDownMono (q : GQ α)
    (hNW : DownNWMon q) (hNE : DownNEMon q) : RestrictorDownwardMono q := by
  intro R R' S hSub hQ
  classical
  let R'' : α → Prop := fun x => R x ∨ (R' x ∧ S x)
  have step1 : q R'' S := by
    apply hNE R' S R'' (fun x hR''x => ?_) (fun x hR'x hSx => ?_) hQ
    · rcases hR''x with h | h
      · exact hSub x h
      · exact h.1
    · exact Or.inr ⟨hR'x, hSx⟩
  apply hNW R'' S R (fun x hRx => Or.inl hRx) ?_ step1
  intro x hR''x hNS
  rcases hR''x with h | h
  · exact h
  · exact absurd h.2 hNS

/-- Anti-persistence ↔ ↓_NW Mon ∧ ↓_NE Mon. -/
theorem anti_persistent_iff_downNW_and_downNE (q : GQ α) :
    RestrictorDownwardMono q ↔ DownNWMon q ∧ DownNEMon q :=
  ⟨fun h => ⟨restrictorDownMono_to_downNW q h, restrictorDownMono_to_downNE q h⟩,
   fun ⟨hNW, hNE⟩ => downNW_downNE_to_restrictorDownMono q hNW hNE⟩

-- Prop 8: Negation rotates basic monotonicities

/-- Outer negation reverses ↑_SE to ↓_NW (@cite{peters-westerstahl-2006} Prop 8a). -/
theorem outerNeg_upSE_to_downNW (q : GQ α)
    (h : UpSEMon q) : DownNWMon (outerNeg q) := by
  intro R S R' hSub hDiff hNQ hQR'
  exact hNQ (h R' S R hSub hDiff hQR')

/-- Outer negation reverses ↓_NW to ↑_SE. -/
theorem outerNeg_downNW_to_upSE (q : GQ α)
    (h : DownNWMon q) : UpSEMon (outerNeg q) := by
  intro R S R' hSub hDiff hNQ hQR'
  exact hNQ (h R' S R hSub hDiff hQR')

/-- Outer negation reverses ↑_SW to ↓_NE. -/
theorem outerNeg_upSW_to_downNE (q : GQ α)
    (h : UpSWMon q) : DownNEMon (outerNeg q) := by
  intro R S R' hSub hDiff hNQ hQR'
  exact hNQ (h R' S R hSub hDiff hQR')

/-- Outer negation reverses ↓_NE to ↑_SW. -/
theorem outerNeg_downNE_to_upSW (q : GQ α)
    (h : DownNEMon q) : UpSWMon (outerNeg q) := by
  intro R S R' hSub hDiff hNQ hQR'
  exact hNQ (h R' S R hSub hDiff hQR')

/-- Inner negation switches ↓_NE ↔ ↓_NW (@cite{peters-westerstahl-2006} Prop 8b). -/
theorem innerNeg_downNE_to_downNW (q : GQ α)
    (h : DownNEMon q) : DownNWMon (innerNeg q) := by
  intro R S R' hSub hDiff hQ
  exact h R (fun x => ¬ S x) R' hSub
    (fun x hRx hNS => hDiff x hRx (fun hSx => hNS hSx)) hQ

/-- Inner negation switches ↓_NW ↔ ↓_NE. -/
theorem innerNeg_downNW_to_downNE (q : GQ α)
    (h : DownNWMon q) : DownNEMon (innerNeg q) := by
  intro R S R' hSub hDiff hQ
  exact h R (fun x => ¬ S x) R' hSub
    (fun x hRx hNNS => hDiff x hRx (Classical.not_not.mp hNNS)) hQ

/-- Inner negation switches ↑_SE ↔ ↑_SW. -/
theorem innerNeg_upSE_to_upSW (q : GQ α)
    (h : UpSEMon q) : UpSWMon (innerNeg q) := by
  intro R S R' hSub hDiff hQ
  exact h R (fun x => ¬ S x) R' hSub
    (fun x hR'x hNNS => hDiff x hR'x (Classical.not_not.mp hNNS)) hQ

/-- Inner negation switches ↑_SW ↔ ↑_SE. -/
theorem innerNeg_upSW_to_upSE (q : GQ α)
    (h : UpSWMon q) : UpSEMon (innerNeg q) := by
  intro R S R' hSub hDiff hQ
  exact h R (fun x => ¬ S x) R' hSub
    (fun x hR'x hNS => hDiff x hR'x (fun hSx => hNS hSx)) hQ

/-- Smooth ↔ outer negation is co-smooth (@cite{peters-westerstahl-2006} Prop 8a). -/
theorem smooth_iff_outerNeg_coSmooth (q : GQ α) :
    Smooth q ↔ CoSmooth (outerNeg q) :=
  ⟨fun ⟨hNE, hSE⟩ => ⟨outerNeg_upSE_to_downNW q hSE, outerNeg_downNE_to_upSW q hNE⟩,
   fun ⟨hNW, hSW⟩ => by
    rw [show q = outerNeg (outerNeg q) from (outerNeg_involution q).symm]
    exact ⟨outerNeg_upSW_to_downNE _ hSW, outerNeg_downNW_to_upSE _ hNW⟩⟩

/-- Smooth ↔ inner negation is co-smooth (@cite{peters-westerstahl-2006} Prop 8b). -/
theorem smooth_iff_innerNeg_coSmooth (q : GQ α) :
    Smooth q ↔ CoSmooth (innerNeg q) :=
  ⟨fun ⟨hNE, hSE⟩ => ⟨innerNeg_downNE_to_downNW q hNE, innerNeg_upSE_to_upSW q hSE⟩,
   fun ⟨hNW, hSW⟩ => by
    rw [show q = innerNeg (innerNeg q) from (innerNeg_involution q).symm]
    exact ⟨innerNeg_downNW_to_downNE _ hNW, innerNeg_upSW_to_upSE _ hSW⟩⟩

-- Prop 9: Smooth → Mon↑

/-- CONSERV ∧ Smooth → Mon↑ (@cite{peters-westerstahl-2006} Prop 9). -/
theorem smooth_conservative_scopeUpMono (q : GQ α)
    (hCons : Conservative q) (hSmooth : Smooth q) : ScopeUpwardMono q := by
  obtain ⟨hNE, hSE⟩ := hSmooth
  intro R S S' hSS' hQ
  classical
  let R' : α → Prop := fun x => R x ∧ (S x ∨ ¬ S' x)
  have hR'S : q R' S := by
    apply hNE R S R' (fun x hR'x => hR'x.1) (fun x hRx hSx => ⟨hRx, Or.inl hSx⟩) hQ
  have key : ∀ x, (R' x ∧ S' x) ↔ (R' x ∧ S x) := by
    intro x
    constructor
    · rintro ⟨hR'x, hS'x⟩
      refine ⟨hR'x, ?_⟩
      rcases hR'x.2 with hSx | hNS'x
      · exact hSx
      · exact absurd hS'x hNS'x
    · rintro ⟨hR'x, hSx⟩
      exact ⟨hR'x, hSS' x hSx⟩
  have hR'S' : q R' S' := by
    rw [hCons R' S']
    have : (fun x => R' x ∧ S' x) = (fun x => R' x ∧ S x) := funext fun x => propext (key x)
    rw [this]
    exact (hCons R' S).mp hR'S
  apply hSE R' S' R (fun x hR'x => hR'x.1) (fun x hRx hS'nS => ?_) hR'S'
  exact ⟨hRx, Or.inr hS'nS⟩

-- Prop 7: Symmetry ↔ ↑_SW + ↓_NE (under CONSERV)

/-- CONSERV ∧ QSymmetric → ↑_SW Mon ∧ ↓_NE Mon (@cite{peters-westerstahl-2006} Prop 7). -/
theorem symmetric_to_upSW_downNE (q : GQ α)
    (hCons : Conservative q) (hSym : QSymmetric q) :
    UpSWMon q ∧ DownNEMon q := by
  have toIntersect : ∀ A B : α → Prop,
      q A B ↔ q (fun x => A x ∧ B x) (fun x => A x ∧ B x) := by
    intro A B
    have h1 : q A B ↔ q A (fun x => A x ∧ B x) := hCons A B
    have h2 : q A (fun x => A x ∧ B x) ↔ q (fun x => A x ∧ B x) A :=
      hSym A (fun x => A x ∧ B x)
    have h3 : q (fun x => A x ∧ B x) A ↔
        q (fun x => A x ∧ B x) (fun x => (A x ∧ B x) ∧ A x) :=
      hCons (fun x => A x ∧ B x) A
    have h4 : (fun x => (A x ∧ B x) ∧ A x) = (fun x => A x ∧ B x) :=
      funext fun x => propext ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, h.1⟩⟩
    rw [h1, h2, h3, h4]
  have intersect_eq (R S R' : α → Prop)
      (hFwd : ∀ x, R x → S x → R' x)
      (hBwd : ∀ x, R' x → S x → R x) :
      (fun x => R x ∧ S x) = (fun x => R' x ∧ S x) := by
    funext x
    apply propext
    exact ⟨fun ⟨hRx, hSx⟩ => ⟨hFwd x hRx hSx, hSx⟩,
           fun ⟨hR'x, hSx⟩ => ⟨hBwd x hR'x hSx, hSx⟩⟩
  refine ⟨?_, ?_⟩
  · intro R S R' hSub hInt hQ
    rw [toIntersect R S] at hQ
    rw [intersect_eq R S R' (fun x hRx _ => hSub x hRx) hInt] at hQ
    rw [← toIntersect R' S] at hQ
    exact hQ
  · intro R S R' hSub hInt hQ
    rw [toIntersect R S] at hQ
    rw [intersect_eq R S R' hInt (fun x hR'x _ => hSub x hR'x)] at hQ
    rw [← toIntersect R' S] at hQ
    exact hQ

/-- ↑_SW Mon ∧ ↓_NE Mon → QSymmetric (under CONSERV). -/
theorem upSW_downNE_to_symmetric (q : GQ α)
    (hCons : Conservative q) (hUpSW : UpSWMon q) (hDownNE : DownNEMon q) :
    QSymmetric q := by
  intro A B
  constructor
  · intro hQ
    rw [hCons A B] at hQ
    have hABint : q (fun x => A x ∨ B x) (fun x => A x ∧ B x) := by
      apply hUpSW A (fun x => A x ∧ B x) (fun x => A x ∨ B x)
        (fun x hAx => Or.inl hAx) (fun x _ hIntx => hIntx.1) hQ
    have hBint : q B (fun x => A x ∧ B x) := by
      apply hDownNE (fun x => A x ∨ B x) (fun x => A x ∧ B x) B
        (fun x hBx => Or.inr hBx) (fun x _ hIntx => hIntx.2) hABint
    rw [hCons B A]
    have hCommSwap : (fun x => B x ∧ A x) = (fun x => A x ∧ B x) :=
      funext fun x => propext ⟨fun ⟨h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1⟩⟩
    rw [hCommSwap]
    exact hBint
  · intro hQ
    rw [hCons B A] at hQ
    have hBAint : q (fun x => B x ∨ A x) (fun x => B x ∧ A x) := by
      apply hUpSW B (fun x => B x ∧ A x) (fun x => B x ∨ A x)
        (fun x hBx => Or.inl hBx) (fun x _ hIntx => hIntx.1) hQ
    have hAint : q A (fun x => B x ∧ A x) := by
      apply hDownNE (fun x => B x ∨ A x) (fun x => B x ∧ A x) A
        (fun x hAx => Or.inr hAx) (fun x _ hIntx => hIntx.2) hBAint
    rw [hCons A B]
    have hCommSwap : (fun x => A x ∧ B x) = (fun x => B x ∧ A x) :=
      funext fun x => propext ⟨fun ⟨h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1⟩⟩
    rw [hCommSwap]
    exact hAint

/-- @cite{peters-westerstahl-2006} Prop 7: a CONSERV type ⟨1,1⟩ quantifier
    is symmetric iff it satisfies ↑_SW Mon and ↓_NE Mon. -/
theorem symmetric_iff_upSW_downNE (q : GQ α) (hCons : Conservative q) :
    QSymmetric q ↔ (UpSWMon q ∧ DownNEMon q) :=
  ⟨symmetric_to_upSW_downNE q hCons,
   fun ⟨h1, h2⟩ => upSW_downNE_to_symmetric q hCons h1 h2⟩

-- ============================================================================
-- §6 Boolean Closure (@cite{keenan-stavi-1986})
-- ============================================================================

/-- Conservativity is closed under complement. -/
theorem conservative_outerNeg (q : GQ α) (h : Conservative q) :
    Conservative (outerNeg q) := by
  intro R S; simp only [outerNeg, not_iff_not]; exact h R S

/-- Conservativity is closed under meet. -/
theorem conservative_gqMeet (f g : GQ α)
    (hf : Conservative f) (hg : Conservative g) :
    Conservative (gqMeet f g) := by
  intro R S; simp only [gqMeet]; exact and_congr (hf R S) (hg R S)

/-- Conservativity is closed under join. -/
theorem conservative_gqJoin (f g : GQ α)
    (hf : Conservative f) (hg : Conservative g) :
    Conservative (gqJoin f g) := by
  intro R S; simp only [gqJoin]; exact or_congr (hf R S) (hg R S)

/-- K&S (26): complement distributes over join via de Morgan. -/
theorem outerNeg_gqJoin (f g : GQ α) :
    outerNeg (gqJoin f g) = gqMeet (outerNeg f) (outerNeg g) := by
  funext R S; simp [outerNeg, gqJoin, gqMeet, not_or]

/-- K&S (26): complement distributes over meet via de Morgan. -/
theorem outerNeg_gqMeet (f g : GQ α) :
    outerNeg (gqMeet f g) = gqJoin (outerNeg f) (outerNeg g) := by
  funext R S
  simp only [outerNeg, gqMeet, gqJoin]
  exact propext not_and_or

/-- K&S PROP 6: Meet of scope-↑ functions is scope-↑. -/
theorem scopeUpMono_gqMeet (f g : GQ α)
    (hf : ScopeUpwardMono f) (hg : ScopeUpwardMono g) :
    ScopeUpwardMono (gqMeet f g) := by
  intro R S S' hSS' ⟨hfRS, hgRS⟩
  exact ⟨hf R S S' hSS' hfRS, hg R S S' hSS' hgRS⟩

/-- K&S PROP 6: Meet of scope-↓ functions is scope-↓. -/
theorem scopeDownMono_gqMeet (f g : GQ α)
    (hf : ScopeDownwardMono f) (hg : ScopeDownwardMono g) :
    ScopeDownwardMono (gqMeet f g) := by
  intro R S S' hSS' ⟨hfRS', hgRS'⟩
  exact ⟨hf R S S' hSS' hfRS', hg R S S' hSS' hgRS'⟩

/-- K&S PROP 6: Join of scope-↑ functions is scope-↑. -/
theorem scopeUpMono_gqJoin (f g : GQ α)
    (hf : ScopeUpwardMono f) (hg : ScopeUpwardMono g) :
    ScopeUpwardMono (gqJoin f g) := by
  intro R S S' hSS' h
  rcases h with hfRS | hgRS
  · exact Or.inl (hf R S S' hSS' hfRS)
  · exact Or.inr (hg R S S' hSS' hgRS)

/-- K&S PROP 3: Conservativity is preserved under adjectival restriction. -/
theorem conservative_adjRestrict (q : GQ α) (adj : α → Prop)
    (h : Conservative q) : Conservative (adjRestrict q adj) := by
  intro R S
  simp only [adjRestrict]
  rw [h (fun x => R x ∧ adj x) S, h (fun x => R x ∧ adj x) (fun x => R x ∧ S x)]
  have heq : (fun x => (R x ∧ adj x) ∧ R x ∧ S x) = (fun x => (R x ∧ adj x) ∧ S x) := by
    funext x; apply propext
    exact ⟨fun ⟨h1, _, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h2⟩ => ⟨h1, h1.1, h2⟩⟩
  rw [heq]

/-- K&S PROP 5: Scope-upward monotonicity is preserved under adjectival restriction. -/
theorem scopeUpMono_adjRestrict (q : GQ α) (adj : α → Prop)
    (h : ScopeUpwardMono q) : ScopeUpwardMono (adjRestrict q adj) := by
  intro R S S' hSS' hAdj
  exact h _ S S' hSS' hAdj

/-- K&S PROP 5: Scope-downward monotonicity is preserved under adjectival restriction. -/
theorem scopeDownMono_adjRestrict (q : GQ α) (adj : α → Prop)
    (h : ScopeDownwardMono q) : ScopeDownwardMono (adjRestrict q adj) := by
  intro R S S' hSS' hAdj
  exact h _ S S' hSS' hAdj

-- ============================================================================
-- §7 Type ⟨1⟩ Theorems (P&W Ch.2-3)
-- ============================================================================

/-- Montagovian individuals are upward closed (ultrafilter property). -/
theorem individual_upward_closed (a : α) (P P' : α → Prop)
    (h : ∀ x, P x → P' x) :
    individual a P → individual a P' := h a

/-- Montagovian individuals are closed under intersection. -/
theorem individual_meet_closed (a : α) (P Q : α → Prop) :
    individual a P → individual a Q →
    individual a (fun x => P x ∧ Q x) := fun hP hQ => ⟨hP, hQ⟩

-- ============================================================================
-- §8 @cite{van-benthem-1984} Characterization
-- ============================================================================

/-- @cite{van-benthem-1984} Theorem 3.1.1: Under conservativity, inclusion (⊆)
    is the only reflexive antisymmetric quantifier. -/
theorem vanBenthem_refl_antisym_is_inclusion (q : GQ α)
    (hCons : Conservative q) (hRefl : PositiveStrong q)
    (hAnti : QAntisymmetric q) :
    ∀ A B, q A B ↔ (∀ x, A x → B x) := by
  intro A B
  constructor
  · intro hQAB
    have h1 : q A (fun x => A x ∧ B x) := (hCons A B).mp hQAB
    have h2 : q (fun x => A x ∧ B x) A := by
      rw [hCons (fun x => A x ∧ B x) A]
      have hEq : (fun x => (A x ∧ B x) ∧ A x) = (fun x => A x ∧ B x) :=
        funext fun x => propext ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, h.1⟩⟩
      rw [hEq]; exact hRefl _
    have hEq := hAnti A (fun x => A x ∧ B x) h1 h2
    intro x hAx
    have hp : A x = (A x ∧ B x) := congr_fun hEq x
    exact ((iff_of_eq hp).mp hAx).2
  · intro hSub
    rw [hCons A B]
    have hEq : (fun x => A x ∧ B x) = A := by
      funext x; apply propext
      exact ⟨fun h => h.1, fun hAx => ⟨hAx, hSub x hAx⟩⟩
    rw [hEq]; exact hRefl A

/-- @cite{van-benthem-1984} Thm 4.1.1 (Zwarts): reflexive + transitive → MON↑. -/
theorem zwarts_refl_trans_scopeUp (q : GQ α)
    (hCons : Conservative q) (hRefl : PositiveStrong q)
    (hTrans : QTransitive q) : ScopeUpwardMono q := by
  intro R S S' hSS' hQRS
  have hQSS' : q S S' := by
    rw [hCons S S']
    have : (fun x => S x ∧ S' x) = S :=
      funext fun x => propext ⟨fun h => h.1, fun hS => ⟨hS, hSS' x hS⟩⟩
    rw [this]; exact hRefl S
  exact hTrans R S S' hQRS hQSS'

/-- @cite{van-benthem-1984} Thm 4.1.1 (Zwarts): reflexive + transitive → ↓MON. -/
theorem zwarts_refl_trans_restrictorDown (q : GQ α)
    (hCons : Conservative q) (hRefl : PositiveStrong q)
    (hTrans : QTransitive q) : RestrictorDownwardMono q := by
  intro R R' S hRR' hQR'S
  have hQRR' : q R R' := by
    rw [hCons R R']
    have : (fun x => R x ∧ R' x) = R :=
      funext fun x => propext ⟨fun h => h.1, fun hR => ⟨hR, hRR' x hR⟩⟩
    rw [this]; exact hRefl R
  exact hTrans R R' S hQRR' hQR'S

/-- @cite{van-benthem-1984} Thm 4.1.3 (Zwarts): for symmetric quantifiers,
    scope-↑ implies quasi-reflexive, under CONSERV. -/
theorem zwarts_sym_scopeUp_quasiRefl (q : GQ α)
    (hCons : Conservative q) (_hSym : QSymmetric q)
    (hUp : ScopeUpwardMono q) : QuasiReflexive q := by
  intro A B hQAB
  have h1 : q A (fun x => A x ∧ B x) := (hCons A B).mp hQAB
  exact hUp A (fun x => A x ∧ B x) A (fun x hx => hx.1) h1

/-- @cite{van-benthem-1984} Thm 4.1.3 (Zwarts): for symmetric quantifiers,
    scope-↓ implies quasi-universal, under CONSERV. -/
theorem zwarts_sym_scopeDown_quasiUniv (q : GQ α)
    (hCons : Conservative q) (_hSym : QSymmetric q)
    (hDown : ScopeDownwardMono q) : QuasiUniversal q := by
  intro A B hQAA
  rw [hCons A B]
  exact hDown A (fun x => A x ∧ B x) A (fun x hx => hx.1) hQAA

/-- Right-monotone quantifiers are right-continuous. -/
theorem scopeUpMono_rightContinuous (q : GQ α)
    (h : ScopeUpwardMono q) : RightContinuous q := by
  intro A B B₁ _ hB₁B _ hQ1 _
  exact h A B₁ B hB₁B hQ1

/-- @cite{van-benthem-1984} Thm 4.1.2: irreflexive + almost-connected → MON↓. -/
theorem irrefl_almostConn_scopeDown (q : GQ α)
    (hCons : Conservative q)
    (hIrrefl : NegativeStrong q)
    (hAC : AlmostConnected q) : ScopeDownwardMono q := by
  have hRefl : PositiveStrong (outerNeg q) := fun R => hIrrefl R
  have hTrans : QTransitive (outerNeg q) := by
    intro A B C hNAB hNBC
    intro hQAC
    rcases hAC A C B hQAC with h | h
    · exact hNAB h
    · exact hNBC h
  have hUp := zwarts_refl_trans_scopeUp (outerNeg q)
    (conservative_outerNeg q hCons) hRefl hTrans
  rw [← outerNeg_involution q]
  exact outerNeg_up_to_down (outerNeg q) hUp

/-- @cite{van-benthem-1984} Thm 4.1.2: irreflexive + almost-connected → ↑MON. -/
theorem irrefl_almostConn_restrictorUp (q : GQ α)
    (hCons : Conservative q)
    (hIrrefl : NegativeStrong q)
    (hAC : AlmostConnected q) : RestrictorUpwardMono q := by
  have hRefl : PositiveStrong (outerNeg q) := fun R => hIrrefl R
  have hTrans : QTransitive (outerNeg q) := by
    intro A B C hNAB hNBC
    intro hQAC
    rcases hAC A C B hQAC with h | h
    · exact hNAB h
    · exact hNBC h
  have hDown := zwarts_refl_trans_restrictorDown (outerNeg q)
    (conservative_outerNeg q hCons) hRefl hTrans
  intro R R' S hRR' hQ
  by_contra h
  exact (hDown R R' S hRR' h) hQ

-- ============================================================================
-- §8b — Asymmetry and Circularity
-- @cite{peters-westerstahl-2006} Ch 6.4
-- ============================================================================

/-- Asymmetric quantifiers are irreflexive. -/
theorem asymmetric_irreflexive (q : GQ α) (hAsym : QAsymmetric q) :
    QIrreflexive q := fun A hQAA => hAsym A A hQAA hQAA

/-- Asymmetric implies antisymmetric (vacuously). -/
theorem asymmetric_antisymmetric (q : GQ α) (hAsym : QAsymmetric q) :
    QAntisymmetric q := fun A B hAB hBA => absurd hBA (hAsym A B hAB)

/-- Circular + symmetric → quasi-reflexive. -/
theorem circular_symmetric_quasiRefl (q : GQ α)
    (hSym : QSymmetric q) (hCirc : QCircular q) :
    QuasiReflexive q := by
  intro A B hAB
  have hBA : q B A := (hSym A B).mp hAB
  exact hCirc A B A hAB hBA

/-- Circularity + reflexivity → symmetry. -/
theorem circular_reflexive_symmetric (q : GQ α)
    (hCirc : QCircular q) (hPS : PositiveStrong q) :
    QSymmetric q := by
  intro A B
  exact ⟨fun hAB => hCirc A A B (hPS A) hAB,
         fun hBA => hCirc B B A (hPS B) hBA⟩

/-- Piecewise involution swapping A\B ↔ B\A, fixing A∩B and the complement.
    Used to witness ISOM in the proof of `isom_asymmetric_eq_diff`. -/
private noncomputable def swapDiff [Fintype α] [DecidableEq α]
    (A B : α → Prop) [DecidablePred A] [DecidablePred B]
    (e : {x // A x ∧ ¬ B x} ≃ {x // B x ∧ ¬ A x}) :
    α → α := fun x =>
  if h : A x ∧ ¬ B x then (e ⟨x, h⟩).val
  else if h : B x ∧ ¬ A x then (e.symm ⟨x, h⟩).val
  else x

private lemma swapDiff_zone_AB [Fintype α] [DecidableEq α]
    {A B : α → Prop} [DecidablePred A] [DecidablePred B]
    {e : {x // A x ∧ ¬ B x} ≃ {x // B x ∧ ¬ A x}}
    {x : α} (h : A x ∧ ¬ B x) :
    swapDiff A B e x = (e ⟨x, h⟩).val := by
  simp only [swapDiff, dif_pos h]

private lemma swapDiff_zone_BA [Fintype α] [DecidableEq α]
    {A B : α → Prop} [DecidablePred A] [DecidablePred B]
    {e : {x // A x ∧ ¬ B x} ≃ {x // B x ∧ ¬ A x}}
    {x : α} (h : B x ∧ ¬ A x) :
    swapDiff A B e x = (e.symm ⟨x, h⟩).val := by
  unfold swapDiff; rw [dif_neg (fun hp => h.2 hp.1), dif_pos h]

private lemma swapDiff_zone_fix [Fintype α] [DecidableEq α]
    {A B : α → Prop} [DecidablePred A] [DecidablePred B]
    {e : {x // A x ∧ ¬ B x} ≃ {x // B x ∧ ¬ A x}}
    {x : α} (h1 : ¬ (A x ∧ ¬ B x))
    (h2 : ¬ (B x ∧ ¬ A x)) :
    swapDiff A B e x = x := by
  simp only [swapDiff, dif_neg h1, dif_neg h2]

private theorem swapDiff_involutive [Fintype α] [DecidableEq α]
    (A B : α → Prop) [DecidablePred A] [DecidablePred B]
    (e : {x // A x ∧ ¬ B x} ≃ {x // B x ∧ ¬ A x}) :
    Function.Involutive (swapDiff A B e) := by
  intro x
  by_cases hA : A x <;> by_cases hB : B x
  · have hf := swapDiff_zone_fix (fun h => h.2 hB) (fun h => h.2 hA) (e := e) (x := x)
    rw [hf, hf]
  · have hAB : A x ∧ ¬ B x := ⟨hA, hB⟩
    rw [swapDiff_zone_AB hAB]
    have hp := (e ⟨x, hAB⟩).prop
    rw [swapDiff_zone_BA hp]
    have : (⟨(e ⟨x, hAB⟩).val, hp⟩ : {x // B x ∧ ¬ A x}) = e ⟨x, hAB⟩ :=
      Subtype.ext rfl
    rw [this]; exact congrArg Subtype.val (e.symm_apply_apply ⟨x, hAB⟩)
  · have hBA : B x ∧ ¬ A x := ⟨hB, hA⟩
    rw [swapDiff_zone_BA hBA]
    have hp := (e.symm ⟨x, hBA⟩).prop
    rw [swapDiff_zone_AB hp]
    have : (⟨(e.symm ⟨x, hBA⟩).val, hp⟩ : {x // A x ∧ ¬ B x}) =
      e.symm ⟨x, hBA⟩ := Subtype.ext rfl
    rw [this]; exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hBA⟩)
  · have hf := swapDiff_zone_fix (fun h => hA h.1) (fun h => hB h.1) (e := e) (x := x)
    rw [hf, hf]

private theorem swapDiff_swaps_A [Fintype α] [DecidableEq α]
    (A B : α → Prop) [DecidablePred A] [DecidablePred B]
    (e : {x // A x ∧ ¬ B x} ≃ {x // B x ∧ ¬ A x})
    (x : α) : A (swapDiff A B e x) ↔ B x := by
  by_cases hA : A x <;> by_cases hB : B x
  · rw [swapDiff_zone_fix (fun h => h.2 hB) (fun h => h.2 hA)]
    exact ⟨fun _ => hB, fun _ => hA⟩
  · rw [swapDiff_zone_AB ⟨hA, hB⟩]
    have hp := (e ⟨x, ⟨hA, hB⟩⟩).prop
    exact ⟨fun hAv => absurd hAv hp.2, fun hBx => absurd hBx hB⟩
  · rw [swapDiff_zone_BA ⟨hB, hA⟩]
    exact ⟨fun _ => hB, fun _ => (e.symm ⟨x, ⟨hB, hA⟩⟩).prop.1⟩
  · rw [swapDiff_zone_fix (fun h => hA h.1) (fun h => hB h.1)]
    exact ⟨fun hAv => absurd hAv hA, fun hBx => absurd hBx hB⟩

private theorem swapDiff_preserves_AB [Fintype α] [DecidableEq α]
    (A B : α → Prop) [DecidablePred A] [DecidablePred B]
    (e : {x // A x ∧ ¬ B x} ≃ {x // B x ∧ ¬ A x})
    (x : α) :
    (A (swapDiff A B e x) ∧ B (swapDiff A B e x)) ↔ (A x ∧ B x) := by
  rw [iff_iff_eq.mp (swapDiff_swaps_A A B e x)]
  -- Now goal: B x ∧ B (swapDiff A B e x) ↔ A x ∧ B x
  -- Equivalent claim using extensional case-analysis
  by_cases hA : A x <;> by_cases hB : B x
  · rw [swapDiff_zone_fix (fun h => h.2 hB) (fun h => h.2 hA)]
    exact ⟨fun ⟨_, h⟩ => ⟨hA, h⟩, fun ⟨_, h⟩ => ⟨hB, h⟩⟩
  · -- A x, ¬ B x: rhs A x ∧ B x is False; lhs B x is False
    exact ⟨fun ⟨hBx, _⟩ => absurd hBx hB, fun ⟨_, hBx⟩ => absurd hBx hB⟩
  · -- ¬ A x, B x: rhs A x ∧ B x is False; lhs B (swapDiff …) is False since e.symm lands in A∧¬B
    rw [swapDiff_zone_BA ⟨hB, hA⟩]
    exact ⟨fun ⟨_, hBv⟩ => absurd hBv (e.symm ⟨x, ⟨hB, hA⟩⟩).prop.2,
           fun ⟨hAx, _⟩ => absurd hAx hA⟩
  · exact ⟨fun ⟨hBx, _⟩ => absurd hBx hB, fun ⟨hAx, _⟩ => absurd hAx hA⟩

/-- @cite{peters-westerstahl-2006} Prop 6.59 (fixed-domain version):
    Under CONSERV + ISOM + asymmetry, ¬Q(A,B) whenever |A \ B| = |B \ A|. -/
theorem isom_asymmetric_eq_diff [Fintype α] [DecidableEq α] (q : GQ α)
    (hCons : Conservative q) (hIsom : QuantityInvariant q)
    (hAsym : QAsymmetric q)
    {A B : α → Prop} [DecidablePred A] [DecidablePred B]
    (hCard : Fintype.card {x // A x ∧ ¬ B x} =
             Fintype.card {x // B x ∧ ¬ A x}) :
    ¬ q A B := by
  intro hQAB
  have hAB_eq_BA : q A B ↔ q B A := by
    rw [hCons A B, hCons B A]
    have hComm : (fun x => B x ∧ A x) = (fun x => A x ∧ B x) :=
      funext fun x => propext ⟨fun ⟨h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1⟩⟩
    rw [hComm]
    let e := Fintype.equivOfCardEq hCard
    let f := swapDiff A B e
    exact hIsom A (fun x => A x ∧ B x) B (fun x => A x ∧ B x) f
      (swapDiff_involutive A B e).bijective
      (swapDiff_swaps_A A B e)
      (swapDiff_preserves_AB A B e)
  exact hAsym A B hQAB (hAB_eq_BA.mp hQAB)

-- ============================================================================
-- §8c — "Aristotle Reversed": Square from Inferential Conditions
-- @cite{van-benthem-1984} §3.3
-- ============================================================================

/-- @cite{van-benthem-1984} Cor 3.3.2: Under conservativity, the ONLY
    symmetric quasi-reflexive quantifier is overlap (= "some"). -/
theorem vanBenthem_symm_quasiRefl_is_overlap [Fintype α] [DecidableEq α] (q : GQ α)
    (hCons : Conservative q) (hSym : QSymmetric q)
    (hQR : QuasiReflexive q)
    (hWitT : ∃ x, q (fun y => y = x) (fun y => y = x))
    (hWitF : ∃ A, ¬ q A A)
    (hIso : QuantityInvariant q) :
    ∀ A B, q A B ↔ (∃ x, A x ∧ B x) := by
  classical
  have hInt := (conserv_symm_iff_int q hCons).mp hSym
  have qAB_eq : ∀ A B, q A B ↔ q (fun x => A x ∧ B x) (fun x => A x ∧ B x) := by
    intro A B
    exact hInt A B (fun x => A x ∧ B x) (fun x => A x ∧ B x)
      (fun _ => ⟨fun h => ⟨h, h⟩, And.left⟩)
  have upward : ∀ C D : α → Prop,
      (∀ x, C x → D x) → q C C → q D D := by
    intro C D hCD hCC
    have hDC : q D C ↔ q C C := by
      apply hInt; intro x
      exact ⟨fun ⟨hD, hC⟩ => ⟨hC, hC⟩, fun ⟨hC, _⟩ => ⟨hCD x hC, hC⟩⟩
    exact hQR D C (hDC.mpr hCC)
  obtain ⟨A₀, hA₀⟩ := hWitF
  have empty_false : ¬ q (fun _ => False) (fun _ => False) := by
    intro h
    exact hA₀ (upward (fun _ => False) A₀ (fun _ hF => hF.elim) h)
  intro A B
  constructor
  · intro hAB
    rw [qAB_eq] at hAB
    by_contra h
    have hAll : ∀ x, ¬ (A x ∧ B x) := fun x ⟨hAx, hBx⟩ => h ⟨x, hAx, hBx⟩
    have : (fun x => A x ∧ B x) = (fun _ => False) := by
      funext x; apply propext
      exact ⟨fun hAB => (hAll x hAB).elim, fun hF => hF.elim⟩
    rw [this] at hAB
    exact empty_false hAB
  · rintro ⟨a, hAa, hBa⟩
    rw [qAB_eq]
    obtain ⟨x, hx⟩ := hWitT
    have h_single : q (fun y => y = a) (fun y => y = a) := by
      let f : α → α := Equiv.swap x a
      have hf_bij : Function.Bijective f := (Equiv.swap x a).bijective
      have hf_prop : ∀ y, (f y = a) ↔ (y = x) := by
        intro y
        constructor
        · intro hy
          have h1 : (Equiv.swap x a).symm a = y :=
            (Equiv.symm_apply_eq (Equiv.swap x a)).mpr hy.symm
          have h2 : (Equiv.swap x a).symm a = x := Equiv.swap_apply_right x a
          rw [h2] at h1; exact h1.symm
        · intro hy
          rw [hy]; exact Equiv.swap_apply_left x a
      have h_eq : q (fun y => y = a) (fun y => y = a) ↔
          q (fun y => y = x) (fun y => y = x) :=
        hIso (fun y => y = a) (fun y => y = a) (fun y => y = x) (fun y => y = x) f hf_bij
          hf_prop hf_prop
      exact h_eq.mpr hx
    apply upward (fun y => y = a) (fun y => A y ∧ B y)
    · intro y hy; subst hy; exact ⟨hAa, hBa⟩
    · exact h_single

/-- @cite{van-benthem-1984} Cor 3.3.3: Under conservativity, the ONLY
    symmetric quasi-universal quantifier is disjointness (= "no"). -/
theorem vanBenthem_symm_quasiUniv_is_disjointness [Fintype α] [DecidableEq α] (q : GQ α)
    (hCons : Conservative q) (hSym : QSymmetric q)
    (hQU : QuasiUniversal q)
    (hWitF : ∃ x, ¬ q (fun y => y = x) (fun y => y = x))
    (hWitT : ∃ A, q A A)
    (hIso : QuantityInvariant q) :
    ∀ A B, q A B ↔ (∀ x, ¬ (A x ∧ B x)) := by
  classical
  have hInt := (conserv_symm_iff_int q hCons).mp hSym
  have qAB_eq : ∀ A B, q A B ↔ q (fun x => A x ∧ B x) (fun x => A x ∧ B x) := by
    intro A B
    exact hInt A B _ _ (fun _ => ⟨fun h => ⟨h, h⟩, And.left⟩)
  have downward : ∀ C D : α → Prop,
      (∀ x, C x → D x) → q D D → q C C := by
    intro C D hCD hDD
    have h1 : q D C := hQU D C hDD
    have h2 : q C D := (hSym D C).mp h1
    have h3 : q C D ↔ q C C := by
      rw [hCons C D]
      have : (fun x => C x ∧ D x) = C :=
        funext fun x => propext ⟨fun h => h.1, fun hC => ⟨hC, hCD x hC⟩⟩
      rw [this]
    exact h3.mp h2
  obtain ⟨A₀, hA₀⟩ := hWitT
  have empty_true : q (fun _ => False) (fun _ => False) :=
    downward (fun _ => False) A₀ (fun _ hF => hF.elim) hA₀
  intro A B
  constructor
  · intro hAB x ⟨hAx, hBx⟩
    rw [qAB_eq] at hAB
    obtain ⟨x₀, hx₀⟩ := hWitF
    have h_single_true : q (fun y => y = x) (fun y => y = x) :=
      downward (fun y => y = x) (fun y => A y ∧ B y)
        (fun y hy => by subst hy; exact ⟨hAx, hBx⟩) hAB
    have h_single_false : ¬ q (fun y => y = x) (fun y => y = x) := by
      let f : α → α := Equiv.swap x₀ x
      have hf_bij : Function.Bijective f := (Equiv.swap x₀ x).bijective
      have hf_prop : ∀ y, (f y = x) ↔ (y = x₀) := by
        intro y
        constructor
        · intro hy
          have h1 : (Equiv.swap x₀ x).symm x = y :=
            (Equiv.symm_apply_eq (Equiv.swap x₀ x)).mpr hy.symm
          have h2 : (Equiv.swap x₀ x).symm x = x₀ := Equiv.swap_apply_right x₀ x
          rw [h2] at h1; exact h1.symm
        · intro hy
          rw [hy]; exact Equiv.swap_apply_left x₀ x
      have h_eq : q (fun y => y = x) (fun y => y = x) ↔
          q (fun y => y = x₀) (fun y => y = x₀) :=
        hIso (fun y => y = x) (fun y => y = x) (fun y => y = x₀) (fun y => y = x₀) f hf_bij
          hf_prop hf_prop
      exact (fun h => hx₀ (h_eq.mp h))
    exact h_single_false h_single_true
  · intro hDisj
    rw [qAB_eq]
    have hEmpty : (fun x => A x ∧ B x) = (fun _ => False) :=
      funext fun x => propext
        ⟨fun ⟨hAx, hBx⟩ => hDisj x ⟨hAx, hBx⟩, fun hF => hF.elim⟩
    rw [hEmpty]
    exact empty_true

-- ============================================================================
-- §9 — Entailment Signature Bridge (@cite{icard-2012})
-- ============================================================================

open Core.NaturalLogic (EntailmentSig ContextPolarity)

/--
Map a pair of entailment signatures (restrictor, scope) to `DoubleMono`,
the @cite{van-benthem-1984} double monotonicity classification.

Returns `none` for signature pairs that don't correspond to a standard
generalized quantifier pattern.
-/
def EntailmentSig.pairToDoubleMono : EntailmentSig → EntailmentSig → Option DoubleMono
  | .additive, .additive => some .upUp
  | .antiAdd, .mult => some .downUp
  | .additive, .antiMult => some .upDown
  | .antiAdd, .antiAdd => some .downDown
  | _, _ => none

#guard EntailmentSig.pairToDoubleMono .additive .additive == some .upUp
#guard EntailmentSig.pairToDoubleMono .antiAdd .mult == some .downUp
#guard EntailmentSig.pairToDoubleMono .additive .antiMult == some .upDown
#guard EntailmentSig.pairToDoubleMono .antiAdd .antiAdd == some .downDown

/-- "every" has signature (◇, ⊞) = (antiAdd in restrictor, mult in scope). -/
def everyEntailmentSig : EntailmentSig × EntailmentSig := (.antiAdd, .mult)

/-- "some" has signature (⊕, ⊕) = (additive in both arguments). -/
def someEntailmentSig : EntailmentSig × EntailmentSig := (.additive, .additive)

/-- "no" has signature (◇, ◇) = (antiAdd in both arguments). -/
def noEntailmentSig : EntailmentSig × EntailmentSig := (.antiAdd, .antiAdd)

/-- "not every" has signature (⊕, ⊟) = (additive in restrictor, antiMult in scope). -/
def notEveryEntailmentSig : EntailmentSig × EntailmentSig := (.additive, .antiMult)

#guard EntailmentSig.pairToDoubleMono everyEntailmentSig.1 everyEntailmentSig.2 == some .downUp
#guard EntailmentSig.pairToDoubleMono someEntailmentSig.1 someEntailmentSig.2 == some .upUp
#guard EntailmentSig.pairToDoubleMono noEntailmentSig.1 noEntailmentSig.2 == some .downDown
#guard EntailmentSig.pairToDoubleMono notEveryEntailmentSig.1 notEveryEntailmentSig.2 == some .upDown

#guard EntailmentSig.toContextPolarity everyEntailmentSig.2 == .upward
#guard EntailmentSig.toContextPolarity someEntailmentSig.2 == .upward
#guard EntailmentSig.toContextPolarity noEntailmentSig.2 == .downward
#guard EntailmentSig.toContextPolarity notEveryEntailmentSig.2 == .downward

#guard EntailmentSig.toContextPolarity everyEntailmentSig.1 == .downward
#guard EntailmentSig.toContextPolarity someEntailmentSig.1 == .upward
#guard EntailmentSig.toContextPolarity noEntailmentSig.1 == .downward
#guard EntailmentSig.toContextPolarity notEveryEntailmentSig.1 == .upward

end Core.Quantification
