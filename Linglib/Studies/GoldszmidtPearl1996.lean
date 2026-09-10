import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Max
import Mathlib.Order.Bounds.Basic
import Linglib.Logic.RankingFunction

/-!
# Goldszmidt and Pearl (1996): Qualitative Probabilities for Default Reasoning, Belief Revision, and Causal Modeling

This file formalizes the default-reasoning core of [goldszmidt-pearl-1996]: system Z and its
variable-strength extension system Z⁺. A ranking function ([spohn-1988]'s ordinal conditional
function, read as the order of magnitude of an infinitesimal probability) is admissible for a
knowledge base of rules φ → ψ when every world falsifying a rule is outranked by one verifying
it. A rule is tolerated by the base when some world verifies it together with the material
counterparts of all the rules; the Consistency-Test peels off the tolerated rules stratum by
stratum, a stratum's index is the Z-priority of its rules, and the ranking κᶻ gives a world one
more than the highest priority it falsifies. Two consequence relations are compared on the paper's
Example 17: the cautious p-entailment, which holds in every admissible ranking, and z-entailment,
which holds in κᶻ. Table 2's verdicts are theorems: z-entailment sanctions rule chaining and the
discounting of an irrelevant feature where p-entailment is undecided (`z_birds_airborne`,
`p_birds_airborne_undecided`), and neither inherits wings to the exceptional penguins.

System Z⁺ attaches a strength δ to each rule and asks a verifying world to lie δ + 1 ranks below
every falsifying one. The coupled equations of the ranking κ⁺ and the priorities Z⁺ are satisfied
by the priorities the paper computes for Example 24 under every choice of strengths
(`isZPlusOrdering_example24`); penguins inherit wings exactly when the wing rule is firmer than
the flying rule (`zPlus_penguins_winged_iff`), and the Nixon diamond of Example 26 is decided by
the relative strengths alone (`nixon_pacifist_iff`).

## Implementation notes

Worlds are the truth assignments to the atoms of each example, given a `Fintype` instance through
the product of Booleans so that tolerance, admissibility, and entailment decide. Uniqueness and
minimality of κᶻ and κ⁺ (Theorems 16 and 21) and the paper's sections on soft evidence, belief
revision, and causal networks are not formalized; Spohn's conditioning lives in `RankingFunction`.

## References

* [goldszmidt-pearl-1996]
* [spohn-1988]
* [adams-1975]
-/

namespace GoldszmidtPearl1996

variable {W : Type*}

/-- A default rule "if φ then normally ψ" on decidable predicates. -/
structure Rule (W : Type*) where
  ante : W → Prop
  cons : W → Prop
  [decAnte : DecidablePred ante]
  [decCons : DecidablePred cons]

attribute [instance] Rule.decAnte Rule.decCons

namespace Rule

variable (r : Rule W) (x : W)

/-- The world satisfies the material counterpart φ ⊃ ψ of the rule. -/
def Verified : Prop := r.ante x → r.cons x

/-- The world satisfies φ ∧ ¬ψ. -/
def Falsified : Prop := r.ante x ∧ ¬ r.cons x

instance : Decidable (r.Verified x) := by unfold Verified; infer_instance
instance : Decidable (r.Falsified x) := by unfold Falsified; infer_instance

end Rule

/-- A knowledge base: a list of rules. -/
abbrev KnowledgeBase (W : Type*) := List (Rule W)

/-- Definition 2: a ranking is admissible for the base when every world falsifying a rule is
outranked by a world verifying it, so that κ(φ ∧ ψ) < κ(φ ∧ ¬ψ). -/
def Admissible (κ : RankingFunction W) (Δ : KnowledgeBase W) : Prop :=
  ∀ r ∈ Δ, ∀ x, r.Falsified x → ∃ y, r.ante y ∧ r.cons y ∧ κ.rank y < κ.rank x

instance [Fintype W] (κ : RankingFunction W) (Δ : KnowledgeBase W) :
    Decidable (Admissible κ Δ) := by
  unfold Admissible; infer_instance

theorem Admissible.mono {κ : RankingFunction W} {Δ Δ' : KnowledgeBase W} (h : Δ ⊆ Δ')
    (hκ : Admissible κ Δ') : Admissible κ Δ :=
  λ r hr => hκ r (h hr)

/-- Definition 3: a rule is tolerated by the base when some world verifies it together with the
material counterparts of every rule of the base. -/
def Tolerated (r : Rule W) (Δ : KnowledgeBase W) : Prop :=
  ∃ x, r.ante x ∧ r.cons x ∧ ∀ r' ∈ Δ, r'.Verified x

instance [Fintype W] (r : Rule W) (Δ : KnowledgeBase W) : Decidable (Tolerated r Δ) := by
  unfold Tolerated; infer_instance

/-- The Consistency-Test (Fig. 2): peel off the rules tolerated by what remains, stratum by
stratum; a stratum's index is the Z-priority of its rules. Each stratum of a consistent base
removes a rule, so the number of rules bounds the iteration; rules that are never tolerated stay
in the last stratum. -/
def zPrioritiesAux [Fintype W] : ℕ → KnowledgeBase W → ℕ → List (Rule W × ℕ)
  | _, [], _ => []
  | 0, Δ, level => Δ.map (·, level)
  | fuel + 1, Δ, level =>
    let (tol, rest) := Δ.partition λ r => decide (Tolerated r Δ)
    if tol.isEmpty then Δ.map (·, level)
    else tol.map (·, level) ++ zPrioritiesAux fuel rest (level + 1)

/-- The Z-priorities of a base, by the Consistency-Test. -/
def zPriorities [Fintype W] (Δ : KnowledgeBase W) : List (Rule W × ℕ) :=
  zPrioritiesAux Δ.length Δ 0

/-- Definition 12 (and Eq. 15): the rank of a world is one more than the highest priority among
the rules it falsifies, zero when it falsifies none. -/
def zRank (rules : List (Rule W × ℕ)) (x : W) : ℕ :=
  ((rules.filter λ p => decide (p.1.Falsified x)).map (·.2 + 1)).foldr max 0

/-- The ranking a prioritized base induces, given a world falsifying no rule. -/
def zRanking (rules : List (Rule W × ℕ)) (h : ∃ x, zRank rules x = 0) : RankingFunction W :=
  ⟨zRank rules, h⟩

/-- Definition 7: σ follows from φ in κ when every φ ∧ ¬σ world is outranked by a φ ∧ σ world,
that is when κ(φ ∧ σ) < κ(φ ∧ ¬σ). -/
def Entails (κ : RankingFunction W) (φ σ : W → Prop) : Prop :=
  ∀ x, φ x → ¬ σ x → ∃ y, φ y ∧ σ y ∧ κ.rank y < κ.rank x

instance [Fintype W] (κ : RankingFunction W) (φ σ : W → Prop) [DecidablePred φ]
    [DecidablePred σ] : Decidable (Entails κ φ σ) := by
  unfold Entails; infer_instance

/-- Principle (3): σ follows from φ exactly when it holds in every most normal φ-world. -/
theorem entails_iff_forall_min [Fintype W] (κ : RankingFunction W) (φ σ : W → Prop)
    [DecidablePred φ] :
    Entails κ φ σ ↔ ∀ x, φ x → (∀ y, φ y → κ.rank x ≤ κ.rank y) → σ x := by
  constructor
  · intro h x hx hmin
    by_contra hσ
    obtain ⟨y, hy, -, hlt⟩ := h x hx hσ
    exact absurd (hmin y hy) (not_le.mpr hlt)
  · intro h x hx hσ
    obtain ⟨m, hm, hmin⟩ := (Finset.univ.filter φ).exists_min_image κ.rank ⟨x, by simpa using hx⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm hmin
    refine ⟨m, hm, h m hm hmin, lt_of_le_of_ne (hmin x hx) λ heq => hσ (h x hx λ y hy => ?_)⟩
    exact heq ▸ hmin y hy

/-- Definition 8: p-entailment holds in every admissible ranking. -/
def PEntails (Δ : KnowledgeBase W) (φ σ : W → Prop) : Prop :=
  ∀ κ : RankingFunction W, Admissible κ Δ → Entails κ φ σ

/-- A rule is p-entailed by its own antecedent. -/
theorem pEntails_of_mem {Δ : KnowledgeBase W} {r : Rule W} (h : r ∈ Δ) : PEntails Δ r.ante r.cons :=
  λ _ hκ x hx hσ => hκ r h x ⟨hx, hσ⟩

/-- An admissible ranking in which σ does not follow from φ refutes p-entailment. -/
theorem not_pEntails {Δ : KnowledgeBase W} {κ : RankingFunction W} (hκ : Admissible κ Δ)
    {φ σ : W → Prop} (h : ¬ Entails κ φ σ) : ¬ PEntails Δ φ σ :=
  λ hp => h (hp κ hκ)

/-! ### System Z⁺ (section 3) -/

/-- A rule with a strength δ. -/
structure StrengthRule (W : Type*) extends Rule W where
  strength : ℕ

/-- A base of variable-strength rules. -/
abbrev StrengthBase (W : Type*) := List (StrengthRule W)

/-- The flat base: the rules without their strengths. -/
def StrengthBase.flat (Δ : StrengthBase W) : KnowledgeBase W := Δ.map (·.toRule)

/-- Definition 18: every falsifying world lies at least δ + 1 ranks above a verifying one. -/
def StrengthAdmissible (κ : RankingFunction W) (Δ : StrengthBase W) : Prop :=
  ∀ r ∈ Δ, ∀ x, r.Falsified x → ∃ y, r.ante y ∧ r.cons y ∧ κ.rank y + r.strength < κ.rank x

private theorem strength_le_foldr_max (Δ : StrengthBase W) {r : StrengthRule W} (hr : r ∈ Δ) :
    r.strength ≤ Δ.foldr (λ r n => max r.strength n) 0 := by
  induction Δ with
  | nil => contradiction
  | cons hd tl ih =>
    simp only [List.foldr]
    rcases List.mem_cons.mp hr with rfl | htl
    · exact le_max_left _ _
    · exact le_trans (ih htl) (le_max_right _ _)

/-- Theorem 19: a strength base admits a δ-admissible ranking exactly when its flat base admits
an admissible one; scaling a ranking by one more than the largest strength widens every gap. -/
theorem strengthAdmissible_iff_flat [Fintype W] (Δ : StrengthBase W) :
    (∃ κ : RankingFunction W, StrengthAdmissible κ Δ) ↔
      ∃ κ : RankingFunction W, Admissible κ Δ.flat := by
  constructor
  · rintro ⟨κ, hκ⟩
    refine ⟨κ, λ r hr x hx => ?_⟩
    obtain ⟨sr, hsr, rfl⟩ := List.mem_map.mp hr
    obtain ⟨y, hya, hyc, hlt⟩ := hκ sr hsr x hx
    exact ⟨y, hya, hyc, by omega⟩
  · rintro ⟨κ, hκ⟩
    set M := 1 + Δ.foldr (λ r n => max r.strength n) 0 with hM
    refine ⟨⟨λ x => κ.rank x * M, ?_⟩, λ r hr x hx => ?_⟩
    · obtain ⟨x, hx⟩ := κ.normalized
      exact ⟨x, by simp [hx]⟩
    · obtain ⟨y, hya, hyc, hlt⟩ := hκ r.toRule (List.mem_map.mpr ⟨r, hr, rfl⟩) x hx
      refine ⟨y, hya, hyc, ?_⟩
      have hδ : r.strength < M := by have := strength_le_foldr_max Δ hr; omega
      show κ.rank y * M + r.strength < κ.rank x * M
      have h := Nat.mul_le_mul_right M (show κ.rank y + 1 ≤ κ.rank x by omega)
      rw [Nat.succ_mul] at h; omega

/-- The rank a prioritized strength base induces (Eq. 15). -/
def zPlusRank (Δ : List (StrengthRule W × ℕ)) : W → ℕ :=
  zRank (Δ.map λ p => (p.1.toRule, p.2))

/-- Definition 20 (Eq. 16): priorities form a Z⁺-ordering when each rule's priority is its
strength plus the least rank, under the ranking the priorities induce, of a world verifying it. -/
def IsZPlusOrdering [Fintype W] (Δ : List (StrengthRule W × ℕ)) : Prop :=
  ∀ p ∈ Δ, IsLeast {n | ∃ x, p.1.ante x ∧ p.1.cons x ∧ n = zPlusRank Δ x + p.1.strength} p.2

/-! ### Example 17: the penguin base -/

/-- A world of Example 17: a truth assignment to bird, penguin, flies, winged, airborne, and the
irrelevant feature red. -/
structure World where
  b : Bool
  p : Bool
  f : Bool
  w : Bool
  a : Bool
  r : Bool
  deriving DecidableEq

/-- Worlds are the assignments to the six atoms. -/
def World.equivProd : World ≃ Bool × Bool × Bool × Bool × Bool × Bool where
  toFun x := (x.b, x.p, x.f, x.w, x.a, x.r)
  invFun t := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype World := Fintype.ofEquiv _ World.equivProd.symm

def bird (x : World) : Prop := x.b = true
def penguin (x : World) : Prop := x.p = true
def flies (x : World) : Prop := x.f = true
def winged (x : World) : Prop := x.w = true
def airborne (x : World) : Prop := x.a = true
def red (x : World) : Prop := x.r = true

instance : DecidablePred bird := λ x => by unfold bird; infer_instance
instance : DecidablePred penguin := λ x => by unfold penguin; infer_instance
instance : DecidablePred flies := λ x => by unfold flies; infer_instance
instance : DecidablePred winged := λ x => by unfold winged; infer_instance
instance : DecidablePred airborne := λ x => by unfold airborne; infer_instance
instance : DecidablePred red := λ x => by unfold red; infer_instance

/-- r₁: birds fly. -/
def r₁ : Rule World := ⟨bird, flies⟩
/-- r₂: penguins are birds. -/
def r₂ : Rule World := ⟨penguin, bird⟩
/-- r₃: penguins do not fly. -/
def r₃ : Rule World := ⟨penguin, λ x => ¬ flies x⟩
/-- r₄: birds have wings. -/
def r₄ : Rule World := ⟨bird, winged⟩
/-- r₅: animals that fly are airborne. -/
def r₅ : Rule World := ⟨flies, airborne⟩

/-- The base Δ_pb of Example 17. -/
def Δpb : KnowledgeBase World := [r₁, r₂, r₃, r₄, r₅]

/-- r₁, r₄, and r₅ are tolerated by the whole base; r₂ and r₃ only by each other. -/
theorem tolerated_Δpb :
    Tolerated r₁ Δpb ∧ Tolerated r₄ Δpb ∧ Tolerated r₅ Δpb ∧
      ¬ Tolerated r₂ Δpb ∧ ¬ Tolerated r₃ Δpb ∧ Tolerated r₂ [r₂, r₃] ∧ Tolerated r₃ [r₂, r₃] := by
  decide

/-- The Consistency-Test labels r₁, r₄, r₅ with 0 and r₂, r₃ with 1. -/
theorem zPriorities_Δpb : (zPriorities Δpb).map (·.2) = [0, 0, 0, 1, 1] := by decide

/-- The ranking κᶻ of the penguin base. -/
def κz : RankingFunction World :=
  zRanking (zPriorities Δpb) ⟨⟨true, false, true, true, true, false⟩, by decide⟩

theorem admissible_κz : Admissible κz Δpb := by decide

/-! Table 2, with a query (φ, σ) answered YES when σ follows from φ, NO when ¬σ does, and
undecided when neither. -/

/-- "Do penguin-birds fly?": NO under z-entailment. -/
theorem z_penguin_birds_dont_fly :
    Entails κz (λ x => penguin x ∧ bird x) (λ x => ¬ flies x) := by decide

/-- "Do penguin-birds fly?": NO under p-entailment, by specificity in every admissible ranking:
a most normal penguin-bird that flew would falsify r₃, and the world r₃ then places below it is
a penguin-bird or, failing r₂, is outranked by one. -/
theorem p_penguin_birds_dont_fly : PEntails Δpb (λ x => penguin x ∧ bird x) (λ x => ¬ flies x) := by
  intro κ hκ
  rw [entails_iff_forall_min]
  rintro x ⟨hp, hb⟩ hmin hf
  obtain ⟨y, hyp, hyf, hlt⟩ := hκ r₃ (by simp [Δpb]) x ⟨hp, not_not.mpr hf⟩
  by_cases hyb : bird y
  · exact absurd (hmin y ⟨hyp, hyb⟩) (not_le.mpr hlt)
  · obtain ⟨z, hzp, hzb, hlt'⟩ := hκ r₂ (by simp [Δpb]) y ⟨hyp, hyb⟩
    exact absurd (hmin z ⟨hzp, hzb⟩) (not_le.mpr (hlt'.trans hlt))

/-- "Are birds typically penguins?": NO under z-entailment. -/
theorem z_birds_not_penguins : Entails κz bird (λ x => ¬ penguin x) := by decide

/-- "Are birds typically penguins?": NO under p-entailment: a most normal bird that was a penguin
would falsify r₁ or r₃, and either rule places a bird below it. -/
theorem p_birds_not_penguins : PEntails Δpb bird (λ x => ¬ penguin x) := by
  intro κ hκ
  rw [entails_iff_forall_min]
  intro x hb hmin hp
  by_cases hf : flies x
  · obtain ⟨y, hyp, hyf, hlt⟩ := hκ r₃ (by simp [Δpb]) x ⟨hp, not_not.mpr hf⟩
    by_cases hyb : bird y
    · exact absurd (hmin y hyb) (not_le.mpr hlt)
    · obtain ⟨z, -, hzb, hlt'⟩ := hκ r₂ (by simp [Δpb]) y ⟨hyp, hyb⟩
      exact absurd (hmin z hzb) (not_le.mpr (hlt'.trans hlt))
  · obtain ⟨y, hyb, -, hlt⟩ := hκ r₁ (by simp [Δpb]) x ⟨hb, hf⟩
    exact absurd (hmin y hyb) (not_le.mpr hlt)

/-- "Do red birds fly?": YES under z-entailment, discounting the irrelevant feature. -/
theorem z_red_birds_fly : Entails κz (λ x => red x ∧ bird x) flies := by decide

/-- "Do red birds fly?": undecided under p-entailment. Adding the rule that red birds do not fly
keeps the base consistent, and its ranking is admissible for Δ_pb; so is κᶻ, where they fly. -/
theorem p_red_birds_fly_undecided :
    ¬ PEntails Δpb (λ x => red x ∧ bird x) flies ∧
      ¬ PEntails Δpb (λ x => red x ∧ bird x) (λ x => ¬ flies x) := by
  refine ⟨not_pEntails
    (κ := zRanking (zPriorities (Δpb ++ [⟨λ x => red x ∧ bird x, λ x => ¬ flies x⟩]))
    ⟨⟨true, false, true, true, true, false⟩, by decide⟩) (by decide) (by decide),
    not_pEntails admissible_κz (by decide)⟩

/-- "Are birds airborne?": YES under z-entailment, by chaining r₁ and r₅. -/
theorem z_birds_airborne : Entails κz bird airborne := by decide

/-- "Are birds airborne?": undecided under p-entailment, since neither "birds are airborne" nor
"birds are not airborne" makes the base inconsistent. -/
theorem p_birds_airborne_undecided :
    ¬ PEntails Δpb bird airborne ∧ ¬ PEntails Δpb bird (λ x => ¬ airborne x) := by
  refine ⟨not_pEntails (κ := zRanking (zPriorities (Δpb ++ [⟨bird, λ x => ¬ airborne x⟩]))
    ⟨⟨false, false, false, false, false, false⟩, by decide⟩)
    (by decide +kernel) (by decide +kernel),
    not_pEntails admissible_κz (by decide)⟩

/-- "Are penguins winged animals?": undecided under z-entailment, the exceptional subclass
inheriting nothing from birds. -/
theorem z_penguins_winged_undecided :
    ¬ Entails κz penguin winged ∧ ¬ Entails κz penguin (λ x => ¬ winged x) := by decide

/-- "Are penguins winged animals?": undecided under p-entailment. -/
theorem p_penguins_winged_undecided :
    ¬ PEntails Δpb penguin winged ∧ ¬ PEntails Δpb penguin (λ x => ¬ winged x) :=
  ⟨not_pEntails admissible_κz z_penguins_winged_undecided.1,
   not_pEntails admissible_κz z_penguins_winged_undecided.2⟩

/-! ### Example 24: the penguin base with strengths -/

private theorem le_foldr_max {l : List ℕ} {n : ℕ} (h : n ∈ l) : n ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons m l ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

/-- A falsified rule bounds the rank from below by one more than its priority. -/
theorem le_zRank_of_falsified {rules : List (Rule W × ℕ)} {q : Rule W × ℕ} (hq : q ∈ rules) {x : W}
    (hx : q.1.Falsified x) : q.2 + 1 ≤ zRank rules x :=
  le_foldr_max (List.mem_map_of_mem (List.mem_filter.mpr ⟨hq, decide_eq_true hx⟩))

theorem le_zPlusRank_of_falsified {Δ : List (StrengthRule W × ℕ)} {q : StrengthRule W × ℕ}
    (hq : q ∈ Δ) {x : W} (hx : q.1.Falsified x) : q.2 + 1 ≤ zPlusRank Δ x :=
  le_zRank_of_falsified (q := (q.1.toRule, q.2))
    (List.mem_map_of_mem (f := λ p : StrengthRule W × ℕ => (p.1.toRule, p.2)) hq) hx

section Example24

variable (δ₁ δ₂ δ₃ δ₄ δ₅ : ℕ)

/-- The paper's Z⁺-ordering for Δ⁺_pb: the tolerated rules keep their strengths, and the
penguin rules, whose verifying worlds must falsify r₁, sit at δ₁ + δᵢ + 1. -/
def ΔpbPlus : List (StrengthRule World × ℕ) :=
  [(⟨r₁, δ₁⟩, δ₁), (⟨r₂, δ₂⟩, δ₁ + δ₂ + 1), (⟨r₃, δ₃⟩, δ₁ + δ₃ + 1), (⟨r₄, δ₄⟩, δ₄),
   (⟨r₅, δ₅⟩, δ₅)]

/-- The normal world: a flying, winged, airborne bird. -/
def w₀ : World := ⟨true, false, true, true, true, false⟩

/-- The most normal penguin: a winged, grounded bird. -/
def w₁ : World := ⟨true, true, false, true, true, false⟩

theorem zPlusRank_w₀ : zPlusRank (ΔpbPlus δ₁ δ₂ δ₃ δ₄ δ₅) w₀ = 0 := by
  simp [zPlusRank, zRank, ΔpbPlus, w₀, Rule.Falsified, r₁, r₂, r₃, r₄, r₅, bird, penguin, flies,
    winged, airborne]

theorem zPlusRank_w₁ : zPlusRank (ΔpbPlus δ₁ δ₂ δ₃ δ₄ δ₅) w₁ = δ₁ + 1 := by
  simp [zPlusRank, zRank, ΔpbPlus, w₁, Rule.Falsified, r₁, r₂, r₃, r₄, r₅, bird, penguin, flies,
    winged, airborne]

/-- Every penguin world ranks at least δ₁ + 1: it falsifies r₂, r₃, or r₁. -/
theorem le_zPlusRank_of_penguin {x : World} (hp : penguin x) :
    δ₁ + 1 ≤ zPlusRank (ΔpbPlus δ₁ δ₂ δ₃ δ₄ δ₅) x := by
  by_cases hb : bird x
  · by_cases hf : flies x
    · have : δ₁ + δ₃ + 1 + 1 ≤ zPlusRank (ΔpbPlus δ₁ δ₂ δ₃ δ₄ δ₅) x :=
          le_zPlusRank_of_falsified (q := (⟨r₃, δ₃⟩, δ₁ + δ₃ + 1)) (by simp [ΔpbPlus])
          ⟨hp, not_not.mpr hf⟩
      omega
    · exact le_zPlusRank_of_falsified (q := (⟨r₁, δ₁⟩, δ₁)) (by simp [ΔpbPlus]) ⟨hb, hf⟩
  · have : δ₁ + δ₂ + 1 + 1 ≤ zPlusRank (ΔpbPlus δ₁ δ₂ δ₃ δ₄ δ₅) x :=
      le_zPlusRank_of_falsified (q := (⟨r₂, δ₂⟩, δ₁ + δ₂ + 1)) (by simp [ΔpbPlus]) ⟨hp, hb⟩
    omega

/-- The paper's priorities satisfy Definition 20 for every choice of strengths. -/
theorem isZPlusOrdering_example24 : IsZPlusOrdering (ΔpbPlus δ₁ δ₂ δ₃ δ₄ δ₅) := by
  intro q hq
  simp only [ΔpbPlus, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨w₀, rfl, rfl, by simp [zPlusRank_w₀]⟩, by rintro n ⟨x, -, -, rfl⟩; dsimp only; omega⟩
  · refine ⟨⟨w₁, rfl, rfl, by simp [zPlusRank_w₁]; omega⟩, ?_⟩
    rintro n ⟨x, hp, -, rfl⟩
    have := le_zPlusRank_of_penguin δ₁ δ₂ δ₃ δ₄ δ₅ hp
    dsimp only; omega
  · refine ⟨⟨w₁, rfl, show ¬ flies w₁ by decide, by simp [zPlusRank_w₁]; omega⟩, ?_⟩
    rintro n ⟨x, hp, -, rfl⟩
    have := le_zPlusRank_of_penguin δ₁ δ₂ δ₃ δ₄ δ₅ hp
    dsimp only; omega
  · exact ⟨⟨w₀, rfl, rfl, by simp [zPlusRank_w₀]⟩, by rintro n ⟨x, -, -, rfl⟩; dsimp only; omega⟩
  · exact ⟨⟨w₀, rfl, rfl, by simp [zPlusRank_w₀]⟩, by rintro n ⟨x, -, -, rfl⟩; dsimp only; omega⟩

/-- The ranking κ⁺ of Example 24. -/
def κPlus : RankingFunction World :=
  ⟨zPlusRank (ΔpbPlus δ₁ δ₂ δ₃ δ₄ δ₅), w₀, zPlusRank_w₀ _ _ _ _ _⟩

/-- Penguin-birds do not fly under κ⁺ whatever the strengths: the preference for r₃ over r₁ is
a matter of specificity, not of the δ's (Theorem 25). -/
theorem zPlus_penguin_birds_dont_fly :
    Entails (κPlus δ₁ δ₂ δ₃ δ₄ δ₅) (λ x => penguin x ∧ bird x) (λ x => ¬ flies x) := by
  rintro x ⟨hp, -⟩ hf
  have : δ₁ + δ₃ + 1 + 1 ≤ zPlusRank (ΔpbPlus δ₁ δ₂ δ₃ δ₄ δ₅) x :=
    le_zPlusRank_of_falsified (q := (⟨r₃, δ₃⟩, δ₁ + δ₃ + 1)) (by simp [ΔpbPlus])
      ⟨hp, not_not.mpr (not_not.mp hf)⟩
  refine ⟨w₁, ⟨rfl, rfl⟩, by decide, ?_⟩
  show zPlusRank _ w₁ < zPlusRank _ x
  rw [zPlusRank_w₁]; omega

/-- Penguins inherit wings under κ⁺ exactly when the wing rule is firmer than the flying rule. -/
theorem zPlus_penguins_winged_iff :
    Entails (κPlus δ₁ δ₂ δ₃ δ₄ δ₅) penguin winged ↔ δ₁ < δ₄ := by
  constructor
  · intro h
    obtain ⟨y, hyp, -, hlt⟩ := h ⟨true, true, false, false, true, false⟩ rfl (by decide)
    have hy := le_zPlusRank_of_penguin δ₁ δ₂ δ₃ δ₄ δ₅ hyp
    have hx : zPlusRank (ΔpbPlus δ₁ δ₂ δ₃ δ₄ δ₅) ⟨true, true, false, false, true, false⟩ =
        max (δ₁ + 1) (δ₄ + 1) := by
      simp [zPlusRank, zRank, ΔpbPlus, Rule.Falsified, r₁, r₂, r₃, r₄, r₅, bird, penguin, flies,
        winged, airborne]
    change zPlusRank _ y < zPlusRank _ _ at hlt
    rw [hx] at hlt
    omega
  · intro hδ x hp hw
    refine ⟨w₁, rfl, rfl, ?_⟩
    show zPlusRank _ w₁ < zPlusRank _ x
    rw [zPlusRank_w₁]
    by_cases hb : bird x
    · have : δ₄ + 1 ≤ zPlusRank (ΔpbPlus δ₁ δ₂ δ₃ δ₄ δ₅) x :=
        le_zPlusRank_of_falsified (q := (⟨r₄, δ₄⟩, δ₄)) (by simp [ΔpbPlus]) ⟨hb, hw⟩
      omega
    · have : δ₁ + δ₂ + 1 + 1 ≤ zPlusRank (ΔpbPlus δ₁ δ₂ δ₃ δ₄ δ₅) x :=
        le_zPlusRank_of_falsified (q := (⟨r₂, δ₂⟩, δ₁ + δ₂ + 1)) (by simp [ΔpbPlus]) ⟨hp, hb⟩
      omega

end Example24

/-! ### Example 26: the Nixon diamond -/

/-- A world of Example 26: Quaker, Republican, pacifist. -/
structure Nixon where
  q : Bool
  r : Bool
  p : Bool
  deriving DecidableEq

def Nixon.equivProd : Nixon ≃ Bool × Bool × Bool where
  toFun x := (x.q, x.r, x.p)
  invFun t := ⟨t.1, t.2.1, t.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype Nixon := Fintype.ofEquiv _ Nixon.equivProd.symm

def quaker (x : Nixon) : Prop := x.q = true
def republican (x : Nixon) : Prop := x.r = true
def pacifist (x : Nixon) : Prop := x.p = true

instance : DecidablePred quaker := λ x => by unfold quaker; infer_instance
instance : DecidablePred republican := λ x => by unfold republican; infer_instance
instance : DecidablePred pacifist := λ x => by unfold pacifist; infer_instance

section Example26

variable (δ₁ δ₂ : ℕ)

/-- Quakers are pacifists with strength δ₁, Republicans are not with strength δ₂; each rule is
tolerated by the other, so each priority is its strength. -/
def Δqr : List (StrengthRule Nixon × ℕ) :=
  [(⟨⟨quaker, pacifist⟩, δ₁⟩, δ₁), (⟨⟨republican, λ x => ¬ pacifist x⟩, δ₂⟩, δ₂)]

theorem isZPlusOrdering_example26 : IsZPlusOrdering (Δqr δ₁ δ₂) := by
  intro q hq
  simp only [Δqr, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact ⟨⟨⟨true, false, true⟩, rfl, rfl, by simp [zPlusRank, zRank, Δqr, Rule.Falsified, quaker,
      republican, pacifist]⟩, by rintro n ⟨x, -, -, rfl⟩; dsimp only; omega⟩
  · exact ⟨⟨⟨false, true, false⟩, rfl, show ¬ pacifist ⟨false, true, false⟩ by decide,
      by simp [zPlusRank, zRank, Δqr, Rule.Falsified, quaker, republican, pacifist]⟩,
      by rintro n ⟨x, -, -, rfl⟩; dsimp only; omega⟩

/-- The ranking κ⁺ of the Nixon diamond. -/
def κqr : RankingFunction Nixon :=
  ⟨zPlusRank (Δqr δ₁ δ₂), ⟨false, false, false⟩, by
    simp [zPlusRank, zRank, Δqr, Rule.Falsified, quaker, republican, pacifist]⟩

private theorem zPlusRank_qrp :
    zPlusRank (Δqr δ₁ δ₂) ⟨true, true, true⟩ = δ₂ + 1 ∧
      zPlusRank (Δqr δ₁ δ₂) ⟨true, true, false⟩ = δ₁ + 1 := by
  constructor <;> simp [zPlusRank, zRank, Δqr, Rule.Falsified, quaker, republican, pacifist]

/-- A Quaker Republican is a pacifist exactly when religious conviction outweighs political
affiliation: no specificity decides the diamond, only the strengths. -/
theorem nixon_pacifist_iff :
    Entails (κqr δ₁ δ₂) (λ x => quaker x ∧ republican x) pacifist ↔ δ₂ < δ₁ := by
  constructor
  · intro h
    obtain ⟨y, ⟨hyq, hyr⟩, hyp, hlt⟩ := h ⟨true, true, false⟩ ⟨rfl, rfl⟩ (by decide)
    obtain ⟨-, hx⟩ := zPlusRank_qrp δ₁ δ₂
    have hy : y = ⟨true, true, true⟩ := by
      obtain ⟨q, r, p⟩ := y
      simp_all [quaker, republican, pacifist]
    subst hy
    change zPlusRank _ _ < zPlusRank _ _ at hlt
    rw [(zPlusRank_qrp δ₁ δ₂).1, hx] at hlt
    omega
  · rintro hδ x ⟨hq, hr⟩ hp
    have : δ₁ + 1 ≤ zPlusRank (Δqr δ₁ δ₂) x :=
      le_zPlusRank_of_falsified (q := (⟨⟨quaker, pacifist⟩, δ₁⟩, δ₁)) (by simp [Δqr]) ⟨hq, hp⟩
    refine ⟨⟨true, true, true⟩, ⟨rfl, rfl⟩, rfl, ?_⟩
    show zPlusRank _ _ < zPlusRank _ x
    rw [(zPlusRank_qrp δ₁ δ₂).1]; omega

end Example26

end GoldszmidtPearl1996
