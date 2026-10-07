module

public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Order.Minimal

/-!
# Pragmatic competition

An expression is blocked when one of its alternatives is strictly stronger along a dimension of
content, and it survives competition at a point where its content holds and no alternative whose
content also holds there is strictly stronger. `Blocked` is the first relation and `useCondition`
the set of points of the second, for any alternative source `S → Set S` and content function
`S → Set W`; `sameAssertion` keeps the alternatives with the same at-issue content.

Along at-issue content over the weakly assertable alternatives, blocking is Katzir's
neo-Gricean principle, and along conventional-implicature content it is Lo Guercio's Maximize
Conventional Implicatures. Along presuppositional content over `sameAssertion` it is Heim's
Maximize Presupposition, and its condition at a context, as Schlenker states it, is
`useCondition`: the presupposition less the presuppositions of the strictly stronger
alternatives, Percus's anti-presupposition and Sauerland's implicated presupposition. The
relations carry no theory of why competition obtains, so pragmatic and grammatical accounts of
each principle state their disagreement over one definition.

## Main definitions

* `Alternatives.Blocked`: some alternative is strictly stronger along the content dimension.
* `Alternatives.useCondition`: the points where no alternative whose content holds is strictly
  stronger.
* `Alternatives.sameAssertion`: the alternatives with the same at-issue content.

## Main results

* `Alternatives.mem_useCondition_iff_minimalFor`: an expression is used where it is a most
  specific competitor whose content holds.
* `Alternatives.useCondition_eq_sdiff_biUnion`: the use condition is the content less the
  contents of the strictly stronger alternatives.
* `Alternatives.disjoint_useCondition`: competitors with strictly nested contents are never used
  at the same point.
* `Alternatives.useCondition_anti`: more alternatives, fewer uses.

## References

* [katzir-2007]
* [lo-guercio-2025]
* [heim-1991]
* [schlenker-2012]
* [percus-2006]
* [sauerland-2008a]
-/

@[expose] public section

namespace Alternatives

variable {S W : Type*} {alts alts' : S → Set S} {content assertion : S → Set W} {φ φ' ψ : S}
  {w : W}

/-- `φ` is blocked when some alternative in `alts φ` has strictly stronger `content`. -/
def Blocked (alts : S → Set S) (content : S → Set W) (φ : S) : Prop :=
  ∃ φ' ∈ alts φ, content φ' ⊂ content φ

/-- Blocking is monotone in the alternative source. -/
theorem Blocked.mono (h : alts ≤ alts') (hb : Blocked alts content φ) :
    Blocked alts' content φ :=
  let ⟨φ', hφ', hss⟩ := hb; ⟨φ', h φ hφ', hss⟩

/-- An expression at least as strong as each of its alternatives is not blocked. -/
theorem not_blocked_of_forall_subset (h : ∀ φ' ∈ alts φ, content φ ⊆ content φ') :
    ¬ Blocked alts content φ :=
  fun ⟨φ', hφ', hss⟩ ↦ hss.not_subset (h φ' hφ')

/-- The alternatives of `φ` with the same at-issue content, the competitors Maximize
Presupposition compares. -/
def sameAssertion (assertion : S → Set W) (alts : S → Set S) (φ : S) : Set S :=
  {φ' ∈ alts φ | assertion φ' = assertion φ}

@[simp] theorem mem_sameAssertion :
    φ' ∈ sameAssertion assertion alts φ ↔ φ' ∈ alts φ ∧ assertion φ' = assertion φ :=
  Iff.rfl

theorem sameAssertion_le (assertion : S → Set W) (alts : S → Set S) :
    sameAssertion assertion alts ≤ alts :=
  fun _ _ h ↦ h.1

/-! ### Use conditions -/

/-- `φ` is used at the points where its content holds and it is not blocked by the alternatives
whose content also holds there. -/
def useCondition (alts : S → Set S) (content : S → Set W) (φ : S) : Set W :=
  {w ∈ content φ | ¬ Blocked (fun ψ ↦ {ψ' ∈ alts ψ | w ∈ content ψ'}) content φ}

theorem mem_useCondition_iff :
    w ∈ useCondition alts content φ ↔
      w ∈ content φ ∧ ∀ ψ ∈ alts φ, w ∈ content ψ → ¬ content ψ ⊂ content φ := by
  simp [useCondition, Blocked]

theorem useCondition_subset (alts : S → Set S) (content : S → Set W) (φ : S) :
    useCondition alts content φ ⊆ content φ :=
  fun _ h ↦ h.1

/-- `φ` is used at `w` exactly when it is a most specific competitor whose content holds at `w`,
among itself and its alternatives. -/
theorem mem_useCondition_iff_minimalFor :
    w ∈ useCondition alts content φ ↔
      MinimalFor (fun ψ ↦ ψ ∈ insert φ (alts φ) ∧ w ∈ content ψ) content φ := by
  simp only [mem_useCondition_iff, MinimalFor, Set.mem_insert_iff, true_or, true_and,
    Set.ssubset_iff_subset_ne, not_and, not_not]
  constructor
  · rintro ⟨hw, h⟩
    refine ⟨hw, fun ψ ⟨hψ, hwψ⟩ hle ↦ ?_⟩
    rcases hψ with rfl | hψ
    exacts [le_rfl, (h ψ hψ hwψ hle).ge]
  · rintro ⟨hw, h⟩
    exact ⟨hw, fun ψ hψ hwψ hle ↦ le_antisymm hle (h ⟨Or.inr hψ, hwψ⟩ hle)⟩

/-- The use condition is the content less the content of every strictly stronger alternative,
whose presuppositions are the anti-presupposition when the content is presuppositional. -/
theorem useCondition_eq_sdiff_biUnion (alts : S → Set S) (content : S → Set W) (φ : S) :
    useCondition alts content φ =
      content φ \ ⋃ ψ ∈ {ψ ∈ alts φ | content ψ ⊂ content φ}, content ψ := by
  ext w
  simp only [mem_useCondition_iff, Set.mem_sdiff, Set.mem_iUnion, Set.mem_ofPred_eq, not_exists,
    not_and, exists_prop]
  exact and_congr_right fun _ ↦
    ⟨fun h ψ ⟨hψ, hss⟩ hw ↦ h ψ hψ hw hss, fun h ψ hψ hw hss ↦ h ψ ⟨hψ, hss⟩ hw⟩

/-- With one strictly stronger alternative containing the others, the use condition is the
content less that alternative's content. -/
theorem useCondition_eq_sdiff (hψ : ψ ∈ alts φ) (hss : content ψ ⊂ content φ)
    (hother : ∀ χ ∈ alts φ, content χ ⊂ content φ → content χ ⊆ content ψ) :
    useCondition alts content φ = content φ \ content ψ := by
  ext w
  rw [mem_useCondition_iff, Set.mem_sdiff]
  exact and_congr_right fun _ ↦
    ⟨fun h hw ↦ h ψ hψ hw hss, fun h χ hχ hw hss' ↦ h (hother χ hχ hss' hw)⟩

/-- An expression blocked by no alternative is used wherever its content holds. -/
theorem useCondition_eq_of_not_blocked (h : ¬ Blocked alts content φ) :
    useCondition alts content φ = content φ :=
  (useCondition_subset _ _ _).antisymm fun _ hw ↦
    mem_useCondition_iff.2 ⟨hw, fun ψ hψ _ hss ↦ h ⟨ψ, hψ, hss⟩⟩

/-- Where `φ` is used, no strictly stronger alternative's content holds. -/
theorem disjoint_useCondition_of_ssubset (hψ : ψ ∈ alts φ) (h : content ψ ⊂ content φ) :
    Disjoint (content ψ) (useCondition alts content φ) :=
  Set.disjoint_left.2 fun _ hw hu ↦ (mem_useCondition_iff.1 hu).2 ψ hψ hw h

/-- Two competitors with strictly nested contents are never used at the same point. -/
theorem disjoint_useCondition (hψ : ψ ∈ alts φ) (h : content ψ ⊂ content φ) :
    Disjoint (useCondition alts content ψ) (useCondition alts content φ) :=
  (disjoint_useCondition_of_ssubset hψ h).mono_left (useCondition_subset _ _ _)

/-- An expression is used at fewer points than its content holds exactly when some alternative
with satisfiable content is strictly stronger. -/
theorem useCondition_ssubset_iff :
    useCondition alts content φ ⊂ content φ ↔
      ∃ ψ ∈ alts φ, content ψ ⊂ content φ ∧ (content ψ).Nonempty := by
  refine ⟨fun h ↦ ?_, fun ⟨ψ, hψ, hss, w, hw⟩ ↦ ?_⟩
  · obtain ⟨w, hw, hu⟩ := Set.exists_of_ssubset h
    simp only [mem_useCondition_iff, hw, true_and, not_forall, not_not] at hu
    obtain ⟨ψ, hψ, hwψ, hss⟩ := hu
    exact ⟨ψ, hψ, hss, w, hwψ⟩
  · exact (useCondition_subset _ _ _).ssubset_of_ne fun heq ↦
      Set.disjoint_left.1 (disjoint_useCondition_of_ssubset hψ hss) hw (heq ▸ hss.1 hw)

/-- Enlarging the alternatives shrinks the use condition, so an expression blocked by an
independent factor widens the use of its competitors. -/
theorem useCondition_anti (h : alts ≤ alts') :
    useCondition alts' content φ ⊆ useCondition alts content φ :=
  fun _ hw ↦ ⟨hw.1, fun hb ↦ hw.2 (hb.mono fun χ _ hχ ↦ ⟨h χ hχ.1, hχ.2⟩)⟩

end Alternatives
