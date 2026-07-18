import Linglib.Morphology.Exponence.Containment.Selection
import Linglib.Morphology.Paradigm.Contiguity

/-!
# Containment hierarchies: contiguity and the suppletion generalizations
[bobaljik-2012] [starke-2009] [caha-2009] [declercq-vandenwyngaerd-2017]

The *ABA generalization and its refinements, over the score selection of
`Containment/Selection.lean`. Both engines are *ABA-free (`isContiguous_realize`,
`isContiguous_spellout`), generate exactly the contiguous patterns
(`isContiguous_iff_generable`, `isContiguous_iff_spelloutGenerable`), and are
equigenerative on total realizations (`spelloutGenerable_iff_generable`). The
DM-specific refinements — the terminal-adjacent plateau, *AAB exclusion
(`realize_const_of_grounded`), and the ABC portmanteau prediction
(`exists_portmanteau_of_ne`) — follow from the plateau lemmas of `maxThreshold`.

## Main declarations

* `isContiguous_realize`, `isContiguous_spellout` — *ABA for both readings
* `isContiguous_iff_generable`, `isContiguous_iff_spelloutGenerable` —
  generable = spellable = contiguous
* `spelloutGenerable_iff_generable` — DM/nanosyntax equigenerativity
* `realize_const_of_terminal_adjacent`, `realize_const_of_grounded`,
  `exists_portmanteau_of_ne` — the plateau, *AAB, and portmanteau prediction
-/

namespace Morphology.Containment

variable {n : ℕ} {F : Type*}

/-! ### *ABA for Elsewhere insertion

[bobaljik-2012] ch. 2: with antihomophonous rules, the Elsewhere
competition over a containment hierarchy cannot generate ABA. Formally:
`maxThreshold` is the monotone score, the winner is a function of it, and
antihomophony makes exponents injective in the winner — so realization
factors as monotone-then-injective. -/

theorem isContiguous_realize {v : List (SpanRule n F)} (hAH : Antihomophonous v) :
    IsContiguous (realize v) := by
  intro i j k hij hjk heq
  cases hwi : winner v i with
  | none =>
    have hri : realize v i = none := by simp [realize, hwi]
    have hmtk : maxThreshold v k = ⊥ := realize_eq_none_iff.mp (heq ▸ hri)
    have hmtj : maxThreshold v j = ⊥ := maxThreshold_eq_bot_of_le hmtk hjk
    rw [hri, realize_eq_none_iff.mpr hmtj]
  | some iti =>
    obtain ⟨hiv, hmti⟩ := winner_spec hwi
    have hri : realize v i = some iti.exponent := by simp [realize, hwi]
    cases hwk : winner v k with
    | none =>
      have : realize v k = none := by simp [realize, hwk]
      rw [heq, this] at hri
      exact absurd hri (by simp)
    | some itk =>
      obtain ⟨hkv, hmtk⟩ := winner_spec hwk
      have hrk : realize v k = some itk.exponent := by simp [realize, hwk]
      have hit : iti = itk :=
        hAH _ hiv _ hkv (Option.some.inj (hri.symm.trans (heq.trans hrk)))
      obtain ⟨-, -, -, hτi⟩ := exists_of_maxThreshold_eq_coe hmti
      have hmtj : maxThreshold v j = ↑iti.threshold :=
        maxThreshold_eq_coe_of_between (hit ▸ hmtk) (le_trans hτi hij) hjk
      exact realize_congr (hmti.trans hmtj.symm)

/-! ### The plateau: terminal adjacency generates only `{AAA, ABB}` -/

theorem applicable_eq_of_cap {v : List (SpanRule n F)} {m g g' : Fin n}
    (hcap : ∀ it ∈ v, it.threshold ≤ m) (hg : m ≤ g) (hg' : m ≤ g') :
    applicable v g = applicable v g' := by
  unfold applicable Exponence.applicable
  refine List.filter_congr (λ it hit => ?_)
  simp only [decide_eq_decide, SpanRule.applies_iff]
  exact iff_of_true (le_trans (hcap it hit) hg) (le_trans (hcap it hit) hg')

theorem realize_const_of_cap {v : List (SpanRule n F)} {m g g' : Fin n}
    (hcap : ∀ it ∈ v, it.threshold ≤ m) (hg : m ≤ g) (hg' : m ≤ g') :
    realize v g = realize v g' :=
  realize_congr (by unfold maxThreshold; rw [applicable_eq_of_cap hcap hg hg'])

private theorem threshold_le_one {it : SpanRule 3 F}
    (h0 : (it.spans : ℕ) = 0)
    (hc : ∀ c : Fin 3, it.context = some c → (c : ℕ) = (it.spans : ℕ) + 1) :
    it.threshold ≤ (1 : Fin 3) := by
  have h1 : it.spans ≤ (1 : Fin 3) := by rw [Fin.le_def]; simp [h0]
  unfold SpanRule.threshold
  cases hcx : it.context with
  | none => simpa using h1
  | some c =>
    have h2 : c ≤ (1 : Fin 3) := by rw [Fin.le_def]; simp [hc c hcx, h0]
    simpa using max_le h1 h2

/-- Terminal rules with adjacent contexts have thresholds at most the
first head, so the comparative and superlative cells coincide: only
AAA and ABB root patterns are generable. -/
theorem realize_const_of_terminal_adjacent {v : List (SpanRule 3 F)}
    (hT : Terminal v) (hA : Adjacent v) : realize v 1 = realize v 2 :=
  realize_const_of_cap (m := (1 : Fin 3))
    (λ it hit => threshold_le_one (hT it hit) (hA it hit)) le_rfl (by decide)

/-! ### Completeness: generable = contiguous -/

section Completeness

variable [DecidableEq F]

/-- The earliest grade sharing `g`'s form. -/
def firstOcc (p : Paradigm n F) (g : Fin n) : Fin n :=
  (Finset.univ.filter (λ j => p j = p g)).min' ⟨g, by simp⟩

theorem apply_firstOcc (p : Paradigm n F) (g : Fin n) : p (firstOcc p g) = p g :=
  (Finset.mem_filter.mp
    (Finset.min'_mem (Finset.univ.filter (λ j => p j = p g)) ⟨g, by simp⟩)).2

theorem firstOcc_le (p : Paradigm n F) (g : Fin n) : firstOcc p g ≤ g :=
  Finset.min'_le _ g (by simp)

theorem firstOcc_congr {p : Paradigm n F} {g g' : Fin n} (h : p g = p g') :
    firstOcc p g = firstOcc p g' := by
  have hset : Finset.univ.filter (λ j => p j = p g)
      = Finset.univ.filter (λ j => p j = p g') := by
    ext j; simp [h]
  exact le_antisymm
    (Finset.min'_le _ _ (hset ▸ Finset.min'_mem _ ⟨g', by simp⟩))
    (Finset.min'_le _ _ (hset.symm ▸ Finset.min'_mem _ ⟨g, by simp⟩))

/-- The canonical vocabulary of a pattern: one rule per form,
introduced at the form's first grade and conditioned on it. -/
def ofPattern (p : Paradigm n F) : List (SpanRule n F) :=
  (List.finRange n).filterMap (λ s =>
    if firstOcc p s = s then some ⟨p s, ⟨0, s.pos⟩, some s⟩ else none)

theorem mem_ofPattern {p : Paradigm n F} {it : SpanRule n F} :
    it ∈ ofPattern p ↔
      ∃ s : Fin n, firstOcc p s = s ∧ it = ⟨p s, ⟨0, s.pos⟩, some s⟩ := by
  simp only [ofPattern, List.mem_filterMap, List.mem_finRange, true_and]
  constructor
  · rintro ⟨s, hs⟩
    split at hs
    · exact ⟨s, by assumption, (Option.some.inj hs).symm⟩
    · exact absurd hs (by simp)
  · rintro ⟨s, hfo, rfl⟩
    exact ⟨s, by rw [if_pos hfo]⟩

omit [DecidableEq F] in
theorem threshold_ofPattern {p : Paradigm n F} {s : Fin n} :
    (⟨p s, ⟨0, s.pos⟩, some s⟩ : SpanRule n F).threshold = s := by
  unfold SpanRule.threshold
  simp only [Option.getD_some]
  exact max_eq_right (by rw [Fin.le_def]; exact Nat.zero_le _)

theorem terminal_ofPattern (p : Paradigm n F) : Terminal (ofPattern p) := by
  intro it hit
  obtain ⟨s, -, rfl⟩ := mem_ofPattern.mp hit
  rfl

theorem antihomophonous_ofPattern (p : Paradigm n F) :
    Antihomophonous (ofPattern p) := by
  intro it hit jt hjt hexp
  obtain ⟨s, hs, rfl⟩ := mem_ofPattern.mp hit
  obtain ⟨t, ht, rfl⟩ := mem_ofPattern.mp hjt
  have hst : s = t := by
    rw [← hs, ← ht]; exact firstOcc_congr hexp
  subst hst
  rfl

theorem realize_ofPattern {p : Paradigm n F} (hp : IsContiguous p) (g : Fin n) :
    realize (ofPattern p) g = some (p g) := by
  have hff : firstOcc p (firstOcc p g) = firstOcc p g :=
    firstOcc_congr (apply_firstOcc p g)
  have hitem : (⟨p (firstOcc p g), ⟨0, (firstOcc p g).pos⟩, some (firstOcc p g)⟩ :
      SpanRule n F) ∈ ofPattern p :=
    mem_ofPattern.mpr ⟨firstOcc p g, hff, rfl⟩
  have hub : ∀ jt ∈ ofPattern p, jt.threshold ≤ g →
      jt.threshold ≤ (⟨p (firstOcc p g), ⟨0, (firstOcc p g).pos⟩,
        some (firstOcc p g)⟩ : SpanRule n F).threshold := by
    intro jt hjv hjle
    obtain ⟨t, htfo, rfl⟩ := mem_ofPattern.mp hjv
    rw [threshold_ofPattern] at hjle ⊢
    by_contra hlt
    push Not at hlt
    have hpt : p (firstOcc p g) = p t := hp hlt.le hjle (apply_firstOcc p g)
    have : t = firstOcc p g := by
      rw [← htfo]
      exact (firstOcc_congr hpt.symm).trans hff
    exact absurd this (ne_of_gt hlt)
  have hmt : maxThreshold (ofPattern p) g = ↑(firstOcc p g) := by
    have h := maxThreshold_eq_coe_intro hitem
      (by rw [threshold_ofPattern]; exact firstOcc_le p g) hub
    rwa [threshold_ofPattern] at h
  obtain ⟨w, hw⟩ := exists_winner_of_coe hmt
  obtain ⟨hwv, hwt⟩ := winner_spec hw
  have hwτ : w.threshold = firstOcc p g :=
    WithBot.coe_inj.mp (hwt.symm.trans hmt)
  obtain ⟨t, htfo, rfl⟩ := mem_ofPattern.mp hwv
  rw [threshold_ofPattern] at hwτ
  subst hwτ
  show (winner (ofPattern p) g).map SpanRule.exponent = some (p g)
  rw [hw, Option.map_some]
  exact congrArg some (apply_firstOcc p g)

end Completeness

/-- A pattern is **Elsewhere-generable**: some terminal antihomophonous
vocabulary realizes it in full. -/
def ElsewhereGenerable (p : Paradigm n F) : Prop :=
  ∃ v : List (SpanRule n F), Terminal v ∧ Antihomophonous v ∧
    ∀ g, realize v g = some (p g)

/-- **Generable = contiguous.** A fully realized pattern arises from
Elsewhere insertion over a terminal antihomophonous vocabulary iff it
is contiguous: the forward direction is the canonical-vocabulary
construction, the backward direction CSG1. -/
theorem isContiguous_iff_generable (p : Paradigm n F) :
    IsContiguous p ↔ ElsewhereGenerable p := by
  classical
  constructor
  · intro hp
    exact ⟨ofPattern p, terminal_ofPattern p, antihomophonous_ofPattern p,
      realize_ofPattern hp⟩
  · rintro ⟨v, -, hAH, hreal⟩
    intro i j k hij hjk heq
    have h1 : realize v i = realize v k := by rw [hreal i, hreal k, heq]
    have h2 := isContiguous_realize hAH hij hjk h1
    rw [hreal i, hreal j] at h2
    exact Option.some.inj h2

/-! ### Three-grade hierarchies: *AAB and the portmanteau prediction -/

/-- **CSG2 / *AAB exclusion** ([bobaljik-2012] ch. 5). Over the three-grade
degree hierarchy, if the positive and comparative cells agree and the
superlative cell is realized, all three agree — `good – gooder – *best` is not
generable — given antihomophony and `Grounded` (the book's condition (202)). -/
theorem realize_const_of_grounded {v : List (SpanRule 3 F)}
    (hAH : Antihomophonous v) (hG : Grounded v)
    (h01 : realize v 0 = realize v 1) (h2 : (realize v 2).isSome) :
    realize v 1 = realize v 2 := by
  obtain ⟨w2, hw2⟩ : ∃ w, winner v 2 = some w := by
    cases hw : winner v 2 with
    | some w => exact ⟨w, rfl⟩
    | none => rw [show realize v 2 = none from by simp [realize, hw]] at h2; simp at h2
  obtain ⟨hw2v, hmt2⟩ := winner_spec hw2
  by_cases hτ : w2.threshold ≤ (1 : Fin 3)
  · exact realize_congr ((maxThreshold_eq_coe_of_between hmt2 hτ (by decide)).trans hmt2.symm)
  · exfalso
    push Not at hτ
    obtain ⟨jt1, hjt1v, hjt1τ⟩ := hG w2 hw2v 1 hτ
    have hmt1 : maxThreshold v 1 = ↑(1 : Fin 3) := by
      have := maxThreshold_eq_coe_intro hjt1v (le_of_eq hjt1τ)
        (λ kt hkv hkle => hjt1τ ▸ hkle)
      rwa [hjt1τ] at this
    obtain ⟨w1, hw1⟩ := exists_winner_of_coe hmt1
    obtain ⟨hw1v, hmt1'⟩ := winner_spec hw1
    have hw1τ : w1.threshold = 1 := (WithBot.coe_inj.mp (hmt1.symm.trans hmt1')).symm
    have h1 : realize v 1 = some w1.exponent := by simp [realize, hw1]
    have h0 : realize v 0 = some w1.exponent := h01.trans h1
    obtain ⟨w0, hw0⟩ : ∃ w, winner v 0 = some w := by
      cases hw : winner v 0 with
      | some w => exact ⟨w, rfl⟩
      | none => rw [show realize v 0 = none from by simp [realize, hw]] at h0; simp at h0
    obtain ⟨hw0v, hmt0⟩ := winner_spec hw0
    have hexp : w0.exponent = w1.exponent :=
      Option.some.inj ((show realize v 0 = some w0.exponent from by
        simp [realize, hw0]).symm.trans h0)
    have heq01 : w0 = w1 := hAH _ hw0v _ hw1v hexp
    obtain ⟨-, -, -, hle0⟩ := exists_of_maxThreshold_eq_coe hmt0
    rw [heq01, hw1τ] at hle0
    exact absurd hle0 (by decide)

/-- **ABC requires a portmanteau** ([bobaljik-2012] §5.3.1, the
degree-domain consequence generalized there as (199)): under
adjacency, root allomorphy at the superlative grade distinct from the
comparative grade arises only via a portmanteau — the winning rule
must expone more than the bare root (Latin `opt-`, Welsh `gor-`). -/
theorem exists_portmanteau_of_ne {v : List (SpanRule 3 F)} (hA : Adjacent v)
    (h12 : realize v 1 ≠ realize v 2) :
    ∃ it ∈ v, winner v 2 = some it ∧ 0 < (it.spans : ℕ) := by
  obtain ⟨w2, hw2⟩ : ∃ w, winner v 2 = some w := by
    cases hw : winner v 2 with
    | some w => exact ⟨w, rfl⟩
    | none =>
      have hmt2 : maxThreshold v 2 = ⊥ := winner_eq_none_iff.mp hw
      have hmt1 : maxThreshold v 1 = ⊥ := maxThreshold_eq_bot_of_le hmt2 (by decide)
      exact absurd (realize_congr (hmt1.trans hmt2.symm)) h12
  obtain ⟨hw2v, hmt2⟩ := winner_spec hw2
  refine ⟨w2, hw2v, hw2, ?_⟩
  by_contra htop
  push Not at htop
  have hτle : w2.threshold ≤ (1 : Fin 3) :=
    threshold_le_one (Nat.le_zero.mp htop) (hA w2 hw2v)
  exact h12 (realize_congr
    ((maxThreshold_eq_coe_of_between hmt2 hτle (by decide)).trans hmt2.symm))

/-! ### *ABA for Superset spellout

The mirror image of `isContiguous_realize`: `minSpan` is monotone in the
grade, the winner is a function of it, and antihomophony makes the winner's
exponent injective — so spellout fibers are convex ([caha-2009]). -/

theorem isContiguous_spellout {v : List (SpanRule n F)}
    (hAH : Antihomophonous v) : IsContiguous (spellout v) := by
  intro i j k hij hjk heq
  cases hwi : spelloutWinner v i with
  | none =>
    have hri : spellout v i = none := by simp [spellout, hwi]
    have hmsj : minSpan v j = ⊤ :=
      minSpan_eq_top_of_le (spelloutWinner_eq_none_iff.mp hwi) hij
    rw [hri, spellout_eq_none_iff.mpr hmsj]
  | some iti =>
    obtain ⟨hiv, hmsi⟩ := spelloutWinner_spec hwi
    have hri : spellout v i = some iti.exponent := by simp [spellout, hwi]
    cases hwk : spelloutWinner v k with
    | none =>
      have : spellout v k = none := by simp [spellout, hwk]
      rw [heq, this] at hri
      exact absurd hri (by simp)
    | some itk =>
      obtain ⟨hkv, hmsk⟩ := spelloutWinner_spec hwk
      have hrk : spellout v k = some itk.exponent := by simp [spellout, hwk]
      have hit : iti = itk :=
        hAH _ hiv _ hkv (Option.some.inj (hri.symm.trans (heq.trans hrk)))
      obtain ⟨-, -, -, hks⟩ := exists_of_minSpan_eq_coe (hit ▸ hmsk)
      have hmsj : minSpan v j = ↑iti.spans :=
        minSpan_eq_coe_of_between hmsi hij (le_trans hjk hks)
      exact spellout_congr (hmsi.trans hmsj.symm)

/-! ### Completeness: spellable = contiguous -/

section Completeness

variable [DecidableEq F]

/-- The latest grade sharing `g`'s form. -/
def lastOcc (p : Paradigm n F) (g : Fin n) : Fin n :=
  (Finset.univ.filter (λ j => p j = p g)).max' ⟨g, by simp⟩

theorem apply_lastOcc (p : Paradigm n F) (g : Fin n) : p (lastOcc p g) = p g :=
  (Finset.mem_filter.mp
    (Finset.max'_mem (Finset.univ.filter (λ j => p j = p g)) ⟨g, by simp⟩)).2

theorem le_lastOcc (p : Paradigm n F) (g : Fin n) : g ≤ lastOcc p g :=
  Finset.le_max' _ g (by simp)

theorem lastOcc_congr {p : Paradigm n F} {g g' : Fin n} (h : p g = p g') :
    lastOcc p g = lastOcc p g' := by
  have hset : Finset.univ.filter (λ j => p j = p g)
      = Finset.univ.filter (λ j => p j = p g') := by
    ext j; simp [h]
  exact le_antisymm
    (Finset.le_max' _ _ (hset.symm ▸ Finset.max'_mem _ ⟨g, by simp⟩))
    (Finset.le_max' _ _ (hset ▸ Finset.max'_mem _ ⟨g', by simp⟩))

/-- The canonical nanosyntax lexicon of a pattern: one context-free
entry per form, storing the form's largest constituent. -/
def spelloutOfPattern (p : Paradigm n F) : List (SpanRule n F) :=
  (List.finRange n).filterMap (λ s =>
    if lastOcc p s = s then some ⟨p s, s, none⟩ else none)

theorem mem_spelloutOfPattern {p : Paradigm n F} {it : SpanRule n F} :
    it ∈ spelloutOfPattern p ↔
      ∃ s : Fin n, lastOcc p s = s ∧ it = ⟨p s, s, none⟩ := by
  simp only [spelloutOfPattern, List.mem_filterMap, List.mem_finRange, true_and]
  constructor
  · rintro ⟨s, hs⟩
    split at hs
    · exact ⟨s, by assumption, (Option.some.inj hs).symm⟩
    · exact absurd hs (by simp)
  · rintro ⟨s, hlo, rfl⟩
    exact ⟨s, by rw [if_pos hlo]⟩

theorem contextFree_spelloutOfPattern (p : Paradigm n F) :
    ContextFree (spelloutOfPattern p) := by
  intro it hit
  obtain ⟨s, -, rfl⟩ := mem_spelloutOfPattern.mp hit
  rfl

theorem antihomophonous_spelloutOfPattern (p : Paradigm n F) :
    Antihomophonous (spelloutOfPattern p) := by
  intro it hit jt hjt hexp
  obtain ⟨s, hs, rfl⟩ := mem_spelloutOfPattern.mp hit
  obtain ⟨t, ht, rfl⟩ := mem_spelloutOfPattern.mp hjt
  have hst : s = t := by
    rw [← hs, ← ht]; exact lastOcc_congr hexp
  subst hst
  rfl

theorem spellout_spelloutOfPattern {p : Paradigm n F} (hp : IsContiguous p)
    (g : Fin n) : spellout (spelloutOfPattern p) g = some (p g) := by
  have hll : lastOcc p (lastOcc p g) = lastOcc p g :=
    lastOcc_congr (apply_lastOcc p g)
  have hitem : (⟨p (lastOcc p g), lastOcc p g, none⟩ : SpanRule n F)
      ∈ spelloutOfPattern p :=
    mem_spelloutOfPattern.mpr ⟨lastOcc p g, hll, rfl⟩
  have hlb : ∀ jt ∈ spelloutOfPattern p, g ≤ jt.spans →
      (⟨p (lastOcc p g), lastOcc p g, none⟩ : SpanRule n F).spans ≤ jt.spans := by
    intro jt hjv hjle
    obtain ⟨t, htlo, rfl⟩ := mem_spelloutOfPattern.mp hjv
    show lastOcc p g ≤ t
    by_contra hlt
    push Not at hlt
    have hpt : p g = p t := hp hjle hlt.le (apply_lastOcc p g).symm
    have : t = lastOcc p g := by
      rw [← htlo]
      exact lastOcc_congr hpt.symm
    exact absurd this (ne_of_lt hlt)
  have hms : minSpan (spelloutOfPattern p) g = ↑(lastOcc p g) :=
    minSpan_eq_coe_intro hitem (le_lastOcc p g) hlb
  obtain ⟨w, hw⟩ := exists_spelloutWinner_of_coe hms
  obtain ⟨hwv, hws⟩ := spelloutWinner_spec hw
  have hwsp : w.spans = lastOcc p g := WithTop.coe_inj.mp (hws.symm.trans hms)
  obtain ⟨t, htlo, rfl⟩ := mem_spelloutOfPattern.mp hwv
  have : t = lastOcc p g := hwsp
  subst this
  show (spelloutWinner (spelloutOfPattern p) g).map SpanRule.exponent
      = some (p g)
  rw [hw, Option.map_some]
  exact congrArg some (apply_lastOcc p g)

end Completeness

/-- A pattern is **Superset-spellable**: some context-free
antihomophonous lexicon spells it out in full. -/
def SupersetSpellable (p : Paradigm n F) : Prop :=
  ∃ v : List (SpanRule n F), ContextFree v ∧ Antihomophonous v ∧
    ∀ g, spellout v g = some (p g)

/-- **Spellable = contiguous**: a fully realized pattern arises from
Superset spellout over a context-free antihomophonous lexicon iff it
is contiguous — [caha-2009]'s Universal Contiguity as a theorem of the
engine; the converse sharpens it to exact generative capacity. -/
theorem isContiguous_iff_spelloutGenerable (p : Paradigm n F) :
    IsContiguous p ↔ SupersetSpellable p := by
  classical
  constructor
  · intro hp
    exact ⟨spelloutOfPattern p, contextFree_spelloutOfPattern p,
      antihomophonous_spelloutOfPattern p, spellout_spelloutOfPattern hp⟩
  · rintro ⟨v, -, hAH, hreal⟩
    intro i j k hij hjk heq
    have h1 : spellout v i = spellout v k := by rw [hreal i, hreal k, heq]
    have h2 := isContiguous_spellout hAH hij hjk h1
    rw [hreal i, hreal j] at h2
    exact Option.some.inj h2

/-- **DM and nanosyntax are equigenerative over linear containment
hierarchies**: Superset spellout from context-free antihomophonous
lexicons and Elsewhere insertion from terminal antihomophonous
vocabularies generate exactly the same fully realized patterns — the
contiguous ones. The frameworks differ intensionally (rule format and
selection direction) but not in generative capacity on this fragment. -/
theorem spelloutGenerable_iff_generable (p : Paradigm n F) :
    SupersetSpellable p ↔ ElsewhereGenerable p :=
  (isContiguous_iff_spelloutGenerable p).symm.trans (isContiguous_iff_generable p)

/-! ### Where the frameworks diverge

On partial lexicons the selection directions come apart: an overspecified
entry realizes smaller structures under the Superset Principle but leaves a
gap under Elsewhere insertion — nanosyntax's characteristic prediction
([declercq-vandenwyngaerd-2017]) against DM's characteristic gaps. -/

example : spellout [(⟨"gwell", 1, none⟩ : SpanRule 3 String)] 0 = some "gwell" := by decide

example : realize [(⟨"gwell", 1, none⟩ : SpanRule 3 String)] 0 = none := by decide

/-! ### Antihomophony is necessary for *ABA

Two distinct entries sharing an exponent — accidental homophony, an
`Antihomophonous` violation — generate ABA. [caha-2009] distinguishes
accidental homophony (phonological) from systematic syncretism (one item
over a contiguous span); the `Antihomophonous` hypothesis is that distinction. -/

/-- Accidental homophony: "A" stored at two non-adjacent grades. -/
private def homophonous : List (SpanRule 3 String) :=
  [⟨"A", 0, none⟩, ⟨"B", 1, none⟩, ⟨"A", 2, none⟩]

example : ¬ Antihomophonous homophonous := by decide

example :
    spellout homophonous 0 = some "A" ∧
    spellout homophonous 1 = some "B" ∧
    spellout homophonous 2 = some "A" := by decide

end Morphology.Containment
