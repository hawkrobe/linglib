import Linglib.Morphology.Exponence.Containment.Defs
import Linglib.Morphology.Exponence.Select
import Linglib.Morphology.Paradigm.Basic
import Mathlib.Data.List.MinMax
import Mathlib.Data.Finset.Max

/-!
# Containment hierarchies: score selection
[bobaljik-2012] [starke-2009] [caha-2009] [kiparsky-1973]

Elsewhere insertion and Superset spellout. The DM `winner` maximizes
`threshold` as an instantiation of the core's `Exponence.selectBy`, so
`winner_isElsewhereWinner` is an instance of `selectBy_isElsewhereWinner`
discharged by `moreSpecific_iff_threshold_le`. The nanosyntax
`spelloutWinner` minimizes `spans`; its `SupersetRule` carrier is a
semireducible synonym that does not sit cleanly under `selectBy`, so it
runs on `SpanRule` directly and `spelloutWinner_isElsewhereWinner`
transports the result onto the core's Superset reading. `maxThreshold`
and `minSpan` are the score aggregates the plateau theorems
(`Containment/Contiguity.lean`) reason about — contexts and scores share
`Fin n`.

## Main declarations

* `winner`, `realize` — Elsewhere selection and the realized pattern
* `spelloutWinner`, `spellout` — Minimize-Junk selection and the spelled pattern
* `winner_isElsewhereWinner`, `spelloutWinner_isElsewhereWinner` — both are
  Elsewhere winners of the shared core
* `maxThreshold`, `minSpan` — the score aggregates, with their transfer lemmas
-/

namespace Morphology.Containment

variable {n : ℕ} {F : Type*}

/-! ### General list helpers -/

/-- On a list with an attained upper bound `m` for `f`, `argmax` is the
first element with score exactly `m`. -/
private theorem argmax_eq_find {α β : Type*} [LinearOrder β] [DecidableEq β]
    (f : α → β) (m : β) : ∀ (l : List α), (∀ a ∈ l, f a ≤ m) → m ∈ l.map f →
    l.argmax f = l.find? (fun x => f x == m)
  | [], _, h => by simp at h
  | x :: xs, hub, hattain => by
    have hxm : f x ≤ m := hub x (List.mem_cons_self ..)
    rw [List.argmax_cons, List.find?_cons]
    by_cases hx : f x = m
    · have hbeq : (f x == m) = true := by simpa using hx
      simp only [hbeq]
      cases hxs : xs.argmax f with
      | none => rfl
      | some c =>
        have hc : f c ≤ m := hub c (List.mem_cons_of_mem _ (List.argmax_mem hxs))
        have hcx : f c ≤ f x := by rw [hx]; exact hc
        simp only [if_neg (not_lt.mpr hcx)]
    · have hbeq : (f x == m) = false := by simpa using hx
      simp only [hbeq]
      have hmxs : m ∈ xs.map f := by
        simp only [List.map_cons, List.mem_cons] at hattain
        rcases hattain with h | h
        · exact absurd h.symm hx
        · exact h
      have hubxs : ∀ a ∈ xs, f a ≤ m := fun a ha => hub a (List.mem_cons_of_mem _ ha)
      have IH := argmax_eq_find f m xs hubxs hmxs
      cases hxs : xs.argmax f with
      | none => rw [List.argmax_eq_none] at hxs; subst hxs; simp at hmxs
      | some c =>
        rw [hxs] at IH
        have hcm : f c = m := by simpa using List.find?_some IH.symm
        have hxc : f x < f c := by rw [hcm]; exact lt_of_le_of_ne hxm hx
        simp only [if_pos hxc, IH]

/-- `find?` ignores a filter that keeps every match. -/
private theorem find?_filter_of_imp {α : Type*} {p q : α → Bool}
    (h : ∀ a, q a = true → p a = true) : ∀ (l : List α),
    (l.filter p).find? q = l.find? q
  | [] => rfl
  | x :: xs => by
    rw [List.filter_cons]
    by_cases hp : p x = true
    · rw [if_pos hp, List.find?_cons, List.find?_cons, find?_filter_of_imp h xs]
    · rw [if_neg hp, find?_filter_of_imp h xs, List.find?_cons]
      have hq : q x = false := by
        by_contra hqx; exact hp (h x (by simpa using hqx))
      simp [hq]

/-! ### Subset reading: Elsewhere selection -/

/-- The rules applicable at grade `g`, in vocabulary order. -/
abbrev applicable (v : List (SpanRule n F)) (g : Fin n) : List (SpanRule n F) :=
  Exponence.applicable v g

theorem mem_applicable {v : List (SpanRule n F)} {g : Fin n} {it : SpanRule n F} :
    it ∈ applicable v g ↔ it ∈ v ∧ it.threshold ≤ g := by
  simp [Exponence.mem_applicable]

/-- The greatest applicable threshold at grade `g` — the specificity
level of the Elsewhere winner, `⊥` when nothing applies. -/
def maxThreshold (v : List (SpanRule n F)) (g : Fin n) : WithBot (Fin n) :=
  ((applicable v g).map SpanRule.threshold).maximum

theorem maxThreshold_eq_bot_iff {v : List (SpanRule n F)} {g : Fin n} :
    maxThreshold v g = ⊥ ↔ applicable v g = [] := by
  rw [maxThreshold, List.maximum_eq_bot, List.map_eq_nil_iff]

theorem exists_of_maxThreshold_eq_coe {v : List (SpanRule n F)} {g m : Fin n}
    (h : maxThreshold v g = ↑m) : ∃ it ∈ v, it.threshold = m ∧ m ≤ g := by
  obtain ⟨hmem, -⟩ := List.maximum_eq_coe_iff.mp h
  obtain ⟨it, hit, hτ⟩ := List.mem_map.mp hmem
  obtain ⟨hitv, hle⟩ := mem_applicable.mp hit
  exact ⟨it, hitv, hτ, hτ ▸ hle⟩

theorem threshold_le_of_maxThreshold_eq_coe {v : List (SpanRule n F)} {g m : Fin n}
    (h : maxThreshold v g = ↑m) {it : SpanRule n F} (hitv : it ∈ v)
    (hle : it.threshold ≤ g) : it.threshold ≤ m :=
  (List.maximum_eq_coe_iff.mp h).2 _
    (List.mem_map_of_mem (mem_applicable.mpr ⟨hitv, hle⟩))

theorem maxThreshold_eq_coe_intro {v : List (SpanRule n F)} {g : Fin n}
    {it : SpanRule n F} (hitv : it ∈ v) (hle : it.threshold ≤ g)
    (hub : ∀ jt ∈ v, jt.threshold ≤ g → jt.threshold ≤ it.threshold) :
    maxThreshold v g = ↑it.threshold := by
  rw [maxThreshold, List.maximum_eq_coe_iff]
  refine ⟨List.mem_map_of_mem (mem_applicable.mpr ⟨hitv, hle⟩), λ b hb => ?_⟩
  obtain ⟨jt, hjt, rfl⟩ := List.mem_map.mp hb
  obtain ⟨hjv, hjle⟩ := mem_applicable.mp hjt
  exact hub jt hjv hjle

/-- A winning threshold persists downward as long as it stays applicable,
which is what makes Elsewhere selection plateau between grades. -/
theorem maxThreshold_eq_coe_of_between {v : List (SpanRule n F)} {g g' m : Fin n}
    (h : maxThreshold v g' = ↑m) (hm : m ≤ g) (hg : g ≤ g') :
    maxThreshold v g = ↑m := by
  obtain ⟨it, hitv, hτ, -⟩ := exists_of_maxThreshold_eq_coe h
  subst hτ
  exact maxThreshold_eq_coe_intro hitv hm
    (λ jt hjv hjle => threshold_le_of_maxThreshold_eq_coe h hjv (le_trans hjle hg))

theorem maxThreshold_eq_bot_of_le {v : List (SpanRule n F)} {g g' : Fin n}
    (h : maxThreshold v g' = ⊥) (hg : g ≤ g') : maxThreshold v g = ⊥ := by
  rw [maxThreshold_eq_bot_iff] at h ⊢
  rw [List.eq_nil_iff_forall_not_mem] at h ⊢
  intro it hit
  obtain ⟨hv, hle⟩ := mem_applicable.mp hit
  exact h it (mem_applicable.mpr ⟨hv, le_trans hle hg⟩)

/-- The Elsewhere winner at grade `g`: the applicable rule with greatest
threshold — the most specific applicable rule — as `Exponence.selectBy`. -/
def winner (v : List (SpanRule n F)) (g : Fin n) : Option (SpanRule n F) :=
  Exponence.selectBy SpanRule.threshold v g

theorem winner_eq_none_of_bot {v : List (SpanRule n F)} {g : Fin n}
    (h : maxThreshold v g = ⊥) : winner v g = none :=
  Exponence.selectBy_eq_none_iff.mpr (maxThreshold_eq_bot_iff.mp h)

theorem winner_of_coe {v : List (SpanRule n F)} {g m : Fin n}
    (h : maxThreshold v g = ↑m) :
    winner v g = v.find? (λ it => it.threshold == m) := by
  obtain ⟨it₀, hit₀v, hτ₀, hmg⟩ := exists_of_maxThreshold_eq_coe h
  have step1 : winner v g = (applicable v g).find? (λ it => it.threshold == m) :=
    argmax_eq_find SpanRule.threshold m (applicable v g)
      (fun a ha => threshold_le_of_maxThreshold_eq_coe h
        (mem_applicable.mp ha).1 (mem_applicable.mp ha).2)
      (by
        rw [List.mem_map]
        exact ⟨it₀, mem_applicable.mpr ⟨hit₀v, by rw [hτ₀]; exact hmg⟩, hτ₀⟩)
  rw [step1]
  refine find?_filter_of_imp (fun a ha => ?_) v
  have hthr : a.threshold = m := by simpa using ha
  exact decide_eq_true (SpanRule.applies_iff.mpr (by rw [hthr]; exact hmg))

theorem winner_spec {v : List (SpanRule n F)} {g : Fin n} {it : SpanRule n F}
    (h : winner v g = some it) :
    it ∈ v ∧ maxThreshold v g = ↑it.threshold := by
  cases hmt : maxThreshold v g with
  | bot => rw [winner_eq_none_of_bot hmt] at h; exact absurd h (by simp)
  | coe m =>
    rw [winner_of_coe hmt] at h
    have hτ : it.threshold = m := by simpa using List.find?_some h
    exact ⟨List.mem_of_find?_eq_some h, by rw [hτ]⟩

theorem exists_winner_of_coe {v : List (SpanRule n F)} {g m : Fin n}
    (h : maxThreshold v g = ↑m) : ∃ it, winner v g = some it := by
  rw [winner_of_coe h]
  obtain ⟨it, hitv, hτ, -⟩ := exists_of_maxThreshold_eq_coe h
  cases hf : v.find? (λ jt => jt.threshold == m) with
  | some jt => exact ⟨jt, rfl⟩
  | none =>
    rw [List.find?_eq_none] at hf
    exact absurd (by simp [hτ] : (it.threshold == m) = true) (by simpa using hf it hitv)

theorem winner_eq_none_iff {v : List (SpanRule n F)} {g : Fin n} :
    winner v g = none ↔ maxThreshold v g = ⊥ := by
  refine ⟨λ h => ?_, winner_eq_none_of_bot⟩
  cases hmt : maxThreshold v g with
  | bot => rfl
  | coe m =>
    obtain ⟨it, hit⟩ := exists_winner_of_coe hmt
    rw [hit] at h
    exact absurd h (by simp)

theorem winner_congr {v : List (SpanRule n F)} {g g' : Fin n}
    (h : maxThreshold v g = maxThreshold v g') : winner v g = winner v g' := by
  cases hmt : maxThreshold v g with
  | bot => rw [winner_eq_none_of_bot hmt, winner_eq_none_of_bot (h ▸ hmt)]
  | coe m => rw [winner_of_coe hmt, winner_of_coe (h ▸ hmt)]

/-- The realized pattern: at each grade, the Elsewhere winner's
exponent (`none` when no rule applies — a paradigm gap). Definitionally
`Exponence.realize SpanRule.threshold`. -/
def realize (v : List (SpanRule n F)) : Paradigm n (Option F) :=
  λ g => (winner v g).map SpanRule.exponent

theorem realize_congr {v : List (SpanRule n F)} {g g' : Fin n}
    (h : maxThreshold v g = maxThreshold v g') : realize v g = realize v g' := by
  show (winner v g).map _ = (winner v g').map _
  rw [winner_congr h]

theorem realize_eq_none_iff {v : List (SpanRule n F)} {g : Fin n} :
    realize v g = none ↔ maxThreshold v g = ⊥ := by
  rw [← winner_eq_none_iff]
  show (winner v g).map _ = none ↔ _
  cases winner v g <;> simp

/-- The containment engine's Elsewhere winner is an Elsewhere winner of
the shared core — an instance of `selectBy_isElsewhereWinner`. -/
theorem winner_isElsewhereWinner {v : List (SpanRule n F)} {g : Fin n}
    {it : SpanRule n F} (h : winner v g = some it) :
    Exponence.IsElsewhereWinner v g it :=
  Exponence.selectBy_isElsewhereWinner
    (fun r _ s _ _ _ => (SpanRule.le_iff.trans SpanRule.moreSpecific_iff_threshold_le :
      r ≤ s ↔ SpanRule.threshold s ≤ SpanRule.threshold r)) h

/-! ### Superset reading: Minimize-Junk selection

The dual engine, on the `SupersetRule` reading. The nanosyntax lexical
entry stores a constituent and can spell out any structure it contains,
with competition selecting the smallest matching entry (Minimize Junk).
`spelloutWinner` selects by least matching span; `minSpan` is the score
aggregate the completeness lemmas reason about. The `SupersetRule`
carrier is a semireducible synonym, so the selection here runs directly
on `SpanRule`; `spelloutWinner_isElsewhereWinner` transports the result
onto the superset reading of the shared core. -/

/-- The entries matching at grade `g`, in vocabulary order. -/
def matching (v : List (SpanRule n F)) (g : Fin n) : List (SpanRule n F) :=
  v.filter (λ it => it.Matches g)

@[simp] theorem mem_matching {v : List (SpanRule n F)} {g : Fin n}
    {it : SpanRule n F} :
    it ∈ matching v g ↔ it ∈ v ∧ g ≤ it.spans := by
  simp [matching, SpanRule.Matches]

/-- The least matching span at grade `g` — Minimize Junk: the winning
entry stores as little unrealized structure as possible. `⊤` when no
entry matches. -/
def minSpan (v : List (SpanRule n F)) (g : Fin n) : WithTop (Fin n) :=
  ((matching v g).map SpanRule.spans).minimum

theorem minSpan_eq_top_iff {v : List (SpanRule n F)} {g : Fin n} :
    minSpan v g = ⊤ ↔ matching v g = [] := by
  rw [minSpan, List.minimum_eq_top, List.map_eq_nil_iff]

theorem exists_of_minSpan_eq_coe {v : List (SpanRule n F)} {g m : Fin n}
    (h : minSpan v g = ↑m) : ∃ it ∈ v, it.spans = m ∧ g ≤ m := by
  obtain ⟨hmem, -⟩ := List.minimum_eq_coe_iff.mp h
  obtain ⟨it, hit, hsp⟩ := List.mem_map.mp hmem
  obtain ⟨hitv, hle⟩ := mem_matching.mp hit
  exact ⟨it, hitv, hsp, hsp ▸ hle⟩

theorem le_spans_of_minSpan_eq_coe {v : List (SpanRule n F)} {g m : Fin n}
    (h : minSpan v g = ↑m) {it : SpanRule n F} (hitv : it ∈ v)
    (hle : g ≤ it.spans) : m ≤ it.spans :=
  (List.minimum_eq_coe_iff.mp h).2 _
    (List.mem_map_of_mem (mem_matching.mpr ⟨hitv, hle⟩))

theorem minSpan_eq_coe_intro {v : List (SpanRule n F)} {g : Fin n}
    {it : SpanRule n F} (hitv : it ∈ v) (hle : g ≤ it.spans)
    (hlb : ∀ jt ∈ v, g ≤ jt.spans → it.spans ≤ jt.spans) :
    minSpan v g = ↑it.spans := by
  rw [minSpan, List.minimum_eq_coe_iff]
  refine ⟨List.mem_map_of_mem (mem_matching.mpr ⟨hitv, hle⟩), λ b hb => ?_⟩
  obtain ⟨jt, hjt, rfl⟩ := List.mem_map.mp hb
  obtain ⟨hjv, hjle⟩ := mem_matching.mp hjt
  exact hlb jt hjv hjle

/-- The key transfer lemma, dual to `maxThreshold_eq_coe_of_between`: a
winning span persists upward as long as the grade stays inside it. -/
theorem minSpan_eq_coe_of_between {v : List (SpanRule n F)} {g g' m : Fin n}
    (h : minSpan v g = ↑m) (hg : g ≤ g') (hm : g' ≤ m) : minSpan v g' = ↑m := by
  obtain ⟨it, hitv, hsp, -⟩ := exists_of_minSpan_eq_coe h
  subst hsp
  exact minSpan_eq_coe_intro hitv hm
    (λ jt hjv hjle => le_spans_of_minSpan_eq_coe h hjv (le_trans hg hjle))

theorem minSpan_eq_top_of_le {v : List (SpanRule n F)} {g g' : Fin n}
    (h : minSpan v g = ⊤) (hg : g ≤ g') : minSpan v g' = ⊤ := by
  rw [minSpan_eq_top_iff] at h ⊢
  rw [List.eq_nil_iff_forall_not_mem] at h ⊢
  intro it hit
  obtain ⟨hv, hle⟩ := mem_matching.mp hit
  exact h it (mem_matching.mpr ⟨hv, le_trans hg hle⟩)

/-- The spellout winner at grade `g`: the first entry attaining the
least matching span. -/
def spelloutWinner (v : List (SpanRule n F)) (g : Fin n) :
    Option (SpanRule n F) :=
  (minSpan v g).recTopCoe none (λ m => v.find? (λ it => it.spans == m))

theorem spelloutWinner_eq_none_of_top {v : List (SpanRule n F)} {g : Fin n}
    (h : minSpan v g = ⊤) : spelloutWinner v g = none := by
  rw [spelloutWinner, h]; rfl

theorem spelloutWinner_of_coe {v : List (SpanRule n F)} {g m : Fin n}
    (h : minSpan v g = ↑m) :
    spelloutWinner v g = v.find? (λ it => it.spans == m) := by
  rw [spelloutWinner, h]; rfl

theorem spelloutWinner_spec {v : List (SpanRule n F)} {g : Fin n}
    {it : SpanRule n F} (h : spelloutWinner v g = some it) :
    it ∈ v ∧ minSpan v g = ↑it.spans := by
  cases hms : minSpan v g with
  | top => rw [spelloutWinner_eq_none_of_top hms] at h; exact absurd h (by simp)
  | coe m =>
    rw [spelloutWinner_of_coe hms] at h
    have hsp : it.spans = m := by simpa using List.find?_some h
    exact ⟨List.mem_of_find?_eq_some h, by rw [hsp]⟩

theorem exists_spelloutWinner_of_coe {v : List (SpanRule n F)} {g m : Fin n}
    (h : minSpan v g = ↑m) : ∃ it, spelloutWinner v g = some it := by
  rw [spelloutWinner_of_coe h]
  obtain ⟨it, hitv, hsp, -⟩ := exists_of_minSpan_eq_coe h
  cases hf : v.find? (λ jt => jt.spans == m) with
  | some jt => exact ⟨jt, rfl⟩
  | none =>
    rw [List.find?_eq_none] at hf
    exact absurd (by simp [hsp] : (it.spans == m) = true) (by simpa using hf it hitv)

theorem spelloutWinner_eq_none_iff {v : List (SpanRule n F)} {g : Fin n} :
    spelloutWinner v g = none ↔ minSpan v g = ⊤ := by
  refine ⟨λ h => ?_, spelloutWinner_eq_none_of_top⟩
  cases hms : minSpan v g with
  | top => rfl
  | coe m =>
    obtain ⟨it, hit⟩ := exists_spelloutWinner_of_coe hms
    rw [hit] at h
    exact absurd h (by simp)

theorem spelloutWinner_congr {v : List (SpanRule n F)} {g g' : Fin n}
    (h : minSpan v g = minSpan v g') : spelloutWinner v g = spelloutWinner v g' := by
  rw [spelloutWinner, spelloutWinner, h]

/-- The spelled-out pattern: at each grade, the Minimize-Junk winner's
exponent (`none` when no entry contains the structure — a spellout
gap). -/
def spellout (v : List (SpanRule n F)) : Paradigm n (Option F) :=
  λ g => (spelloutWinner v g).map SpanRule.exponent

theorem spellout_congr {v : List (SpanRule n F)} {g g' : Fin n}
    (h : minSpan v g = minSpan v g') : spellout v g = spellout v g' := by
  show (spelloutWinner v g).map _ = (spelloutWinner v g').map _
  rw [spelloutWinner_congr h]

theorem spellout_eq_none_iff {v : List (SpanRule n F)} {g : Fin n} :
    spellout v g = none ↔ minSpan v g = ⊤ := by
  rw [← spelloutWinner_eq_none_iff]
  unfold spellout
  cases spelloutWinner v g <;> simp

/-- Spellout gaps propagate upward: an entry matching a higher grade
would match the lower one too, so a gap at `g` forces gaps at every
`g' ≥ g` — [dekier-2021]'s paradigm-gap monotonicity for indefinites. -/
theorem spellout_eq_none_of_le {v : List (SpanRule n F)} {g g' : Fin n}
    (h : spellout v g = none) (hg : g ≤ g') : spellout v g' = none :=
  spellout_eq_none_iff.mpr
    (minSpan_eq_top_of_le (spellout_eq_none_iff.mp h) hg)

/-- Minimize-Junk selection is an Elsewhere winner of the shared core
under the Superset reading — with no side conditions: over a linear
hierarchy the span order is total, so the least-span match is maximally
specific. -/
theorem spelloutWinner_isElsewhereWinner {v : List (SpanRule n F)}
    {g : Fin n} {it : SpanRule n F} (h : spelloutWinner v g = some it) :
    Exponence.IsElsewhereWinner (v.map SpanRule.superset) g it.superset := by
  obtain ⟨hmem, hms⟩ := spelloutWinner_spec h
  obtain ⟨-, -, -, hle⟩ := exists_of_minSpan_eq_coe hms
  refine ⟨⟨List.mem_map_of_mem hmem, hle⟩, ?_⟩
  rintro s ⟨hs, hsapp⟩ -
  obtain ⟨jt, hjt, rfl⟩ := List.mem_map.mp hs
  rw [SupersetRule.le_iff]
  exact le_spans_of_minSpan_eq_coe hms hjt hsapp

end Morphology.Containment
