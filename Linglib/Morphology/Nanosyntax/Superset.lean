import Linglib.Morphology.Exponence.Hierarchy

/-!
# Superset spellout over containment hierarchies
[starke-2009] [caha-2009] [bobaljik-2012]

The static core of the nanosyntax selection rule (no cyclic override
or spellout-driven movement), stated over the same `ExponenceRule`
vocabularies as the Elsewhere engine of
`Morphology/Exponence/Hierarchy.lean`. A nanosyntax lexical entry
stores a constituent and carries no contextual restriction
(`ContextFree`); it can spell out any structure it *contains* — the
Superset Principle ([starke-2009]) — and competition selects the
smallest matching entry (Minimize Junk, which [starke-2009] himself
identifies with the Elsewhere Condition: the directional asymmetry
lives in the matching relation, not in the competition). The two
engines are dual: Elsewhere insertion maximizes the threshold over
rules the *structure contains*; Superset spellout minimizes the span
over entries that *contain the structure*.

The headline is the cross-framework theorem
`spelloutGenerable_iff_generable`: over a linear containment hierarchy,
Superset spellout from context-free antihomophonous entries and
Elsewhere insertion from terminal antihomophonous rules generate
exactly the same fully-realized patterns — the contiguous ones. The
frameworks are extensionally equivalent on this fragment while
differing intensionally: an overspecified entry realizes *smaller*
structures under Superset but yields a gap under Elsewhere insertion
(see the divergence examples at the end), which is how nanosyntax
derives ABC with no contextual apparatus — suppletion as pure phrasal
spellout, portmanteau by constituent size with no environment
restriction ([declercq-vandenwyngaerd-2017] for exactly this Latin
degree case) — where DM needs the context-restricted portmanteau of
[bobaljik-2012] ch. 5.

## Main declarations

* `ExponenceRule.Matches` — the Superset Principle: entry contains the
  target structure
* `ContextFree` — the nanosyntax restriction on vocabularies
* `minSpan`, `spelloutWinner`, `spellout` — Minimize-Junk competition
  and the realized pattern
* `isContiguous_spellout` — *ABA for Superset spellout
* `isContiguous_iff_spelloutGenerable` — spellable = contiguous
* `spelloutGenerable_iff_generable` — DM/nanosyntax equigenerativity

Tree-structured phrasal spellout
(`Morphology/Nanosyntax/TreeSpellout.lean`) generalizes this
rank-based engine: for right-branching chains, tree containment
reduces to rank comparison (`chain_contains_iff_le`).
-/

namespace Morphology.Containment

variable {n : ℕ} {F : Type*}

/-! ### The Superset Principle -/

/-- The **Superset Principle** ([starke-2009]): an entry can spell out
grade `g` when the constituent it stores contains grade `g`'s
structure. Anti-monotone in `g`, dually to `AppliesAt`. -/
def ExponenceRule.Matches (it : ExponenceRule n F) (g : Fin n) : Prop :=
  g ≤ it.spans

instance (it : ExponenceRule n F) (g : Fin n) : Decidable (it.Matches g) :=
  inferInstanceAs (Decidable (_ ≤ _))

theorem ExponenceRule.Matches.anti {it : ExponenceRule n F} {g g' : Fin n}
    (h : it.Matches g') (hg : g ≤ g') : it.Matches g :=
  le_trans hg h

/-- Minimize Junk derived, dually to
`ExponenceRule.moreSpecific_iff_threshold_le`: an entry matches in a
subset of the structures another matches in iff it stores the smaller
constituent — smallest-match selection is Pāṇinian specificity under
superset matching. -/
theorem ExponenceRule.matches_imp_iff_spans_le {it jt : ExponenceRule n F} :
    (∀ ⦃g : Fin n⦄, it.Matches g → jt.Matches g) ↔ it.spans ≤ jt.spans :=
  ⟨λ h => h (le_refl it.spans), λ h _ hg => le_trans hg h⟩

/-- The nanosyntax restriction, in the pointer-free idealization of
[caha-2009]: entries store bare constituents, with no DM-style
contextual environment. -/
def ContextFree (v : List (ExponenceRule n F)) : Prop :=
  ∀ it ∈ v, it.context = none

instance (v : List (ExponenceRule n F)) : Decidable (ContextFree v) := by
  unfold ContextFree; infer_instance

/-! ### Minimize-Junk competition -/

/-- The entries matching at grade `g`, in vocabulary order. -/
def matching (v : List (ExponenceRule n F)) (g : Fin n) : List (ExponenceRule n F) :=
  v.filter (λ it => it.Matches g)

@[simp] theorem mem_matching {v : List (ExponenceRule n F)} {g : Fin n}
    {it : ExponenceRule n F} :
    it ∈ matching v g ↔ it ∈ v ∧ g ≤ it.spans := by
  simp [matching, ExponenceRule.Matches]

/-- The least matching span at grade `g` — Minimize Junk: the winning
entry stores as little unrealized structure as possible. `⊤` when no
entry matches. -/
def minSpan (v : List (ExponenceRule n F)) (g : Fin n) : WithTop (Fin n) :=
  ((matching v g).map ExponenceRule.spans).minimum

theorem minSpan_eq_top_iff {v : List (ExponenceRule n F)} {g : Fin n} :
    minSpan v g = ⊤ ↔ matching v g = [] := by
  rw [minSpan, List.minimum_eq_top, List.map_eq_nil_iff]

theorem exists_of_minSpan_eq_coe {v : List (ExponenceRule n F)} {g m : Fin n}
    (h : minSpan v g = ↑m) : ∃ it ∈ v, it.spans = m ∧ g ≤ m := by
  obtain ⟨hmem, -⟩ := List.minimum_eq_coe_iff.mp h
  obtain ⟨it, hit, hsp⟩ := List.mem_map.mp hmem
  obtain ⟨hitv, hle⟩ := mem_matching.mp hit
  exact ⟨it, hitv, hsp, hsp ▸ hle⟩

theorem le_spans_of_minSpan_eq_coe {v : List (ExponenceRule n F)} {g m : Fin n}
    (h : minSpan v g = ↑m) {it : ExponenceRule n F} (hitv : it ∈ v)
    (hle : g ≤ it.spans) : m ≤ it.spans :=
  (List.minimum_eq_coe_iff.mp h).2 _
    (List.mem_map_of_mem (mem_matching.mpr ⟨hitv, hle⟩))

theorem minSpan_eq_coe_intro {v : List (ExponenceRule n F)} {g : Fin n}
    {it : ExponenceRule n F} (hitv : it ∈ v) (hle : g ≤ it.spans)
    (hlb : ∀ jt ∈ v, g ≤ jt.spans → it.spans ≤ jt.spans) :
    minSpan v g = ↑it.spans := by
  rw [minSpan, List.minimum_eq_coe_iff]
  refine ⟨List.mem_map_of_mem (mem_matching.mpr ⟨hitv, hle⟩), λ b hb => ?_⟩
  obtain ⟨jt, hjt, rfl⟩ := List.mem_map.mp hb
  obtain ⟨hjv, hjle⟩ := mem_matching.mp hjt
  exact hlb jt hjv hjle

/-- The key transfer lemma, dual to `maxThreshold_eq_coe_of_le`: a
winning span persists upward as long as the grade stays inside it. -/
theorem minSpan_eq_coe_of_between {v : List (ExponenceRule n F)} {g g' m : Fin n}
    (h : minSpan v g = ↑m) (hg : g ≤ g') (hm : g' ≤ m) : minSpan v g' = ↑m := by
  obtain ⟨it, hitv, hsp, -⟩ := exists_of_minSpan_eq_coe h
  subst hsp
  exact minSpan_eq_coe_intro hitv hm
    (λ jt hjv hjle => le_spans_of_minSpan_eq_coe h hjv (le_trans hg hjle))

theorem minSpan_eq_top_of_le {v : List (ExponenceRule n F)} {g g' : Fin n}
    (h : minSpan v g = ⊤) (hg : g ≤ g') : minSpan v g' = ⊤ := by
  rw [minSpan_eq_top_iff] at h ⊢
  rw [List.eq_nil_iff_forall_not_mem] at h ⊢
  intro it hit
  obtain ⟨hv, hle⟩ := mem_matching.mp hit
  exact h it (mem_matching.mpr ⟨hv, le_trans hg hle⟩)

/-- The spellout winner at grade `g`: the first entry attaining the
least matching span. -/
def spelloutWinner (v : List (ExponenceRule n F)) (g : Fin n) :
    Option (ExponenceRule n F) :=
  (minSpan v g).recTopCoe none (λ m => v.find? (λ it => it.spans == m))

theorem spelloutWinner_eq_none_of_top {v : List (ExponenceRule n F)} {g : Fin n}
    (h : minSpan v g = ⊤) : spelloutWinner v g = none := by
  rw [spelloutWinner, h]; rfl

theorem spelloutWinner_of_coe {v : List (ExponenceRule n F)} {g m : Fin n}
    (h : minSpan v g = ↑m) :
    spelloutWinner v g = v.find? (λ it => it.spans == m) := by
  rw [spelloutWinner, h]; rfl

theorem spelloutWinner_spec {v : List (ExponenceRule n F)} {g : Fin n}
    {it : ExponenceRule n F} (h : spelloutWinner v g = some it) :
    it ∈ v ∧ minSpan v g = ↑it.spans := by
  cases hms : minSpan v g with
  | top => rw [spelloutWinner_eq_none_of_top hms] at h; exact absurd h (by simp)
  | coe m =>
    rw [spelloutWinner_of_coe hms] at h
    have hsp : it.spans = m := by simpa using List.find?_some h
    exact ⟨List.mem_of_find?_eq_some h, by rw [hsp]⟩

theorem exists_spelloutWinner_of_coe {v : List (ExponenceRule n F)} {g m : Fin n}
    (h : minSpan v g = ↑m) : ∃ it, spelloutWinner v g = some it := by
  rw [spelloutWinner_of_coe h]
  obtain ⟨it, hitv, hsp, -⟩ := exists_of_minSpan_eq_coe h
  cases hf : v.find? (λ jt => jt.spans == m) with
  | some jt => exact ⟨jt, rfl⟩
  | none =>
    rw [List.find?_eq_none] at hf
    exact absurd (by simp [hsp] : (it.spans == m) = true) (by simpa using hf it hitv)

theorem spelloutWinner_eq_none_iff {v : List (ExponenceRule n F)} {g : Fin n} :
    spelloutWinner v g = none ↔ minSpan v g = ⊤ := by
  refine ⟨λ h => ?_, spelloutWinner_eq_none_of_top⟩
  cases hms : minSpan v g with
  | top => rfl
  | coe m =>
    obtain ⟨it, hit⟩ := exists_spelloutWinner_of_coe hms
    rw [hit] at h
    exact absurd h (by simp)

theorem spelloutWinner_congr {v : List (ExponenceRule n F)} {g g' : Fin n}
    (h : minSpan v g = minSpan v g') : spelloutWinner v g = spelloutWinner v g' := by
  rw [spelloutWinner, spelloutWinner, h]

/-- The spelled-out pattern: at each grade, the Minimize-Junk winner's
exponent (`none` when no entry contains the structure — a spellout
gap; full nanosyntax would attempt rescue operations before declaring
ineffability). -/
def spellout (v : List (ExponenceRule n F)) : Paradigm n (Option F) :=
  λ g => (spelloutWinner v g).map ExponenceRule.exponent

theorem spellout_congr {v : List (ExponenceRule n F)} {g g' : Fin n}
    (h : minSpan v g = minSpan v g') : spellout v g = spellout v g' := by
  show (spelloutWinner v g).map _ = (spelloutWinner v g').map _
  rw [spelloutWinner_congr h]

theorem spellout_eq_none_iff {v : List (ExponenceRule n F)} {g : Fin n} :
    spellout v g = none ↔ minSpan v g = ⊤ := by
  rw [← spelloutWinner_eq_none_iff]
  unfold spellout
  cases spelloutWinner v g <;> simp

/-- Spellout gaps propagate upward: an entry matching a higher grade
would match the lower one too, so a gap at `g` forces gaps at every
`g' ≥ g` — [dekier-2021]'s paradigm-gap monotonicity for indefinites. -/
theorem spellout_eq_none_of_le {v : List (ExponenceRule n F)} {g g' : Fin n}
    (h : spellout v g = none) (hg : g ≤ g') : spellout v g' = none :=
  spellout_eq_none_iff.mpr
    (minSpan_eq_top_of_le (spellout_eq_none_iff.mp h) hg)

/-! ### *ABA for Superset spellout

The mirror image of `isContiguous_realize`: `minSpan` is monotone in
the grade (matching sets shrink upward, so the least span weakly
grows), the winner is a function of it, and antihomophony makes
the winner's exponent injective — so spellout fibers are convex. This
is the nanosyntax derivation of *ABA ([caha-2009]), run on the same
vocabulary type as the DM derivation. -/

theorem isContiguous_spellout {v : List (ExponenceRule n F)}
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
def spelloutOfPattern (p : Paradigm n F) : List (ExponenceRule n F) :=
  (List.finRange n).filterMap (λ s =>
    if lastOcc p s = s then some ⟨p s, s, none⟩ else none)

theorem mem_spelloutOfPattern {p : Paradigm n F} {it : ExponenceRule n F} :
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
  have hitem : (⟨p (lastOcc p g), lastOcc p g, none⟩ : ExponenceRule n F)
      ∈ spelloutOfPattern p :=
    mem_spelloutOfPattern.mpr ⟨lastOcc p g, hll, rfl⟩
  have hlb : ∀ jt ∈ spelloutOfPattern p, g ≤ jt.spans →
      (⟨p (lastOcc p g), lastOcc p g, none⟩ : ExponenceRule n F).spans ≤ jt.spans := by
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
  show (spelloutWinner (spelloutOfPattern p) g).map ExponenceRule.exponent
      = some (p g)
  rw [hw, Option.map_some]
  exact congrArg some (apply_lastOcc p g)

end Completeness

/-- A pattern is **Superset-spellable**: some context-free
antihomophonous lexicon spells it out in full. -/
def SupersetSpellable (p : Paradigm n F) : Prop :=
  ∃ v : List (ExponenceRule n F), ContextFree v ∧ Antihomophonous v ∧
    ∀ g, spellout v g = some (p g)

/-- **Spellable = contiguous**: a fully realized pattern arises from
Superset spellout over a context-free antihomophonous lexicon iff it
is contiguous — [caha-2009]'s Universal Contiguity as a theorem of the
engine, mirroring Caha's own derivation of UC from the Superset
Principle; the converse direction sharpens it to exact generative
capacity. -/
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
selection direction; see the divergence examples below) but not in
generative capacity on this fragment. -/
theorem spelloutGenerable_iff_generable (p : Paradigm n F) :
    SupersetSpellable p ↔ ElsewhereGenerable p :=
  (isContiguous_iff_spelloutGenerable p).symm.trans (isContiguous_iff_generable p)

/-! ### Where the frameworks diverge

The equivalence is extensional, over total realizations. On partial
lexicons the selection directions come apart: an overspecified entry
realizes smaller structures under the Superset Principle but leaves a
gap under Elsewhere insertion. This is nanosyntax's characteristic
prediction — overspecified entries double as defaults for smaller
structures — against DM's characteristic gaps. -/

example : spellout [(⟨"gwell", 1, none⟩ : ExponenceRule 3 String)] 0
    = some "gwell" := by decide

example : realize [(⟨"gwell", 1, none⟩ : ExponenceRule 3 String)] 0
    = none := by decide

/-! ### Antihomophony is necessary for *ABA

Two distinct entries sharing an exponent — accidental homophony, an
`Antihomophonous` violation — generate ABA: with "A" stored at grades 0
and 2 and "B" at grade 1, Minimize Junk yields A–B–A. [caha-2009]
distinguishes accidental homophony (phonological) from systematic
syncretism (one item over a contiguous span); the `Antihomophonous`
hypothesis of `isContiguous_spellout` is exactly that distinction. -/

/-- Accidental homophony: "A" stored at two non-adjacent grades. -/
private def homophonous : List (ExponenceRule 3 String) :=
  [⟨"A", 0, none⟩, ⟨"B", 1, none⟩, ⟨"A", 2, none⟩]

example : ¬ Antihomophonous homophonous := by decide

example :
    spellout homophonous 0 = some "A" ∧
    spellout homophonous 1 = some "B" ∧
    spellout homophonous 2 = some "A" := by decide

/-! ### The shared exponence core

One carrier, two `Rule` views: the Subset reading
(`ExponenceRule.toRule`, `Morphology/Exponence/Hierarchy.lean`) and the
Superset reading below instantiate the shared core with dual
applicability conditions and opposite derived-specificity orders. -/

section ExponenceCore

open Morphology.Exponence

/-- View an entry under the **Superset** reading as a rule of the
shared exponence core: applicability is `Matches` (the stored
constituent contains the structure), dually to `ExponenceRule.toRule`'s
Subset reading. -/
def ExponenceRule.toSupersetRule (it : ExponenceRule n F) :
    Exponence.Rule (Fin n) F :=
  ⟨it.exponent, it.Matches⟩

/-- Minimize Junk is the shared core's specificity order under the
Superset reading: smaller span = more specific. -/
theorem ExponenceRule.toSupersetRule_le_iff
    {it jt : ExponenceRule n F} :
    it.toSupersetRule ≤ jt.toSupersetRule ↔ it.spans ≤ jt.spans :=
  Exponence.Rule.le_iff.trans ExponenceRule.matches_imp_iff_spans_le

/-- **Subset/Superset duality** over context-free vocabularies (the
nanosyntax idealization): DM-style Subset specificity of `it` over `jt`
is Superset specificity of `jt` over `it`. With contextual restrictions
the Subset order compares thresholds, not spans, and the duality is
only one-directional. -/
theorem ExponenceRule.toRule_le_iff_toSupersetRule_le
    {it jt : ExponenceRule n F}
    (hit : it.context = none) (hjt : jt.context = none) :
    it.toRule ≤ jt.toRule ↔
      jt.toSupersetRule ≤ it.toSupersetRule := by
  rw [ExponenceRule.toRule_le_iff,
    ExponenceRule.moreSpecific_iff_threshold_le,
    ExponenceRule.toSupersetRule_le_iff]
  unfold ExponenceRule.threshold
  rw [hit, hjt]
  simp

/-- Minimize-Junk selection is an Elsewhere winner of the shared core
under the Superset reading — with no side conditions: over a linear
hierarchy the span order is total, so the least-span match is maximally
specific. -/
theorem spelloutWinner_isElsewhereWinner {v : List (ExponenceRule n F)}
    {g : Fin n} {it : ExponenceRule n F}
    (h : spelloutWinner v g = some it) :
    Exponence.IsElsewhereWinner (v.map ExponenceRule.toSupersetRule) g
      it.toSupersetRule := by
  obtain ⟨hmem, hms⟩ := spelloutWinner_spec h
  obtain ⟨-, -, -, hle⟩ := exists_of_minSpan_eq_coe hms
  refine ⟨⟨List.mem_map_of_mem hmem, hle⟩, ?_⟩
  rintro s ⟨hs, hsapp⟩ -
  obtain ⟨jt, hjt, rfl⟩ := List.mem_map.mp hs
  rw [ExponenceRule.toSupersetRule_le_iff]
  exact le_spans_of_minSpan_eq_coe hms hjt hsapp

end ExponenceCore

end Morphology.Containment
