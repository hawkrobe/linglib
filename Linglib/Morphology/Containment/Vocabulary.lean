import Linglib.Morphology.Paradigm.Contiguity
import Mathlib.Data.List.MinMax
import Mathlib.Data.Finset.Max

/-!
# Vocabularies over containment hierarchies: Elsewhere insertion
[bobaljik-2012] [halle-marantz-1993] [kiparsky-1973]

The realizational engine behind [bobaljik-2012]'s comparative-suppletion
generalizations, stated over an arbitrary `n`-grade containment
hierarchy. An `ExponenceRule` realizes the initial span `[0, spans]` of
the hierarchy (the root, possibly fused with the first `spans` heads —
the portmanteau exponence of [bobaljik-2012]'s ch. 5, via Fusion (196)
or Radkevich's Vocabulary Insertion Principle (197)), optionally
conditioned on the presence of a higher head. Selection at each grade
is by the Elsewhere Condition ([kiparsky-1973]): the most specific
applicable rule wins, where Pāṇinian specificity is *derived* as
applicability-set inclusion
(`ExponenceRule.moreSpecific_iff_threshold_le`) — over a linear
hierarchy applicability sets are nested upward sets, so the Elsewhere
ordering is total.

Each of [bobaljik-2012]'s generalizations is a theorem with its own
hypothesis set, mirroring the book's cost accounting:

* CSG1 / *ABA (`isContiguous_realize`): Antihomophony alone — the
  book's ch. 2 derivation from containment + Elsewhere + the
  antihomophony assumption (44). The homophony loophole is real: a
  non-antihomophonous vocabulary generating surface ABA is exhibited in
  `Studies/Bobaljik2012.lean`.
* Completeness (`isContiguous_iff_generable`): generable = contiguous
  over terminal antihomophonous vocabularies.
* The plateau (`realize_const_of_terminal_adjacent`): terminal rules +
  adjacent contexts generate only `{AAA, ABB}` — the
  Bobaljik-minus-portmanteaux fragment, which over-excludes the
  attested ABC (Latin *bon- ~ mel- ~ opt-*); portmanteau rules repair it.
* CSG2 / *AAB (`csg2`): Antihomophony + `Grounded` (the book's
  markedness condition (202)). The book blocks the two AAB routes by
  two mechanisms — adjacency for root-rules conditioned across an
  intervening head (190a), condition (202) for context-sensitive
  portmanteaux (201); under the threshold encoding both reduce to
  downward closure of the threshold set, so one hypothesis suffices.
* ABC requires a portmanteau (`exists_portmanteau_of_ne`;
  [bobaljik-2012] §5.3.1, the degree-domain consequence generalized
  there as (199)): under adjacency, superlative-grade root allomorphy
  distinct from the comparative grade arises only via a portmanteau
  rule.

## Main declarations

* `ExponenceRule n F` — rule of exponence: exponent, exponed span
  `[0, spans]`, optional conditioning head
* `Terminal`, `Adjacent`, `Antihomophonous`, `Grounded` — the axiom
  Props on vocabularies, à la carte
* `winner`, `realize` — Elsewhere selection and the realized pattern
* `isContiguous_realize`, `isContiguous_iff_generable`,
  `realize_const_of_terminal_adjacent`, `csg2`,
  `exists_portmanteau_of_ne`

The dual Superset engine lives in
`Morphology/Containment/Superset.lean`; synthetic/analytic structure
(Merger) in `Morphology/DM/Merger.lean`; the n = 3 degree
instantiations with the book's worked vocabularies in
`Studies/Bobaljik2012.lean`.
-/

namespace Morphology.Containment

variable {n : ℕ} {F : Type*}

/-! ### Rules of exponence and derived specificity -/

/-- A **rule of exponence** ([bobaljik-2012]'s term — Matthews's
*exponence*, used in the realizational sense of [stump-2001]) over an
`n`-grade containment hierarchy. The rule realizes the initial span
`[0, spans]` — the root when `spans = 0`, a root+heads portmanteau
when `spans > 0` — and applies only when the (optional) conditioning
head `context` is present in the structure. DM vocabulary items are
the `Terminal`-restricted special case; nanosyntax lexical entries
share the context-free span format but pair it with Superset-based
selection (`Morphology/Containment/Superset.lean`) rather than this
file's containment-directed `AppliesAt`, so the insertion semantics
differs.
Latin ([bobaljik-2012] (204)): `bon` is `⟨bon, 0, none⟩`, `mel-` is
`⟨mel, 0, some 1⟩`, the portmanteau `opt-` is `⟨opt, 1, some 2⟩`. -/
structure ExponenceRule (n : ℕ) (F : Type*) where
  /-- The phonological exponent inserted for the span. -/
  exponent : F
  /-- Upper end of the exponed initial span `[0, spans]`. -/
  spans : Fin n
  /-- Head whose presence conditions the rule, if any. -/
  context : Option (Fin n)
  deriving DecidableEq, Repr

namespace ExponenceRule

/-- The least grade at which the rule is applicable: everything the
rule mentions — exponed span and conditioning context — must be
contained in the structure. -/
def threshold (it : ExponenceRule n F) : Fin n :=
  max it.spans (it.context.getD it.spans)

/-- A rule applies at grade `g` when grade `g`'s structure contains
everything the rule mentions. -/
def AppliesAt (it : ExponenceRule n F) (g : Fin n) : Prop :=
  it.threshold ≤ g

instance (it : ExponenceRule n F) (g : Fin n) : Decidable (it.AppliesAt g) :=
  inferInstanceAs (Decidable (_ ≤ _))

theorem appliesAt_iff {it : ExponenceRule n F} {g : Fin n} :
    it.AppliesAt g ↔ it.spans ≤ g ∧ ∀ c : Fin n, it.context = some c → c ≤ g := by
  unfold AppliesAt threshold
  cases hc : it.context with
  | none => simp
  | some c => simp

/-- Pāṇinian specificity: `it` is at least as specific as `jt` when it
applies in a subset of the structures `jt` applies in. -/
def MoreSpecific (it jt : ExponenceRule n F) : Prop :=
  ∀ ⦃g : Fin n⦄, it.AppliesAt g → jt.AppliesAt g

/-- Over a linear containment hierarchy, applicability sets are nested
upward sets, so derived specificity is threshold comparison — the
Elsewhere ordering ([kiparsky-1973]) is total and needs no stipulated
specificity ranking. -/
theorem moreSpecific_iff_threshold_le {it jt : ExponenceRule n F} :
    it.MoreSpecific jt ↔ jt.threshold ≤ it.threshold :=
  ⟨λ h => h (le_refl it.threshold), λ h _ hg => le_trans h hg⟩

end ExponenceRule

/-! ### Well-formedness conditions on vocabularies

Each generalization below hypothesizes exactly the conditions it
needs; vocabularies violating a condition witness the corresponding
unattested pattern (see the worked examples in
`Studies/Bobaljik2012.lean`). -/

/-- No portmanteaux: every rule expones the bare root. -/
def Terminal (v : List (ExponenceRule n F)) : Prop :=
  ∀ it ∈ v, (it.spans : ℕ) = 0

instance (v : List (ExponenceRule n F)) : Decidable (Terminal v) := by
  unfold Terminal; infer_instance

/-- Conditioning heads are adjacent to the exponed span —
[bobaljik-2012]'s (tentatively adopted) adjacency condition on
contextual allomorphy. -/
def Adjacent (v : List (ExponenceRule n F)) : Prop :=
  ∀ it ∈ v, ∀ c : Fin n, it.context = some c → (c : ℕ) = (it.spans : ℕ) + 1

instance (v : List (ExponenceRule n F)) : Decidable (Adjacent v) := by
  unfold Adjacent; infer_instance

/-- Distinct rules carry distinct exponents — [bobaljik-2012]'s
Antihomophony assumption (44), closing the loophole of a surface-ABA
pattern that is really an ABC with accidental A ≡ C homophony. Stated
as pairwise antihomophony, a mild strengthening of the book's
default-vs-contextual formulation; all worked vocabularies satisfy
it. -/
def Antihomophonous (v : List (ExponenceRule n F)) : Prop :=
  ∀ it ∈ v, ∀ jt ∈ v, it.exponent = jt.exponent → it = jt

instance [DecidableEq F] (v : List (ExponenceRule n F)) : Decidable (Antihomophonous v) := by
  unfold Antihomophonous; infer_instance

/-- [bobaljik-2012]'s markedness condition (202): a context-sensitive
rule of exponence involving a node requires a context-free rule
involving that node. A rule is context-free *for* the node `[0, k]`
when nothing it mentions extends beyond `k` — i.e. its threshold is
`k` (the book's fn. 15 rewrites Latin `mel- / __]CMPR]` as the
node-level context-free `GOOD, CMPR → mel-CMPR`) — so (202) says the
vocabulary's threshold set is downward closed. On `Adjacent`
vocabularies this is exactly the book's condition; on non-adjacent
ones it is a mild strengthening (it also covers the skipped-head items
the book independently excludes by adjacency). -/
def Grounded (v : List (ExponenceRule n F)) : Prop :=
  ∀ it ∈ v, ∀ k : Fin n, k < it.threshold → ∃ jt ∈ v, jt.threshold = k

instance (v : List (ExponenceRule n F)) : Decidable (Grounded v) := by
  unfold Grounded; infer_instance

/-! ### Elsewhere selection -/

/-- The rules applicable at grade `g`, in vocabulary order. -/
def applicable (v : List (ExponenceRule n F)) (g : Fin n) : List (ExponenceRule n F) :=
  v.filter (λ it => it.threshold ≤ g)

@[simp] theorem mem_applicable {v : List (ExponenceRule n F)} {g : Fin n} {it : ExponenceRule n F} :
    it ∈ applicable v g ↔ it ∈ v ∧ it.threshold ≤ g := by
  simp [applicable]

/-- The greatest applicable threshold at grade `g` — the specificity
level of the Elsewhere winner, `⊥` when nothing applies. -/
def maxThreshold (v : List (ExponenceRule n F)) (g : Fin n) : WithBot (Fin n) :=
  ((applicable v g).map ExponenceRule.threshold).maximum

theorem maxThreshold_eq_bot_iff {v : List (ExponenceRule n F)} {g : Fin n} :
    maxThreshold v g = ⊥ ↔ applicable v g = [] := by
  rw [maxThreshold, List.maximum_eq_bot, List.map_eq_nil_iff]

theorem exists_of_maxThreshold_eq_coe {v : List (ExponenceRule n F)} {g m : Fin n}
    (h : maxThreshold v g = ↑m) : ∃ it ∈ v, it.threshold = m ∧ m ≤ g := by
  obtain ⟨hmem, -⟩ := List.maximum_eq_coe_iff.mp h
  obtain ⟨it, hit, hτ⟩ := List.mem_map.mp hmem
  obtain ⟨hitv, hle⟩ := mem_applicable.mp hit
  exact ⟨it, hitv, hτ, hτ ▸ hle⟩

theorem threshold_le_of_maxThreshold_eq_coe {v : List (ExponenceRule n F)} {g m : Fin n}
    (h : maxThreshold v g = ↑m) {it : ExponenceRule n F} (hitv : it ∈ v)
    (hle : it.threshold ≤ g) : it.threshold ≤ m :=
  (List.maximum_eq_coe_iff.mp h).2 _
    (List.mem_map_of_mem (mem_applicable.mpr ⟨hitv, hle⟩))

theorem maxThreshold_eq_coe_intro {v : List (ExponenceRule n F)} {g : Fin n}
    {it : ExponenceRule n F} (hitv : it ∈ v) (hle : it.threshold ≤ g)
    (hub : ∀ jt ∈ v, jt.threshold ≤ g → jt.threshold ≤ it.threshold) :
    maxThreshold v g = ↑it.threshold := by
  rw [maxThreshold, List.maximum_eq_coe_iff]
  refine ⟨List.mem_map_of_mem (mem_applicable.mpr ⟨hitv, hle⟩), λ b hb => ?_⟩
  obtain ⟨jt, hjt, rfl⟩ := List.mem_map.mp hb
  obtain ⟨hjv, hjle⟩ := mem_applicable.mp hjt
  exact hub jt hjv hjle

/-- The key transfer lemma: a winning threshold persists downward as
long as it stays applicable. With monotone applicability this is what
makes Elsewhere selection plateau between grades. -/
theorem maxThreshold_eq_coe_of_between {v : List (ExponenceRule n F)} {g g' m : Fin n}
    (h : maxThreshold v g' = ↑m) (hm : m ≤ g) (hg : g ≤ g') :
    maxThreshold v g = ↑m := by
  obtain ⟨it, hitv, hτ, -⟩ := exists_of_maxThreshold_eq_coe h
  subst hτ
  exact maxThreshold_eq_coe_intro hitv hm
    (λ jt hjv hjle => threshold_le_of_maxThreshold_eq_coe h hjv (le_trans hjle hg))

theorem maxThreshold_eq_bot_of_le {v : List (ExponenceRule n F)} {g g' : Fin n}
    (h : maxThreshold v g' = ⊥) (hg : g ≤ g') : maxThreshold v g = ⊥ := by
  rw [maxThreshold_eq_bot_iff] at h ⊢
  rw [List.eq_nil_iff_forall_not_mem] at h ⊢
  intro it hit
  obtain ⟨hv, hle⟩ := mem_applicable.mp hit
  exact h it (mem_applicable.mpr ⟨hv, le_trans hle hg⟩)

/-- The Elsewhere winner at grade `g`: the first rule attaining the
greatest applicable threshold. By
`ExponenceRule.moreSpecific_iff_threshold_le`, this is the most specific
applicable rule. -/
def winner (v : List (ExponenceRule n F)) (g : Fin n) : Option (ExponenceRule n F) :=
  (maxThreshold v g).recBotCoe none (λ m => v.find? (λ it => it.threshold == m))

theorem winner_eq_none_of_bot {v : List (ExponenceRule n F)} {g : Fin n}
    (h : maxThreshold v g = ⊥) : winner v g = none := by
  rw [winner, h]; rfl

theorem winner_of_coe {v : List (ExponenceRule n F)} {g m : Fin n}
    (h : maxThreshold v g = ↑m) :
    winner v g = v.find? (λ it => it.threshold == m) := by
  rw [winner, h]; rfl

theorem winner_spec {v : List (ExponenceRule n F)} {g : Fin n} {it : ExponenceRule n F}
    (h : winner v g = some it) :
    it ∈ v ∧ maxThreshold v g = ↑it.threshold := by
  cases hmt : maxThreshold v g with
  | bot => rw [winner_eq_none_of_bot hmt] at h; exact absurd h (by simp)
  | coe m =>
    rw [winner_of_coe hmt] at h
    have hτ : it.threshold = m := by simpa using List.find?_some h
    exact ⟨List.mem_of_find?_eq_some h, by rw [hτ]⟩

theorem exists_winner_of_coe {v : List (ExponenceRule n F)} {g m : Fin n}
    (h : maxThreshold v g = ↑m) : ∃ it, winner v g = some it := by
  rw [winner_of_coe h]
  obtain ⟨it, hitv, hτ, -⟩ := exists_of_maxThreshold_eq_coe h
  cases hf : v.find? (λ jt => jt.threshold == m) with
  | some jt => exact ⟨jt, rfl⟩
  | none =>
    rw [List.find?_eq_none] at hf
    exact absurd (by simp [hτ] : (it.threshold == m) = true) (by simpa using hf it hitv)

theorem winner_eq_none_iff {v : List (ExponenceRule n F)} {g : Fin n} :
    winner v g = none ↔ maxThreshold v g = ⊥ := by
  refine ⟨λ h => ?_, winner_eq_none_of_bot⟩
  cases hmt : maxThreshold v g with
  | bot => rfl
  | coe m =>
    obtain ⟨it, hit⟩ := exists_winner_of_coe hmt
    rw [hit] at h
    exact absurd h (by simp)

theorem winner_congr {v : List (ExponenceRule n F)} {g g' : Fin n}
    (h : maxThreshold v g = maxThreshold v g') : winner v g = winner v g' := by
  rw [winner, winner, h]

/-- The realized pattern: at each grade, the Elsewhere winner's
exponent (`none` when no rule applies — a paradigm gap). -/
def realize (v : List (ExponenceRule n F)) : Paradigm n (Option F) :=
  λ g => (winner v g).map ExponenceRule.exponent

theorem realize_congr {v : List (ExponenceRule n F)} {g g' : Fin n}
    (h : maxThreshold v g = maxThreshold v g') : realize v g = realize v g' := by
  show (winner v g).map _ = (winner v g').map _
  rw [winner_congr h]

theorem realize_eq_none_iff {v : List (ExponenceRule n F)} {g : Fin n} :
    realize v g = none ↔ maxThreshold v g = ⊥ := by
  rw [← winner_eq_none_iff]
  unfold realize
  cases winner v g <;> simp

/-! ### CSG1: realization is contiguous

[bobaljik-2012] ch. 2: with antihomophonous rules, the Elsewhere
competition over a containment hierarchy cannot generate ABA — with
only two distinct listed root forms, no ordering of the rules yields
an ABA pattern (p. 35). Formally: `maxThreshold` is the
monotone score, the winner is a function of it, and antihomophony
makes exponents injective in the winner — so realization factors as
monotone-then-injective and `Basic.lean`'s composition principle
applies (here inlined as the sandwich argument). -/

theorem isContiguous_realize {v : List (ExponenceRule n F)} (hAH : Antihomophonous v) :
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

/-! ### The plateau: terminal adjacency generates only `{AAA, ABB}`

Capping all thresholds makes realization constant above the cap. With
terminal rules and adjacent contexts the cap is the first head — this
is the "Bobaljik-minus-portmanteaux" engine, which forces the
comparative and superlative cells to coincide and so *over-excludes*
the attested ABC patterns (Latin *bon- ~ mel- ~ opt-*). Portmanteau items
(`0 < spans`) are what license ABC; see `exists_portmanteau_of_ne`. -/

theorem applicable_eq_of_cap {v : List (ExponenceRule n F)} {m g g' : Fin n}
    (hcap : ∀ it ∈ v, it.threshold ≤ m) (hg : m ≤ g) (hg' : m ≤ g') :
    applicable v g = applicable v g' := by
  unfold applicable
  refine List.filter_congr (λ it hit => ?_)
  simp only [decide_eq_decide]
  exact iff_of_true (le_trans (hcap it hit) hg) (le_trans (hcap it hit) hg')

theorem realize_const_of_cap {v : List (ExponenceRule n F)} {m g g' : Fin n}
    (hcap : ∀ it ∈ v, it.threshold ≤ m) (hg : m ≤ g) (hg' : m ≤ g') :
    realize v g = realize v g' :=
  realize_congr (by unfold maxThreshold; rw [applicable_eq_of_cap hcap hg hg'])

private theorem threshold_le_one {it : ExponenceRule 3 F}
    (h0 : (it.spans : ℕ) = 0)
    (hc : ∀ c : Fin 3, it.context = some c → (c : ℕ) = (it.spans : ℕ) + 1) :
    it.threshold ≤ (1 : Fin 3) := by
  have h1 : it.spans ≤ (1 : Fin 3) := by rw [Fin.le_def]; simp [h0]
  unfold ExponenceRule.threshold
  cases hcx : it.context with
  | none => simpa using h1
  | some c =>
    have h2 : c ≤ (1 : Fin 3) := by rw [Fin.le_def]; simp [hc c hcx, h0]
    simpa using max_le h1 h2

/-- Terminal rules with adjacent contexts have thresholds at most the
first head, so the comparative and superlative cells coincide: only
AAA and ABB root patterns are generable. -/
theorem realize_const_of_terminal_adjacent {v : List (ExponenceRule 3 F)}
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
def ofPattern (p : Paradigm n F) : List (ExponenceRule n F) :=
  (List.finRange n).filterMap (λ s =>
    if firstOcc p s = s then some ⟨p s, ⟨0, s.pos⟩, some s⟩ else none)

theorem mem_ofPattern {p : Paradigm n F} {it : ExponenceRule n F} :
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
    (⟨p s, ⟨0, s.pos⟩, some s⟩ : ExponenceRule n F).threshold = s := by
  unfold ExponenceRule.threshold
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
      ExponenceRule n F) ∈ ofPattern p :=
    mem_ofPattern.mpr ⟨firstOcc p g, hff, rfl⟩
  have hub : ∀ jt ∈ ofPattern p, jt.threshold ≤ g →
      jt.threshold ≤ (⟨p (firstOcc p g), ⟨0, (firstOcc p g).pos⟩,
        some (firstOcc p g)⟩ : ExponenceRule n F).threshold := by
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
  show (winner (ofPattern p) g).map ExponenceRule.exponent = some (p g)
  rw [hw, Option.map_some]
  exact congrArg some (apply_firstOcc p g)

end Completeness

/-- A pattern is **Elsewhere-generable**: some terminal antihomophonous
vocabulary realizes it in full. -/
def ElsewhereGenerable (p : Paradigm n F) : Prop :=
  ∃ v : List (ExponenceRule n F), Terminal v ∧ Antihomophonous v ∧
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

/-- **CSG2 / *AAB exclusion** ([bobaljik-2012] ch. 5). Over the
three-grade degree hierarchy, if the positive and comparative cells
agree and the superlative cell is realized, all three agree:
`good – gooder – *best` is not generable. Hypotheses: antihomophony
plus `Grounded` (the book's markedness condition (202)); the
threshold-set downward closure makes both of the book's AAB routes —
the skipped-head root rule (190a) and the context-sensitive
portmanteau (201) — fail for the same reason, a threshold gap at the
comparative grade. -/
theorem csg2 {v : List (ExponenceRule 3 F)} (hAH : Antihomophonous v) (hG : Grounded v)
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
theorem exists_portmanteau_of_ne {v : List (ExponenceRule 3 F)} (hA : Adjacent v)
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

end Morphology.Containment
