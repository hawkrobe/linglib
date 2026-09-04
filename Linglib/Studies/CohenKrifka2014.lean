import Linglib.Discourse.Commitment.Space
import Linglib.Semantics.Quantification.Numerals.Basic

/-!
# Cohen and Krifka 2014: superlative quantifiers and meta-speech acts

Over commitment spaces (§2), Cohen and Krifka define the meta-speech act GRANT as the
denegation of asserting the negation (38): it keeps the root and prunes the continuations
in which the speaker asserts the negation, so it includes but does not enforce the
assertion (39), and asserting is conversely the denegation of granting the negation (40).
Superlative quantifiers quantify over GRANTs (§3): *at most n* says the greatest value
whose GRANT the speaker leaves open is n (43), performed as the conjunction, over the
values above n, of denegations of GRANTs (44) — by (40) a conjunction of assertions of
the negations (46) — and *at least n* is the same over the values below n (48)–(51). We
state the exclusion schema over an arbitrary set of values on a linear scale, after the
paper's generalization beyond numerals (§3.6), and derive both conjunction forms, the
greatest- and least-grantable characterizations, and the derived truth conditions (§3.2):
the context set of the updated root is the intersection of the asserted denials, which on
count scales is exactly the classical Keenan and Stavi meaning of the numeral quantifier
(82), while no denial of an in-range value is entailed (53) — the model-level trace of
the paper's claim that the sentence's falsity is semantic and its truth an implicature.

Speech-act strength is inclusion of updated spaces (86): excluding more values is the
stronger act, so *at most* strengthens as the bound drops and *at least* as it rises, and
on count scales a pointwise larger count strengthens *at most* but weakens *at least* on
derived truth conditions — the asymmetry behind NPI licensing with *at most* (84)–(88).
The denegation of a superlative is, by de Morgan (34), the disjunction of the GRANTs it
denied (98); it keeps the root, so it commits the speaker to nothing — the paper's
account of why superlative quantifiers resist downward-entailing contexts (§5.2.2).

## Implementation notes

* The strength comparisons across different count scales ((87): denying *n ever* against
  denying *n last year*) are stated on the context sets of the updated roots rather than
  as (86)'s inclusion of spaces: the latter needs states closed under entailment, which
  the paper invokes as a consistency requirement and this representation does not impose.
  The per-value entailment claimed there also fails for the exact propositions of
  (44)/(46) — with three visitors ever and two last year, ¬(exactly two ever) holds while
  ¬(exactly two last year) does not — though the whole conjunctions are ordered as (87)
  concludes.
* The general theorems carry freshness (no denial already in the root), injectivity of
  the scale, and membership hypotheses locating the updated roots among the space's
  states; the free space satisfies all of them, as the count model checks.

## TODO

* The evaluative reading (§5.2.3–§5.2.4) and its good/bad-consequent presupposition are
  left informal by the paper.
* The compositional route through the superlative morphology ((67), (70)) needs degree
  composition with an illocutionary operator in the lexical entry.
* Wide-scope *at most* over deontic *may* (p. 71) denies permissions, which the
  preferential commitment force could express.

## References

* [A. Cohen and M. Krifka, *Superlative quantifiers and meta-speech acts*
  (2014)][cohen-krifka-2014]
* [B. Geurts and R. Nouwen, *`At least' et al.: The semantics of scalar modifiers*
  (2007)][geurts-nouwen-2007]
* [E. Keenan and J. Stavi, *A Semantic Characterization of Natural Language Determiners*
  (1986)][keenan-stavi-1986]
-/

namespace CohenKrifka2014

open Commitment Commitment.Space

/-! ### Quantifying over GRANTs (§3.1, §3.6) -/

section Scale

variable {A W ι : Type*} (C : Space (State A W)) (a : A) (φ : ι → Set W) (s : Set ι)

/-- The meta-speech act excluding the values of `φ` in `s`: `a` asserts `¬φ(m)` for every
`m ∈ s` at once ((46), (51)). -/
def exclude : Space (State A W) :=
  C.reroot (C.root ∪ (fun m => commit a (φ m)ᶜ) '' s)

@[simp] theorem exclude_root :
    (exclude C a φ s).root = C.root ∪ (fun m => commit a (φ m)ᶜ) '' s := rfl

/-- The exclusion denies `φ(m)` exactly for the excluded values. -/
theorem commit_mem_exclude_root_iff (hroot : ∀ m, commit a (φ m)ᶜ ∉ C.root)
    (hinj : Function.Injective φ) {m : ι} :
    commit a (φ m)ᶜ ∈ (exclude C a φ s).root ↔ m ∈ s := by
  simp only [exclude_root, Set.mem_union, Set.mem_image]
  constructor
  · rintro (h | ⟨k, hk, e⟩)
    · exact absurd h (hroot m)
    · rwa [hinj (compl_injective (congrArg Commitment.content e))] at hk
  · exact fun hm => Or.inr ⟨m, hm, rfl⟩

/-- The denegation of the exclusion keeps the root: it commits the speaker to nothing
(§5.2.2). -/
theorem root_notMem_exclude_states (hne : s.Nonempty)
    (hroot : ∀ m ∈ s, commit a (φ m)ᶜ ∉ C.root) :
    C.root ∉ (exclude C a φ s).states := by
  obtain ⟨m₀, hm₀⟩ := hne
  have hK : commit a (φ m₀)ᶜ ∈ (fun m => commit a (φ m)ᶜ) '' s := ⟨m₀, hm₀, rfl⟩
  rintro (h | ⟨-, hsub⟩)
  · exact hroot m₀ hm₀ ((Set.union_eq_left.1 h.symm) hK)
  · exact hroot m₀ hm₀ (hsub (Or.inr hK))

/-- The exclusion is the generalized conjunction ((31)) of the single assertions of the
denials ((44)⇒(46), (49)⇒(51) via (40)). -/
theorem exclude_states (hne : s.Nonempty)
    (hroot : ∀ m ∈ s, commit a (φ m)ᶜ ∉ C.root) (hinj : s.InjOn φ)
    (hK : C.root ∪ (fun m => commit a (φ m)ᶜ) '' s ∈ C.states) :
    (exclude C a φ s).states = ⋂ m ∈ s, (C.assert a (φ m)ᶜ).states := by
  obtain ⟨m₀, hm₀⟩ := hne
  ext d
  simp only [exclude, assert, reroot_states, Set.mem_insert_iff, Set.mem_ofPred_eq,
    Set.mem_iInter]
  constructor
  · rintro (rfl | ⟨hd, hsub⟩) m hm
    · exact Or.inr ⟨hK, Set.insert_subset (Or.inr ⟨m, hm, rfl⟩) Set.subset_union_left⟩
    · exact Or.inr ⟨hd, Set.insert_subset (hsub (Or.inr ⟨m, hm, rfl⟩))
        (Set.subset_union_left.trans hsub)⟩
  · intro hd
    have hsub : C.root ∪ (fun m => commit a (φ m)ᶜ) '' s ⊆ d := by
      refine Set.union_subset ?_ ?_
      · rcases hd m₀ hm₀ with rfl | ⟨-, h⟩
        exacts [Set.subset_insert _ _, (Set.subset_insert _ _).trans h]
      · rintro - ⟨m, hm, rfl⟩
        rcases hd m hm with rfl | ⟨-, h⟩
        exacts [Set.mem_insert _ _, h (Set.mem_insert _ _)]
    rcases hd m₀ hm₀ with rfl | ⟨hmem, -⟩
    · left
      have hs : s = {m₀} := Set.eq_singleton_iff_unique_mem.2 ⟨hm₀, fun m hm => by
        rcases hsub (Or.inr ⟨m, hm, rfl⟩) with e | he
        · exact hinj hm hm₀ (compl_injective (congrArg Commitment.content e))
        · exact absurd he (hroot m hm)⟩
      rw [hs, Set.image_singleton, Set.union_singleton]
      rfl
    · exact Or.inr ⟨hmem, hsub⟩

/-- (44) and (49) themselves: each conjunct is the denegation of the GRANT of `φ(m)`,
rewritten by (40). -/
theorem exclude_states_grant (hne : s.Nonempty)
    (hroot : ∀ m ∈ s, commit a (φ m)ᶜ ∉ C.root) (hinj : s.InjOn φ)
    (hK : C.root ∪ (fun m => commit a (φ m)ᶜ) '' s ∈ C.states)
    (hmem : ∀ m ∈ s, insert (commit a (φ m)ᶜ) C.root ∈ C.states) :
    (exclude C a φ s).states =
      ⋂ m, ⋂ (hm : m ∈ s), C.states \ (C.grant a (φ m) (hroot m hm)).states := by
  rw [exclude_states C a φ s hne hroot hinj hK]
  refine Set.iInter_congr fun m => Set.iInter_congr fun hm => ?_
  have hsub : (C.assert a (φ m)ᶜ).states ⊆ C.states := by
    rw [C.assert_states_of_mem a (φ m)ᶜ .doxastic (hmem m hm)]
    exact fun d hd => hd.1
  exact (Set.sdiff_sdiff_cancel_left hsub).symm

/-- The denegation of the superlative is the disjunction of the GRANTs it denied
((97)–(98), by (34)). -/
theorem sdiff_exclude_states (hne : s.Nonempty)
    (hroot : ∀ m ∈ s, commit a (φ m)ᶜ ∉ C.root) (hinj : s.InjOn φ)
    (hK : C.root ∪ (fun m => commit a (φ m)ᶜ) '' s ∈ C.states)
    (hmem : ∀ m ∈ s, insert (commit a (φ m)ᶜ) C.root ∈ C.states) :
    C.states \ (exclude C a φ s).states =
      ⋃ m, ⋃ (hm : m ∈ s), (C.grant a (φ m) (hroot m hm)).states := by
  rw [exclude_states_grant C a φ s hne hroot hinj hK hmem, Set.sdiff_iInter]
  refine Set.iUnion_congr fun m => ?_
  rw [Set.sdiff_iInter]
  refine Set.iUnion_congr fun hm => ?_
  exact Set.sdiff_sdiff_cancel_left fun d hd => hd.1

/-- Excluding more values is the stronger speech act ((86)): its update is included in the
weaker one's. -/
theorem exclude_states_anti {s t : Set ι} (hst : s ⊆ t)
    (hK : C.root ∪ (fun m => commit a (φ m)ᶜ) '' t ∈ C.states) :
    (exclude C a φ t).states ⊆ (exclude C a φ s).states := by
  have hsub : C.root ∪ (fun m => commit a (φ m)ᶜ) '' s ⊆
      C.root ∪ (fun m => commit a (φ m)ᶜ) '' t :=
    Set.union_subset_union_right _ (Set.image_mono hst)
  rintro d (rfl | ⟨hd, hsub'⟩)
  · exact Or.inr ⟨hK, hsub⟩
  · exact Or.inr ⟨hd, hsub.trans hsub'⟩

/-- The derived truth conditions (§3.2): what the exclusion asserts is the intersection of
the asserted denials ((52)). -/
theorem contextSet_exclude_root :
    contextSet (exclude C a φ s).root = (⋂ m ∈ s, (φ m)ᶜ) ∩ contextSet C.root := by
  rw [exclude_root, contextSet_union, Set.inter_comm]
  congr 1
  rw [contextSet, contents_image_commit, Set.sInter_image]

end Scale

/-! ### At most and at least over a linear scale -/

section Bounds

variable {A W ι : Type*} [LinearOrder ι] (C : Space (State A W)) (a : A) (φ : ι → Set W)
  (n : ι)

/-- *At most `n`* ((42)–(46)): the values above `n` are excluded. -/
def atMost : Space (State A W) := exclude C a φ (Set.Ioi n)

/-- *At least `n`* ((47)–(51)): the values below `n` are excluded. -/
def atLeast : Space (State A W) := exclude C a φ (Set.Iio n)

/-- A lower bound makes *at most* stronger ((55), (118), by (86)). -/
theorem atMost_states_mono {n n' : ι} (hnn : n ≤ n')
    (hK : C.root ∪ (fun m => commit a (φ m)ᶜ) '' Set.Ioi n ∈ C.states) :
    (atMost C a φ n).states ⊆ (atMost C a φ n').states :=
  exclude_states_anti C a φ (Set.Ioi_subset_Ioi hnn) hK

/-- A higher bound makes *at least* stronger ((86)). -/
theorem atLeast_states_anti {n n' : ι} (hnn : n ≤ n')
    (hK : C.root ∪ (fun m => commit a (φ m)ᶜ) '' Set.Iio n' ∈ C.states) :
    (atLeast C a φ n').states ⊆ (atLeast C a φ n).states :=
  exclude_states_anti C a φ (Set.Iio_subset_Iio hnn) hK

/-- (43), (60b): `n` is the greatest value whose GRANT *at most `n`* leaves performable. -/
theorem atMost_isGreatest (hroot : ∀ m, commit a (φ m)ᶜ ∉ C.root)
    (hinj : Function.Injective φ) :
    IsGreatest {m | commit a (φ m)ᶜ ∉ (atMost C a φ n).root} n := by
  have hs : {m | commit a (φ m)ᶜ ∉ (atMost C a φ n).root} = Set.Iic n := by
    ext m
    rw [Set.mem_ofPred_eq, atMost, commit_mem_exclude_root_iff C a φ _ hroot hinj,
      Set.mem_Ioi, not_lt, Set.mem_Iic]
  exact hs ▸ isGreatest_Iic

/-- (48), (60a): `n` is the least value whose GRANT *at least `n`* leaves performable. -/
theorem atLeast_isLeast (hroot : ∀ m, commit a (φ m)ᶜ ∉ C.root)
    (hinj : Function.Injective φ) :
    IsLeast {m | commit a (φ m)ᶜ ∉ (atLeast C a φ n).root} n := by
  have hs : {m | commit a (φ m)ᶜ ∉ (atLeast C a φ n).root} = Set.Ici n := by
    ext m
    rw [Set.mem_ofPred_eq, atLeast, commit_mem_exclude_root_iff C a φ _ hroot hinj,
      Set.mem_Iio, not_lt, Set.mem_Ici]
  exact hs ▸ isLeast_Ici

end Bounds

/-! ### Count scales and the classical truth conditions (§3.2, §4) -/

section Numeral

open Numerals

variable {A W : Type*} (C : Space (State A W)) (a : A) (n : ℕ)

/-- The scale of exact numeral claims over the count `f` ((74)): the bare numeral meaning
at each value. -/
def exactly (f : W → ℕ) : ℕ → Set W := fun m => {w | bareMeaning m (f w)}

/-- The derived truth conditions of *at most `n`* are the classical Keenan and Stavi
meaning of the quantifier ((82)). -/
theorem contextSet_atMost_exactly (f : W → ℕ) :
    contextSet (atMost C a (exactly f) n).root
      = {w | atMostMeaning n (f w)} ∩ contextSet C.root := by
  rw [atMost, contextSet_exclude_root]
  congr 1
  ext w
  simp only [Set.mem_iInter, Set.mem_compl_iff, exactly, Set.mem_ofPred_eq, bareMeaning_def,
    atMostMeaning_def, Set.mem_Ioi]
  exact ⟨fun h => not_lt.1 fun hlt => h (f w) hlt rfl,
    fun h m hm e => absurd hm (not_lt.2 (e ▸ h))⟩

/-- The derived truth conditions of *at least `n`* are the classical Keenan and Stavi
meaning of the quantifier ((82)). -/
theorem contextSet_atLeast_exactly (f : W → ℕ) :
    contextSet (atLeast C a (exactly f) n).root
      = {w | atLeastMeaning n (f w)} ∩ contextSet C.root := by
  rw [atLeast, contextSet_exclude_root]
  congr 1
  ext w
  simp only [Set.mem_iInter, Set.mem_compl_iff, exactly, Set.mem_ofPred_eq, bareMeaning_def,
    atLeastMeaning_def, Set.mem_Iio]
  exact ⟨fun h => not_lt.1 fun hlt => h (f w) hlt rfl,
    fun h m hm e => absurd hm (not_lt.2 (e ▸ h))⟩

/-- A pointwise larger count strengthens *at most* on derived truth conditions: denying
counts of visitors ever entails denying counts last year ((84b), (87)). -/
theorem contextSet_atMost_exactly_anti {f g : W → ℕ} (hfg : ∀ w, g w ≤ f w) :
    contextSet (atMost C a (exactly f) n).root ⊆
      contextSet (atMost C a (exactly g) n).root := by
  rw [contextSet_atMost_exactly, contextSet_atMost_exactly]
  exact Set.inter_subset_inter_left _ fun w hw => le_trans (hfg w) hw

/-- …while it weakens *at least*: the asymmetry behind NPI licensing ((84a), (88)). -/
theorem contextSet_atLeast_exactly_mono {f g : W → ℕ} (hfg : ∀ w, g w ≤ f w) :
    contextSet (atLeast C a (exactly g) n).root ⊆
      contextSet (atLeast C a (exactly f) n).root := by
  rw [contextSet_atLeast_exactly, contextSet_atLeast_exactly]
  exact Set.inter_subset_inter_left _ fun w hw => le_trans hw (hfg w)

end Numeral

/-! ### John petted at least three rabbits ((1a), (47))

Worlds are the possible counts of petted rabbits, the acts the speaker's, and the space
the free one, so every hypothesis of the general theorems holds and the pipeline runs end
to end: the derived truth conditions are the classical *at least three*, a four-rabbit
world verifies them and a two-rabbit world falsifies them ((52)), the denial of four is
not among the commitments ((53)), and three is the least grantable value ((48)). -/

section Model

open Numerals

/-- The free space over counting worlds, with no prior commitments. -/
def rabbits : Space (State DiscourseRole ℕ) := full ∅

theorem exactly_id_injective : Function.Injective (exactly (id : ℕ → ℕ)) := by
  intro m k h
  have hm := (Set.ext_iff.1 h m).1
  simpa [exactly] using hm rfl

theorem rabbits_root_fresh (m : ℕ) :
    commit DiscourseRole.speaker (exactly id m)ᶜ ∉ rabbits.root :=
  Set.notMem_empty _

/-- The derived truth conditions of (1a) are the classical *at least three* ((82)). -/
theorem rabbits_atLeast_contextSet :
    contextSet (atLeast rabbits .speaker (exactly id) 3).root = {w | atLeastMeaning 3 w} := by
  rw [contextSet_atLeast_exactly]
  simp [rabbits]

/-- Petting four rabbits verifies (1a): every asserted denial holds ((52)). -/
theorem four_mem_rabbits_atLeast :
    4 ∈ contextSet (atLeast rabbits .speaker (exactly id) 3).root := by
  rw [rabbits_atLeast_contextSet]; exact by decide

/-- Petting two rabbits falsifies (1a) semantically ((52a)). -/
theorem two_notMem_rabbits_atLeast :
    2 ∉ contextSet (atLeast rabbits .speaker (exactly id) 3).root := by
  rw [rabbits_atLeast_contextSet]; exact by decide

/-- The denial of four is not among the speaker's commitments ((53)): that (1a) is true at
four is implicature, not entailment. -/
theorem rabbits_atLeast_grant_four :
    commit DiscourseRole.speaker (exactly id 4)ᶜ ∉
      (atLeast rabbits .speaker (exactly id) 3).root := by
  rw [atLeast, commit_mem_exclude_root_iff rabbits .speaker (exactly id) _ rabbits_root_fresh
    exactly_id_injective]
  decide

/-- Three is the least value the speaker leaves grantable ((48), (60a)). -/
theorem rabbits_atLeast_isLeast :
    IsLeast {m | commit DiscourseRole.speaker (exactly id m)ᶜ ∉
      (atLeast rabbits .speaker (exactly id) 3).root} 3 :=
  atLeast_isLeast rabbits .speaker (exactly id) 3 rabbits_root_fresh exactly_id_injective

/-- Denegating (1a) leaves the disjunction of the three GRANTs ((89b), (97)–(98)). -/
theorem rabbits_sdiff_atLeast :
    rabbits.states \ (atLeast rabbits .speaker (exactly id) 3).states =
      ⋃ m, ⋃ (_ : m ∈ Set.Iio 3),
        (rabbits.grant .speaker (exactly id m) (Set.notMem_empty _)).states :=
  sdiff_exclude_states rabbits .speaker (exactly id) _ ⟨0, by decide⟩
    (fun m _ => rabbits_root_fresh m) exactly_id_injective.injOn
    (Set.mem_Ici.2 (Set.empty_subset _)) fun _ _ => Set.mem_Ici.2 (Set.empty_subset _)

/-- The denegation keeps the root ((98)): the negated superlative asserts nothing, which is
why superlative quantifiers resist downward-entailing contexts (§5.2.2). -/
theorem rabbits_root_notMem_atLeast :
    rabbits.root ∉ (atLeast rabbits .speaker (exactly id) 3).states :=
  root_notMem_exclude_states rabbits .speaker (exactly id) _ ⟨0, by decide⟩
    fun m _ => rabbits_root_fresh m

end Model

/-! ### Granting includes but does not enforce asserting ((39), p. 54)

A two-state consistent space: nothing conceded, or `φ` asserted. Granting `φ` keeps both
states while asserting reaches only the second. -/

section Granting


/-- It is raining, over two weather worlds. -/
def raining : Set Bool := {true}

/-- The two-state space: no commitments, or the speaker's assertion of `raining`. -/
def granting : Space (State DiscourseRole Bool) :=
  ⟨{∅, insert (commit .speaker raining) ∅}, ∅, Or.inl rfl,
    by rintro d (rfl | rfl) <;> simp⟩

theorem raining_ne_compl : (raining : Set Bool) ≠ rainingᶜ := fun h =>
  (h ▸ rfl : true ∈ rainingᶜ) rfl

theorem granting_consistent : ∀ d ∈ granting.states,
    ¬((⟨.speaker, raining, .commit, .doxastic, .selfGenerated⟩ :
        Commitment DiscourseRole Bool) ∈ d ∧
      (⟨.speaker, rainingᶜ, .commit, .doxastic, .selfGenerated⟩ :
        Commitment DiscourseRole Bool) ∈ d) := by
  rintro d (rfl | rfl) ⟨h₁, h₂⟩
  · exact Set.notMem_empty _ h₁
  · rcases Set.mem_insert_iff.1 h₂ with h₂ | h₂
    · exact raining_ne_compl (congrArg Commitment.content h₂).symm
    · exact Set.notMem_empty _ h₂

/-- Granting `raining` includes every state its assertion reaches ((39), p. 54)… -/
theorem granting_assert_subset_grant :
    (granting.assert .speaker raining).states ⊆
      (granting.grant .speaker raining (Set.notMem_empty _)).states :=
  granting.assert_states_subset_grant .speaker raining (Or.inr rfl) granting_consistent _

/-- …but does not enforce the assertion: the unchanged root survives the grant. -/
theorem granting_root_mem_grant :
    granting.root ∈ (granting.grant .speaker raining (Set.notMem_empty _)).states :=
  granting.root_mem_grant .speaker raining _

end Granting

end CohenKrifka2014
