import Linglib.Logic.Team.Kripke
import Linglib.Logic.Team.Definability
import Linglib.Semantics.Questions.Basic

/-!
# Inquisitive modal logic

Inquisitive logic evaluates formulas at information states, sets of possible worlds, by a
relation of support in place of truth ([ciardelli-2022]). The propositional system InqB
extends the classical connectives `⊥`, `∧`, `→` with the inquisitive disjunction `\\/`,
supported by a state that supports either disjunct (Definitions 3.1.3 and 3.2.3); negation and
classical disjunction are defined (Definition 3.1.2) and `?φ := φ \\/ ¬φ` is the polar question
(Definition 3.2.2). Inquisitive modal logic adds two modalities over an inquisitive modal
model, which relates each world `w` to a set `Σ(w)` of states with the induced accessibility
`σ(w) = ⋃ Σ(w)` (Chapter 8; [ciardelli-2014], [ciardelli-roelofsen-2015]): `□φ` is supported
when `σ(w)` supports `φ` at every world `w` of the state (§8.2), `⊞φ` when every state in
`Σ(w)` does (§8.3). Support is persistent and holds at the empty state (Proposition 3.3.1), so
the support set of a formula is an inquisitive proposition `[φ]_M`, a `Question` (Definition
2.4.2), on which the connectives act as the operations of the Heyting algebra of propositions
([ciardelli-groenendijk-roelofsen-2018]). Truth at a world is support at its singleton
(Proposition 3.1.7), and a formula is truth-conditional, a statement rather than a question,
when support is truth at every world of the state (Definitions 2.6.3 and 3.4.1): classical
formulas are (Proposition 3.1.8), `∧` and `→` preserve truth-conditionality (Proposition
3.4.7), `¬¬φ` is the statement with `φ`'s truth set (Proposition 3.4.9), and every modal
formula is a statement (§8.2, §8.3), so that the two modalities agree on statements while `□`,
but not `⊞`, distributes over `\\/`. Inquisitive disjunction breaks union closure, which
places InqML with dependence logic in the downward-closed, empty-team cell of
[anttila-2025]'s definability programme.

## Main definitions

* `InquisitiveModalModel`: a valuation and a map from worlds to sets of information states, with
  the induced accessibility `access`; `KripkeModel.toInquisitive` embeds Kripke models.
* `Formula` and `support`: the language with `□` and `⊞`, and support of a formula by a state.
* `TruthConditional`: the statements, the formulas whose support is truth at every world.
* `proposition`: the inquisitive proposition `[φ]_M`, the support set as a `Question`.

## Main results

* `isLowerSet_support` and `support_empty`: support is persistent and holds at the empty state,
  so the support set is a proposition on which the connectives are the Heyting operations.
* `truthConditional_of_isClassical`, `truthConditional_nec` and `truthConditional_ent`: classical
  and modal formulas are statements, and `truthConditional_iff_neg_neg`: the double negation law
  holds exactly for statements.
* `support_nec_inqDisj` and `support_ent_iff_nec_of_truthConditional`: `□` distributes over
  inquisitive disjunction, and `⊞` agrees with `□` on statements.

## References

* [I. Ciardelli, *Inquisitive Logic: Consequence and Inference in the Realm of Questions*
  (2022)][ciardelli-2022]
* [I. Ciardelli, *Modalities in the realm of questions: Axiomatizing inquisitive epistemic
  logic* (2014)][ciardelli-2014]
* [I. Ciardelli and F. Roelofsen, *Inquisitive dynamic epistemic logic*
  (2015)][ciardelli-roelofsen-2015]
* [I. Ciardelli, J. Groenendijk and F. Roelofsen, *Inquisitive Semantics*
  (2018)][ciardelli-groenendijk-roelofsen-2018]
* [A. Anttila, *Expressive completeness in team semantics* (2025)][anttila-2025]
-/

namespace ModalLogic.Inquisitive

variable {W Atom : Type*}

/-! ### Models (§8.3) -/

/-- An **inquisitive modal model**: a valuation and, at each world `w`, the set `Σ(w)` of
information states related to it — under the epistemic reading, the states in which the
agent's issues are settled. -/
structure InquisitiveModalModel (W Atom : Type*) where
  /-- `Σ(w)`, the states related to `w`. -/
  inq : W → Finset (Finset W)
  /-- The valuation. -/
  val : Atom → W → Bool

namespace InquisitiveModalModel

variable [DecidableEq W] (M : InquisitiveModalModel W Atom)

/-- The induced accessibility `σ(w) = ⋃ Σ(w)`, the agent's epistemic state at `w`. -/
def access (w : W) : Finset W := (M.inq w).sup id

@[simp] theorem mem_access {w v : W} : v ∈ M.access w ↔ ∃ t ∈ M.inq w, v ∈ t := by
  simp [access]

theorem subset_access {w : W} {t : Finset W} (ht : t ∈ M.inq w) : t ⊆ M.access w :=
  Finset.le_sup (f := id) ht

end InquisitiveModalModel

/-- A Kripke model as the inquisitive modal model relating each world to its single successor
state `R[w]` (§8.2). -/
def _root_.ModalLogic.KripkeModel.toInquisitive (M : KripkeModel W Atom) :
    InquisitiveModalModel W Atom :=
  ⟨fun w => {M.access w}, M.val⟩

@[simp] theorem _root_.ModalLogic.KripkeModel.access_toInquisitive [DecidableEq W]
    (M : KripkeModel W Atom) (w : W) : M.toInquisitive.access w = M.access w :=
  Finset.sup_singleton

/-! ### Syntax (Definition 3.2.1; §8.2, §8.3) -/

/-- Formulas of InqML: the classical base `⊥`, `∧`, `→` over atoms, inquisitive disjunction
`\\/` and the two modalities. -/
inductive Formula (Atom : Type*) where
  | atom (p : Atom)
  | bot
  | conj (φ ψ : Formula Atom)
  | impl (φ ψ : Formula Atom)
  /-- Inquisitive disjunction `φ \\/ ψ`. -/
  | inqDisj (φ ψ : Formula Atom)
  /-- The Kripke modality `□φ` (§8.2). -/
  | nec (φ : Formula Atom)
  /-- The properly inquisitive modality `⊞φ` (§8.3), the entertain modality of
  [ciardelli-roelofsen-2015]. -/
  | ent (φ : Formula Atom)
  deriving Repr, DecidableEq

namespace Formula

variable (φ ψ : Formula Atom)

/-- `¬φ := φ → ⊥` (Definition 3.1.2). -/
abbrev neg : Formula Atom := impl φ bot

/-- Classical disjunction `φ ∨ ψ := ¬(¬φ ∧ ¬ψ)` (Definition 3.1.2). -/
abbrev disj : Formula Atom := (conj φ.neg ψ.neg).neg

/-- The polar question `?φ := φ \\/ ¬φ` (Definition 3.2.2). -/
abbrev polarQ : Formula Atom := inqDisj φ φ.neg

/-- The classical formulas, those without inquisitive disjunction (§3.1, §8.2). -/
def IsClassical : Formula Atom → Prop
  | atom _ => True
  | bot => True
  | conj φ ψ => φ.IsClassical ∧ ψ.IsClassical
  | impl φ ψ => φ.IsClassical ∧ ψ.IsClassical
  | inqDisj _ _ => False
  | nec φ => φ.IsClassical
  | ent φ => φ.IsClassical

end Formula

private theorem isLowerSet_image_coe [Fintype W] {S : Set (Finset W)} (hS : IsLowerSet S) :
    IsLowerSet ((fun t : Finset W => (↑t : Set W)) '' S) := by
  rintro a b hba ⟨t, ht, rfl⟩
  exact ⟨(Set.toFinite b).toFinset,
    hS (fun w hw => hba ((Set.Finite.mem_toFinset _).1 hw)) ht, by simp⟩

/-! ### Support (Definitions 3.1.3 and 3.2.3; §8.2, §8.3) -/

variable [DecidableEq W]

/-- `support M φ s`: the information state `s` settles `φ` in `M`. -/
def support (M : InquisitiveModalModel W Atom) : Formula Atom → Finset W → Prop
  | .atom p, s => ∀ w ∈ s, M.val p w = true
  | .bot, s => s = ∅
  | .conj φ ψ, s => support M φ s ∧ support M ψ s
  | .impl φ ψ, s => ∀ t ⊆ s, support M φ t → support M ψ t
  | .inqDisj φ ψ, s => support M φ s ∨ support M ψ s
  | .nec φ, s => ∀ w ∈ s, support M φ (M.access w)
  | .ent φ, s => ∀ w ∈ s, ∀ t ∈ M.inq w, support M φ t

variable (M : InquisitiveModalModel W Atom) (φ ψ : Formula Atom) (s : Finset W) (w : W)

@[simp] theorem support_atom (p : Atom) :
    support M (.atom p) s ↔ ∀ w ∈ s, M.val p w = true := Iff.rfl

@[simp] theorem support_bot : support M (.bot : Formula Atom) s ↔ s = ∅ := Iff.rfl

@[simp] theorem support_conj :
    support M (.conj φ ψ) s ↔ support M φ s ∧ support M ψ s := Iff.rfl

@[simp] theorem support_impl :
    support M (.impl φ ψ) s ↔ ∀ t ⊆ s, support M φ t → support M ψ t := Iff.rfl

@[simp] theorem support_inqDisj :
    support M (.inqDisj φ ψ) s ↔ support M φ s ∨ support M ψ s := Iff.rfl

@[simp] theorem support_nec :
    support M (.nec φ) s ↔ ∀ w ∈ s, support M φ (M.access w) := Iff.rfl

@[simp] theorem support_ent :
    support M (.ent φ) s ↔ ∀ w ∈ s, ∀ t ∈ M.inq w, support M φ t := Iff.rfl

/-- Support is decidable over a finite set of worlds, by structural recursion. -/
instance decidableSupport [Fintype W] :
    (φ : Formula Atom) → (s : Finset W) → Decidable (support M φ s)
  | .atom _, _ => by unfold support; infer_instance
  | .bot, _ => by unfold support; infer_instance
  | .conj φ ψ, s => by
    unfold support; exact @instDecidableAnd _ _ (decidableSupport φ s) (decidableSupport ψ s)
  | .impl φ ψ, s => by
    unfold support; have := decidableSupport φ; have := decidableSupport ψ; infer_instance
  | .inqDisj φ ψ, s => by
    unfold support; exact @instDecidableOr _ _ (decidableSupport φ s) (decidableSupport ψ s)
  | .nec φ, s => by unfold support; have := decidableSupport φ; infer_instance
  | .ent φ, s => by unfold support; have := decidableSupport φ; infer_instance

/-! ### Persistence and the empty state (Proposition 3.3.1) -/

/-- **Persistence**: the support set of a formula is downward closed. -/
theorem isLowerSet_support : IsLowerSet {s : Finset W | support M φ s} := by
  induction φ with
  | atom p => exact fun s t hts hs w hw => hs w (hts hw)
  | bot => exact fun s t hts hs => Finset.subset_empty.1 (hs ▸ hts)
  | conj φ ψ ihφ ihψ => exact fun s t hts hs => ⟨ihφ hts hs.1, ihψ hts hs.2⟩
  | impl φ ψ _ _ => exact fun s t hts hs u hut => hs u (hut.trans hts)
  | inqDisj φ ψ ihφ ihψ => exact fun s t hts hs => hs.imp (ihφ hts) (ihψ hts)
  | nec φ _ => exact fun s t hts hs w hw => hs w (hts hw)
  | ent φ _ => exact fun s t hts hs w hw => hs w (hts hw)

/-- **The empty state property**: the inconsistent state supports every formula. -/
theorem support_empty : support M φ ∅ := by
  induction φ with
  | atom p => simp
  | bot => rfl
  | conj φ ψ ihφ ihψ => exact ⟨ihφ, ihψ⟩
  | impl φ ψ _ ihψ => exact fun t ht _ => by obtain rfl := Finset.subset_empty.1 ht; exact ihψ
  | inqDisj φ ψ ihφ _ => exact Or.inl ihφ
  | nec φ _ => simp
  | ent φ _ => simp

/-! ### Truth (Proposition 3.1.7) -/

theorem support_neg : support M φ.neg s ↔ ∀ t ⊆ s, support M φ t → t = ∅ := Iff.rfl

theorem support_singleton_impl :
    support M (.impl φ ψ) {w} ↔ (support M φ {w} → support M ψ {w}) := by
  refine ⟨fun h => h _ subset_rfl, fun h t ht hφ => ?_⟩
  rcases Finset.subset_singleton_iff.1 ht with rfl | rfl
  · exact support_empty M ψ
  · exact h hφ

theorem support_singleton_neg : support M φ.neg {w} ↔ ¬ support M φ {w} := by
  simp only [Formula.neg, support_singleton_impl, support_bot, Finset.singleton_ne_empty,
    imp_false]

theorem support_singleton_disj :
    support M (φ.disj ψ) {w} ↔ support M φ {w} ∨ support M ψ {w} := by
  simp only [Formula.disj, support_singleton_neg, support_conj, not_and_or, not_not]

/-! ### Truth-conditional formulas (§3.4) -/

/-- The truth set `|φ|_M` (§3.1): the worlds at which `φ` is true, truth being support at the
singleton state. -/
def truthSet : Set W := {w | support M φ {w}}

/-- `φ` is **truth-conditional** in `M` (Definitions 2.6.3 and 3.4.1) when a state supports it
iff it is true at each of its worlds: a statement rather than a question. -/
def TruthConditional : Prop := ∀ s : Finset W, support M φ s ↔ ∀ w ∈ s, support M φ {w}

theorem truthConditional_atom (p : Atom) : TruthConditional M (.atom p) := fun s => by simp

theorem truthConditional_bot : TruthConditional M (.bot : Formula Atom) := fun s => by
  simp [Finset.eq_empty_iff_forall_notMem]

theorem truthConditional_nec : TruthConditional M (.nec φ) := fun s => by simp

theorem truthConditional_ent : TruthConditional M (.ent φ) := fun s => by simp

variable {M φ ψ}

theorem TruthConditional.support_iff (h : TruthConditional M φ) :
    support M φ s ↔ (↑s : Set W) ⊆ truthSet M φ :=
  h s

theorem TruthConditional.conj (hφ : TruthConditional M φ) (hψ : TruthConditional M ψ) :
    TruthConditional M (.conj φ ψ) := fun s => by
  rw [support_conj, hφ s, hψ s]
  exact ⟨fun h w hw => ⟨h.1 w hw, h.2 w hw⟩,
    fun h => ⟨fun w hw => (h w hw).1, fun w hw => (h w hw).2⟩⟩

/-- Proposition 3.4.7: an implication with a truth-conditional consequent is truth-conditional,
whatever its antecedent. -/
theorem TruthConditional.impl (hψ : TruthConditional M ψ) (φ : Formula Atom) :
    TruthConditional M (.impl φ ψ) := fun s => by
  refine ⟨fun h w hw => isLowerSet_support M (.impl φ ψ) (Finset.singleton_subset_iff.2 hw) h,
    fun h t hts hφ => (hψ t).2 fun w hw => ?_⟩
  exact (support_singleton_impl M φ ψ w).1 (h w (hts hw))
    (isLowerSet_support M φ (Finset.singleton_subset_iff.2 hw) hφ)

variable (M φ ψ)

/-- Proposition 3.4.8: every negation is truth-conditional. -/
theorem truthConditional_neg : TruthConditional M φ.neg := (truthConditional_bot M).impl φ

theorem truthConditional_disj : TruthConditional M (φ.disj ψ) := truthConditional_neg M _

/-- Proposition 3.1.8: classical formulas are truth-conditional. -/
theorem truthConditional_of_isClassical (h : φ.IsClassical) : TruthConditional M φ := by
  induction φ with
  | atom p => exact truthConditional_atom M p
  | bot => exact truthConditional_bot M
  | conj φ ψ ihφ ihψ => exact (ihφ h.1).conj (ihψ h.2)
  | impl φ ψ _ ihψ => exact (ihψ h.2).impl φ
  | inqDisj φ ψ _ _ => exact h.elim
  | nec φ _ => exact truthConditional_nec M φ
  | ent φ _ => exact truthConditional_ent M φ

/-- Proposition 3.4.9: `¬¬φ` is supported exactly where `φ` is true at every world. -/
theorem support_neg_neg : support M φ.neg.neg s ↔ ∀ w ∈ s, support M φ {w} := by
  simp only [Formula.neg, support_impl, support_bot]
  constructor
  · intro h w hw
    by_contra hφ
    refine Finset.singleton_ne_empty w (h {w} (Finset.singleton_subset_iff.2 hw) fun u hu hφu => ?_)
    rcases Finset.subset_singleton_iff.1 hu with rfl | rfl
    · rfl
    · exact absurd hφu hφ
  · intro h t hts ht
    by_contra hne
    obtain ⟨w, hw⟩ := Finset.nonempty_iff_ne_empty.2 hne
    exact Finset.singleton_ne_empty w (ht {w} (Finset.singleton_subset_iff.2 hw) (h w (hts hw)))

theorem truthSet_neg_neg : truthSet M φ.neg.neg = truthSet M φ :=
  Set.ext fun w => (support_neg_neg M φ {w}).trans (by simp [truthSet])

/-- Proposition 3.4.10: the double negation law holds exactly for statements. -/
theorem truthConditional_iff_neg_neg :
    TruthConditional M φ ↔ ∀ s, (support M φ.neg.neg s ↔ support M φ s) := by
  simp only [TruthConditional, support_neg_neg]
  exact forall_congr' fun s => Iff.comm

/-- Proposition 2.5.2, the Ramsey test: for a statement `α`, `α → ψ` is supported at `s` iff
`ψ` is supported at the `α`-worlds of `s`. -/
theorem support_impl_iff_of_truthConditional [Fintype W] {α : Formula Atom}
    (hα : TruthConditional M α) :
    support M (.impl α ψ) s ↔ support M ψ (s.filter fun w => support M α {w}) :=
  ⟨fun h => h _ (Finset.filter_subset _ _) ((hα _).2 fun _ hw => (Finset.mem_filter.1 hw).2),
    fun h t hts hαt => isLowerSet_support M ψ
      (fun w hw => Finset.mem_filter.2 ⟨hts hw, (hα t).1 hαt w hw⟩) h⟩

/-! ### The proposition expressed (Proposition 3.3.1, §3.5) -/

section Proposition

variable [Fintype W]

/-- The inquisitive proposition `[φ]_M` expressed by `φ`: its support set, a `Question` by
persistence and the empty state property. -/
def proposition : Question W :=
  Question.ofLowerSet ((fun t : Finset W => (↑t : Set W)) '' {t | support M φ t})
    ⟨∅, support_empty M φ, by simp⟩ (isLowerSet_image_coe (isLowerSet_support M φ))

@[simp] theorem mem_proposition {s : Set W} :
    s ∈ proposition M φ ↔ ∃ t : Finset W, ↑t = s ∧ support M φ t := by
  simp only [proposition, Question.mem_ofLowerSet, Set.mem_image, Set.mem_ofPred_eq, and_comm]

@[simp] theorem coe_mem_proposition : (↑s : Set W) ∈ proposition M φ ↔ support M φ s := by
  simp

/-- Conjunction is the meet of propositions. -/
theorem proposition_conj : proposition M (.conj φ ψ) = proposition M φ ⊓ proposition M ψ := by
  ext s
  simp only [mem_proposition, support_conj, Question.mem_inf]
  constructor
  · rintro ⟨t, hts, hφ, hψ⟩
    exact ⟨⟨t, hts, hφ⟩, ⟨t, hts, hψ⟩⟩
  · rintro ⟨⟨t, hts, hφ⟩, ⟨u, hus, hψ⟩⟩
    obtain rfl := Finset.coe_injective (hts.trans hus.symm)
    exact ⟨t, hts, hφ, hψ⟩

/-- Inquisitive disjunction is the join. -/
theorem proposition_inqDisj :
    proposition M (.inqDisj φ ψ) = proposition M φ ⊔ proposition M ψ := by
  ext s
  simp only [mem_proposition, support_inqDisj, Question.mem_sup]
  constructor
  · rintro ⟨t, hts, hφ | hψ⟩
    · exact Or.inl ⟨t, hts, hφ⟩
    · exact Or.inr ⟨t, hts, hψ⟩
  · rintro (⟨t, hts, hφ⟩ | ⟨t, hts, hψ⟩)
    · exact ⟨t, hts, Or.inl hφ⟩
    · exact ⟨t, hts, Or.inr hψ⟩

/-- Implication is the Heyting arrow. -/
theorem proposition_impl : proposition M (.impl φ ψ) = proposition M φ ⇨ proposition M ψ := by
  ext s
  rw [Question.mem_himp]
  simp only [mem_proposition, support_impl]
  constructor
  · rintro ⟨t, rfl, hsupp⟩ r hrs ⟨a, ha, haφ⟩
    exact ⟨a, ha, hsupp a (Finset.coe_subset.1 (ha.le.trans hrs)) haφ⟩
  · intro h
    refine ⟨(Set.toFinite s).toFinset, by simp, fun u hu hφu => ?_⟩
    have hus : (↑u : Set W) ⊆ s := by
      rw [← (Set.toFinite s).coe_toFinset]; exact Finset.coe_subset.2 hu
    obtain ⟨b, hb, hψb⟩ := h ↑u hus ⟨u, rfl, hφu⟩
    rwa [← Finset.coe_injective hb]

/-- `⊥` is the bottom. -/
theorem proposition_bot : proposition M (.bot : Formula Atom) = ⊥ := by
  ext s
  simp only [mem_proposition, support_bot, Question.mem_bot]
  constructor
  · rintro ⟨t, rfl, rfl⟩; simp
  · rintro rfl; exact ⟨∅, by simp, rfl⟩

/-- Proposition 3.3.5: the truth set is the union of the proposition. -/
theorem info_proposition : (proposition M φ).info = truthSet M φ := by
  ext w
  simp only [Question.info, Set.mem_sUnion]
  constructor
  · rintro ⟨_, ⟨t, ht, rfl⟩, hw⟩
    exact isLowerSet_support M φ (Finset.singleton_subset_iff.2 (Finset.mem_coe.1 hw)) ht
  · exact fun h => ⟨_, ⟨{w}, h, rfl⟩, by simp⟩

/-- Definition 3.4.1 on propositions: `φ` is a statement iff it expresses the declarative
proposition of its truth set. -/
theorem truthConditional_iff_proposition_eq :
    TruthConditional M φ ↔ proposition M φ = Question.ofSet (truthSet M φ) := by
  constructor
  · intro h
    ext s
    rw [mem_proposition, Question.mem_ofSet]
    constructor
    · rintro ⟨t, rfl, ht⟩
      exact fun w hw => (h t).1 ht w (Finset.mem_coe.1 hw)
    · intro hs
      exact ⟨(Set.toFinite s).toFinset, by simp, (h _).2 fun w hw => hs (by simpa using hw)⟩
  · intro h s
    rw [← coe_mem_proposition, h, Question.mem_ofSet]
    exact Iff.rfl

/-- Proposition 3.4.9 on propositions: `¬¬φ` expresses the non-inquisitive projection of
`[φ]_M`. -/
theorem proposition_neg_neg : proposition M φ.neg.neg = (proposition M φ).proj := by
  rw [Question.proj, info_proposition, ← truthSet_neg_neg,
    ← (truthConditional_iff_proposition_eq M _).1 (truthConditional_neg M φ.neg)]

end Proposition

/-! ### Modalities (§8.2, §8.3) -/

variable {M φ ψ}

/-- Two statements that agree at every world agree at every state. -/
theorem TruthConditional.iff_of_singleton (hφ : TruthConditional M φ) (hψ : TruthConditional M ψ)
    (h : ∀ w, support M φ {w} ↔ support M ψ {w}) : support M φ s ↔ support M ψ s := by
  rw [hφ s, hψ s]
  exact forall₂_congr fun w _ => h w

variable (M φ ψ)

/-- `□` commutes with `∧` (§8.2). -/
theorem support_nec_conj :
    support M (.nec (.conj φ ψ)) s ↔ support M (.conj (.nec φ) (.nec ψ)) s := by
  simp [imp_and, forall_and]

/-- The K axiom for `□` (§8.2). -/
theorem support_nec_impl_nec :
    support M (.impl (.nec (.impl φ ψ)) (.impl (.nec φ) (.nec ψ))) s :=
  fun _ _ ht _ hut hu w hw => ht w (hut hw) _ subset_rfl (hu w hw)

/-- Necessitation for `□` (§8.2). -/
theorem support_nec_of_forall (h : ∀ s, support M φ s) (s : Finset W) : support M (.nec φ) s :=
  fun _ _ => h _

/-- `□` distributes over inquisitive disjunction (§8.2): `□(φ \\/ ψ) ≡ □φ ∨ □ψ`. -/
theorem support_nec_inqDisj :
    support M (.nec (.inqDisj φ ψ)) s ↔ support M ((Formula.nec φ).disj (.nec ψ)) s :=
  (truthConditional_nec M _).iff_of_singleton s (truthConditional_disj M _ _) fun w => by
    rw [support_singleton_disj]; simp

/-- `⊞` commutes with `∧` (§8.3). -/
theorem support_ent_conj :
    support M (.ent (.conj φ ψ)) s ↔ support M (.conj (.ent φ) (.ent ψ)) s := by
  simp [imp_and, forall_and]

/-- The K axiom for `⊞` (§8.3). -/
theorem support_ent_impl_ent :
    support M (.impl (.ent (.impl φ ψ)) (.impl (.ent φ) (.ent ψ))) s :=
  fun _ _ ht _ hut hu w hw v hv => ht w (hut hw) v hv _ subset_rfl (hu w hw v hv)

/-- Necessitation for `⊞` (§8.3). -/
theorem support_ent_of_forall (h : ∀ s, support M φ s) (s : Finset W) : support M (.ent φ) s :=
  fun _ _ _ _ => h _

/-- `□φ` entails `⊞φ`: each related state lies in the epistemic state, and support is
persistent (§8.3). -/
theorem support_ent_of_nec (h : support M (.nec φ) s) : support M (.ent φ) s :=
  fun w hw _ ht => isLowerSet_support M φ (M.subset_access ht) (h w hw)

/-- On statements the two modalities coincide (§8.3). -/
theorem support_ent_iff_nec_of_truthConditional (h : TruthConditional M φ) :
    support M (.ent φ) s ↔ support M (.nec φ) s :=
  ⟨fun hent w hw => (h _).2 fun v hv => by
      obtain ⟨t, ht, hvt⟩ := M.mem_access.1 hv
      exact (h t).1 (hent w hw t ht) v hvt,
    support_ent_of_nec M φ s⟩

/-- On a Kripke model `⊞` is `□`, the only related state being `R[w]` (§8.2). -/
theorem support_ent_toInquisitive (M : KripkeModel W Atom) :
    support M.toInquisitive (.ent φ) s ↔ support M.toInquisitive (.nec φ) s := by
  simp [KripkeModel.toInquisitive, InquisitiveModalModel.access]

/-! ### The closure cell -/

/-- Inquisitive disjunction breaks union closure: with `p` true only at `w₁` and `q` only at
`w₂`, the singletons support `p \\/ q` but their union supports neither disjunct. -/
theorem not_supClosed_inqDisj_of_witness {p q : Atom} {w₁ w₂ : W}
    (hp₁ : M.val p w₁ = true) (hq₁ : M.val q w₁ = false)
    (hp₂ : M.val p w₂ = false) (hq₂ : M.val q w₂ = true) :
    ¬ SupClosed {s : Finset W | support M (.inqDisj (.atom p) (.atom q)) s} := fun h => by
  have := h (a := {w₁}) (b := {w₂}) (by simp [hp₁]) (by simp [hq₂])
  simp [hp₂, hq₁] at this

open Team in
/-- InqML is sound for the downward-closed, empty-team cell of [anttila-2025]'s programme,
which it shares with dependence logic. -/
theorem soundFor_downwardClosed_inter_empty :
    SoundFor (support M) (downwardClosedProperties ∩ emptyTeamProperties) :=
  Set.subset_inter (definableClass_subset (isLowerSet_support M))
    (definableClass_subset (support_empty M))

end ModalLogic.Inquisitive
