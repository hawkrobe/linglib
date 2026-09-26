module

public import Linglib.Logic.Team.BSML.Enrichment
public import Linglib.Logic.Team.BSML.ClassicalValidities
public import Linglib.Logic.Team.BSML.Scenarios

/-!
# Free choice from neglect-zero: the BSML facts of [aloni-2022]

[aloni-2022] derives free-choice inferences from a *neglect-zero* tendency: the
pragmatic enrichment `[·]⁺` (`BSML.enrich`) conjoins `NE` to every subformula, so
an enriched split disjunction needs two non-empty witnesses, and under a
possibility modal each witness is a live option. This file proves the paper's
free-choice facts for arbitrary `NE`-free `α β`: Modal Disjunction (Fact 3,
state-based `R`), Narrow Scope FC (Fact 4) and its dependent-disjunct corollary,
Wide Scope FC (Fact 5, indisputable `R`), Dual Prohibition (Fact 11), Double
Negation (Fact 12), the epistemic contradiction that motivates the state-based
reading of epistemic modals (§4.1), and the BSML⁺ failure of Negative FC
(Fact 14). The paper's illustrations (Figures 1–5) are checked by `decide` on its
four-world model `w_∅, w_a, w_b, w_ab` (`BSML.TwoAtomWorld`), whose running
state is `{w_a, w_b}`.

The remaining facts are substrate: Facts 1, 2, 9, 10, 13 and the BSML* half of
Fact 14 in `Logic/Team/BSML/Enrichment.lean`, Facts 6–8 in
`ClassicalValidities.lean`, Fact 15 in `Bridge.lean`. Out of scope: the
first-order extension (§6.2, see [aloni-vanormondt-2023]) and the BSML◇
conjecture of §7 beyond its countermodel (63b).
-/

@[expose] public section

namespace Aloni2022

open BSML
open ModalLogic (KripkeModel)

variable {W : Type*} [DecidableEq W] {Atom : Type*} {M : KripkeModel W Atom}
  {α β φ : Formula Atom} {t : Finset W}

/-! ### Free-choice facts -/

/-- An enriched split disjunction has a non-empty witness subteam for each disjunct,
`[α ∨ β]⁺ ⊨ (α ∧ NE) ∨ (β ∧ NE)`. -/
theorem witnesses_of_enrich_disj (hα : α.NEFree) (hβ : β.NEFree)
    (h : support M (enrich (.disj α β)) t) :
    (∃ s ⊆ t, s.Nonempty ∧ support M α s) ∧ ∃ s ⊆ t, s.Nonempty ∧ support M β s :=
  have ⟨t₁, t₂, hu, h₁, h₂⟩ := h.1
  ⟨⟨t₁, hu ▸ Finset.subset_union_left, nonempty_of_support_enrich h₁,
      support_of_support_enrich hα h₁⟩,
    ⟨t₂, hu ▸ Finset.subset_union_right, nonempty_of_support_enrich h₂,
      support_of_support_enrich hβ h₂⟩⟩

/-- Modal Disjunction (Fact 3) is `[α ∨ β]⁺ ⊨ ◇α ∧ ◇β` on a state-based `R`. -/
theorem modalDisjunction (hα : α.NEFree) (hβ : β.NEFree) (hSB : M.IsStateBased t)
    (h : support M (enrich (.disj α β)) t) :
    support M (.poss α) t ∧ support M (.poss β) t :=
  have ⟨⟨s₁, hs₁, hne₁, h₁⟩, ⟨s₂, hs₂, hne₂, h₂⟩⟩ := witnesses_of_enrich_disj hα hβ h
  ⟨fun w hw ↦ ⟨s₁, (hSB w hw).symm ▸ hs₁, hne₁, h₁⟩,
   fun w hw ↦ ⟨s₂, (hSB w hw).symm ▸ hs₂, hne₂, h₂⟩⟩

/-- Narrow Scope FC (Fact 4) is `[◇(α ∨ β)]⁺ ⊨ ◇α ∧ ◇β`. -/
theorem narrowScopeFC (hα : α.NEFree) (hβ : β.NEFree)
    (h : support M (enrich (.poss (.disj α β))) t) :
    support M (.poss α) t ∧ support M (.poss β) t :=
  ⟨fun w hw ↦
    have ⟨_, hs, _, h'⟩ := h.1 w hw
    (witnesses_of_enrich_disj hα hβ h').1.imp fun _ ⟨hs', hne, h₁⟩ ↦ ⟨hs'.trans hs, hne, h₁⟩,
   fun w hw ↦
    have ⟨_, hs, _, h'⟩ := h.1 w hw
    (witnesses_of_enrich_disj hα hβ h').2.imp fun _ ⟨hs', hne, h₂⟩ ↦ ⟨hs'.trans hs, hne, h₂⟩⟩

/-- Free choice for logically dependent disjuncts is
`[◇(α ∨ (α ∧ β))]⁺ ⊨ ◇α ∧ ◇(α ∧ β)`. -/
theorem narrowScopeFC_dependent (hα : α.NEFree) (hβ : β.NEFree)
    (h : support M (enrich (.poss (.disj α (.conj α β)))) t) :
    support M (.poss α) t ∧ support M (.poss (.conj α β)) t :=
  narrowScopeFC hα ⟨hα, hβ⟩ h

/-- Wide Scope FC (Fact 5) is `[◇α ∨ ◇β]⁺ ⊨ ◇α ∧ ◇β` on an indisputable `R`. -/
theorem wideScopeFC (hα : α.NEFree) (hβ : β.NEFree) (hInd : M.IsIndisputable t)
    (h : support M (enrich (.disj (.poss α) (.poss β))) t) :
    support M (.poss α) t ∧ support M (.poss β) t :=
  have ⟨⟨_, ht₁, ⟨w₁, hw₁⟩, h₁⟩, ⟨_, ht₂, ⟨w₂, hw₂⟩, h₂⟩⟩ :=
    witnesses_of_enrich_disj (α := .poss α) (β := .poss β) hα hβ h
  ⟨fun w hw ↦ (h₁ w₁ hw₁).imp fun _ ⟨hs, hne, hs'⟩ ↦ ⟨hInd w₁ (ht₁ hw₁) w hw ▸ hs, hne, hs'⟩,
   fun w hw ↦ (h₂ w₂ hw₂).imp fun _ ⟨hs, hne, hs'⟩ ↦ ⟨hInd w₂ (ht₂ hw₂) w hw ▸ hs, hne, hs'⟩⟩

/-- Dual Prohibition (Fact 11) is `[¬◇(α ∨ β)]⁺ ⊨ ¬◇α ∧ ¬◇β`. -/
theorem dualProhibition (hα : α.NEFree) (hβ : β.NEFree)
    (h : support M (enrich (.neg (.poss (.disj α β)))) t) :
    support M (.neg (.poss α)) t ∧ support M (.neg (.poss β)) t :=
  have h' := (antiSupport_conj_ne M _ t).mp h.1
  have hαβ : (Formula.disj α β).NEFree := ⟨hα, hβ⟩
  ⟨fun w hw ↦ (antiSupport_of_antiSupport_enrich hαβ (h' w hw)).1,
   fun w hw ↦ (antiSupport_of_antiSupport_enrich hαβ (h' w hw)).2⟩

/-- Double Negation (Fact 12) is `[¬¬◇(α ∨ β)]⁺ ⊨ ◇α ∧ ◇β`. -/
theorem doubleNegationFC (hα : α.NEFree) (hβ : β.NEFree)
    (h : support M (enrich (.neg (.neg (.poss (.disj α β))))) t) :
    support M (.poss α) t ∧ support M (.poss β) t :=
  narrowScopeFC hα hβ ((support_enrich_neg_neg M _ t).mp h)

/-- Epistemic contradiction (§4.1) says that on a state-based `R`, `◇φ ∧ ¬φ` is supported
only by `∅`, the sole team supporting the weak contradiction `⊥`. -/
theorem epistemicContradiction (hSB : M.IsStateBased t)
    (h : support M (.conj (.poss φ) (.neg φ)) t) : t = ∅ :=
  Finset.eq_empty_of_forall_notMem fun w hw ↦
    have ⟨_, hs, ⟨_, hv⟩, hsupp⟩ := h.1 w hw
    Finset.disjoint_left.mp (disjoint_support_antiSupport M φ h.2 hsupp) (hSB w hw ▸ hs hv) hv

/-! ### The four-world illustrations

The paper's figures are model–state pairs on `TwoAtomWorld`; each `figNx` fixes
the accessibility arrows drawn in Figure N(x), worlds without arrows seeing `∅`. -/

/-- The paper's Kripke models on the four worlds have valuation `TwoAtomWorld.holds` and
accessibility `R`. -/
def model (R : TwoAtomWorld → Finset TwoAtomWorld) : KripkeModel TwoAtomWorld FCAtom :=
  ⟨R, fun p w ↦ w.holds p⟩

/-- The state `{w_a, w_b}` of Figures 1, 2(a), 3 and 5. -/
def state : Finset TwoAtomWorld := {.onlyA, .onlyB}

/-- Figures 1–2 draw no arrows, so only atoms and disjunction are evaluated. -/
def propositional : KripkeModel TwoAtomWorld FCAtom := model fun _ ↦ ∅

/-- Figure 3(a) has `R[w_a] = R[w_b] = {w_ab, w_∅}`. -/
def fig3a : KripkeModel TwoAtomWorld FCAtom :=
  model fun | .onlyA | .onlyB => {.both, .nothing} | _ => ∅

/-- Figure 3(b) has `R[w_a] = R[w_b] = {w_a, w_b}`. -/
def fig3b : KripkeModel TwoAtomWorld FCAtom :=
  model fun | .onlyA | .onlyB => {.onlyA, .onlyB} | _ => ∅

/-- Figure 3(c) has `R[w_a] = {w_ab}`, `R[w_b] = {w_a, w_∅}`. -/
def fig3c : KripkeModel TwoAtomWorld FCAtom :=
  model fun | .onlyA => {.both} | .onlyB => {.onlyA, .nothing} | _ => ∅

/-- Figure 4(a) has `R[w_ab] = {w_a}`. -/
def fig4a : KripkeModel TwoAtomWorld FCAtom := model fun | .both => {.onlyA} | _ => ∅

/-- Figure 4(b) has `R[w_ab] = {w_a, w_b}`. -/
def fig4b : KripkeModel TwoAtomWorld FCAtom := model fun | .both => {.onlyA, .onlyB} | _ => ∅

/-- Figure 5(a) has `R[w_a] = R[w_b] = {w_b}`. -/
def fig5a : KripkeModel TwoAtomWorld FCAtom := model fun | .onlyA | .onlyB => {.onlyB} | _ => ∅

/-- Figure 5(b) has `R[w_a] = {w_a}`, `R[w_b] = {w_b}`. -/
def fig5b : KripkeModel TwoAtomWorld FCAtom :=
  model fun | .onlyA => {.onlyA} | .onlyB => {.onlyB} | _ => ∅

/-- The disjunction `a ∨ b`. -/
def aOrB : Formula FCAtom := .disj (.atom .a) (.atom .b)

/-- `◇a`. -/
def mayA : Formula FCAtom := .poss (.atom .a)

/-- `◇b`. -/
def mayB : Formula FCAtom := .poss (.atom .b)

-- Figure 1: the state supports neither `a` nor `¬a`.
example : ¬ support propositional (.atom .a) state ∧
    ¬ support propositional (.neg (.atom .a)) state := by decide

-- Figure 2: `a ∨ b` against `[a ∨ b]⁺` on (a) `{w_a, w_b}`, (b) `{w_ab, w_b}`,
-- (c) `{w_a}` — a zero-model, `b` witnessed by `∅` — and (d) `{w_a, w_b, w_∅}`.
example : support propositional aOrB state ∧ support propositional (enrich aOrB) state := by
  decide
example : support propositional aOrB {.both, .onlyB} ∧
    support propositional (enrich aOrB) {.both, .onlyB} := by decide
example : support propositional aOrB {.onlyA} ∧ ¬ support propositional (enrich aOrB) {.onlyA} := by
  decide
example : ¬ support propositional aOrB {.onlyA, .onlyB, .nothing} ∧
    ¬ support propositional (enrich aOrB) {.onlyA, .onlyB, .nothing} := by decide

-- Figure 3: indisputability against state-basedness on `{w_a, w_b}`.
example : fig3a.IsIndisputable state ∧ ¬ fig3a.IsStateBased state := by decide
example : fig3b.IsStateBased state := by decide
example : ¬ fig3c.IsIndisputable state := by decide

-- §4.1 on Figure 3(b): `◇a` is supported but neither `a` (non-factivity) nor `¬a`
-- is, so the epistemic contradiction `◇a ∧ ¬a` fails (`epistemicContradiction`).
example : support fig3b mayA state ∧ ¬ support fig3b (.atom .a) state ∧
    ¬ support fig3b (.neg (.atom .a)) state := by decide

-- Figure 4: at `{w_ab}`, (a) supports `◇(a ∨ b)` but not `[◇(a ∨ b)]⁺`, since `b` is
-- no open possibility in `R[w_ab]`; (b) supports `[◇(a ∨ b)]⁺`.
example : support fig4a (.poss aOrB) {.both} ∧ ¬ support fig4a (enrich (.poss aOrB)) {.both} := by
  decide
example : support fig4b (enrich (.poss aOrB)) {.both} := by decide

-- Figure 5: wide-scope FC fails (a) without enrichment on an indisputable `R` and
-- (b) with enrichment on a non-indisputable `R`; (63b) is the locally enriched
-- `◇[a]⁺ ∨ ◇[b]⁺` of the BSML◇ conjecture, refuted on the same pair.
example : fig5a.IsIndisputable state ∧ support fig5a (.disj mayA mayB) state ∧
    ¬ support fig5a mayA state := by decide
example : ¬ fig5b.IsIndisputable state ∧ support fig5b (enrich (.disj mayA mayB)) state ∧
    ¬ support fig5b mayA state := by decide
example : support fig5b (.disj (.poss (enrich (.atom .a))) (.poss (enrich (.atom .b)))) state := by
  decide

/-! ### Negative free choice (Fact 14)

BSML⁺ validates neither `◇¬(α ∧ β) ⊨ ◇¬α` nor `¬□(α ∧ β) ⊨ ¬□α` — the paper's
(50), "Mary might not speak both Arabic and Bengali" ⇏ "she might not speak
Arabic". The countermodel is Figure 5(b)'s frame at the state `{w_a}`: inside
`[¬(a ∧ b)]⁺` a zero witness anti-supports `a`, but no non-empty subteam of
`R[w_a] = {w_a}` anti-supports `a`. BSML* validates both inferences
(`BSML.negativeFC_star_poss`, `BSML.negativeFC_star_nec`). -/

theorem not_negativeFC_poss :
    ¬ consequencePlus (W := TwoAtomWorld) (Atom := FCAtom)
      (.poss (.neg (.conj (.atom .a) (.atom .b)))) (.poss (.neg (.atom .a))) :=
  fun h ↦ (by decide : ¬ support fig5b (enrich (.poss (.neg (.atom .a)))) {.onlyA})
    (h fig5b {.onlyA} (by decide))

/-- The `□` form follows from the `◇` form by the duality `□φ := ¬◇¬φ`. -/
theorem not_negativeFC_nec :
    ¬ consequencePlus (W := TwoAtomWorld) (Atom := FCAtom)
      (.neg (Formula.nec (.conj (.atom .a) (.atom .b)))) (.neg (Formula.nec (.atom .a))) :=
  fun h ↦ not_negativeFC_poss fun M t hp ↦
    (support_enrich_neg_neg M _ t).mp (h M t ((support_enrich_neg_neg M _ t).mpr hp))

end Aloni2022
