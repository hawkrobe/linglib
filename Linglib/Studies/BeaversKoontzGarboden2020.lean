import Linglib.Semantics.Verb.Root.Defs
import Linglib.Semantics.Verb.Denotation
import Linglib.Semantics.ArgumentStructure.EventStructure

/-!
# Beavers & Koontz-Garboden (2020): The Roots of Verbal Meaning

[beavers-koontz-garboden-2020]

The six representative roots of the book's root typology (ch. 5), and
the falsification of the Bifurcation Thesis of Roots ([embick-2009];
[arad-2005]) and of Manner/Result Complementarity
([rappaport-hovav-levin-2010]).

| Root     | manner | cause | result | state | position   |
|----------|--------|-------|--------|-------|------------|
| √flat    |        |       |        |   ✓   | complement |
| √blossom |        |       |   ✓    |   ✓   | complement |
| √crack   |        |   ✓   |   ✓    |   ✓   | complement |
| √jog     |   ✓    |       |        |       | adjoined   |
| √hand    |   ✓    |   ✓   |   ✓    |   ✓   | adjoined   |
| √drown   |   ✓    |   ✓   |   ✓    |   ✓   | complement |

The +state cells of √blossom, √crack, √hand, √drown are *derived*:
the book's typology values are the collocational closures
(`Root.closedKinds`) of the base atom kinds, and each
closed signature is one of the canonical typology rows
(`Root.Kinds.pureResult`, `causativeResult`, `fullSpec`).
√blossom falsifies Bifurcation on its own, since change of state is
templatic (`v_become`) content. √hand and √drown additionally falsify
Manner/Result Complementarity; they differ only in root position
(adjoined vs complement), the contrast carrying the book's account of
which root types are attested.

## Main declarations

* `Root.Kinds.ViolatesBifurcation`, `Root.HasMannerAndResult` and
  relatives — the two thesis predicates, at signature and root level
* `flat`, `jog`, `blossom`, `crack`, `hand`, `drown`
* `exists_violatesBifurcation`, `bifurcation_thesis_false`
* `exists_hasMannerAndResult`, `manner_result_complementarity_false`
* `Verb.CosModel.again` and the (25)–(27) reading hierarchy

The thesis predicates and the sublexical *again* operator are carried
here as single-consumer apparatus (this study is their only consumer);
they graduate back to the theory layer when a second study lands.
-/

namespace Verb.Root.Kinds

/-! ### The two theses, at signature level -/

/-- The ontological kinds — all the Bifurcation Thesis allows a root
    to carry. -/
def ontological : Root.Kinds := {.state, .manner}

/-- A signature violates the Bifurcation Thesis ([embick-2009]; the
    assumption of [arad-2005]) iff it carries templatic (eventive)
    content — it is not bounded by `ontological`. -/
def ViolatesBifurcation (s : Root.Kinds) : Prop := ¬ s ≤ ontological

instance (s : Root.Kinds) : Decidable s.ViolatesBifurcation :=
  inferInstanceAs (Decidable (¬ _ ≤ _))

/-- Violation is carrying a `result` or `cause` kind. -/
theorem violatesBifurcation_iff :
    ∀ s : Root.Kinds,
      s.ViolatesBifurcation ↔ .result ∈ s ∨ .cause ∈ s := by decide

/-- Bifurcation violation is monotone: adding entailments cannot
    repair a violation. -/
theorem violatesBifurcation_mono :
    ∀ {s t : Root.Kinds}, s ≤ t →
      s.ViolatesBifurcation → t.ViolatesBifurcation := by decide

/-- A signature has both manner and result — the configuration
    Manner/Result Complementarity ([rappaport-hovav-levin-2010])
    claims no root realizes. -/
def HasMannerAndResult (s : Root.Kinds) : Prop :=
  {LexKind.manner, LexKind.result} ≤ s

instance (s : Root.Kinds) : Decidable s.HasMannerAndResult :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- MRC violation is monotone in the signature order. -/
theorem hasMannerAndResult_mono :
    ∀ {s t : Root.Kinds}, s ≤ t →
      s.HasMannerAndResult → t.HasMannerAndResult := by decide

/-- Bifurcation is invariant under collocational closure: `close` only
    adds `state`/`result` kinds forced by `cause`, never `manner`. -/
theorem violatesBifurcation_close_iff :
    ∀ s : Root.Kinds,
      (close s).ViolatesBifurcation ↔ s.ViolatesBifurcation := by decide

theorem hasMannerAndResult_close_iff :
    ∀ s : Root.Kinds,
      (close s).HasMannerAndResult ↔
        s.HasMannerAndResult ∨ (.manner ∈ s ∧ .cause ∈ s) := by decide

end Verb.Root.Kinds

namespace Verb.Root

/-! ### The two theses, at root level -/

/-- A root *violates* Bifurcation iff it itself carries templatic
    (eventive) meaning — change of state or cause
    (`Root.Kinds.violatesBifurcation_iff`). -/
def ViolatesBifurcation (r : Root) : Prop :=
  r.kinds.ViolatesBifurcation

instance (r : Root) : Decidable r.ViolatesBifurcation :=
  inferInstanceAs (Decidable (Root.Kinds.ViolatesBifurcation _))

/-- Negation of `ViolatesBifurcation`: the root carries only
    ontological entailments (state, manner). -/
def RespectsBifurcation (r : Root) : Prop :=
  ¬ r.ViolatesBifurcation

instance (r : Root) : Decidable r.RespectsBifurcation :=
  inferInstanceAs (Decidable (¬ _))

/-- The thesis as an order statement: a root respects Bifurcation iff
    its signature is bounded by the ontological kinds. -/
theorem respectsBifurcation_iff_le {r : Root} :
    r.RespectsBifurcation ↔
      r.kinds ≤ Root.Kinds.ontological :=
  not_not

/-- A root has both manner and result entailments — Manner/Result
    Complementarity ([rappaport-hovav-levin-2010]) is the universal
    claim that no root does. -/
def HasMannerAndResult (r : Root) : Prop :=
  r.kinds.HasMannerAndResult

instance (r : Root) : Decidable r.HasMannerAndResult :=
  inferInstanceAs (Decidable (Root.Kinds.HasMannerAndResult _))

/-- Negation of `HasMannerAndResult`. -/
def RespectsMannerResultComplementarity (r : Root) : Prop :=
  ¬ r.HasMannerAndResult

instance (r : Root) : Decidable r.RespectsMannerResultComplementarity :=
  inferInstanceAs (Decidable (¬ _))

end Verb.Root

namespace Verb.CosModel

/-! ### Sublexical *again* — the restitutive/repetitive hierarchy (§1.3.2, exs (25)–(27))

`again` is a presupposition trigger that can attach at three points in the
change-of-state structure — the root, `vbecome`, or `vcause` — yielding the
three readings of *Mary flattened the rug again* in (25): restitutive ("it
had been flat", a prior **state**), repetitive over the change ("it had
flattened", a prior **become** event), and repetitive over the causation
("Mary had flattened it", a prior **cause** event). (26) (a simplified
[von-stechow-1996]) defines `⟦again⟧ = λPλe. P(e) ∧ ∂∃e′[e′ ≪ e ∧ P(e′)]`.
The reading hierarchy `(25c) ⊨ (25b) ⊨ (25a)` and the result-root collapse
(§2.4, exs (43)/(45)) fall out of the change-of-state entailments of
`Verb.CosModel`. -/

variable {Entity State Time : Type*} [LinearOrder Time]

/-- (26): the sublexical modifier *again*. Given a precedence `≪` (`lt`) on an
    eventuality type `ι` and a predicate `P`, *again* asserts `P e` and
    presupposes a strictly earlier `e′ ≪ e` with `P e′`. The `∂` operator is
    not analysed further — the earlier-eventuality conjunct *is* the
    presupposition (`againPresup`). -/
def again {ι : Type*} (lt : ι → ι → Prop) (P : ι → Prop) (e : ι) : Prop :=
  P e ∧ ∃ e', lt e' e ∧ P e'

/-- The presupposition *again* contributes ((26), the `∂`-marked conjunct):
    a strictly earlier eventuality also satisfying `P`. -/
def againPresup {ι : Type*} (lt : ι → ι → Prop) (P : ι → Prop) (e : ι) : Prop :=
  ∃ e', lt e' e ∧ P e'

theorem again_iff {ι : Type*} (lt : ι → ι → Prop) (P : ι → Prop) (e : ι) :
    again lt P e ↔ P e ∧ againPresup lt P e := Iff.rfl

/-- (27a): *again* attached low, to the root `√V`. The asserted/presupposed
    predicate is the root **state** — the restitutive reading. -/
def againRestitutive (M : CosModel Entity State Time)
    (ltS : State → State → Prop) (v : Verb) (x : Entity) (s : State) : Prop :=
  again ltS (M.rootState v x) s

/-- (27b): *again* attached to `vbecomeP` — the repetitive-over-change
    reading. -/
def againRepetitiveBecome (M : CosModel Entity State Time)
    (ltE : Event Time → Event Time → Prop) (v : Verb) (x : Entity)
    (e : Event Time) : Prop :=
  again ltE (M.inchoative v x) e

/-- (27c): *again* attached high, to `vcauseP` — the
    repetitive-over-causation reading. -/
def againRepetitiveCause (M : CosModel Entity State Time)
    (ltE : Event Time → Event Time → Prop) (v : Verb) (y x : Entity)
    (w : Event Time) : Prop :=
  again ltE (M.causative v y x) w

/-- (25) hierarchy, upper step: the repetitive-causation presupposition (25c)
    entails the repetitive-change presupposition (25b) — the earlier causing
    event *is* an earlier change, by `causative_entails_inchoative`. -/
theorem againPresup_cause_entails_become (M : CosModel Entity State Time)
    (lt : Event Time → Event Time → Prop) (v : Verb) (y x : Entity)
    (w : Event Time) (h : againPresup lt (M.causative v y x) w) :
    ∃ w', lt w' w ∧ ∃ e, M.inchoative v x e := by
  obtain ⟨w', hlt, hcaus⟩ := h
  exact ⟨w', hlt, M.causative_entails_inchoative v y x w' hcaus⟩

/-- (25) hierarchy, lower step: the repetitive-change presupposition (25b)
    entails the restitutive presupposition (25a) — the earlier change gives
    rise to an earlier root state, by `inchoative_entails_resultState`. -/
theorem againPresup_become_entails_state (M : CosModel Entity State Time)
    (lt : Event Time → Event Time → Prop) (v : Verb) (x : Entity)
    (e : Event Time) (h : againPresup lt (M.inchoative v x) e) :
    ∃ e', lt e' e ∧ ∃ s, M.become s e' ∧ M.rootState v x s := by
  obtain ⟨e', hlt, hinch⟩ := h
  exact ⟨e', hlt, M.inchoative_entails_resultState v x e' hinch⟩

/-- (25) hierarchy, end to end: "Mary had flattened it before" ⊨ "it had
    been flat before", composed through the change-of-state decomposition
    (`causative_entails_resultState`). -/
theorem againPresup_cause_entails_state (M : CosModel Entity State Time)
    (lt : Event Time → Event Time → Prop) (v : Verb) (y x : Entity)
    (w : Event Time) (h : againPresup lt (M.causative v y x) w) :
    ∃ w', lt w' w ∧ ∃ e s, M.become s e ∧ M.rootState v x s := by
  obtain ⟨w', hlt, hcaus⟩ := h
  exact ⟨w', hlt, M.causative_entails_resultState v y x w' hcaus⟩

/-- §2.4 (45): for a *result* root the root state itself entails a prior
    change, so even the low/restitutive attachment of *again* carries a change
    entailment — the restitutive reading collapses into the repetitive one
    ("result roots never admit truly restitutive readings"). -/
theorem result_restitution_entails_change (M : CosModel Entity State Time)
    (ltS : State → State → Prop) (v : Verb) (x : Entity) (s : State)
    (hres : ∀ s, M.rootState v x s → ∃ e, M.become s e)
    (h : againPresup ltS (M.rootState v x) s) :
    ∃ s', ltS s' s ∧ ∃ e, M.become s' e := by
  obtain ⟨s', hlt, hst⟩ := h
  obtain ⟨e, hbec⟩ := hres s' hst
  exact ⟨s', hlt, e, hbec⟩

end Verb.CosModel

namespace BeaversKoontzGarboden2020

open Verb

/-! ### The six representative roots -/

/-- √flat — pure state. -/
def flat : Root := ⟨"flat", {.hasState "flat"}, {}⟩

/-- √jog — pure manner of motion. -/
def jog : Root := ⟨"jog", {.hasManner "jogging-gait"}, {}⟩

/-- √blossom — result with no specified manner or cause (an
    internally caused change of state). -/
def blossom : Root := ⟨"blossom", {.becomesState "flowering"}, {}⟩

/-- √crack — caused result without specified manner. -/
def crack : Root := ⟨"crack", {.becomesState "fissured", .hasCause}, {}⟩

/-- √hand — manner + cause + result, adjoined position. The
    possession result is non-cancelable ("#Mary handed John the book,
    but he never got it"), so it is root-entailed rather than
    implicated ([beavers-koontz-garboden-2020] ch. 3). -/
def hand : Root := ⟨"hand",
  {.hasManner "by-hand-transfer",
   .becomesState "in-recipient-possession",
   .hasCause}, {}⟩

/-- √drown — manner of killing (Levin 1993's *crucify, drown, hang,
    electrocute* class; [beavers-koontz-garboden-2020] ch. 4):
    manner + cause + result, complement position. -/
def drown : Root := ⟨"drown",
  {.hasManner "submersion-in-liquid", .becomesState "dead", .hasCause}, {}⟩

/-! ### Kind signatures

Base signatures record the atom kinds; closed signatures are their
collocational closures, and coincide with the canonical rows of the
book's typology. -/

theorem flat_kinds : flat.kinds = {.state} := by
  decide

theorem jog_kinds : jog.kinds = {.manner} := by
  decide

theorem blossom_kinds :
    blossom.kinds = {.result} := by decide

theorem crack_kinds :
    crack.kinds = {.result, .cause} := by decide

theorem hand_kinds :
    hand.kinds = {.manner, .result, .cause} := by decide

theorem drown_kinds :
    drown.kinds = {.manner, .result, .cause} := by decide

theorem flat_closedKinds :
    flat.closedKinds = Root.Kinds.propertyConcept := by
  decide

theorem jog_closedKinds :
    jog.closedKinds = Root.Kinds.pureManner := by decide

theorem blossom_closedKinds :
    blossom.closedKinds = Root.Kinds.pureResult := by
  decide

theorem crack_closedKinds :
    crack.closedKinds = Root.Kinds.causativeResult := by
  decide

theorem hand_closedKinds :
    hand.closedKinds = Root.Kinds.fullSpec := by decide

theorem drown_closedKinds :
    drown.closedKinds = Root.Kinds.fullSpec := by decide

/-! ### Falsifying the Bifurcation Thesis -/

/-- √blossom entails change of state — templatic (`v_become`) content
    in the root — falsifying Bifurcation without any manner or cause
    entailment. -/
theorem blossom_violatesBifurcation : blossom.ViolatesBifurcation := by
  decide

theorem crack_violatesBifurcation : crack.ViolatesBifurcation := by
  decide

theorem hand_violatesBifurcation : hand.ViolatesBifurcation := by decide

theorem drown_violatesBifurcation : drown.ViolatesBifurcation := by
  decide

/-- Some root carries templatic content. -/
theorem exists_violatesBifurcation : ∃ r : Root, r.ViolatesBifurcation :=
  ⟨blossom, blossom_violatesBifurcation⟩

/-- The universal closure of the Bifurcation Thesis is false. -/
theorem bifurcation_thesis_false :
    ¬ ∀ r : Root, r.RespectsBifurcation := fun h =>
  h blossom blossom_violatesBifurcation

/-! ### Falsifying Manner/Result Complementarity -/

/-- √hand entails both a manner (by-hand transfer) and a result
    (recipient possession). -/
theorem hand_hasMannerAndResult : hand.HasMannerAndResult := by decide

/-- √drown entails both a manner (submersion) and a result (death);
    it differs from √hand in root position. -/
theorem drown_hasMannerAndResult : drown.HasMannerAndResult := by decide

/-- Some root entails both a manner and a result. -/
theorem exists_hasMannerAndResult : ∃ r : Root, r.HasMannerAndResult :=
  ⟨hand, hand_hasMannerAndResult⟩

/-- The universal closure of Manner/Result Complementarity is false. -/
theorem manner_result_complementarity_false :
    ¬ ∀ r : Root, r.RespectsMannerResultComplementarity := fun h =>
  h hand hand_hasMannerAndResult

/-! ### Roots respecting each constraint -/

/-- √flat (pure state) respects Bifurcation: its signature is bounded
    by the ontological kinds. -/
theorem flat_respectsBifurcation : flat.RespectsBifurcation := by decide

/-- √jog (pure manner) respects Bifurcation. -/
theorem jog_respectsBifurcation : jog.RespectsBifurcation := by decide

/-- √crack (cause + result, no manner) respects Manner/Result
    Complementarity. -/
theorem crack_respectsMannerResultComplementarity :
    crack.RespectsMannerResultComplementarity := by decide

/-! ### The roots cash out denotationally ([beavers-koontz-garboden-2020] §1.3.2)

Threading the roots through the change-of-state denotation (`Verb.CosModel`): a
verb's denotation is dispatched on its root's `kinds`, so the kinds
proven above *select the event template* and the result entailment of (6)
follows from the signature. √crack (`+cause+result`) entails a result state in
any model; √jog (pure manner) does not — the *break*/*hit* contrast. -/

/-- `crack` the change-of-state verb (`Mary cracked the vase`). -/
def crackV : Verb := { form := "crack", frames := [Frame.np], root := crack }

/-- `jog` the pure-manner activity verb (`Mary jogged`). -/
def jogV : Verb := { form := "jog", frames := [], root := jog }

/-- √crack carries `.result`, so in **any** model its denotation entails the
    result state — the non-cancelable result of [beavers-koontz-garboden-2020]
    (6), derived from crack's signature rather than stipulated. -/
theorem crack_denote_entails_result {Entity State Time : Type*} [LinearOrder Time]
    (M : Verb.CosModel Entity State Time) (y x : Entity) (e : Event Time)
    (h : M.denote crackV y x e) : ∃ e' s, M.become s e' ∧ M.rootState crackV x s :=
  M.denote_result_entails_resultState crackV y x e (by decide) h

/-- √jog has no `.result` (nor `.cause`), so its denotation is the bare manner
    core — no `become`, no result state. Only the change-of-state root entails a
    result. -/
theorem jog_denote_eq_manner {Entity State Time : Type*} [LinearOrder Time]
    (M : Verb.CosModel Entity State Time) (y x : Entity) :
    M.denote jogV y x = M.manner jogV := by
  unfold Verb.CosModel.denote
  rw [if_neg (by decide), if_neg (by decide)]

/-! ### The same contrast at the template level ([rappaport-hovav-levin-1998])

`Verb.Root.template` reads the event-structure template off a root's
collocational closure; the kinds proven above fix it, and `HasResultState`
reduces to carrying `result` (`Verb.Root.template_hasResultState_iff`). So the
denotational result entailment (√crack) and the template result diagnostic are
*one fact* seen through `kinds`. -/

theorem flat_template : flat.template = .state := by decide
theorem jog_template : jog.template = .activity := by decide
theorem blossom_template : blossom.template = .achievement := by decide
theorem crack_template : crack.template = .accomplishment := by decide

/-- √crack's template embeds a result state (it carries `result`); √jog's does
    not — the *break*/*hit* contrast, now at the template layer and provably the
    same signature fact as `crack_denote_entails_result`. -/
theorem crack_template_hasResultState : crack.template.HasResultState := by decide

theorem jog_template_no_resultState : ¬ jog.template.HasResultState := by decide

/-- √crack's template embeds a result state, so by `denote_result_from_template`
    its denotation entails the result state in any model — the template diagnostic
    and the denotational entailment are *one* fact through `crack`'s `kinds`. -/
theorem crack_template_forces_denote_result {Entity State Time : Type*}
    [LinearOrder Time] (M : Verb.CosModel Entity State Time) (y x : Entity)
    (e : Event Time) (h : M.denote crackV y x e) :
    ∃ e' s, M.become s e' ∧ M.rootState crackV x s :=
  M.denote_result_from_template crackV crack_template_hasResultState y x e h

end BeaversKoontzGarboden2020
