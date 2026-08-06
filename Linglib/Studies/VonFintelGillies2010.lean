import Linglib.Semantics.Evidential.Source
import Linglib.Semantics.Modality.Kernel
import Linglib.Data.Examples.VonFintelGillies2010
import Linglib.Studies.Izvorski1997

/-!
# von Fintel & Gillies (2010): *Must* ... Stay! Strong!
[von-fintel-gillies-2010] [kratzer-1991]

Epistemic *must* carries an indirect-evidence signal yet is semantically
strong: *must φ* entails φ.

**Karttunen's Problem**: standard modal logic gives *must φ* ⊨ φ, yet the
bare prejacent is felt to convey more confidence than the *must*-claim
([kratzer-1991] p. 645: "I make a stronger claim in uttering (5a) than in
(5b)"). VF&G's resolution keeps *must* at the top of the strength ordering
(p. 352: *must* > *almost certainly* > *presumably* > *might*) and locates
the felt weakness in an evidential presupposition: the speaker's kernel
must not directly settle the prejacent.

## Main declarations

- `EvidenceType`, `EvidenceType.toCoarseSource`: VF&G's evidence-type
  classification and its collapse onto the Aikhenvald taxonomy
- `must_felicitous_iff_indirect`: over the example rows, the modalized
  member of a bare/modal minimal pair is felicitous iff the speaker's
  evidence source `IsIndirect`
- `cant_patterns_with_must`: the same biconditional restricted to the
  *can't* rows, derived from the previous theorem
- `must_entails_prejacent`: every minimal pair records prejacent
  entailment — including the infelicitous direct-evidence rows
- `must_evidence_matches_izvorski_ev`: *must* imposes the same
  indirect-evidence restriction as [izvorski-1997]'s Bulgarian EV
- `entailment_settling_gap`: B_K can entail φ without K directly settling
  it — the gap that makes the evidential presupposition non-trivial
- `subjectMatter`, `settlesByPartition`: the paper's second implementation
  of directly-settles (Def 7, §7.2) — the subject matter S_K as an
  equivalence relation on worlds
- `explicit_not_implies_partition`, `partition_not_implies_explicit`: the
  §7.2 boundary cases showing the two implementations are non-equivalent
-/

namespace VonFintelGillies2010

open Semantics.Evidential
open Data.Examples

/-! ### Evidence types -/

/-- The type of evidence the speaker has for the prejacent. -/
inductive EvidenceType where
  /-- Direct sensory observation (seeing, hearing). -/
  | direct
  /-- Indirect inference from observable effects. -/
  | indirect
  /-- Elimination reasoning (ruling out alternatives). -/
  | elimination
  deriving Repr, DecidableEq, Inhabited

/-- Collapse to the Aikhenvald taxonomy. Elimination reasoning is
    inference, not direct access: the kernel does not directly settle the
    prejacent — which is why elimination licenses *must* (VF&G ex. 12). -/
def EvidenceType.toCoarseSource : EvidenceType → CoarseSource
  | .direct => .direct
  | .indirect => .inference
  | .elimination => .inference

/-- VF&G evidence types declare their coarse source; the evidential
    perspective derives via the canonical source mapping. -/
instance : HasCoarseSource EvidenceType where
  toCoarseSource e := some e.toCoarseSource

/-- All VF&G evidence types are nonfuture: their perspective is always
    retrospective or contemporaneous (T ≤ A). -/
theorem all_evidence_types_nonfuture (e : EvidenceType) :
    Semantics.Evidential.IsNonfuture e := by
  cases e <;> decide

/-! ### Adapters over the example rows -/

/-- Evidence-type adapter: the row's `evidence` feature as an
    `EvidenceType`. -/
def evidenceOf (row : LinguisticExample) : Option EvidenceType :=
  match row.feature? "evidence" with
  | some "direct" => some .direct
  | some "indirect" => some .indirect
  | some "elimination" => some .elimination
  | _ => none

/-- Rows whose primary text is the modalized member of a bare/modal
    minimal pair. -/
def mustPairs : List LinguisticExample :=
  Examples.all.filter (·.feature? "kind" == some "must_pair")

/-! ### The evidential restriction -/

/-- **Evidential restriction**: a *must*/*can't* sentence is felicitous
    iff the speaker's evidence source `IsIndirect`. Direct perception
    (exx. 6, 23) blocks the modal; inference — causal (exx. 7, 21, 24, 26)
    or by elimination (ex. 12) — licenses it. -/
theorem must_felicitous_iff_indirect :
    ∀ row ∈ mustPairs,
      row.judgment = .acceptable ↔
        ∀ e ∈ evidenceOf row, e.toCoarseSource.IsIndirect := by
  decide

/-- **Can't patterns with must**: the evidential restriction holds
    uniformly on the negative-modal rows (exx. 21, 23, 24) — *can't*
    groups with *must*, not with weak modals. -/
theorem cant_patterns_with_must :
    ∀ row ∈ mustPairs.filter (·.feature? "modal" == some "cant"),
      row.judgment = .acceptable ↔
        ∀ e ∈ evidenceOf row, e.toCoarseSource.IsIndirect :=
  fun row hrow => must_felicitous_iff_indirect row (List.mem_filter.mp hrow).1

/-- ***Must* imposes [izvorski-1997]'s EV restriction**: felicity of the
    modalized member tracks `CoarseSource.IsIndirect` of the evidence
    source in VF&G's *must* rows exactly as in Izvorski's Bulgarian EV
    paradigm — the two epistemic operators presuppose the same coarse
    indirect-evidence basis. -/
theorem must_evidence_matches_izvorski_ev :
    (∀ row ∈ mustPairs,
      row.judgment = .acceptable ↔
        ∀ e ∈ evidenceOf row, e.toCoarseSource.IsIndirect) ∧
    ∀ d ∈ Izvorski1997.evMustData, Izvorski1997.EvRequiresIndirect d :=
  ⟨must_felicitous_iff_indirect, Izvorski1997.all_evRequiresIndirect⟩

/-! ### Must is strong -/

/-- **Must is strong**: every minimal pair records that the modalized
    sentence entails its prejacent — including the direct-evidence rows
    where the modal is infelicitous. The restriction is evidential, not a
    weakening of content. The supporting inference rows (modus ponens is
    valid, *must φ ∧ perhaps ¬φ* is contradictory, retraction fails) are
    in the same JSON under `kind = inference`. -/
theorem must_entails_prejacent :
    ∀ row ∈ mustPairs, row.feature? "must_entails_prejacent" = some "true" := by
  decide

/-- The bare prejacent is felicitous in every context: the felicity
    restriction is contributed by the modal, not by the content. -/
theorem bare_always_felicitous :
    ∀ row ∈ mustPairs, ∀ alt ∈ row.alternatives, alt.2 = .acceptable := by
  decide

/-! ### The kernel model ([von-fintel-gillies-2010] §7.1)

A four-world instantiation of §7.1's worked kernel `K = {P ∪ Q, W \ P}`
(Billy's weather report, Figure 3(a)), skinned with the colors of the §2
Mastermind scenario (Pascal asking Mordecai *Must there be two reds?*):
`P` = red-only, `Q` = blue, so `redOrBlue = P ∪ Q` and `notRed = W \ P`.
`B_K = {w1}` entails *blue* without either kernel proposition settling it. -/

open Semantics.Modality
open Intensional.Premise

/-- Four worlds: w0 = red, w1 = blue, w2 = green, w3 = unknown. -/
inductive World where
  | w0 | w1 | w2 | w3
  deriving DecidableEq, Repr, Inhabited

/-- ⟦red or blue⟧ = {w0, w1}: the paper's `P ∪ Q`. -/
abbrev redOrBlue : World → Prop := λ w => w = .w0 ∨ w = .w1

/-- ⟦not red⟧ = {w1, w2, w3}: the paper's `W \ P`. -/
abbrev notRed : World → Prop := (· ≠ .w0)

/-- ⟦blue⟧ = {w1}: the paper's `Q`. -/
abbrev blue : World → Prop := (· = .w1)

/-- ⟦red⟧ = {w0}: the paper's `P`. -/
abbrev red : World → Prop := (· = .w0)

/-- ⟦not blue⟧ (used by the [von-fintel-gillies-2021] can't dilemma). -/
abbrev notBlue : World → Prop := (· ≠ .w1)

/-- The §7.1 kernel `{P ∪ Q, W \ P}` in Mastermind colors. -/
def mastermindK : Kernel World := ⟨[redOrBlue, notRed]⟩

/-- A one-proposition kernel whose base properly contains ⟦blue⟧. -/
def indirectK : Kernel World := ⟨[redOrBlue]⟩

theorem mastermind_base : mastermindK.base = ({.w1} : Set World) := by
  ext w
  cases w <;> simp [Kernel.base, mastermindK, propIntersection, redOrBlue, notRed]

theorem mastermind_blue_unsettled :
    ¬ directlySettlesExplicit mastermindK blue := by
  rintro ⟨x, hx, hxor⟩
  rcases List.mem_cons.mp hx with rfl | hx'
  · rcases hxor with h_ent | h_exc
    · exact absurd (h_ent .w0 (show redOrBlue .w0 from by decide)) (by decide)
    · exact h_exc ⟨.w1, show redOrBlue .w1 from by decide, by decide⟩
  · rcases List.mem_singleton.mp hx' with rfl
    rcases hxor with h_ent | h_exc
    · exact absurd (h_ent .w2 (show notRed .w2 from by decide)) (by decide)
    · exact h_exc ⟨.w1, show notRed .w1 from by decide, by decide⟩

theorem mastermind_blue_follows : mastermindK.followsFrom blue := by
  rw [Kernel.followsFrom_iff, mastermind_base]
  rintro w rfl
  rfl

theorem mastermind_must_blue_defined :
    (kernelMust mastermindK blue).presup .w0 :=
  mastermind_blue_unsettled

theorem mastermind_must_blue_true :
    (kernelMust mastermindK blue).assertion .w0 :=
  mastermind_blue_follows

theorem mastermind_red_settled :
    directlySettlesExplicit mastermindK red := by
  refine ⟨notRed, by simp [mastermindK], Or.inr ?_⟩
  rintro ⟨w, hnr, hr⟩
  exact hnr hr

theorem mastermind_might_red_undefined :
    ¬(kernelMight mastermindK red).presup .w0 := λ h =>
  h mastermind_red_settled

theorem mastermind_redOrBlue_settled :
    directlySettlesExplicit mastermindK redOrBlue :=
  ⟨redOrBlue, by simp [mastermindK], Or.inl λ _ hw => hw⟩

/-! ### Deep theorems -/

/-- **Entailment-settling gap**: B_K can entail φ without K settling it.
This gap makes the evidential presupposition non-trivial: must φ can be
simultaneously defined and true. -/
theorem entailment_settling_gap :
    ∃ (k : Kernel World) (φ : (World → Prop)),
      k.followsFrom φ ∧ ¬ directlySettlesExplicit k φ :=
  ⟨mastermindK, blue, mastermind_blue_follows, mastermind_blue_unsettled⟩

/-- **Indirectness ≠ weakness** (§4.1): three independent cases show
indirectness and assertion strength are orthogonal dimensions. -/
theorem indirectness_neq_weakness :
    ((kernelMust mastermindK blue).presup .w0 ∧
     (kernelMust mastermindK blue).assertion .w0) ∧
    ¬(kernelMust mastermindK red).presup .w0 ∧
    ((kernelMust indirectK blue).presup .w0 ∧
     ¬(kernelMust indirectK blue).assertion .w0) := by
  refine ⟨⟨mastermind_must_blue_defined, mastermind_must_blue_true⟩,
    λ h => h mastermind_red_settled, ?_, ?_⟩
  · rintro ⟨x, hx, hxor⟩
    rcases List.mem_singleton.mp hx with rfl
    rcases hxor with h_ent | h_exc
    · exact absurd (h_ent .w0 (show redOrBlue .w0 from by decide)) (by decide)
    · exact h_exc ⟨.w1, show redOrBlue .w1 from by decide, by decide⟩
  · intro h
    have hw0 : World.w0 ∈ indirectK.base :=
      mem_propIntersection.mpr λ p hp => by
        rcases List.mem_singleton.mp hp with rfl; decide
    exact (by decide : ¬ blue World.w0) (h hw0)

variable {W : Type*}

/-- **Modus ponens with must** ([von-fintel-gillies-2010] Argument 4.3.1): the
argument form "if φ, must ψ; φ; ∴ ψ" is valid under realistic B_K. -/
theorem modus_ponens_with_must (k : Kernel W) (φ ψ : (W → Prop)) (w : W)
    (hReal : w ∈ k.base)
    (_hDef : (kernelMust k ψ).presup w)
    (hCond : φ w → (kernelMust k ψ).assertion w)
    (hPhi : φ w) :
    ψ w :=
  hCond hPhi hReal

/-- **Must-perhaps contradiction** ([von-fintel-gillies-2010] Argument 4.3.2):
must φ ∧ might ¬φ is contradictory. When B_K ⊆ ⟦φ⟧, B_K ∩ ⟦¬φ⟧ = ∅. -/
theorem must_perhaps_contradiction (k : Kernel W) (φ : (W → Prop)) (w : W)
    (_hDef : (kernelMust k φ).presup w)
    (hMust : (kernelMust k φ).assertion w) :
    ¬(kernelMight k (λ w' => ¬ φ w')).assertion w := by
  intro hc
  obtain ⟨w', hw', hφneg⟩ := (Kernel.compatibleWith_iff _ _).mp hc
  exact hφneg (hMust hw')

/-! ### Implementation 2: settling by partitions ([von-fintel-gillies-2010] Def 7, §7.2)

Def 7 presents subject matters as equivalence relations on `W`: `S[P]` keeps
the pairs of `S` that agree on `P`, and `P` is an *issue* in `S` iff
`S[P] = S`. The subject matter S_K determined by a kernel is the refinement
`S_o[P₁]…[Pₙ]` of the universal relation along each kernel proposition —
equivalently, the relation "agrees with on every `X ∈ K`". Implementation 2:
K directly settles P iff P is an issue in S_K. -/

/-- The subject matter S_K determined by a kernel ([von-fintel-gillies-2010]
    Implementation 2(i)): worlds are equivalent iff they agree on every
    proposition in K. -/
def subjectMatter (k : Kernel W) : Setoid W where
  r w v := ∀ p ∈ k.props, (p w ↔ p v)
  iseqv := ⟨λ _ _ _ => Iff.rfl, λ h p hp => (h p hp).symm,
    λ h h' p hp => (h p hp).trans (h' p hp)⟩

/-- `P` is an **issue** in a subject matter `S` ([von-fintel-gillies-2010]
    Def 7(iii)): refining `S` along the `P`-boundary changes nothing, i.e.
    `S`-equivalent worlds never disagree on `P`. -/
def IsIssue (s : Setoid W) (φ : W → Prop) : Prop :=
  ∀ w v, s.r w v → (φ w ↔ φ v)

/-- K settles P by partition ([von-fintel-gillies-2010] Implementation 2(ii)):
    P is an issue in S_K. -/
def settlesByPartition (k : Kernel W) (φ : W → Prop) : Prop :=
  IsIssue (subjectMatter k) φ

/-- Partition settling implies entailment: all worlds in B_K agree on every
    X ∈ K, so they are S_K-equivalent; if φ is an issue in S_K, B_K is
    φ-uniform. Both implementations therefore imply entailment (cf.
    `explicit_implies_entailment`); the converse fails for both. -/
theorem partition_implies_entailment (k : Kernel W) (φ : (W → Prop))
    (h : settlesByPartition k φ) :
    k.followsFrom φ ∨ k.followsFrom (λ w => ¬ φ w) := by
  rcases Set.eq_empty_or_nonempty k.base with hEmpty | ⟨w₀, hw₀⟩
  · exact Or.inl ((Kernel.followsFrom_iff _ _).mpr λ w hw =>
      absurd (hEmpty ▸ hw) (Set.notMem_empty w))
  · have hrel : ∀ v ∈ k.base, (subjectMatter k).r w₀ v := λ v hv p hp =>
      ⟨λ _ => mem_propIntersection.mp hv p hp,
       λ _ => mem_propIntersection.mp hw₀ p hp⟩
    rcases Classical.em (φ w₀) with hφ | hφ
    · exact Or.inl ((Kernel.followsFrom_iff _ _).mpr λ v hv =>
        (h w₀ v (hrel v hv)).mp hφ)
    · exact Or.inr ((Kernel.followsFrom_iff _ _).mpr λ v hv hφv =>
        hφ ((h w₀ v (hrel v hv)).mpr hφv))

/-! ### Non-equivalence of the two implementations (§7.2)

Implementation 1 settles supersets of K-propositions that Implementation 2
misses (`K = {P}` settles `P ∪ Q` explicitly, but there are worlds agreeing
on `P` that disagree on `P ∪ Q`); Implementation 2 settles propositions
determined jointly by K-propositions that no single proposition settles
(`blue` is determined by `redOrBlue` together with `notRed`). -/

/-- S_{K} for `K = {red}` does not make `redOrBlue` an issue: w1 and w2
    agree on `red` but disagree on `redOrBlue`. -/
private theorem not_settles_redOrBlue :
    ¬ settlesByPartition ⟨[red]⟩ redOrBlue := by
  intro h
  have h12 := h .w1 .w2 (λ p hp => by
    rcases List.mem_singleton.mp hp with rfl; decide)
  exact absurd (h12.mp (by decide)) (by decide)

/-- Counterexample (Impl 1 ↛ Impl 2): `K = {red}` settles `redOrBlue`
    explicitly (red ⊆ redOrBlue), but not by partition. -/
theorem explicit_not_implies_partition :
    ∃ (k : Kernel World) (φ : (World → Prop)),
      directlySettlesExplicit k φ ∧ ¬ settlesByPartition k φ :=
  ⟨⟨[red]⟩, redOrBlue,
    ⟨red, by simp, Or.inl λ _ hw => Or.inl hw⟩, not_settles_redOrBlue⟩

/-- Counterexample (Impl 2 ↛ Impl 1): `mastermindK` settles `blue` by
    partition — S_K-equivalent worlds agree on `redOrBlue` and `notRed`,
    which jointly determine `blue` — but no single kernel proposition
    entails or excludes it. -/
theorem partition_not_implies_explicit :
    ∃ (k : Kernel World) (φ : (World → Prop)),
      settlesByPartition k φ ∧ ¬ directlySettlesExplicit k φ := by
  refine ⟨mastermindK, blue, λ w v h => ?_, mastermind_blue_unsettled⟩
  have h1 := h redOrBlue (by simp [mastermindK])
  have h2 := h notRed (by simp [mastermindK])
  revert h1 h2
  cases w <;> cases v <;> decide

/-- Entailment does not imply partition settling: `K = {red}` entails
    `redOrBlue` (B_K = {w0} ⊆ ⟦redOrBlue⟧) but does not settle it by
    partition. -/
theorem entailment_not_implies_partition :
    ∃ (k : Kernel World) (φ : (World → Prop)),
      k.followsFrom φ ∧ ¬ settlesByPartition k φ :=
  ⟨⟨[red]⟩, redOrBlue,
    λ w hw => Or.inl (mem_propIntersection.mp hw red (by simp)),
    not_settles_redOrBlue⟩

end VonFintelGillies2010
