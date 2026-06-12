import Linglib.Syntax.Minimalist.Phi.Probing
import Linglib.Syntax.Minimalist.CyclicAgree
import Linglib.Syntax.Minimalist.PConstraint
import Linglib.Studies.BejarRezac2003

/-!
# Coon & Keine 2021 — Feature Gluttony [coon-keine-2021]

[coon-keine-2021] (LI 52(4)): hierarchy effects — PCC,
dative-nominative restrictions, copula effects — do not come from
failed Agree or failed nominal licensing, but from **feature
gluttony**: a single probe entering more than one Agree dependency.
Agree (their (14)) is segment-based ([bejar-rezac-2009]'s
articulated probes): each segment [uF] independently agrees with the
closest accessible DP bearing [F], copying that DP's whole geometry
(coarse copying; not Multiple Agree — each segment agrees with at
most one DP, their fn. 10). Probing is obligatory but
failure-tolerant ([preminger-2014]).

Gluttony — distinct segments agreeing with distinct DPs (their
(15)–(16)) — arises only in *inverse* configurations: when the lower
DP bears probe-relevant segments the higher DP lacks
(`gluttonous_only_inverse`). It is not itself fatal; for
clitic-doubling probes, their (30) (every segment-agreed DP must
cliticize onto the host) is jointly unsatisfiable under gluttony
(cliticizing one-at-a-time violates (30) mid-derivation; cliticizing
simultaneously violates binary Merge) — that argument is carried in
prose; `pccViolation` states its upshot, gluttony itself.

## PCC typology from probe articulation (their (39))

- Weak (`weakProbe`, Catalan (22)–(32)): *3>[PART].
- Ultrastrong (`ultrastrongProbe`): additionally *2>1.
- Me-First (`meFirstProbe`, missing intermediate segment — their
  fn. 22 flags this as non-innocuous): the probe derives *{2,3}>1;
  their table 1 describes Me-First as *1/2/3>1 — the 1>1 cell is
  where description and mechanism part ways (cf. their fn. 22's
  alternative treatment of Me-First as clitic ordering).
- Strong (Basque (35)–(38)): weak probe + **K-opaque datives**
  (datives expose only [PERS], their §3.4.1) — or the branching
  probe of their fn. 22 (i) with φ-transparent datives.

Universal predictions (§3.4.2): no probe bans [PART]>3 or 3>3
(`direct_never_banned` — the geometry makes such gluttony
impossible), and for well-articulated probes a [PART]>[PART] ban
entails a 3>[PART] ban (`ban_part_part_implies_ban_three_part`).

## Rival accounts (their §2, comparisons drawn by the paper)

- Against PLC/licensing accounts ([bejar-rezac-2003]): hierarchy
  effects track the *probe*, not licensing needs — in probeless
  environments (their (10), Basque nonfinite clauses) PCC vanishes;
  a PLC with no probe to satisfy it predicts the opposite
  (`probeless_divergence_from_plc`; B&R's own F-licensing route is
  the escape their §4 provides, so the disagreement is over where
  the explanatory work happens).
- Against [pancheva-zubizarreta-2018]'s P-Constraint (criticized in
  their §2 as stipulating the licensing parameter): the gluttony
  tables match `PConstraint.IsLicit` exactly for the weak and strong
  grammars, and diverge on one cell each for ultrastrong (2>2) and
  me-first (1>1) — `*_matches_pConstraint` / `*_diverges_from_pConstraint`.

Segments are `CyclicAgree.Segment` — the same inventory, since both
formalizations descend from [bejar-rezac-2009]. `ckSpec` follows
their (11), where SPKR and ADDR are sister leaves in one geometry
(2nd person always bears ADDR); it differs from
`CyclicAgree.personSpec .standard` only there
(`ckSpec_filter_eq_personSpec`), and is grounded in
`decomposePerson` (`ckSpec_grounded`).

Phase 2 (planned): §4's agreement-side resolution — gluttony
survives iff the conflicting bundles are realized syncretically
(Icelandic DAT-NOM, German copulas) — via `VocabSimple.spellout`.
-/

namespace CoonKeine2021

open Minimalist
open Minimalist.CyclicAgree (Segment)

/-! ### Feature geometry and goals (their (11), §3.4.1) -/

/-- Person geometry, their (11): [PERS [PART [SPKR][ADDR]]] — 1st is
    [PERS, PART, SPKR], 2nd is [PERS, PART, ADDR], 3rd is bare
    [PERS]. Segments are [bejar-rezac-2009]'s
    (`CyclicAgree.Segment`); deviates from
    `CyclicAgree.personSpec .standard` only in 2nd person's ADDR
    leaf. -/
def ckSpec : Person → List Segment
  | .first | .firstInclusive | .firstExclusive =>
      [.pi, .participant, .speaker]
  | .second => [.pi, .participant, .addressee]
  | .third | .zero => [.pi]

/-- `ckSpec` is grounded in the [harley-ritter-2002] decomposition:
    PART and SPKR membership match `decomposePerson`. -/
theorem ckSpec_grounded (p : Person) :
    ((ckSpec p).contains .participant = (decomposePerson p).hasParticipant) ∧
    ((ckSpec p).contains .speaker = (decomposePerson p).hasAuthor) := by
  cases p <;> exact ⟨rfl, rfl⟩

/-- Forgetting the ADDR leaf recovers `personSpec .standard`. -/
theorem ckSpec_filter_eq_personSpec (p : Person) :
    (ckSpec p).filter (· != Segment.addressee) =
      CyclicAgree.personSpec .standard p := by
  cases p <;> rfl

/-- A goal DP: its person, and whether it is encapsulated under a
    K(ase) shell (their §3.4.1: Basque datives are formally 3rd
    person — only [PERS] is visible from outside). -/
structure Goal where
  person : Person
  kOpaque : Bool := false
  deriving DecidableEq, Repr

/-- The φ-segments a goal exposes to outside probing. -/
def Goal.visibleSegs (g : Goal) : List Segment :=
  if g.kOpaque then [.pi] else ckSpec g.person

/-! ### Probes and segment-based Agree (their (13), (14), (39)) -/

/-- A probe: its unvalued segments (their (13)). -/
abbrev Probe := List Segment

/-- Their (39a): [uPERS [uPART]] — Weak PCC (Catalan). -/
def weakProbe : Probe := [.pi, .participant]

/-- Their (39b): [uPERS [uPART [uSPKR]]] — Ultrastrong PCC. -/
def ultrastrongProbe : Probe := [.pi, .participant, .speaker]

/-- Their (39c): [uPERS [uSPKR]] — Me-First PCC (missing
    intermediate segment; see their fn. 22). -/
def meFirstProbe : Probe := [.pi, .speaker]

/-- Their fn. 22 (i): [uPERS [uPART [uSPKR][uADDR]]] — Strong PCC
    with φ-transparent datives. -/
def branchingStrongProbe : Probe := [.pi, .participant, .speaker, .addressee]

/-- Agree, their (14): a segment agrees with the closest accessible
    goal bearing it — `probeSearch` over position-indexed tokens
    (two same-φ arguments remain distinct agreed-with tokens). -/
def segGoal (s : Segment) (goals : List Goal) : Option (Goal × Nat) :=
  probeSearch (fun t => decide (s ∈ t.1.visibleSegs)) goals.zipIdx

/-- Feature gluttony (their (15)–(16)): two segments of one probe
    agree with distinct DPs. Not itself fatal; the crash comes from
    downstream resolution (their (30) for clitics, syncretism for
    agreement). -/
def Gluttonous (P : Probe) (goals : List Goal) : Prop :=
  ∃ s₁ ∈ P, ∃ s₂ ∈ P, ∃ t₁ ∈ goals.zipIdx, ∃ t₂ ∈ goals.zipIdx,
    segGoal s₁ goals = some t₁ ∧ segGoal s₂ goals = some t₂ ∧ t₁.2 ≠ t₂.2

instance (P : Probe) (goals : List Goal) : Decidable (Gluttonous P goals) := by
  unfold Gluttonous; infer_instance

/-! ### Gluttony is limited to inverse configurations -/

/-- `segGoal` on a two-goal configuration, by cases on visibility. -/
private theorem segGoal_pair (s : Segment) (hi lo : Goal) :
    segGoal s [hi, lo] =
      if s ∈ hi.visibleSegs then some (hi, 0)
      else if s ∈ lo.visibleSegs then some (lo, 1)
      else none := by
  show (([(hi, 0), (lo, 1)] : List (Goal × Nat)).find?
    (fun t => decide (s ∈ t.1.visibleSegs))) = _
  by_cases h1 : s ∈ hi.visibleSegs <;>
    by_cases h2 : s ∈ lo.visibleSegs <;>
      simp [List.find?, h1, h2]

/-- Their "general consequence" (after (20)): gluttony arises only
    in inverse configurations. If every segment the lower goal
    exposes is also borne by the higher goal, no probe is
    gluttonous over them — direct (17)–(18) and balanced (19)–(20)
    configurations are safe. -/
theorem gluttonous_only_inverse (P : Probe) {hi lo : Goal}
    (hsub : ∀ s, s ∈ lo.visibleSegs → s ∈ hi.visibleSegs) :
    ¬ Gluttonous P [hi, lo] := by
  rintro ⟨s₁, _, s₂, _, t₁, _, t₂, _, h₁, h₂, hne⟩
  have hkey : ∀ s, ∀ t : Goal × Nat, segGoal s [hi, lo] = some t → t.2 = 0 := by
    intro s t ht
    rw [segGoal_pair] at ht
    by_cases hhi : s ∈ hi.visibleSegs
    · rw [if_pos hhi] at ht
      exact Option.some.inj ht ▸ rfl
    · rw [if_neg hhi, if_neg (fun hl => hhi (hsub s hl))] at ht
      exact nomatch ht
  exact hne ((hkey s₁ t₁ h₁).trans (hkey s₂ t₂ h₂).symm)

/-! ### The PCC tables, derived (their §3.3–3.4) -/

/-- The PCC configuration: a clitic-doubling probe over IO > DO. By
    their (30), every segment-agreed DP must cliticize onto the
    host; under gluttony this is jointly unsatisfiable (one-at-a-time
    violates (30) mid-derivation, simultaneous violates binary
    Merge), so gluttony here IS the predicted ban. -/
def pccViolation (P : Probe) (ioOpaque : Bool) (io do_ : Person) : Prop :=
  Gluttonous P [⟨io, ioOpaque⟩, ⟨do_, false⟩]

instance (P : Probe) (b : Bool) (io do_ : Person) :
    Decidable (pccViolation P b io do_) :=
  inferInstanceAs (Decidable (Gluttonous _ _))

/-- The 1/2/3 grid the PCC literature states its varieties over. -/
def persons : List Person := [.first, .second, .third]

/-- Weak PCC (their (22), Catalan (24)/(28)/(31)): exactly
    *3>[PART]. -/
theorem weak_pcc_table :
    ∀ io ∈ persons, ∀ do_ ∈ persons,
      pccViolation weakProbe false io do_ ↔
        (io = .third ∧ do_ ≠ .third) := by
  decide

/-- Ultrastrong PCC (their (39b)): *3>[PART] and *2>1. -/
theorem ultrastrong_pcc_table :
    ∀ io ∈ persons, ∀ do_ ∈ persons,
      pccViolation ultrastrongProbe false io do_ ↔
        ((io = .third ∧ do_ ≠ .third) ∨ (io = .second ∧ do_ = .first)) := by
  decide

/-- What the Me-First probe (39c) derives: *{2,3}>1. (Their table 1
    describes Me-First as *X>1 for all X; the 1>1 cell is underivable
    by gluttony — their fn. 22 discusses alternatives.) -/
theorem mefirst_pcc_table :
    ∀ io ∈ persons, ∀ do_ ∈ persons,
      pccViolation meFirstProbe false io do_ ↔
        (do_ = .first ∧ io ≠ .first) := by
  decide

/-- Strong PCC via K-opaque datives (their (35)–(36), Basque): with
    the dative exposing only [PERS], the weak probe bans every
    [PART] direct object — *X>[PART] for all X. -/
theorem strong_pcc_table :
    ∀ io ∈ persons, ∀ do_ ∈ persons,
      pccViolation weakProbe true io do_ ↔ do_ ≠ .third := by
  decide

/-- Strong PCC via the branching probe (their fn. 22 (i)), datives
    φ-transparent: bans every *distinct-person* cluster with a
    [PART] direct object. Unlike K-opacity, same-person clusters
    (1>1, 2>2) are not gluttonous — the second leaf segment finds no
    second goal — but those are independently unattestable in clitic
    clusters (binding). -/
theorem branching_strong_pcc_table :
    ∀ io ∈ persons, ∀ do_ ∈ persons,
      pccViolation branchingStrongProbe false io do_ ↔
        (do_ ≠ .third ∧ io ≠ do_) := by
  decide

/-- Their (37a/b) Basque contrast: a DAT>ABS experiencer
    configuration is gluttonous (*3DAT>1ABS), but the ABS>DAT order
    of motion verbs is not — with opaque datives, reversing the
    order removes the inversion. -/
theorem basque_dat_abs_contrast :
    pccViolation weakProbe true .third .first ∧
    ¬ Gluttonous weakProbe [⟨.first, false⟩, ⟨.third, true⟩] := by
  decide

/-! ### Universal predictions (their §3.4.2) -/

/-- No probe whatsoever bans a direct ([PART]>3) or balanced (3>3)
    configuration: the lower goal's bare [PERS] is contained in any
    goal's geometry, so gluttony is impossible — "the gluttony
    account therefore derives the fact that no such PCC pattern
    exists". -/
theorem direct_never_banned (P : Probe) (io : Person) :
    ¬ pccViolation P false io .third := by
  apply gluttonous_only_inverse
  intro s hs
  have : s = .pi := by
    cases hs with
    | head => rfl
    | tail _ h => exact nomatch h
  subst this
  cases io <;> decide

/-- Probes articulated along the geometry (their (13)/(39a,b)/(i)):
    rooted in [uPERS], downward-closed. `meFirstProbe` violates this
    (their fn. 22: missing intermediates are "not innocuous"). -/
def WellArticulated (P : Probe) : Prop :=
  Segment.pi ∈ P ∧
  (Segment.speaker ∈ P → Segment.participant ∈ P) ∧
  (Segment.addressee ∈ P → Segment.participant ∈ P)

/-- For well-articulated probes, banning [PART]>[PART] entails
    banning 3>[PART] (their §3.4.2 implicational universal,
    instantiated at 2>1 ⇒ 3>1): the only segment a 1st-person DO
    can win against a 2nd-person IO is [uSPKR], and it wins against
    a 3rd-person IO a fortiori, while [uPERS] still lands on the
    IO. -/
theorem ban_part_part_implies_ban_three_part (P : Probe)
    (hwf : WellArticulated P)
    (h : pccViolation P false .second .first) :
    pccViolation P false .third .first := by
  obtain ⟨s₁, hs₁, s₂, hs₂, t₁, ht₁m, t₂, ht₂m, h₁, h₂, hne⟩ := h
  -- the only segment a 1st-person DO can win against a 2nd-person IO
  -- is [uSPKR] — checked segment by segment
  have spk_of : ∀ s : Segment,
      segGoal s [⟨.second, false⟩, ⟨.first, false⟩] =
        some (⟨.first, false⟩, 1) → s = .speaker := by
    intro s h
    cases s
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · rfl
    · exact absurd h (by decide)
  have hspk : Segment.speaker ∈ P := by
    rcases List.mem_pair.mp ht₁m with rfl | rfl <;>
      rcases List.mem_pair.mp ht₂m with rfl | rfl
    · exact absurd rfl hne
    · exact spk_of s₂ h₂ ▸ hs₂
    · exact spk_of s₁ h₁ ▸ hs₁
    · exact absurd rfl hne
  -- with [uPERS] and [uSPKR] both on the probe, 3>1 is gluttonous
  exact ⟨.pi, hwf.1, .speaker, hspk,
    (⟨.third, false⟩, 0), by decide, (⟨.first, false⟩, 1), by decide,
    by decide, by decide, by decide⟩

/-! ### Rival accounts (their §2) -/

/-- Probeless environments (their (10): Basque nonfinite clauses lose
    the PCC): no probe, no gluttony — the configuration is predicted
    grammatical. A bare PLC with no Agree cycle available
    ([bejar-rezac-2003] as formalized in `BejarRezac2003.PLCOk`)
    deems an unembedded participant unlicensed in the same
    environment. (B&R's F-licensing route is their escape — the
    disagreement is over whether hierarchy effects track licensing
    needs or the probe.) -/
theorem probeless_divergence_from_plc :
    ¬ Gluttonous [] [⟨.first, false⟩, ⟨.second, false⟩] ∧
    ¬ BejarRezac2003.PLCOk [] [⟨.first, false⟩] := by
  decide

open Minimalist.PConstraint in
/-- Gluttony reproduces [pancheva-zubizarreta-2018]'s weak and
    strong grammars cell-for-cell over the 1/2/3 grid. -/
theorem weak_strong_match_pConstraint :
    (∀ io ∈ persons, ∀ do_ ∈ persons,
      (pccViolation weakProbe false io do_ ↔ ¬ IsLicit weakGrammar io do_)) ∧
    (∀ io ∈ persons, ∀ do_ ∈ persons,
      (pccViolation weakProbe true io do_ ↔ ¬ IsLicit strongGrammar io do_)) := by
  decide

open Minimalist.PConstraint in
/-- Where the two formal systems part ways, ultrastrong half:
    P-Constraint's ultrastrong grammar additionally rules out 2>2
    (P-Uniqueness with no [+author] rescue), which gluttony permits
    (a 2nd-person IO fully matches the probe). All other cells
    agree. -/
theorem ultrastrong_diverges_from_pConstraint :
    (∀ io ∈ persons, ∀ do_ ∈ persons, (io, do_) ≠ (.second, .second) →
      (pccViolation ultrastrongProbe false io do_ ↔
        ¬ IsLicit ultraStrongGrammar io do_)) ∧
    ¬ pccViolation ultrastrongProbe false .second .second ∧
    ¬ IsLicit ultraStrongGrammar .second .second := by
  decide

open Minimalist.PConstraint in
/-- Me-first half: P-Constraint's me-first grammar rules out 1>1,
    which gluttony permits (the probe's [uSPKR] is matched by the
    IO) — the same cell where the probe (39c) departs from the
    descriptive *X>1 statement. All other cells agree. -/
theorem mefirst_diverges_from_pConstraint :
    (∀ io ∈ persons, ∀ do_ ∈ persons, (io, do_) ≠ (.first, .first) →
      (pccViolation meFirstProbe false io do_ ↔
        ¬ IsLicit meFirstGrammar io do_)) ∧
    ¬ pccViolation meFirstProbe false .first .first ∧
    ¬ IsLicit meFirstGrammar .first .first := by
  decide

end CoonKeine2021
