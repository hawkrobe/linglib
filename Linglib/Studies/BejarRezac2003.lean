import Linglib.Syntax.Minimalist.Probe.Phi

/-!
# Béjar & Rezac 2003 — Person Licensing and the Derivation of PCC Effects
[bejar-rezac-2003]

[bejar-rezac-2003]: the Person Case Constraint ([bonet-1991]: in
combinations of a phonologically weak direct and indirect object, the
direct object may not be 1st/2nd person) derives from two ingredients
in a [chomsky-2000] probe-goal system:

- **Split probes** (§3): [π] and [#] are separate probes on a single
  head F (v⁰ in double-object constructions, T⁰ in
  dative-nominative ones), probing in that order. The [π]-probe
  matches the *closest* goal — every NP bears a person value, the
  dative's included (their (8): dative π=3 matches) — but the dative
  is inactive (its Case already valued), so [π] is absorbed without
  Agree: it "never enters into an Agree relationship with the
  accusative; remaining unvalued, it gets a default value".
- **The PLC** (§3): "An interpretable 1st/2nd person feature must be
  licensed by entering into an Agree relation with a functional
  category." Datives, PP-embedded themes, and strong pronouns are
  licensed by their own φ-bearing F (§4: the applicative P, dative
  marker, or focus F — inherent Case reduces to structural Case from
  F); a weak 1st/2nd accusative has only the [π]-probe, which the
  dative absorbs — the PCC.

Through `Probe/Basic.lean`, the [π]-probe is the **off-diagonal**
licensing shape: visibility is total (`pi.vis = ⊤` — closest goal),
neediness is bearing [participant] — the same shape as Mam's Voice_TR
(visible, halting, non-valuing intervener; `Studies/Scott2023.lean`)
and Zulu's L⁰ (`Studies/Halpert2012.lean`). [preminger-2014] Ch. 4's
Kichean application moves this very system onto the diagonal by
feature-relativizing the probes.

**Repairs** (§4–6): embed the theme under P (their (3)); or — the
French/Spanish dative-nominative repair (their (16)–(17)) — raise the
nominative over the dative, whereupon the projection of T introduces
a fresh [π]-probe and a *second Agree cycle* finds the nominative
first. Icelandic, where the dative itself satisfies the EPP and stays
highest, keeps the PCC in dative-nominative constructions (their
(12)). Modeled here as a list of probe cycles, each an ordered goal
sequence. The second-cycle mechanism prefigures [bejar-rezac-2009]'s
cyclic Agree (see `CyclicAgree.lean`), but the two are formally
distinct: 2003 varies the goal *order* under one probe; 2009 varies
the *relativization* (per-segment) over one order.
-/

namespace BejarRezac2003

open Minimalist

/-- A weak (X⁰) nominal in a single Case-licensing domain: its person
    value, and whether it sits under a φ-bearing functional category F
    (applicative P, dative marker, focus F). F assigns the nominal's
    Case — deactivating it for outside Agree — and licenses its [π]
    itself (§4). -/
structure Argument where
  person : Person
  fLicensed : Bool
  deriving DecidableEq, Repr

/-- Bears an interpretable 1st/2nd person feature (the PLC's domain),
    via [harley-ritter-2002] decomposition. -/
def Argument.IsParticipant (a : Argument) : Prop :=
  (decomposePerson a.person).hasParticipant = true

instance : DecidablePred Argument.IsParticipant := fun a =>
  inferInstanceAs (Decidable ((decomposePerson a.person).hasParticipant = true))

/-- One cycle of [π]-Agree over an ordered goal sequence: the probe
    matches the closest goal (every NP bears [π], per their (8), so
    visibility is total) and Agrees with it only if it is active —
    not licensed by its own φ-bearing F. An inactive match absorbs
    the probe without valuing it (their (9)). (The paper glosses
    activity as Caselessness but leaves open why same-projection
    Case valuation does not deactivate the French nominative for the
    second cycle; ¬F gives the right extension.) -/
def pi : Probe Argument :=
  { vis := fun _ => true, act := fun a => !a.fLicensed }

/-- One cycle of [π]-Agree: `pi.agree` over the ordered goals. -/
def piAgree (goals : List Argument) : Option Argument :=
  pi.agree goals

/-- The PLC over a derivation's [π]-Agree cycles: every interpretable
    1st/2nd person feature enters an Agree relation with a functional
    category — its own F, or some cycle's [π]-probe. Intended
    invariant (not enforced): each cycle is a reordering of `args`
    (the French repair re-probes the *same* two arguments in reversed
    order). Differs from the substrate `Minimalist.PLC` — Preminger's
    single-cycle, search-only, probe-relativized rendering — by the
    paper's F-licensing disjunct and the multiplicity of cycles; the
    single-cycle case collapses onto the substrate shape
    (`plcOk_singleCycle_iff_allLicensed`). -/
def PLCOk (cycles : List (List Argument)) (args : List Argument) : Prop :=
  ∀ a ∈ args, a.IsParticipant →
    (a.fLicensed = true ∨ ∃ goals ∈ cycles, piAgree goals = some a)

instance (cycles : List (List Argument)) (args : List Argument) :
    Decidable (PLCOk cycles args) :=
  inferInstanceAs (Decidable (∀ a ∈ args, a.IsParticipant →
    (a.fLicensed = true ∨ ∃ goals ∈ cycles, piAgree goals = some a)))

/-! ### The strong PCC, derived -/

/-- A dative absorbs the [π]-probe without valuing it: the closest
    goal matches but is inactive, so the cycle Agrees with nothing —
    "remaining unvalued, it gets a default value". The default is not
    a crash (a `Probe.outcome` of `unvalued`, tolerated per [preminger-2014]
    Ch. 5); ungrammaticality comes only from the PLC. -/
theorem piAgree_absorbed (dat acc : Argument) (hd : dat.fLicensed = true) :
    piAgree [dat, acc] = none :=
  Probe.agree_eq_none_of_inactive rfl (by simp [pi, hd])

/-- Single-cycle collapse onto the substrate's `(needs, vis)`
    licensing shape: one [π]-cycle over the base order satisfies the
    PLC iff `AllLicensed` holds with neediness "participant and not
    F-licensed" and total visibility. The recoding is lossy by
    design: it folds the F-licensing route into ¬needy, whereas the
    paper counts F-licensing as itself an Agree relation; and the
    multi-cycle repairs ((16)–(17)) escape this signature entirely. -/
theorem plcOk_singleCycle_iff_allLicensed (goals : List Argument) :
    PLCOk [goals] goals ↔
      (Probe.indiscriminate (α := Argument)).AllLicensed
        (fun a => decide a.IsParticipant && !a.fLicensed) goals := by
  unfold PLCOk Probe.AllLicensed
  constructor
  · intro h a ha hneeds
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hneeds
    rcases h a ha hneeds.1 with hF' | ⟨gs, hgs, hag⟩
    · exact nomatch hneeds.2.symm.trans hF'
    · rw [List.mem_singleton.mp hgs] at hag
      exact (Probe.agree_eq_some_iff.mp hag).1
  · intro h a ha hpart
    cases hF : a.fLicensed with
    | true => exact Or.inl rfl
    | false =>
      refine Or.inr ⟨goals, List.mem_singleton_self _, ?_⟩
      exact (Probe.agree_eq_some_iff (p := pi)).mpr
        ⟨h a ha (by simp [hpart, hF]), by simp [pi, hF]⟩

/-- **The PCC** (their (1)/(7), generalized): in a double-object
    configuration — dative over accusative, one [π]-Agree cycle on
    v⁰ — the PLC holds iff the accusative is 3rd person. Left-to-right
    is Bonet's strong PCC; right-to-left says 3rd-person accusatives
    and F-licensed datives of any person are unconstrained. -/
theorem strong_pcc (dat acc : Argument)
    (hd : dat.fLicensed = true) (ha : acc.fLicensed = false) :
    PLCOk [[dat, acc]] [dat, acc] ↔ ¬ acc.IsParticipant := by
  constructor
  · intro h hacc
    rcases h acc (List.mem_pair.mpr (Or.inr rfl)) hacc with hF | ⟨gs, hgs, hag⟩
    · exact nomatch ha.symm.trans hF
    · rw [List.mem_singleton.mp hgs, piAgree_absorbed dat acc hd] at hag
      exact nomatch hag
  · intro hacc a ha' hpart
    rcases List.mem_pair.mp ha' with rfl | rfl
    · exact Or.inl hd
    · exact absurd hpart hacc

/-- The French clitic cluster (their (1)): *le lui* licit, **te lui*
    a PCC violation. -/
theorem french_cluster :
    PLCOk [[⟨.third, true⟩, ⟨.third, false⟩]]
      [⟨.third, true⟩, ⟨.third, false⟩] ∧
    ¬ PLCOk [[⟨.third, true⟩, ⟨.second, false⟩]]
      [⟨.third, true⟩, ⟨.second, false⟩] := by
  decide

/-! ### Repairs -/

/-- Repair by P-embedding (their (3), *je te ai présenté à lui*): in
    the prepositional construction the theme is the highest goal and
    the dative sits in a low PP — the [π]-probe finds the active theme
    and Agrees, and the PP-internal goal is licensed by P itself. -/
theorem pp_repair :
    PLCOk [[⟨.second, false⟩, ⟨.third, true⟩]]
      [⟨.second, false⟩, ⟨.third, true⟩] := by
  decide

/-- The dative-nominative split (their (12) vs. (13)/(16)–(17)):
    Icelandic datives satisfy the EPP and stay highest, so the
    [π]-cycle is absorbed and a 1st/2nd nominative violates the PLC
    (*þið*, their (12)). (Modeled as a single cycle; per their (25c)
    Icelandic also projects a second one, but the dative still
    intervenes — extensionally the same.) In French the nominative
    raises over the dative and T's projection opens a second
    [π]-cycle over the reversed order, which finds the now-highest
    active nominative — PCC obviated (their (13)). -/
theorem dnc_split :
    -- Icelandic: one cycle, dative highest — 2nd-person nominative out
    ¬ PLCOk [[⟨.third, true⟩, ⟨.second, false⟩]]
      [⟨.third, true⟩, ⟨.second, false⟩] ∧
    -- French: second cycle over the reversed order — 1st-person nominative in
    PLCOk [[⟨.third, true⟩, ⟨.first, false⟩],
           [⟨.first, false⟩, ⟨.third, true⟩]]
      [⟨.third, true⟩, ⟨.first, false⟩] := by
  decide

end BejarRezac2003
