import Linglib.Syntax.Minimalist.Phi.Probing

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

Through `Phi/Probing.lean`, the [π]-probe is the **off-diagonal**
licensing shape: visibility is total (`probeSearch ⊤` = closest goal),
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
(12)). The second-cycle mechanism is the seed of [bejar-rezac-2009]'s
cyclic Agree (`Syntax/Minimalist/CyclicAgree.lean`). Modeled here as
a list of probe cycles, each an ordered goal sequence.
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
    matches the closest goal (every NP bears [π], so visibility is
    total — `probeSearch ⊤`) and Agrees with it only if it is still
    active (Case not yet valued, ¬F). An inactive match absorbs the
    probe without valuing it (their (9)). -/
def piAgree (goals : List Argument) : Option Argument :=
  (probeSearch (fun _ => true) goals).bind
    (fun a => if a.fLicensed then none else some a)

/-- The PLC over a derivation's [π]-Agree cycles: every interpretable
    1st/2nd person feature enters an Agree relation with a functional
    category — its own F, or some cycle's [π]-probe. -/
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
    a crash (cf. `ObligatoryOperations`); ungrammaticality comes only
    from the PLC. -/
theorem piAgree_absorbed (dat acc : Argument) (hd : dat.fLicensed = true) :
    piAgree [dat, acc] = none := by
  simp [piAgree, probeSearch, List.find?, hd]

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
    · exact absurd hF (by simp [ha])
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
    Icelandic datives satisfy the EPP and stay highest, so the single
    [π]-cycle is absorbed and a 1st/2nd nominative violates the PLC
    (*þið*, their (12)). In French the nominative raises over the
    dative and T's projection opens a second [π]-cycle over the
    reversed order, which finds the now-highest active nominative —
    PCC obviated (their (13)). -/
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
