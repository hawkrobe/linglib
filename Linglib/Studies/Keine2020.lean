import Linglib.Syntax.Minimalist.Probe.Profile
import Linglib.Syntax.Minimalist.ExtendedProjection.ClauseSpine

/-!
# Keine (2020): Probes and Their Horizons

This file formalizes the horizons theory of [keine-2020] as it parameterizes probes across
languages. A probe's search terminates at its horizon category ((33)); labels are bilateral within
an extended projection, so a clause is opaque to a probe exactly when its label contains the
horizon, and Upward Entailment holds for every probe (`upward_entailment`). Hindi's four clause
sizes ((168)) follow from the probes of (219), with NmlzP and CP incomparable, the one transparent
to wh-licensing and the other to Ā-movement (`hindi_table`, `nmlzP_cP_incomparable`), and the
A-Movement–Agreement Generalization ((231)) from the two probes on T⁰ sharing a horizon. English
((241)) and German ((367)), with ForceP above CP, follow the same way (`english_table`,
`german_table`), and the Itelmen ((269)) and Tsez ((271)) probes mismatch movement and
agreement in both directions (`mismatches`). Vacuity ((274)–(278)) yields the Height–Locality
Theorem ((279)), which the attested probes obey, and the default horizon ((307)) is the strictest
nonvacuous one (`hlt_location_to_horizon`, `default_horizon_strictest`). Variation is a horizon
parameter: the A-movement settings of (300) form an entailment chain (`a_movement_chain`), and
the Ban on Improper Movement (Section 6.2) with the smuggling and remnant-movement restrictions
(Section 3.4.3) is the opacity of a CP to the A-probes whose horizon it inherits
(`improper_movement`).

## Implementation notes

Labels are the projected heads of the substrate's `ClauseSpine`s, with the Tsez TopP and ForceP
defined here; the probes are the substrate's `LanguageProbeConfig.hindi` and
`LanguageProbeConfig.english`, `english_extr` and `lubukusuAProbe` where the book's settings are
recorded there, and are defined here for German, Itelmen and Tsez, whose heads (269) and (271)
leave open. Chapters 4 and 5, on CP and vP phases, are not formalized beyond the opacity facts the
tables record.

## References

* [keine-2020]
* [bobaljik-wurmbrand-2005]
* [polinsky-potsdam-2001]
-/

namespace Keine2020

open Minimalist

/-- A probe's row of a transparency table over clause sizes. -/
def row (sizes : List ClauseSpine) (p : Probe.Profile) : List Bool :=
  sizes.map λ s => p.transparentToLabel s.projectedHeads

/-! ### Upward Entailment -/

/-- Larger clauses are at least as opaque, for every probe, since a clause's label extends the
labels of the smaller clauses of its extended projection: TP extends vP, CP and NmlzP extend
TP, ForceP extends CP. -/
theorem upward_entailment (p : Probe.Profile) :
    (p.transparentToLabel ClauseSpine.vP.projectedHeads = false →
        p.transparentToLabel ClauseSpine.tP.projectedHeads = false) ∧
      (p.transparentToLabel ClauseSpine.tP.projectedHeads = false →
        p.transparentToLabel ClauseSpine.cP.projectedHeads = false ∧
          p.transparentToLabel ClauseSpine.nmlzP.projectedHeads = false) ∧
      (p.transparentToLabel ClauseSpine.cP.projectedHeads = false →
        p.transparentToLabel ClauseSpine.forceP.projectedHeads = false) :=
  ⟨upward_entailment_label p _ _ (by decide),
    λ h => ⟨upward_entailment_label p _ _ (by decide) h,
      upward_entailment_label p _ _ (by decide) h⟩,
    upward_entailment_label p _ _ (by decide)⟩

/-! ### Hindi (Chapters 2 and 3) -/

/-- The four Hindi clause sizes of (168), the nominalized clause beside the finite one. -/
def hindiSizes : List ClauseSpine := [.vP, .tP, .cP, .nmlzP]

/-- (168) from (219): A-movement and φ-agreement, on T⁰ with horizon T, enter only vP clauses;
wh-licensing, on C⁰ with horizon C, every clause but CP; Ā-movement, on C⁰ with horizon Nmlz,
every clause but NmlzP. -/
theorem hindi_table :
    row hindiSizes LanguageProbeConfig.hindi.aMove = [true, false, false, false] ∧
      row hindiSizes LanguageProbeConfig.hindi.phi = [true, false, false, false] ∧
      row hindiSizes LanguageProbeConfig.hindi.wh = [true, true, false, true] ∧
      row hindiSizes LanguageProbeConfig.hindi.ābar = [true, true, true, false] := by
  decide

/-- NmlzP and CP are incomparable, each opaque to a probe on C⁰ that the other admits, so
transparency does not order the clause sizes linearly and three locality profiles arise. -/
theorem nmlzP_cP_incomparable :
    (LanguageProbeConfig.hindi.wh.transparentToLabel ClauseSpine.nmlzP.projectedHeads = true ∧
        LanguageProbeConfig.hindi.wh.transparentToLabel ClauseSpine.cP.projectedHeads = false) ∧
      (LanguageProbeConfig.hindi.ābar.transparentToLabel ClauseSpine.cP.projectedHeads = true ∧
        LanguageProbeConfig.hindi.ābar.transparentToLabel ClauseSpine.nmlzP.projectedHeads =
          false) ∧
      ([LanguageProbeConfig.hindi.phi, LanguageProbeConfig.hindi.wh,
        LanguageProbeConfig.hindi.ābar].map (row hindiSizes)).Nodup := by
  decide

/-- (231): the A- and φ-probes coincide, so a clause that A-extraction has entered is transparent
to agreement, which is then obligatory; the Ā-probe's horizon differs, and a finite clause shows
it. -/
theorem a_movement_agreement_generalization :
    LanguageProbeConfig.hindi.aMove = LanguageProbeConfig.hindi.phi ∧
      LanguageProbeConfig.hindi.ābar.transparentToLabel ClauseSpine.cP.projectedHeads = true ∧
      LanguageProbeConfig.hindi.phi.transparentToLabel ClauseSpine.cP.projectedHeads = false :=
  ⟨rfl, by decide, by decide⟩

/-! ### English and German (Section 3.4.2 and Chapter 4) -/

/-- The English clause sizes. -/
def englishSizes : List ClauseSpine := [.vP, .tP, .cP]

/-- (241): the A-probe, with horizon C, enters nonfinite clauses but not finite ones, the ban on
hyperraising (242); the wh-probe has no horizon; extraposition, with horizon T, leaves no clause
larger than vP. -/
theorem english_table :
    row englishSizes LanguageProbeConfig.english.aMove = [true, true, false] ∧
      row englishSizes LanguageProbeConfig.english.wh = [true, true, true] ∧
      row englishSizes english_extr = [true, false, false] := by
  decide

/-- The German probes of (367): scrambling on T⁰ with horizon T, relativization on C⁰ with
horizon C, wh-movement into a verb-final clause on C⁰ with horizon Force, and topicalization on
Force⁰ without a horizon. -/
def germanScr : Probe.Profile := ⟨.T, some .T⟩

def germanRel : Probe.Profile := ⟨.C, some .C⟩

def germanWh : Probe.Profile := ⟨.C, some .Force⟩

def germanTop : Probe.Profile := ⟨.Force, none⟩

/-- The German clause sizes: verb-second clauses project ForceP above CP. -/
def germanSizes : List ClauseSpine := [.vP, .tP, .cP, .forceP]

/-- Chapter 4: the four German movements cut off at successive clause sizes. -/
theorem german_table :
    row germanSizes germanScr = [true, false, false, false] ∧
      row germanSizes germanRel = [true, true, false, false] ∧
      row germanSizes germanWh = [true, true, true, false] ∧
      row germanSizes germanTop = [true, true, true, true] := by
  decide

/-! ### Movement–agreement mismatches (Section 3.4.5) -/

/-- Itelmen ((269)): φ-agreement with horizon T, movement without a horizon. -/
def itelmenPhi (head : Cat) : Probe.Profile := ⟨head, some .T⟩

def itelmenMove (head : Cat) : Probe.Profile := ⟨head, none⟩

/-- Tsez ((271)): φ-agreement with horizon Force, movement with horizon Top. -/
def tsezPhi (head : Cat) : Probe.Profile := ⟨head, some .Force⟩

def tsezMove (head : Cat) : Probe.Profile := ⟨head, some .Top⟩

/-- The Tsez clause sizes above TP: TopP, and ForceP, which requires TopP below it. -/
def tsezTopP : ClauseSpine := ⟨[.V, .v, .T, .Top], by decide⟩

def tsezForceP : ClauseSpine := ⟨[.V, .v, .T, .Top, .Force], by decide⟩

/-- (269), (271): movement and agreement mismatch in both directions. An Itelmen TP clause is
transparent to movement but opaque to agreement; a Tsez TopP clause is transparent to agreement
but opaque to movement, and a ForceP clause, inheriting Top, to neither. -/
theorem mismatches (head : Cat) :
    ((itelmenMove head).transparentToLabel ClauseSpine.tP.projectedHeads = true ∧
        (itelmenPhi head).transparentToLabel ClauseSpine.tP.projectedHeads = false) ∧
      ((tsezPhi head).transparentToLabel tsezTopP.projectedHeads = true ∧
        (tsezMove head).transparentToLabel tsezTopP.projectedHeads = false) ∧
      (tsezPhi head).transparentToLabel tsezForceP.projectedHeads = false ∧
        (tsezMove head).transparentToLabel tsezForceP.projectedHeads = false :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl⟩

/-! ### The Height–Locality Theorem (Section 3.5) -/

/-- (274)–(278): a probe on C⁰ whose horizon is a category of its sister TP terminates there and
is vacuous. -/
theorem vacuous_on_C :
    ∀ h ∈ ClauseSpine.tP.projectedHeads, (⟨.C, some h⟩ : Probe.Profile).isVacuous = true := by
  decide

/-- (279a), location to horizon: a probe on T⁰, C⁰ or Force⁰ with a horizon among the
projections below it is vacuous. -/
theorem hlt_location_to_horizon :
    (∀ h ∈ ClauseSpine.vP.projectedHeads, (⟨.T, some h⟩ : Probe.Profile).isVacuous = true) ∧
      (∀ h ∈ ClauseSpine.tP.projectedHeads, (⟨.C, some h⟩ : Probe.Profile).isVacuous = true) ∧
      ∀ h ∈ ClauseSpine.cP.projectedHeads,
        (⟨.Force, some h⟩ : Probe.Profile).isVacuous = true := by
  decide

/-- (279b), horizon to location: a probe with horizon T is vacuous above T⁰, and one with
horizon C above C⁰. -/
theorem hlt_horizon_to_location :
    (∀ head ∈ [Cat.C, .Force], (⟨head, some .T⟩ : Probe.Profile).isVacuous = true) ∧
      (⟨.Force, some .C⟩ : Probe.Profile).isVacuous = true := by
  decide

/-- The attested probes of (219), (241) and (367) are nonvacuous, as (279) requires. -/
theorem attested_nonvacuous :
    ∀ p ∈ [LanguageProbeConfig.hindi.aMove, LanguageProbeConfig.hindi.phi,
      LanguageProbeConfig.hindi.wh, LanguageProbeConfig.hindi.ābar,
      LanguageProbeConfig.english.aMove, LanguageProbeConfig.english.wh, english_extr,
      germanScr, germanRel, germanWh, germanTop], p.isVacuous = false := by
  decide

/-- (307): the default horizon of a probe on X⁰ is X, the strictest choice that is not vacuous;
the Hindi probes on T⁰, English extraposition and German scrambling take it. -/
theorem default_horizon_strictest :
    (∀ X ∈ [Cat.T, .C, .Force], (Probe.Profile.defaultHorizon X).isVacuous = false) ∧
      LanguageProbeConfig.hindi.phi = Probe.Profile.defaultHorizon .T ∧
      english_extr = Probe.Profile.defaultHorizon .T ∧
      germanScr = Probe.Profile.defaultHorizon .T :=
  ⟨by decide, rfl, rfl, rfl⟩

/-! ### Variation and improper movement (Sections 3.6, 3.4.3, 6.2) -/

/-- (300): the A-movement settings, Lubukusu without a horizon, English with C and Hindi with T,
form an entailment chain over the clauses of an extended projection, whose labels contain T
whenever they contain C. -/
theorem a_movement_chain (L : List Cat) (hL : Cat.C ∈ L → Cat.T ∈ L) :
    (LanguageProbeConfig.hindi.aMove.transparentToLabel L = true →
        LanguageProbeConfig.english.aMove.transparentToLabel L = true) ∧
      (LanguageProbeConfig.english.aMove.transparentToLabel L = true →
        lubukusuAProbe.transparentToLabel L = true) := by
  simp only [LanguageProbeConfig.hindi, LanguageProbeConfig.english, lubukusuAProbe,
    Probe.Profile.transparentToLabel, Bool.not_eq_true', List.any_eq_false, beq_iff_eq]
  exact ⟨λ h c hc hcC => h _ (hL (hcC ▸ hc)) rfl, λ _ => trivial⟩

/-- Sections 3.4.3 and 6.2: the Ban on Improper Movement and the smuggling and remnant-movement
restrictions are one fact about domains rather than items: a CP is opaque to every A-probe whose
horizon it inherits, edge included, so nothing Ā-movement has placed in or under a CP is
reachable by A-movement, while Ā-probes with no horizon or one outside the label are unaffected. -/
theorem improper_movement (h : Cat) (hh : h ∈ ClauseSpine.cP.projectedHeads) :
    (⟨.T, some h⟩ : Probe.Profile).transparentToLabel ClauseSpine.cP.projectedHeads = false := by
  simp only [Probe.Profile.transparentToLabel, Bool.not_eq_false', List.any_eq_true, beq_iff_eq]
  exact ⟨h, hh, rfl⟩

/-- The three A-probes of (300) with a horizon are blocked by CP, and the Hindi and English
Ā-probes are not. -/
theorem improper_movement_attested :
    (∀ p ∈ [LanguageProbeConfig.hindi.aMove, LanguageProbeConfig.english.aMove, germanScr],
        p.transparentToLabel ClauseSpine.cP.projectedHeads = false) ∧
      ∀ p ∈ [LanguageProbeConfig.hindi.ābar, LanguageProbeConfig.english.wh],
        p.transparentToLabel ClauseSpine.cP.projectedHeads = true := by
  decide

end Keine2020
