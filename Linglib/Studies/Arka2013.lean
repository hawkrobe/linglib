/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Fragments.Indonesian.TAM
import Linglib.Fragments.Indonesian.Complementation
import Linglib.Semantics.Tense.Reichenbach
import Linglib.Studies.Kiparsky2002
import Linglib.Data.Examples.Arka2013

/-!
# Arka 2013: the typology and syntax of TAM in Indonesian

Indonesian has no grammatical TAM: there is no obligatory morphosyntactic opposition, a bare
verb is anchored in time by context or by an optional adjunct, and the perfect auxiliary
*sudah/telah* expresses only that the event precedes the reference time, which is free to sit
at the moment of speech or in the past — so Klein's puzzle about the English present perfect,
which pins the reference time to the present, does not arise. The language nonetheless
shows finiteness: the TAM auxiliaries occupy I, a finite clause projects IP whether or not an
auxiliary is present, and truncated or controlled complements, resultatives, and *sambil*
adjuncts are bare VPs that admit none of them, while nominal predicates project no I at all.
The clitic *=nya* nominalises verbs of saying and feeling, modals, and evidential roots; a
nominalisation carries a default past temporal axis that an adjunct like *nanti* cancels, a
nominalised modal reports a past or present state of affairs counterfactually where the bare
modal points to a future one, and the copula *adalah* and the negator *bukan* show that these
structures are equational.

## Main definitions

* `Annotation`: the paper's E/R/S annotations, with `Annotation.frame` the Reichenbach
  frame they describe.
* `Aux`, `Aux.frame`: the auxiliaries the paper analyses and the frame relation each
  expresses; `englishPresentPerfect` the English contrast.
* `projectsI`: a clause projects I exactly when its complement coding is not reduced; the
  selecting verbs and subordinators are fragment entries.

## References

* [arka-2013]
* [klein-1992] — the present perfect puzzle
* [kibort-2009] — languages grammaticalise different E, R, S configurations
* [sneddon-1996] — the marker inventory in the fragment
-/

namespace Arka2013

open Tense Indonesian Data.Examples

/-! ### Tense theory and the status of Indonesian TAM (§2) -/

/-- An E/R/S annotation as the paper prints it — `E-R<S`, `S<E-R`, `E<S,R` — read as the
temporal group each primitive falls in, later groups later in time. -/
structure Annotation where
  e : ℕ
  r : ℕ
  s : ℕ
  deriving DecidableEq, Repr

/-- Read an annotation: `<` opens a later group, `-` and `,` keep the current one. -/
def Annotation.parse? (str : String) : Option Annotation :=
  let step : Option (Annotation × ℕ) → Char → Option (Annotation × ℕ)
    | some (a, g), 'E' => some ({ a with e := g }, g)
    | some (a, g), 'R' => some ({ a with r := g }, g)
    | some (a, g), 'S' => some ({ a with s := g }, g)
    | some (a, g), '<' => some (a, g + 1)
    | some (a, g), '-' => some (a, g)
    | some (a, g), ',' => some (a, g)
    | some (a, g), ' ' => some (a, g)
    | _, _ => none
  (str.toList.foldl step (some (⟨0, 0, 0⟩, 0))).map (·.1)

/-- The frame an annotation describes, with the perspective at speech time. -/
def Annotation.frame (a : Annotation) : ReichenbachFrame ℤ := ⟨a.s, a.s, a.r, a.e⟩

/-- The auxiliaries the paper assigns a frame relation: *akan* future, *sedang* progressive,
*sudah/telah* perfect. -/
inductive Aux
  | akan
  | sedang
  | sudah
  deriving DecidableEq, Repr, Fintype

/-- The auxiliary a fragment marker realises, by its meaning. -/
def Aux.ofMarker (m : TemporalMarker) : Option Aux :=
  match m.meaning with
  | .future => some .akan
  | .inProgress => some .sedang
  | .occurred => some .sudah
  | _ => none

/-- The auxiliary written as a form, through the fragment's inventory. -/
def Aux.ofForm (s : String) : Option Aux :=
  (temporalMarkers.find? (·.form = s)).bind Aux.ofMarker

/-- The frame relation each auxiliary expresses: *akan* S < E-R, *sedang* E = R, *sudah* E < R
with R free. -/
def Aux.frame {T : Type*} [LinearOrder T] : Aux → ReichenbachFrame T → Prop
  | .akan, f => f.isFuture ∧ f.isPerfective
  | .sedang, f => f.isPerfective
  | .sudah, f => f.isPerfect

instance {T : Type*} [LinearOrder T] (a : Aux) (f : ReichenbachFrame T) :
    Decidable (a.frame f) := by
  cases a <;> dsimp only [Aux.frame] <;> infer_instance

/-- *telah* and *sudah* realise the same auxiliary. -/
theorem telah_sudah : Aux.ofMarker telah = Aux.ofMarker sudah := rfl

/-- Every annotated sentence with an auxiliary satisfies the auxiliary's frame relation. -/
theorem rows_annotations :
    ∀ r ∈ Examples.all, ∀ a ∈ (r.feature? "aux" >>= Aux.ofForm).toList,
      ∀ ann ∈ (r.feature? "frame" >>= Annotation.parse?).toList, a.frame ann.frame := by
  decide +kernel

/-- The annotations of the *sudah* sentences (5). -/
def sudahAnnotations : List Annotation :=
  Examples.all.filterMap fun r => do
    let a ← r.feature? "aux" >>= Aux.ofForm
    guard (a = .sudah)
    r.feature? "frame" >>= Annotation.parse?

/-- R is free under *sudah*: it sits at speech time in one annotation and before it in
another, the event preceding it in both. -/
theorem sudah_reference_free :
    (∃ a ∈ sudahAnnotations, a.r = a.s) ∧ (∃ a ∈ sudahAnnotations, a.r < a.s) ∧
      ∀ a ∈ sudahAnnotations, a.e < a.r := by
  decide +kernel

/-- The English present perfect grammaticalises E < R together with R at the deictic
centre. -/
def englishPresentPerfect {T : Type*} [LinearOrder T] (f : ReichenbachFrame T) : Prop :=
  f.isPerfect ∧ f.isPresent

instance {T : Type*} [LinearOrder T] (f : ReichenbachFrame T) :
    Decidable (englishPresentPerfect f) := by
  unfold englishPresentPerfect; infer_instance

/-- Klein's puzzle and its Indonesian dissolution: with a past reference time the English
present perfect is contradictory (`Kiparsky2002.present_perfect_puzzle`), while *sudah*
under the same reference time is satisfiable — (5b) *Dia sudah pergi kemarin*. -/
theorem klein_puzzle_dissolved :
    (∀ f : ReichenbachFrame ℤ, englishPresentPerfect f → f.isPast → False) ∧
      ∃ f : ReichenbachFrame ℤ, Aux.sudah.frame f ∧ f.isPast :=
  ⟨fun f hpp hpast => Kiparsky2002.present_perfect_puzzle f hpp.2
      ((ReichenbachFrame.isPast_def f).mp hpast),
    ⟨⟨2, 2, 1, 0⟩, by decide⟩⟩

/-- The English present perfect strictly strengthens *sudah*. -/
theorem english_pp_strictly_stronger {T : Type*} [LinearOrder T] :
    (∀ f : ReichenbachFrame T, englishPresentPerfect f → Aux.sudah.frame f) ∧
      ∃ f : ReichenbachFrame ℤ, Aux.sudah.frame f ∧ ¬ englishPresentPerfect f :=
  ⟨fun _ h => h.1, ⟨⟨2, 2, 1, 0⟩, by decide⟩⟩

/-! ### Finiteness (§3) -/

/-- The verb selecting a row's complement clause, from the fragment. -/
def matrixVerb : String → Option Verb
  | "ingin" => some Complementation.ingin
  | "belajar" => some Complementation.belajar
  | "menyuruh" => some Complementation.menyuruh
  | "mendorong" => some Complementation.mendorong
  | "tahu" => some Complementation.tahu
  | _ => none

/-- The subordinator typing a row's dependent clause, from the fragment. -/
def subordinator : String → Option Complementizer
  | "bahwa" => some Complementation.bahwa
  | "agar" => some Complementation.agar
  | _ => none

/-- A clause projects I — the position of the TAM auxiliaries (16) — exactly when its coding is
not reduced: a full clause anchors its own temporal axis, a reduced complement is a bare VP
(17). -/
def projectsI (c : Complement.Coding) : Bool := !c.isReduced

/-- The coding of the clause a verb's citation frame selects. -/
def complementCoding (v : Verb) : Option Complement.Coding :=
  v.frames.head?.bind fun fr => fr.codings.head?

/-- A TAM auxiliary is acceptable in a dependent clause exactly when the clause its selector
takes projects I; root clauses do, and a nominal predicate projects no verbal structure. -/
theorem rows_finiteness :
    ∀ r ∈ Examples.all,
      (∀ v ∈ (r.feature? "matrix" >>= matrixVerb).toList, ∀ c ∈ (complementCoding v).toList,
        (projectsI c = true ↔ r.feature? "withAux" = some "acceptable")) ∧
      (∀ s ∈ (r.feature? "subordinator" >>= subordinator).toList, ∀ c ∈ s.coding.toList,
        (projectsI c = true ↔ r.feature? "withAux" = some "acceptable")) ∧
      (r.feature? "clause" = some "root" → r.feature? "withAux" = some "acceptable") ∧
      (r.feature? "predicate" = some "nominal" →
        ∀ j ∈ (r.feature? "withAux").toList, j ≠ "acceptable") := by
  decide +kernel

/-! ### Morphosemantic TAM: *=nya* nominalisation (§4) -/

/-- The default past axis of a nominalisation is cancelled exactly by a future adjunct
(34)–(36). -/
theorem rows_nya_default_past :
    ∀ r ∈ Examples.all, r.feature? "nominalised" = some "true" →
      ∀ axis ∈ (r.feature? "axis").toList,
        (axis = "future" ↔ r.feature? "adjunct" = some "nanti") := by
  decide +kernel

/-- A bare modal evaluates a future state of affairs; its nominalisation a past or present
one (37)–(39). -/
theorem rows_modal_nominalisation :
    ∀ r ∈ Examples.all, ∀ soa ∈ (r.feature? "soa").toList,
      (soa = "future" ↔ r.feature? "nominalised" = some "false") := by
  decide +kernel

/-- The copula *adalah* and the negator *bukan* take nominal predicates only, the
nominalisations among them (44)–(48). -/
theorem rows_equational :
    ∀ r ∈ Examples.all, ∀ key ∈ ["adalah", "bukan"], ∀ j ∈ (r.feature? key).toList,
      (j = "acceptable" ↔ r.feature? "predicate" = some "nominal") := by
  decide +kernel

end Arka2013
