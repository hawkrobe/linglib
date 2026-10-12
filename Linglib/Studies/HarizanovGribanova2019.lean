module

public import Linglib.Core.Data.List.Sublist
public import Linglib.Data.Examples.HarizanovGribanova2019
public import Mathlib.Algebra.Free
public import Mathlib.Algebra.FreeMonoid.Basic

/-!
# Harizanov and Gribanova (2019): Whither head movement?

Harizanov and Gribanova divide the work of head movement between two operations. Words are
formed by postsyntactic amalgamation: a head whose feature is [M:+] Raises into the next head
up, a head whose feature is [M:−] Lowers into the nearest head below, and the result is a
head-adjunction structure in the position of the target. Displacement is syntactic movement of a
head to the root, which comes first and forms no word. How complex a verb is and where it is
pronounced therefore vary independently, the same verbal complex surfacing in T in French, in
Neg in Russian and in V in Danish.

## Main statements

* `flatMap_members_amalgamateSpine`: the complex heads partition the spine into contiguous
  stretches in the order of syntactic composition, which gives the Head Movement Constraint,
  the mirror generalization and the ban on excorporation.
* `mem_of_mem_amalgamateSpine_of_nodup`: amalgamation alone skips no head, so a complex head
  that skips one shows that a head has moved in the syntax.
* `verb_placement`: the finite verbs of French, Danish and Russian precede a low adverb,
  negation or a floating quantifier exactly where their complex head is pronounced in T or
  above.

## Implementation notes

* A spine lists the heads of an extended projection, lowest first, each with its [M] feature;
  specifiers and adjuncts, which are islands for amalgamation, are left out. A head that has
  moved in the syntax occupies two positions of the spine, the paper's multidominance.
* A complex head is an element of the free magma over the heads, each product listing the lower
  constituent first. The paper's adjunction structures are unordered.
* Chain Reduction pronounces the highest occurrence, as in the paper's German, Danish and
  Russian derivations.
* The paper also places the English verbal complex in v, but takes T to join the English verb
  by an operation other than amalgamation, one that an intervening specifier blocks. No English
  derivation is given here.

## TODO

* The pronunciation of both occurrences of the verb in Hebrew bare-infinitive fronting.
* French nonfinite clauses, whose verbs stay low; the paper gives their [M] features no
  derivation.

## References

* [harizanov-gribanova-2019]
* [embick-noyer-2001]
* [travis-1984]
-/

@[expose] public section

namespace HarizanovGribanova2019

open FreeMagma

/-! ### Amalgamation -/

/-- The direction of amalgamation that the [M] feature of a head demands. A head with [M:+]
Raises into the next head up and a head with [M:−] Lowers into the nearest head below. -/
inductive Direction
  | raising | lowering
  deriving DecidableEq, Repr

variable {H : Type*}

/-- A complex head in the course of the postsyntactic derivation. -/
structure Amalgam (H : Type*) where
  /-- The head whose position the complex head occupies. -/
  site : H
  /-- The head-adjunction structure, each product listing the lower constituent first. -/
  complex : FreeMagma H
  /-- The [M] feature projected from the site. -/
  m : Option Direction
  deriving DecidableEq, Repr

namespace Amalgam

/-- A lexical head with its [M] feature, before any amalgamation. -/
def single (h : H) (m : Option Direction) : Amalgam H := ⟨h, of h, m⟩

/-- The heads that a complex head contains, lowest first. -/
def members (a : Amalgam H) : List H := (FreeMagma.lift FreeMonoid.of a.complex).toList

end Amalgam

/-- Bottom-up amalgamation. `below` lists the complex heads already formed, nearest first,
`pending` is the complex head that has Raised and awaits the next head up, and `above` lists the
heads still to be considered, lowest first. A Raising head adjoins to the next head up, whose
[M] feature the complex keeps, a Lowering head adjoins to the nearest complex head below, and a
demanded operation with no target is a derivation that does not converge. -/
def amalgamate : List (Amalgam H) → Option (FreeMagma H) → List (Amalgam H) →
    Option (List (Amalgam H))
  | below, none, [] => some below
  | _, some _, [] => none
  | below, pending, a :: above =>
    let complex := pending.elim a.complex (· * a.complex)
    match a.m, below with
    | none, below => amalgamate ({ a with complex } :: below) none above
    | some .raising, below => amalgamate below (some complex) above
    | some .lowering, [] => none
    | some .lowering, b :: below =>
      amalgamate ({ b with complex := b.complex * complex } :: below) none above

/-- The complex heads that amalgamation forms on a spine, lowest first, or `none` when the
postsyntactic derivation does not converge. -/
def amalgamateSpine (spine : List (Amalgam H)) : Option (List (Amalgam H)) :=
  (amalgamate [] none spine).map List.reverse

/-- Syntactic movement of the head `y` to the root, which precedes amalgamation, gives `y` a
second occurrence at the top of the spine. -/
def moveToRoot (spine : List (Amalgam H)) (y : H) : List (Amalgam H) :=
  spine ++ [Amalgam.single y none]

private theorem flatMap_members_amalgamate {below : List (Amalgam H)}
    {pending : Option (FreeMagma H)} {above out : List (Amalgam H)}
    (h : amalgamate below pending above = some out) :
    out.reverse.flatMap Amalgam.members =
      below.reverse.flatMap Amalgam.members ++
        pending.elim [] (fun x ↦ (FreeMagma.lift FreeMonoid.of x).toList) ++
        above.flatMap Amalgam.members := by
  induction above generalizing below pending out with
  | nil => cases pending <;> simp_all [amalgamate]
  | cons a above ih =>
    rcases ha : a.m with _ | _ | _ <;> cases below <;> cases pending <;>
      simp only [amalgamate, ha] at h <;>
      first | simpa [List.append_assoc, Amalgam.members] using ih h | simp at h

/-- The complex heads partition the spine in the order of syntactic composition: the affixes of
a complex head mirror that order, and no head gains or loses an occurrence. -/
theorem flatMap_members_amalgamateSpine {spine out : List (Amalgam H)}
    (h : amalgamateSpine spine = some out) :
    out.flatMap Amalgam.members = spine.flatMap Amalgam.members := by
  obtain ⟨out', h', rfl⟩ := Option.map_eq_some_iff.mp h
  simpa using flatMap_members_amalgamate h'

/-- Each complex head is a contiguous stretch of the spine, which is the Head Movement Constraint
and the ban on excorporation. -/
theorem members_infix_of_mem_amalgamateSpine {spine out : List (Amalgam H)}
    (h : amalgamateSpine spine = some out) {a : Amalgam H} (ha : a ∈ out) :
    a.members <:+: spine.flatMap Amalgam.members :=
  flatMap_members_amalgamateSpine h ▸ List.infix_of_mem_flatten (List.mem_map_of_mem ha)

/-- Without syntactic movement no head is skipped. A head of the spine that lies between two
members of a complex head is a member of it, so a complex head that skips a head shows that one
of its heads has a second occurrence. -/
theorem mem_of_mem_amalgamateSpine_of_nodup [DecidableEq H] {spine out : List (Amalgam H)}
    (h : amalgamateSpine spine = some out) (hnd : (spine.flatMap Amalgam.members).Nodup)
    {a : Amalgam H} (ha : a ∈ out) {x y z : H} (hx : x ∈ a.members) (hy : y ∈ a.members)
    (hz : z ∈ spine.flatMap Amalgam.members)
    (hxz : (spine.flatMap Amalgam.members).idxOf x ≤ (spine.flatMap Amalgam.members).idxOf z)
    (hzy : (spine.flatMap Amalgam.members).idxOf z ≤ (spine.flatMap Amalgam.members).idxOf y) :
    z ∈ a.members :=
  (members_infix_of_mem_amalgamateSpine h ha).mem_of_idxOf_le_of_le hnd hx hy hz hxz hzy

private theorem amalgamate_append_single_none {below : List (Amalgam H)}
    {pending : Option (FreeMagma H)} {above out : List (Amalgam H)} (y : H)
    (h : amalgamate below pending above = some out) :
    amalgamate below pending (above ++ [Amalgam.single y none]) =
      some (Amalgam.single y none :: out) := by
  induction above generalizing below pending out with
  | nil => cases pending <;> simp_all [amalgamate, Amalgam.single]
  | cons a above ih =>
    rcases ha : a.m with _ | _ | _ <;> cases below <;>
      simp only [List.cons_append, amalgamate, ha] at h ⊢ <;> first | exact ih h | simp at h

/-- Syntactic movement leaves the derivation below the root as it was. The high occurrence of
the moved head is one more complex head, containing that head alone. -/
theorem amalgamateSpine_moveToRoot {spine out : List (Amalgam H)} (y : H)
    (h : amalgamateSpine spine = some out) :
    amalgamateSpine (moveToRoot spine y) = some (out ++ [Amalgam.single y none]) := by
  obtain ⟨out', h', rfl⟩ := Option.map_eq_some_iff.mp h
  simp [amalgamateSpine, moveToRoot, amalgamate_append_single_none y h']

open Amalgam

/-- A head that Raises and a head that Lowers meet in the head between them. -/
theorem raising_and_lowering (x y z : H) :
    amalgamateSpine [single z (some .raising), single y none, single x (some .lowering)] =
      some [⟨y, of z * of y * of x, none⟩] :=
  rfl

/-- A head Lowers past the position of a head that has itself Lowered, into a head that is not
the head of its complement. -/
theorem lowering_twice (x y z : H) :
    amalgamateSpine [single z none, single y (some .lowering), single x (some .lowering)] =
      some [⟨z, of z * of y * of x, none⟩] :=
  rfl

/-- Once the lowest head has Raised into a Lowering head, the complex head has no head below it
to Lower into, and the derivation does not converge. -/
theorem lowering_without_target (x y z : H) :
    amalgamateSpine [single z (some .raising), single y (some .lowering), single x none] = none :=
  rfl

/-- Chain Reduction pronounces the highest occurrence of a head, and a complex head formed at
one occurrence of a moved head belongs to all of them. `PronouncedFrom spine h x` says that the
complex head containing `h` is thereby pronounced in the position of `x` or above it. -/
def PronouncedFrom [DecidableEq H] (spine : List (Amalgam H)) (h x : H) : Prop :=
  ∃ out ∈ amalgamateSpine spine, ∃ a ∈ out,
    h ∈ a.members ∧ a.site ∈ (spine.map (·.site)).dropWhile (· ≠ x)

instance [DecidableEq H] (spine : List (Amalgam H)) (h x : H) :
    Decidable (PronouncedFrom spine h x) :=
  inferInstanceAs (Decidable (∃ out ∈ amalgamateSpine spine, _))

/-! ### The clausal spine -/

/-- The heads of the clausal spine in the paper's derivations. -/
inductive ClausalHead
  | V | v | Asp | Neg | T | Top
  deriving DecidableEq, Repr

open ClausalHead

/-- The Russian clause, in which V, v and Asp Raise and T Lowers. -/
def russian : List (Amalgam ClausalHead) :=
  [single V (some .raising), single v (some .raising), single Asp (some .raising), single Neg none,
    single T (some .lowering)]

/-- The Danish clause, in which v and T Lower. -/
def danish : List (Amalgam ClausalHead) :=
  [single V none, single v (some .lowering), single T (some .lowering)]

/-- The French finite clause, in which V, v and Neg Raise. The negator *pas* is a specifier and
not on the spine. -/
def french : List (Amalgam ClausalHead) :=
  [single V (some .raising), single v (some .raising), single Neg (some .raising), single T none]

/-- The German clause, in which V Raises into T. -/
def german : List (Amalgam ClausalHead) := [single V (some .raising), single T none]

/-- The Hebrew clause with a topic, in which V Raises into T. -/
def hebrew : List (Amalgam ClausalHead) :=
  [single V (some .raising), single T none, single Top none]

/-- The Russian verbal complex is pronounced in Neg, above V and below T. -/
theorem russian_amalgamateSpine :
    amalgamateSpine russian = some [⟨.Neg, of V * of v * of Asp * of .Neg * of T, none⟩] :=
  rfl

/-- The Danish verbal complex is pronounced in V. -/
theorem danish_amalgamateSpine : amalgamateSpine danish = some [⟨V, of V * of v * of T, none⟩] :=
  rfl

/-- The French verbal complex is pronounced in T. -/
theorem french_amalgamateSpine :
    amalgamateSpine french = some [⟨T, of V * of v * of .Neg * of T, none⟩] :=
  rfl

/-! ### Syntactic movement of a head -/

/-- In a German root clause T moves to the C domain and V Raises into its low occurrence, so the
complex head T pronounced at the root contains V. -/
theorem german_root :
    amalgamateSpine (moveToRoot german T) = some [⟨T, of V * of T, none⟩, single T none] :=
  rfl

/-- In a Danish root clause V moves to the C domain and v and T Lower into its low occurrence,
so the complex head V pronounced at the root contains them. -/
theorem danish_root :
    amalgamateSpine (moveToRoot danish V) = some [⟨V, of V * of v * of T, none⟩, single V none] :=
  amalgamateSpine_moveToRoot V danish_amalgamateSpine

/-- In a Russian clause with polarity focus Neg moves to Pol and the verbal complex forms at its
low occurrence, so the whole complex is pronounced before the subject. -/
theorem russian_polarity_focus :
    amalgamateSpine (moveToRoot russian .Neg) =
      some [⟨.Neg, of V * of v * of Asp * of .Neg * of T, none⟩, single .Neg none] :=
  amalgamateSpine_moveToRoot .Neg russian_amalgamateSpine

/-- In Hebrew bare-infinitive fronting V moves to the topic position and its low occurrence
Raises into T, so the fronted occurrence is the verb alone, an infinitive, and the verb with
tense and agreement is in T. -/
theorem hebrew_fronting :
    amalgamateSpine (moveToRoot hebrew V) =
      some [⟨T, of V * of T, none⟩, single .Top none, single V none] :=
  rfl

/-- With H1 to H6 as `0` to `5`, the moved H1 occupies the bottom and the top of the spine. H6
Lowers into its low occurrence and the complex of H3 and H2 Raises into its high one, so H1 has
gained three heads across the inert H4 and H5. -/
theorem skipping :
    amalgamateSpine [single (0 : Fin 6) none, single 5 (some .lowering), single 4 none,
        single 3 none, single 2 (some .raising), single 1 (some .raising), single 0 none] =
      some [⟨0, of 0 * of 5, none⟩, single 4 none, single 3 none, ⟨0, of 2 * of 1 * of 0, none⟩] :=
  rfl

/-! ### Verb placement -/

/-- `spine? r` is the spine of the clause of `r`, a French or Russian finite clause, a Danish
embedded clause, or a Danish root clause, in which V has moved. -/
def spine? (r : Datum) : Option (List (Amalgam ClausalHead)) :=
  match r.language, r.feature? "clause" with
  | "stan1290", none => some french
  | "russ1263", none => some russian
  | "dani1285", some "embedded" => some danish
  | "dani1285", some "root" => some (moveToRoot danish V)
  | _, _ => none

/-- The canonical tests for verb movement place a finite verb before a low adverb, sentential
negation or a floating quantifier exactly when it is pronounced in T or above. The paper's
examples of French, Danish and Russian finite clauses are acceptable in exactly the order that
the position of the verbal complex predicts. -/
theorem verb_placement :
    ∀ r ∈ Examples.all, r.feature? "phenomenon" = some "finiteVerbPlacement" →
      r.feature? "diagnostic" ≠ some "coordination" →
        ∃ s ∈ spine? r, ∃ b ∈ r.parse? "verbPrecedes" [("true", true), ("false", false)],
          (r.judgment = .acceptable ↔ (b = true ↔ PronouncedFrom s V T)) := by
  decide +kernel

end HarizanovGribanova2019
