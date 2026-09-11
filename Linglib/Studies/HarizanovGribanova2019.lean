import Linglib.Core.Data.List.Sublist

/-!
# Harizanov and Gribanova (2019): Whither head movement?

This file formalizes the postsyntactic amalgamation of [harizanov-gribanova-2019], the
word-forming half of what head movement used to do, split off from genuinely syntactic movement
of heads. A head of the extended projection carries a morphological selection feature `[m]`:
`[m:+]` Raises it into the next head up and `[m:−]` Lowers it into the nearest head below, the
derivation proceeds bottom-up, the target's feature projects to the complex head, and a demanded
operation with no target does not converge (their (37)–(40)). `amalgamateSpine` runs this
derivation on a spine given lowest head first, and `flatMap_members_amalgamateSpine` shows that
the complex heads it forms partition the spine into contiguous stretches in the order of
syntactic composition: the Head Movement Constraint, the mirror generalization and the ban on
excorporation are consequences, and amalgamation creates no new occurrence of any head. The four
settings of the `[m]` features in their (41) put one and the same verbal complex at T (French),
Neg (Russian), v (English) and V (Danish).

Syntactic head movement is Internal Merge of the head with the root; it precedes amalgamation,
and a complex head formed at one occurrence of a moved head belongs to every occurrence (their
§4.1). `moveToRoot` adds the high occurrence, `amalgamateSpine_moveToRoot` shows the derivation
below it unaffected, and `amalgamatedInto` reads off what a moved head carries along: V into the
moved T in German verb second, T and v into the moved V in Danish, the whole verbal complex into
the moved Neg in Russian polarity-focus VSO, and, in their (68), a complex head that skips two
inert heads, which `mem_of_mem_amalgamateSpine_of_nodup` shows amalgamation alone never produces.

## Implementation notes

The spine is a list of heads, lowest first, each with its `[m]` feature; specifiers and adjuncts
are islands for amalgamation and are omitted. A head that has moved syntactically occupies two
positions of the spine, so the spine repeats a head exactly when syntactic head movement has
applied; the paper's multidominance is this repetition. Chain Reduction, which pronounces the
highest occurrence in the languages discussed, stays in prose. The paper's examples, with the
Bulgarian long head movement of their (29)–(33), which crosses auxiliaries that remain separate
words, clause boundaries and islands, are the rows of `Data/Examples/HarizanovGribanova2019.json`;
by `mem_of_mem_amalgamateSpine_of_nodup` a participle pronounced above two auxiliaries by
amalgamation would form one complex head with them, so its displacement is syntactic, which is
the paper's argument. The English complex of their (41) is built without a Neg head, as the
parenthesis there indicates.

## TODO

* Chain Reduction, and the Hebrew bare-infinitive fronting of their (67), where the moved V
  amalgamates outbound into T and both of its occurrences are pronounced.

## References

* [harizanov-gribanova-2019]
* [embick-noyer-2001]
* [travis-1984]
-/

namespace HarizanovGribanova2019

/-- The direction of amalgamation a head's `[m]` feature demands: `[m:+]` Raises the head into the
next head up, `[m:−]` Lowers it into the nearest head below. -/
inductive Direction
  | raising
  | lowering
  deriving DecidableEq, Repr

variable {H : Type*}

/-- A complex head in the course of the postsyntactic derivation: the head whose position it
occupies, the heads it contains, lowest first, and the `[m]` feature projected from its site. -/
structure Amalgam (H : Type*) where
  site : H
  members : List H
  m : Option Direction
  deriving DecidableEq, Repr

/-- A lexical head with its `[m]` specification, before any amalgamation. -/
def Amalgam.single (h : H) (m : Option Direction) : Amalgam H := ⟨h, [h], m⟩

/-- Bottom-up amalgamation: `below` lists the complex heads already formed, nearest first,
`pending` the heads that have Raised and await the next head up, and `above` the heads still to
be considered, lowest first. A Raising head joins the next head up, whose `[m]` feature the
complex keeps, a Lowering head the nearest complex head below, and a demanded operation with no
target is a nonconvergent derivation. -/
def amalgamate : List (Amalgam H) → List H → List (Amalgam H) → Option (List (Amalgam H))
  | below, [], [] => some below
  | _, _ :: _, [] => none
  | below, pending, a :: above =>
    match a.m, below with
    | none, below => amalgamate ({ a with members := pending ++ a.members } :: below) [] above
    | some .raising, below => amalgamate below (pending ++ a.members) above
    | some .lowering, [] => none
    | some .lowering, b :: below =>
      amalgamate ({ b with members := b.members ++ pending ++ a.members } :: below) [] above

/-- The complex heads amalgamation forms on a spine given lowest head first, lowest first, or
`none` when the postsyntactic derivation does not converge. -/
def amalgamateSpine (spine : List (Amalgam H)) : Option (List (Amalgam H)) :=
  (amalgamate [] [] spine).map List.reverse

/-- Syntactic head movement of `y` to the root, which precedes amalgamation: a second occurrence
of `y` at the top of the spine, with no `[m]` feature of its own. -/
def moveToRoot (spine : List (Amalgam H)) (y : H) : List (Amalgam H) :=
  spine ++ [Amalgam.single y none]

/-- The heads amalgamated into the syntactic object `y` at any of its occurrences: amalgamation
into one occurrence of a moved head is reflected in all of them. -/
def amalgamatedInto [DecidableEq H] (out : List (Amalgam H)) (y : H) : List H :=
  ((out.filter (·.site = y)).flatMap Amalgam.members).filter (· ≠ y)

theorem flatMap_members_amalgamate {below : List (Amalgam H)} {pending : List H}
    {above out : List (Amalgam H)} (h : amalgamate below pending above = some out) :
    out.reverse.flatMap Amalgam.members =
      below.reverse.flatMap Amalgam.members ++ pending ++ above.flatMap Amalgam.members := by
  induction above generalizing below pending out with
  | nil => cases pending <;> simp_all [amalgamate]
  | cons a above ih =>
    rcases ha : a.m with _ | _ | _ <;> cases below <;> simp only [amalgamate, ha] at h <;>
      first | simpa [List.append_assoc] using ih h | simp at h

/-- The complex heads partition the spine in the order of syntactic composition: the mirror
generalization, and no head gains or loses an occurrence. -/
theorem flatMap_members_amalgamateSpine {spine out : List (Amalgam H)}
    (h : amalgamateSpine spine = some out) :
    out.flatMap Amalgam.members = spine.flatMap Amalgam.members := by
  obtain ⟨out', h', rfl⟩ := Option.map_eq_some_iff.mp h
  simpa using flatMap_members_amalgamate h'

/-- Each complex head is a contiguous stretch of the spine: the Head Movement Constraint and the
ban on excorporation. -/
theorem members_infix_of_mem_amalgamateSpine {spine out : List (Amalgam H)}
    (h : amalgamateSpine spine = some out) {a : Amalgam H} (ha : a ∈ out) :
    a.members <:+: spine.flatMap Amalgam.members :=
  flatMap_members_amalgamateSpine h ▸ List.infix_of_mem_flatten (List.mem_map_of_mem ha)

/-- Without syntactic movement no head is skipped: a head of the spine lying between two members
of a complex head is a member of it, so morphological growth that skips heads betrays a second
occurrence of the moved head (their fifth prediction, §4.2). -/
theorem mem_of_mem_amalgamateSpine_of_nodup [DecidableEq H] {spine out : List (Amalgam H)}
    (h : amalgamateSpine spine = some out) (hnd : (spine.flatMap Amalgam.members).Nodup)
    {a : Amalgam H} (ha : a ∈ out) {x y z : H} (hx : x ∈ a.members) (hy : y ∈ a.members)
    (hz : z ∈ spine.flatMap Amalgam.members)
    (hxz : (spine.flatMap Amalgam.members).idxOf x ≤ (spine.flatMap Amalgam.members).idxOf z)
    (hzy : (spine.flatMap Amalgam.members).idxOf z ≤ (spine.flatMap Amalgam.members).idxOf y) :
    z ∈ a.members :=
  (members_infix_of_mem_amalgamateSpine h ha).mem_of_idxOf_le_of_le hnd hx hy hz hxz hzy

theorem amalgamate_append_single_none {below : List (Amalgam H)} {pending : List H}
    {above out : List (Amalgam H)} (y : H) (h : amalgamate below pending above = some out) :
    amalgamate below pending (above ++ [Amalgam.single y none]) =
      some (Amalgam.single y none :: out) := by
  induction above generalizing below pending out with
  | nil => cases pending <;> simp_all [amalgamate, Amalgam.single]
  | cons a above ih =>
    rcases ha : a.m with _ | _ | _ <;> cases below <;>
      simp only [List.cons_append, amalgamate, ha] at h ⊢ <;> first | exact ih h | simp at h

/-- Syntactic head movement precedes amalgamation and leaves the derivation below the root
untouched: the moved head's high occurrence is one more complex head, containing itself alone. -/
theorem amalgamateSpine_moveToRoot {spine out : List (Amalgam H)} (y : H)
    (h : amalgamateSpine spine = some out) :
    amalgamateSpine (moveToRoot spine y) = some (out ++ [Amalgam.single y none]) := by
  obtain ⟨out', h', rfl⟩ := Option.map_eq_some_iff.mp h
  simp [amalgamateSpine, moveToRoot, amalgamate_append_single_none y h']

/-! ### The clausal spine (their §3–§4) -/

/-- The heads of the clausal spine in the paper's derivations. -/
inductive ClausalHead
  | V
  | v
  | Asp
  | Neg
  | T
  | C
  deriving DecidableEq, Repr

open ClausalHead Amalgam

/-- Their (43): the Russian spine, V, v and Asp Raising and T Lowering. -/
def russian : List (Amalgam ClausalHead) :=
  [single V (some .raising), single v (some .raising), single Asp (some .raising), single Neg none,
    single T (some .lowering), single C none]

/-- Their (48): the Danish spine, v and T Lowering. -/
def danish : List (Amalgam ClausalHead) :=
  [single V none, single v (some .lowering), single T (some .lowering), single C none]

/-- Their (50): the French spine, V, v and Neg Raising; *pas* in Spec,NegP is not on the spine. -/
def french : List (Amalgam ClausalHead) :=
  [single V (some .raising), single v (some .raising), single Neg (some .raising), single T none,
    single C none]

/-- Their (41): the English spine, V Raising and T Lowering. -/
def english : List (Amalgam ClausalHead) :=
  [single V (some .raising), single v none, single T (some .lowering), single C none]

/-- Their (44)–(47): the Russian verbal complex is pronounced at Neg, above V but below T. -/
theorem russian_amalgamateSpine :
    amalgamateSpine russian = some [⟨Neg, [V, v, Asp, Neg, T], none⟩, single C none] := rfl

/-- Their (49): the Danish verbal complex is pronounced at V. -/
theorem danish_amalgamateSpine :
    amalgamateSpine danish = some [⟨V, [V, v, T], none⟩, single C none] := rfl

/-- Their (51): the French verbal complex is pronounced at T. -/
theorem french_amalgamateSpine :
    amalgamateSpine french = some [⟨T, [V, v, Neg, T], none⟩, single C none] := rfl

/-- Their (41): the English verbal complex is pronounced at v. -/
theorem english_amalgamateSpine :
    amalgamateSpine english = some [⟨v, [V, v, T], none⟩, single C none] := rfl

/-- Their (39a) with `Y` specified `[m:−]`: once V has Raised into v, the complex has no head
below to Lower into, and the derivation does not converge. -/
theorem amalgamateSpine_lowering_bottom :
    amalgamateSpine [single V (some .raising), single v (some .lowering), single T none] = none :=
  rfl

/-! ### Verb second and polarity focus (their §4.1) -/

/-- Their (59a): the German embedded clause, V Raising into T. -/
def germanEmbedded : List (Amalgam ClausalHead) := [single V (some .raising), single T none]

/-- Their (61a): the Danish embedded clause, T Lowering into v and v into V. -/
def danishEmbedded : List (Amalgam ClausalHead) :=
  [single V none, single v (some .lowering), single T (some .lowering)]

/-- Their (63): Russian SVO, the verbal complex amalgamated at Neg below the subject in Spec,TP. -/
def russianSVO : List (Amalgam ClausalHead) :=
  [single V (some .raising), single v (some .raising), single Asp (some .raising), single Neg none,
    single T (some .lowering)]

theorem germanEmbedded_amalgamateSpine :
    amalgamateSpine germanEmbedded = some [⟨T, [V, T], none⟩] := rfl

theorem danishEmbedded_amalgamateSpine :
    amalgamateSpine danishEmbedded = some [⟨V, [V, v, T], none⟩] := rfl

theorem russianSVO_amalgamateSpine :
    amalgamateSpine russianSVO = some [⟨Neg, [V, v, Asp, Neg, T], none⟩] := rfl

/-- Their (59b–c): in the German root clause T moves to the C domain and V Raises into its low
occurrence, so the complex T pronounced at the root carries V. -/
theorem german_root :
    amalgamateSpine (moveToRoot germanEmbedded T) =
      some [⟨T, [V, T], none⟩, single T none] :=
  amalgamateSpine_moveToRoot T germanEmbedded_amalgamateSpine

/-- Their (62): in the Danish root clause V moves to the C domain and T and v Lower into its low
occurrence, so the complex V pronounced at the root carries T and v. -/
theorem danish_root :
    amalgamateSpine (moveToRoot danishEmbedded V) =
      some [⟨V, [V, v, T], none⟩, single V none] :=
  amalgamateSpine_moveToRoot V danishEmbedded_amalgamateSpine

/-- Their (65): Russian VSO under polarity focus, Neg moving to Pol and the verbal complex
amalgamating into its low occurrence, so the whole complex is dragged along to Pol. -/
theorem russianVSO :
    amalgamateSpine (moveToRoot russianSVO .Neg) =
      some [⟨.Neg, [V, v, Asp, .Neg, T], none⟩, single .Neg none] :=
  amalgamateSpine_moveToRoot .Neg russianSVO_amalgamateSpine

/-- German and Danish verb second differ in the head that moves and in the `[m]` features, and
agree on the surface: what reaches the root is a T–V complex either way. -/
theorem amalgamatedInto_german_danish :
    amalgamatedInto [⟨T, [V, T], none⟩, single T none] T = [V] ∧
      amalgamatedInto [⟨V, [V, v, T], none⟩, single V none] V = [v, T] := ⟨rfl, rfl⟩

/-- Their (68), with H1 to H6 as `0` to `5`: the moved H1 occupies the bottom and the top of the
spine, H6 Lowers into its low occurrence, H3 and H2 Raise into its high one, and the complex head
H1 acquires H6, H3 and H2 while skipping the inert H4 and H5. -/
theorem skipping_68 :
    amalgamatedInto ((amalgamateSpine [single (0 : Fin 6) none, single 5 (some .lowering),
      single 4 none, single 3 none, single 2 (some .raising), single 1 (some .raising),
      single 0 none]).getD []) 0 = [5, 2, 1] := rfl

end HarizanovGribanova2019
