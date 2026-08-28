import Mathlib.Tactic.DeriveFintype
import Linglib.Semantics.Focus.Unalternatives
import Linglib.Studies.HartmannZimmermann2004
import Linglib.Data.Examples.AssmannEtAl2023

/-!
# Assmann, Büring, Jordanoska & Prüller 2023: morphosyntactic focus marking

In languages that mark focus with morphemes or positions, each focal marking marks exactly
one constituent as focal, which may be a phrase or the whole clause; the marked constituent may
then realize any focus within it (no projection), and among the markings that would do, the
most specific must be chosen (Blocking). A language's pattern of focus syncretism is thereby
fixed by one thing: which constituents have a marking of their own. Gùrùntùm's marking between
verb and object marks the VP and so serves verb, object and VP focus alike (a disjunctive
syncretism), while its clausal marking, blocked by the subject and VP markings, serves clausal
focus only (an exocentric focus); Buli's post-subject marking marks the clause, so subject
focus is syncretic with clausal focus; Hausa's relative form marks the subject and the absolute
form is the default, marking the clause; Wolof has markings for subject, object, VP and clause,
Aymara for subject, object and clause, Awing for nothing but the clause. Syncretic foci always
form a continuous stretch of the tree, and each focus has exactly one marking. Tangale, in the
paper's footnotes, follows Hausa in the progressive and Gùrùntùm in the perfective, which agrees
cell by cell with the reflex analysis of Hartmann and Zimmermann on which foci are overtly
marked.

## Main definitions

* `Node`: the clause skeleton, a tree under constituent containment.
* `marking`: the usable marking an inventory assigns a focus, with the inventories `guruntum`,
  `buli`, `hausa`, `wolof`, `aymara`, `awing` and their syncretism tables.
* `Exocentric`, `Disjunctive`: the two patterns projection theories cannot express.
* `tangale`, `overt_iff_marking_ne_default`: the Tangale inventories and their agreement with
  the reflex analysis.
* `rows_marking`: the paper's examples, each reading realized by the predicted marking.

## References

* [assmann-etal-2023]
* [buring-2015] — unalternative semantics
* [hartmann-zimmermann-2004] — the Tangale reflex analysis
* [schwarzschild-1999], [selkirk-1995] — projection and AvoidF
-/

namespace AssmannEtAl2023

open Data.Examples
open Focus (Usable)

/-! ### The clause skeleton -/

/-- Subject and VP within the clause; verb and object within VP. -/
inductive Node
  | s | sbj | vp | v | obj
  deriving DecidableEq, Repr, Fintype

/-- Constituent containment. -/
def Node.contained : Node → Node → Bool
  | _, .s => true
  | .v, .vp | .obj, .vp | .vp, .vp => true
  | .sbj, .sbj | .v, .v | .obj, .obj => true
  | _, _ => false

instance : PartialOrder Node where
  le a b := a.contained b = true
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide

instance : DecidableLE Node := λ _ _ => inferInstanceAs (Decidable (_ = true))

/-- The constituents containing a focus form a chain: the skeleton is a tree. -/
theorem isChain_Ici (f : Node) : IsChain (· ≤ ·) (Set.Ici f) := by
  intro x hx y hy hne
  rw [Set.mem_Ici] at hx hy
  revert f x y
  decide

/-- A word: a constituent containing no other. -/
def Node.Word (n : Node) : Prop := ∀ g, g ≤ n → g = n

instance (n : Node) : Decidable n.Word := by unfold Node.Word; infer_instance

/-! ### Markings -/

/-- The marking an inventory uses for a focus: its usable constituent. -/
def marking (inv : List Node) (f : Node) : Option Node :=
  inv.find? λ m => decide (Usable inv m f)

/-- The usable marking is the one found: on a tree there is exactly one. -/
theorem marking_eq_some {inv : List Node} {m f : Node} (h : Usable inv m f) :
    marking inv f = some m := by
  have hsome : (inv.find? λ m => decide (Usable inv m f)).isSome :=
    List.find?_isSome.2 ⟨m, h.1, decide_eq_true h⟩
  obtain ⟨m', hm'⟩ := Option.isSome_iff_exists.1 hsome
  have hp := List.find?_some hm'
  have hu : Usable inv m' f := of_decide_eq_true hp
  exact hm'.trans (congrArg some (hu.unique (isChain_Ici f) h))

/-- Gùrùntùm: *a* before the subject, *a* between verb and object, clause-final *á*. -/
def guruntum : List Node := [.sbj, .vp, .s]

/-- Buli: *(à)lē* after the subject marks the clause, *ká* before the object marks the VP,
    *kámā* after the VP marks the verb. -/
def buli : List Node := [.s, .vp, .v]

/-- Hausa: the relative form marks the subject; the absolute form is the default, marking the
    clause. -/
def hausa : List Node := [.sbj, .s]

/-- Wolof: *a* the subject, *la* with fronting the object, *da(fa)* the VP, *na* or *ngi* the
    clause. -/
def wolof : List Node := [.sbj, .obj, .vp, .s]

/-- Aymara: *-wa* on the subject, on the object, or on the verb marking the clause. -/
def aymara : List Node := [.sbj, .obj, .s]

/-- Awing: nothing but the unmarked clause. -/
def awing : List Node := [.s]

/-- Verb, object and VP focus share the VP marking; the clausal marking serves clausal focus
    only. -/
theorem marking_guruntum :
    ∀ f, marking guruntum f = some (match f with | .sbj => .sbj | .s => .s | _ => .vp) := by
  decide

/-- Subject focus is syncretic with clausal focus, object focus with VP focus. -/
theorem marking_buli :
    ∀ f, marking buli f =
      some (match f with | .s | .sbj => .s | .vp | .obj => .vp | .v => .v) := by
  decide

/-- Only subject focus has to be marked; the default serves every other focus. -/
theorem marking_hausa : ∀ f, marking hausa f = some (match f with | .sbj => .sbj | _ => .s) := by
  decide

/-- Verb and VP focus are syncretic; subject, object and clause each have their marking. -/
theorem marking_wolof :
    ∀ f, marking wolof f =
      some (match f with | .sbj => .sbj | .obj => .obj | .s => .s | _ => .vp) := by
  decide

/-- Verb, VP and clausal focus are syncretic. -/
theorem marking_aymara :
    ∀ f, marking aymara f = some (match f with | .sbj => .sbj | .obj => .obj | _ => .s) := by
  decide

/-- Anything can be the focus of the unmarked clause. -/
theorem marking_awing : ∀ f, marking awing f = some .s := by decide

/-! ### Exocentric and disjunctive foci -/

/-- An exocentric marking realizes no focus below the constituent it marks. -/
def Exocentric (inv : List Node) (m : Node) : Prop :=
  Usable inv m m ∧ ∀ f, f ≤ m → f ≠ m → ¬ Usable inv m f

instance (inv : List Node) (m : Node) : Decidable (Exocentric inv m) := by
  unfold Exocentric; infer_instance

/-- A disjunctive marking realizes foci on two disjoint constituents. -/
def Disjunctive (inv : List Node) (m : Node) : Prop :=
  ∃ a b, ¬ a ≤ b ∧ ¬ b ≤ a ∧ Usable inv m a ∧ Usable inv m b

instance (inv : List Node) (m : Node) : Decidable (Disjunctive inv m) := by
  unfold Disjunctive; infer_instance

/-- Gùrùntùm's clausal marking is exocentric and its VP marking disjunctive. -/
theorem guruntum_exocentric_disjunctive : Exocentric guruntum .s ∧ Disjunctive guruntum .vp := by
  decide

/-- Downward Syncretism — every marking of a phrase is syncretic with focus on some word —
    fails on Gùrùntùm. -/
theorem not_downward_syncretism : ¬ ∀ m ∈ guruntum, ∃ f, f.Word ∧ Usable guruntum m f := by
  decide

/-- A marking that realizes narrow verb focus and reaches the VP realizes VP focus too: the
    disjunctive syncretism predicts the broad focus. -/
theorem usable_vp_of_v {inv : List Node} {m : Node} (h : Usable inv m .v) (hm : Node.vp ≤ m) :
    Usable inv m .vp :=
  h.of_le (by decide) hm

/-! ### Tangale and the reflex analysis -/

open HartmannZimmermann2004

/-- Tangale follows Hausa in the progressive, where only subject focus must be marked, and
    Gùrùntùm in the perfective, where verb, VP and object focus share a marking. -/
def tangale : Tangale.TAM → Option (List Node)
  | .continuous => some hausa
  | .perfective => some guruntum
  | _ => none

/-- The focused constituent of a configuration as a node. -/
def focusNode : Focused → Node
  | .subject => .sbj
  | .verb => .v
  | .vp => .vp
  | .object => .obj

/-- A configuration has an overt reflex on the reflex analysis exactly when its marking here is
    not the default clausal one. -/
theorem overt_iff_marking_ne_default :
    ∀ c : Config, c.WF → ∀ inv ∈ tangale c.tam,
      ((realize c).IsOvert ↔ marking inv (focusNode c.focused) ≠ some .s) := by
  intro c
  obtain ⟨f, a, t⟩ := c
  cases f <;> cases a <;> cases t <;> decide

/-! ### The paper's examples -/

/-- A reading as the focused constituent. -/
def Node.parse? : String → Option Node
  | "subject" => some .sbj
  | "verb" => some .v
  | "VP" => some .vp
  | "object" => some .obj
  | "clause" => some .s
  | _ => none

/-- The inventory of a row's language. -/
def inventory? (r : LinguisticExample) : Option (List Node) :=
  match r.language with
  | "guru1271" => some guruntum
  | "buli1254" => some buli
  | "haus1257" => some hausa
  | "nucl1347" => some wolof
  | "cent2142" => some aymara
  | "awin1248" => some awing
  | _ => none

/-- The constituent a row's marking marks as focal. -/
def marked? (r : LinguisticExample) : Option Node :=
  match r.language, r.feature? "marking" with
  | "guru1271", some "a before subject" => some .sbj
  | "guru1271", some "a between verb and object" => some .vp
  | "guru1271", some "a clause-final" => some .s
  | "buli1254", some "le after subject" => some .s
  | "buli1254", some "ka before object" => some .vp
  | "buli1254", some "kama after VP" => some .v
  | "haus1257", some "relative form" => some .sbj
  | "haus1257", some "absolute form" => some .s
  | "nucl1347", some "a" => some .sbj
  | "nucl1347", some "la" => some .obj
  | "nucl1347", some "dafa" => some .vp
  | "nucl1347", some "na" | "nucl1347", some "ngi" => some .s
  | "cent2142", some "wa on verb" => some .s
  | "awin1248", some "none" => some .s
  | _, _ => none

/-- Every reading of a row is realized by the marking the row shows, which is the marking the
    inventory predicts for that focus. -/
theorem rows_marking :
    ∀ r ∈ Examples.all, ∀ inv ∈ inventory? r, ∀ m ∈ marked? r, ∀ x ∈ r.readings,
      ∀ f ∈ Node.parse? x.1, x.2 = .acceptable ∧ marking inv f = some m := by
  decide

end AssmannEtAl2023
