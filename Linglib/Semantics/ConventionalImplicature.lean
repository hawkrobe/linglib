module

public import Linglib.Semantics.Composition.Writer
public import Linglib.Semantics.Presupposition.Basic

/-!
# Conventional implicature

This file defines two-dimensional meanings, the carrier of Potts's logic of conventional
implicatures (CIs). A two-dimensional meaning has an at-issue value, which composes as usual,
and not-at-issue content, a proposition the speaker contributes without putting it at issue;
`TwoDim W α` pairs an at-issue value of type `α` with not-at-issue content over worlds `W`.
Not-at-issue content only accumulates, so `TwoDim W` is the writer monad over propositions
under meet. Applying an at-issue operator with `f <$> p` passes the not-at-issue content up
(`map_notAtIssue`), and binding with `p >>= f` lets at-issue content feed later not-at-issue
content but never the reverse (`bind_atIssue`). Potts's rule of CI application, which applies a
CI functor `f` to an at-issue argument and returns the argument unmodified, is
`p >>= fun a ↦ ⟨a, f a⟩`. The connectives `neg`, `and`, `or` and `imp` act on at-issue
propositions and meet the not-at-issue content of their parts, so CIs project from under every
connective.

Potts collects the CIs of a parsetree at its root, and Giorgolo and Asudeh recast that
collection as a writer monad whose log lists the CIs. The map `ofWriter` conjoins such a log.
It is a monad morphism (`ofWriter_pure`, `ofWriter_bind`), so composing two-dimensional meanings
node by node predicts what collecting at the root does. Conjoining forgets how the log was
itemized, for instance how often a CI was contributed (`ofWriter_not_injective`).

Reading a presupposition as not-at-issue content (`ofPartialProp`) turns the classical,
non-filtering connectives on presuppositions into the two-dimensional ones
(`ofPartialProp_neg`, `ofPartialProp_imp`). The two part at Karttunen's filtering. A filtering
conditional presupposes at most what the unfiltered one does
(`imp_notAtIssue_le_impFilter_presup`), and less in general, because its antecedent's at-issue
content can satisfy its consequent's presupposition. No at-issue operator on two-dimensional
meanings allows that (`exists_ofPartialProp_impFilter_ne`).

## Main definitions

* `TwoDim`: an at-issue value and not-at-issue content, with its `Monad` instance.
* `TwoDim.neg`, `TwoDim.and`, `TwoDim.or`, `TwoDim.imp`: the connectives on propositions.
* `TwoDim.ofWriter`: the conjunction of a writer's log of CIs.
* `TwoDim.ofPartialProp`: a presupposition read as not-at-issue content.

## Implementation notes

The not-at-issue dimension is the meet of the collected content rather than the collection, so a
repeated CI adds nothing. That suits content whose repetition is redundant, but not the
strengthening Potts reports for repeated expressives, which needs graded expressive content.
The dimension also carries not-at-issue content that is not a CI in Potts's sense, such as the
appositive impositions of AnderBois, Brasoveanu and Henderson and evidential content. How an
utterance updates the context with each kind is not modelled here.

## References

* [potts-2005]
* [potts-2007b]
* [giorgolo-asudeh-2012]
* [karttunen-1973]
* [anderbois-brasoveanu-henderson-2015]
-/

@[expose] public section

namespace ConventionalImplicature

universe u

open Presupposition (PartialProp)

/-- A two-dimensional meaning pairs an at-issue value with the not-at-issue proposition it
carries ([potts-2005]). *That bastard John is late* has at-issue content "John is late" and
not-at-issue content "the speaker disdains John". -/
@[ext]
structure TwoDim (W : Type u) (α : Type u) where
  /-- The at-issue value. -/
  atIssue : α
  /-- The not-at-issue content. -/
  notAtIssue : W → Prop

namespace TwoDim

variable {W α β : Type u}

/-! ### The monad -/

/-- Two-dimensional meanings form the writer monad over propositions under meet. A `pure`
value contributes no not-at-issue content, and composition meets the not-at-issue content of
its parts. -/
instance : Monad (TwoDim W) where
  pure a := ⟨a, ⊤⟩
  map f p := ⟨f p.atIssue, p.notAtIssue⟩
  seq f p := ⟨f.atIssue (p ()).atIssue, f.notAtIssue ⊓ (p ()).notAtIssue⟩
  bind p f := ⟨(f p.atIssue).atIssue, p.notAtIssue ⊓ (f p.atIssue).notAtIssue⟩

@[simp] theorem pure_atIssue (a : α) : (pure a : TwoDim W α).atIssue = a := rfl

@[simp] theorem pure_notAtIssue (a : α) : (pure a : TwoDim W α).notAtIssue = ⊤ := rfl

@[simp] theorem map_atIssue (f : α → β) (p : TwoDim W α) : (f <$> p).atIssue = f p.atIssue :=
  rfl

@[simp] theorem map_notAtIssue (f : α → β) (p : TwoDim W α) :
    (f <$> p).notAtIssue = p.notAtIssue := rfl

@[simp] theorem seq_atIssue (f : TwoDim W (α → β)) (p : TwoDim W α) :
    (f <*> p).atIssue = f.atIssue p.atIssue := rfl

@[simp] theorem seq_notAtIssue (f : TwoDim W (α → β)) (p : TwoDim W α) :
    (f <*> p).notAtIssue = f.notAtIssue ⊓ p.notAtIssue := rfl

/-- The at-issue value of a composition depends on the input's at-issue value alone, so
not-at-issue content never flows into the at-issue dimension ([potts-2005]). -/
@[simp] theorem bind_atIssue (p : TwoDim W α) (f : α → TwoDim W β) :
    (p >>= f).atIssue = (f p.atIssue).atIssue := rfl

@[simp] theorem bind_notAtIssue (p : TwoDim W α) (f : α → TwoDim W β) :
    (p >>= f).notAtIssue = p.notAtIssue ⊓ (f p.atIssue).notAtIssue := rfl

instance : LawfulMonad (TwoDim W) := LawfulMonad.mk' (TwoDim W)
  (id_map := fun _ ↦ rfl)
  (pure_bind := fun _ _ ↦ TwoDim.ext rfl (top_inf_eq _))
  (bind_assoc := fun _ _ _ ↦ TwoDim.ext rfl (inf_assoc ..))
  (bind_pure_comp := fun _ _ ↦ TwoDim.ext rfl (inf_top_eq _))
  (bind_map := fun _ _ ↦ rfl)

/-! ### Connectives -/

section Connectives

variable (p q : TwoDim W (W → Prop))

/-- Negation complements the at-issue proposition and passes the not-at-issue content up. -/
def neg : TwoDim W (W → Prop) := compl <$> p

/-- Conjunction conjoins the at-issue propositions. -/
def and : TwoDim W (W → Prop) := (· ⊓ ·) <$> p <*> q

/-- Disjunction disjoins the at-issue propositions. -/
def or : TwoDim W (W → Prop) := (· ⊔ ·) <$> p <*> q

/-- Implication takes the conditional of the at-issue propositions. -/
def imp : TwoDim W (W → Prop) := (· ⇨ ·) <$> p <*> q

@[simp] theorem neg_atIssue : p.neg.atIssue = p.atIssueᶜ := rfl

@[simp] theorem neg_notAtIssue : p.neg.notAtIssue = p.notAtIssue := rfl

@[simp] theorem neg_neg : p.neg.neg = p := TwoDim.ext (compl_compl _) rfl

@[simp] theorem and_atIssue : (p.and q).atIssue = p.atIssue ⊓ q.atIssue := rfl

@[simp] theorem and_notAtIssue : (p.and q).notAtIssue = p.notAtIssue ⊓ q.notAtIssue := rfl

@[simp] theorem or_atIssue : (p.or q).atIssue = p.atIssue ⊔ q.atIssue := rfl

@[simp] theorem or_notAtIssue : (p.or q).notAtIssue = p.notAtIssue ⊓ q.notAtIssue := rfl

@[simp] theorem imp_atIssue : (p.imp q).atIssue = p.atIssue ⇨ q.atIssue := rfl

@[simp] theorem imp_notAtIssue : (p.imp q).notAtIssue = p.notAtIssue ⊓ q.notAtIssue := rfl

end Connectives

/-! ### Collecting at the root -/

/-- `ofWriter m` reads a computation that logs its CIs ([giorgolo-asudeh-2012]) as a
two-dimensional meaning, conjoining the log. -/
def ofWriter (m : Writer (List (W → Prop)) α) : TwoDim W α :=
  ⟨m.val, fun w ↦ ∀ c ∈ m.log, c w⟩

@[simp] theorem ofWriter_atIssue (m : Writer (List (W → Prop)) α) :
    (ofWriter m).atIssue = m.val := rfl

@[simp] theorem ofWriter_notAtIssue (m : Writer (List (W → Prop)) α) (w : W) :
    (ofWriter m).notAtIssue w ↔ ∀ c ∈ m.log, c w := Iff.rfl

@[simp] theorem ofWriter_pure (a : α) : ofWriter (pure a : Writer (List (W → Prop)) α) = pure a :=
  TwoDim.ext rfl (funext fun _ ↦ propext (by simp))

/-- Composing node by node and collecting at the root agree, since `ofWriter` is a monad
morphism. -/
theorem ofWriter_bind (m : Writer (List (W → Prop)) α) (f : α → Writer (List (W → Prop)) β) :
    ofWriter (m >>= f) = ofWriter m >>= fun a ↦ ofWriter (f a) :=
  TwoDim.ext rfl (funext fun _ ↦ propext List.forall_mem_append)

/-- A CI logged twice contributes what it contributes logged once. -/
theorem ofWriter_mk_cons_self (a : α) (c : W → Prop) (l : List (W → Prop)) :
    ofWriter (Writer.mk a (c :: c :: l)) = ofWriter (Writer.mk a (c :: l)) :=
  TwoDim.ext rfl (funext fun _ ↦ propext (by simp))

/-- Conjoining the log forgets how often a CI was contributed. -/
theorem ofWriter_not_injective [Nonempty α] :
    ¬ Function.Injective (ofWriter : Writer (List (W → Prop)) α → TwoDim W α) := fun h ↦ by
  simpa using congrArg Writer.log (h (ofWriter_mk_cons_self (Classical.arbitrary α) ⊤ []))

/-! ### Presuppositions as not-at-issue content -/

/-- `ofPartialProp p` reads the presupposition of `p` as not-at-issue content, forgetting that it
conditions definedness. -/
def ofPartialProp (p : PartialProp W) : TwoDim W (W → Prop) := ⟨p.assertion, p.presup⟩

@[simp] theorem ofPartialProp_neg (p : PartialProp W) :
    ofPartialProp p.neg = (ofPartialProp p).neg := rfl

@[simp] theorem ofPartialProp_and (p q : PartialProp W) :
    ofPartialProp (p.and q) = (ofPartialProp p).and (ofPartialProp q) := rfl

@[simp] theorem ofPartialProp_or (p q : PartialProp W) :
    ofPartialProp (p.or q) = (ofPartialProp p).or (ofPartialProp q) := rfl

@[simp] theorem ofPartialProp_imp (p q : PartialProp W) :
    ofPartialProp (p.imp q) = (ofPartialProp p).imp (ofPartialProp q) := rfl

/-- A filtering conditional presupposes at most what the antecedent and consequent presuppose
together. -/
theorem imp_notAtIssue_le_impFilter_presup (p q : PartialProp W) :
    ((ofPartialProp p).imp (ofPartialProp q)).notAtIssue ≤ (p.impFilter q).presup :=
  fun _ h ↦ ⟨h.1, fun _ ↦ h.2⟩

/-- Filtering is no composition of two-dimensional meanings. A filtering conditional's
presupposition depends on its antecedent's at-issue content, which no at-issue operator passes
to the not-at-issue dimension ([karttunen-1973]). -/
theorem exists_ofPartialProp_impFilter_ne [Nonempty W] :
    ∃ p q : PartialProp W, ∀ f : (W → Prop) → (W → Prop) → W → Prop,
      ofPartialProp (p.impFilter q) ≠ f <$> ofPartialProp p <*> ofPartialProp q := by
  refine ⟨⟨⊤, ⊥⟩, ⟨⊥, ⊥⟩, fun f h ↦ ?_⟩
  obtain ⟨w⟩ := ‹Nonempty W›
  simpa [ofPartialProp, PartialProp.impFilter] using congrFun (congrArg notAtIssue h) w

end TwoDim

end ConventionalImplicature
