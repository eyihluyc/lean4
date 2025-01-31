/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Std.Data.DTreeMap.Raw

/-
# Tree maps with unbundled well-formedness invariant

This file develops the type `Std.Data.TreeMap.Raw` of tree maps with unbundled
well-formedness invariant.

This version is safe to use in nested inductive types. The well-formedness predicate is
available as `Std.Data.TreeMap.Raw.WF` and we prove in this file that all operations preserve
well-formedness. When in doubt, prefer `TreeMap` over `TreeMap.Raw`.

Lemmas about the operations on `Std.Data.TreeMap.Raw` are available in the module
`Std.Data.TreeMap.RawLemmas`.
-/

set_option autoImplicit false
set_option linter.missingDocs true

universe u v

variable {α : Type u} {β : Type v} {cmp : α → α → Ordering}

namespace Std

namespace TreeMap

/--
Tree maps without a bundled well-formedness invariant, suitable for use in nested
inductive types. The well-formedness invariant is called `Raw.WF`. When in doubt, prefer `TreeMap`
over `TreeMap.Raw`. Lemmas about the operations on `Std.Data.TreeMap.Raw` are available in the
module `Std.Data.TreeMap.RawLemmas`.

A tree map stores an assignment of keys to values. It depends on a comparator function that
defines an ordering on the keys and provides efficient order-dependent queries, such as retrieval
of the minimum or maximum.

To ensure that the operations behave as expected, the comparator function `cmp` should satisfy
certain laws that ensure a consistent ordering:

* If `a` is less than (or equal) to `b`, then `b` is greater than (or equal) to `a`
and vice versa (see the `OrientedCmp` typeclass)
* If `a` is less than or equal to `b` and `b` is, in turn, less than or equal to `c`, then `a`
id less than or equal to `c` (see the `TransCmp` typeclass).

Keys for which `cmp a b = Ordering.eq` are considered the same, i.e there can be only one entry
with key either `a` or `b` in a tree map. Looking up either `a` or `b` always yield the same entry,
if any is present.

To avoid expensive copies, users should make sure that the tree map is used linearly to avoid
expensive copies.

Internally, the tree maps are represented as weight-balanced trees.
-/
structure Raw (α : Type u) (β : Type v) (cmp : α → α → Ordering) where
  /-- Internal implementation detail of the tree map. -/
  inner : DTreeMap.Raw α (fun _ => β) cmp

namespace Raw

/--
Well-formedness predicate for tree maps. Users of `TreeMap` will not need to interact with
this. Users of `TreeMap.Raw` will need to provide proofs of `WF` to lemmas and should use lemmas
like `WF.empty` and `WF.insert` (which are always named exactly like the operations they are about)
to show that map operations preserve well-formedness. The constructors of this type are internal
implementation details and should not be accessed by users.
-/
structure WF (l : Raw α β cmp) where
  /-- Internal implementation detail of the tree map. -/
  out : l.inner.WF

instance {t : Raw α β cmp} : Coe t.WF t.inner.WF where
  coe t := t.out

@[inline, inherit_doc DTreeMap.Raw.empty]
def empty : Raw α β cmp :=
  ⟨DTreeMap.Raw.empty⟩

instance : EmptyCollection (Raw α β cmp) where
  emptyCollection := empty

@[inline, inherit_doc DTreeMap.Raw.isEmpty]
def isEmpty (t : Raw α β cmp) : Bool :=
  t.inner.isEmpty

@[inline, inherit_doc DTreeMap.Raw.isSingleton]
def isSingleton (t : Raw α β cmp) : Bool :=
  t.inner.isSingleton

@[inline, inherit_doc DTreeMap.Raw.insert]
def insert (l : Raw α β cmp) (a : α) (b : β) : Raw α β cmp :=
  ⟨l.inner.insert a b⟩

@[inline, inherit_doc DTreeMap.Raw.insertFast]
def insertFast (l : Raw α β cmp) (h : l.WF) (a : α) (b : β) : Raw α β cmp :=
  ⟨l.inner.insertFast h.out a b⟩

@[inline, inherit_doc DTreeMap.Raw.contains]
def contains (l : Raw α β cmp) (a : α) : Bool :=
  l.inner.contains a

@[inline, inherit_doc DTreeMap.Raw.size]
def size (t : Raw α β cmp) : Nat :=
  t.inner.size

@[inline, inherit_doc DTreeMap.Raw.erase]
def erase (t : Raw α β cmp) (a : α) : Raw α β cmp :=
  ⟨t.inner.erase a⟩

@[inline, inherit_doc DTreeMap.Raw.containsThenInsert]
def containsThenInsert (t : Raw α β cmp) (a : α) (b : β) : Bool × Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩
  let p := t.inner.containsThenInsert a b
  (p.1, ⟨p.2⟩)

@[inline, inherit_doc DTreeMap.Raw.insertIfNew]
def insertIfNew (t : Raw α β cmp) (a : α) (b : β) : Raw α β cmp :=
    letI : Ord α := ⟨cmp⟩; ⟨t.inner.insertIfNew a b⟩

@[inline, inherit_doc DTreeMap.Raw.containsThenInsertIfNew]
def containsThenInsertIfNew (t : Raw α β cmp) (a : α) (b : β) :
    Bool × Raw α β cmp :=
  let p := t.inner.containsThenInsertIfNew a b
  (p.1, ⟨p.2⟩)

@[inline, inherit_doc DTreeMap.Raw.get?]
def get? (t : Raw α β cmp) (a : α) : Option β :=
  DTreeMap.Raw.Const.get? t.inner a

@[inline, inherit_doc DTreeMap.Raw.get]
def get (l : Raw α β cmp) (a : α) (h : l.contains a) : β :=
  DTreeMap.Raw.Const.get l.inner a h

@[inline, inherit_doc DTreeMap.Raw.get!]
def get! (l : Raw α β cmp) (a : α) [Inhabited β]  : β :=
  DTreeMap.Raw.Const.get! l.inner a

@[inline]
def getD (l : Raw α β cmp) (a : α) (fallback : β) : β :=
  DTreeMap.Raw.Const.getD l.inner a fallback

universe w

@[inline, inherit_doc DTreeMap.Raw.forM]
def forM {m} [Monad m] (f : α → β → m PUnit) (t : Raw α β cmp) : m PUnit :=
  t.inner.forM f

@[inline, inherit_doc DTreeMap.Raw.forIn] def forIn {m : Type w → Type w} [Monad m]
    {γ : Type w} (f : α → β → γ → m (ForInStep γ)) (init : γ) (b : Raw α β cmp) : m γ :=
  b.inner.forIn (fun a b c => f a b c) init

instance {m : Type w → Type w} : ForIn m (Raw α β cmp) (α × β) where
  forIn m init f := m.forIn (fun a b acc => f ⟨a, b⟩ acc) init

@[inline, inherit_doc DTreeMap.Raw.any]
def any (l : Raw α β cmp) (p : α → β → Bool) : Bool :=
  l.inner.any p

@[inline, inherit_doc DTreeMap.Raw.all]
def all (l : Raw α β cmp) (p : α → β → Bool) : Bool :=
  l.inner.all p

@[inline, inherit_doc DTreeMap.Raw.foldlM]
def foldlM {m δ} [Monad m] (f : δ → (a : α) → β → m δ) (init : δ) (t : Raw α β cmp) : m δ :=
  t.inner.foldlM f init

@[inline, inherit_doc DTreeMap.Raw.foldl]
def foldl {γ : Type w}
    (f : γ → (a : α) → β → γ) (init : γ) (b : Raw α β cmp) : γ :=
  b.inner.foldl f init

@[inline, inherit_doc DTreeMap.Raw.toList]
def toList (t : Raw α β cmp) : List (α × β) :=
  DTreeMap.Raw.Const.toList t.inner

@[inline, inherit_doc DTreeMap.Raw.fromList]
def fromList (l : List (α × β)) (cmp : α → α → Ordering) : Raw α β cmp :=
  l.foldl (fun r p => r.insert p.1 p.2) ∅

@[inline, inherit_doc DTreeMap.Raw.toArray]
def toArray (t : Raw α β cmp) : Array (α × β) :=
  t.foldl (init := ∅) fun acc k v => acc.push ⟨k,v⟩

@[inline, inherit_doc DTreeMap.Raw.fromArray]
def fromArray (l : Array (α × β)) (cmp : α → α → Ordering) : Raw α β cmp :=
  l.foldl (fun t e => t.insert e.1 e.2) ∅

@[inline, inherit_doc DTreeMap.Raw.mergeBy]
def mergeBy (mergeFn : α → β → β → β) (t₁ t₂ : Raw α β cmp) : Raw α β cmp :=
  ⟨DTreeMap.Raw.Const.mergeBy mergeFn t₁.inner t₂.inner⟩

variable {γ : Type w} in
def filterMap (f : (a : α) → β → Option γ) (m : Raw α β cmp) : Raw α γ cmp :=
  ⟨m.inner.filterMap f⟩

variable {γ : Type w} in
@[inline]
def map (f : α → β → γ) (t : Raw α β cmp) : Raw α γ cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨t.inner.map f⟩

def filter (f : α → β → Bool) (m : Raw α β cmp) : Raw α β cmp :=
  ⟨m.inner.filter f⟩

instance : Membership α (Raw α β cmp) where
  mem m a := m.contains a

instance {m : Raw α β cmp} {a : α} : Decidable (a ∈ m) :=
  show Decidable (m.contains a) from inferInstance

instance : Inhabited (Raw α β cmp) := ⟨empty⟩

instance : Repr (Raw α β cmp) where
  reprPrec _ _ := Format.nil

end Raw

end TreeMap

end Std
