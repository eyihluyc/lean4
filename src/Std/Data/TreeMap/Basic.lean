/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Std.Data.DTreeMap.Basic

/-!
# Tree maps

This file develops the type `Std.Data.TreeMap` of tree maps.

Lemmas about the operations on `Std.Data.TreeMap` are available in the
module `Std.Data.TreeMap.Lemmas`.

See the module `Std.Data.TreeMap.Raw` for a variant of this type which is safe to use in
nested inductive types.
-/

set_option autoImplicit false
set_option linter.missingDocs true

universe u v

variable {α : Type u} {β : Type v} {cmp : α → α → Ordering}

namespace Std

/--
Tree maps.

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

These tree maps contain a bundled well-formedness invariant, which means that they cannot
be used in nested inductive types. For these use cases, `Std.Data.TreeMap.Raw` and
`Std.Data.TreeMap.Raw.WF` unbundle the invariant from the tree map. When in doubt, prefer
`TreeMap` over `TreeMap.Raw`.
-/
structure TreeMap (α : Type u) (β : Type v) (cmp : α → α → Ordering) where
  /-- Internal implementation detail of the tree map. -/
  inner : DTreeMap α (fun _ => β) cmp

namespace TreeMap

@[inline, inherit_doc DTreeMap.empty]
def empty : TreeMap α β cmp :=
  ⟨DTreeMap.empty⟩

instance : EmptyCollection (TreeMap α β cmp) where
  emptyCollection := empty

@[inline, inherit_doc DTreeMap.isEmpty]
def isEmpty (t : TreeMap α β cmp) : Bool :=
  t.inner.isEmpty

@[inline, inherit_doc DTreeMap.isSingleton]
def isSingleton (t : TreeMap α β cmp) : Bool :=
  t.inner.isSingleton

@[inline, inherit_doc DTreeMap.insert]
def insert (l : TreeMap α β cmp) (a : α) (b : β) : TreeMap α β cmp :=
  ⟨l.inner.insert a b⟩

@[inline, inherit_doc DTreeMap.contains]
def contains (l : TreeMap α β cmp) (a : α) : Bool :=
  l.inner.contains a

@[inline, inherit_doc DTreeMap.size]
def size (t : TreeMap α β cmp) : Nat :=
  t.inner.size

@[inline, inherit_doc DTreeMap.erase]
def erase (t : TreeMap α β cmp) (a : α) : TreeMap α β cmp :=
  ⟨t.inner.erase a⟩

@[inline, inherit_doc DTreeMap.containsThenInsert]
def containsThenInsert (t : TreeMap α β cmp) (a : α) (b : β) : Bool × TreeMap α β cmp :=
  let p := t.inner.containsThenInsert a b
  (p.1, ⟨p.2⟩)

@[inline, inherit_doc DTreeMap.insertIfNew]
def insertIfNew (t : TreeMap α β cmp) (a : α) (b : β) : TreeMap α β cmp :=
  ⟨t.inner.insertIfNew a b⟩

@[inline, inherit_doc DTreeMap.containsThenInsertIfNew]
def containsThenInsertIfNew (t : TreeMap α β cmp) (a : α) (b : β) :
    Bool × TreeMap α β cmp :=
  let p := t.inner.containsThenInsertIfNew a b
  (p.1, ⟨p.2⟩)

@[inline, inherit_doc DTreeMap.get?]
def get? (t : TreeMap α β cmp) (a : α) : Option β :=
  DTreeMap.Const.get? t.inner a

@[inline, inherit_doc DTreeMap.get]
def get (l : TreeMap α β cmp) (a : α) (h : l.contains a) : β :=
   DTreeMap.Const.get l.inner a h

@[inline, inherit_doc DTreeMap.get!]
def get! (l : TreeMap α β cmp) (a : α) [Inhabited β]  : β :=
  DTreeMap.Const.get! l.inner a

@[inline]
def getD (l : TreeMap α β cmp) (a : α) (fallback : β) : β :=
  DTreeMap.Const.getD l.inner a fallback

universe w

@[inline, inherit_doc DTreeMap.forM]
def forM {m} [Monad m] (f : α → β → m PUnit) (t : TreeMap α β cmp) : m PUnit :=
  t.inner.forM f

@[inline, inherit_doc DTreeMap.forIn] def forIn {m : Type w → Type w} [Monad m]
    {γ : Type w} (f : α → β → γ → m (ForInStep γ)) (init : γ) (b : TreeMap α β cmp) : m γ :=
  b.inner.forIn (fun a b c => f a b c) init

instance {m : Type w → Type w} : ForIn m (TreeMap α β cmp) (α × β) where
  forIn m init f := m.forIn (fun a b acc => f ⟨a, b⟩ acc) init

@[inline, inherit_doc DTreeMap.any]
def any (l : TreeMap α β cmp) (p : α → β → Bool) : Bool :=
  l.inner.any p

@[inline, inherit_doc DTreeMap.all]
def all (l : TreeMap α β cmp) (p : α → β → Bool) : Bool :=
  l.inner.all p

@[inline, inherit_doc DTreeMap.foldlM]
def foldlM {m δ} [Monad m] (f : δ → (a : α) → β → m δ) (init : δ) (t : TreeMap α β cmp) : m δ :=
  t.inner.foldlM f init

@[inline, inherit_doc TreeMap.foldl]
def foldl {γ : Type w}
    (f : γ → (a : α) → β → γ) (init : γ) (b : TreeMap α β cmp) : γ :=
  b.inner.foldl f init

@[inline, inherit_doc TreeMap.toList]
def toList (t : TreeMap α β cmp) : List (α × β) :=
  DTreeMap.Const.toList t.inner

@[inline, inherit_doc TreeMap.fromList]
def fromList (l : List (α × β)) (cmp : α → α → Ordering) : TreeMap α β cmp :=
  l.foldl (fun r p => r.insert p.1 p.2) ∅

@[inline, inherit_doc TreeMap.toArray]
def toArray (t : TreeMap α β cmp) : Array (α × β) :=
  t.foldl (init := ∅) fun acc k v => acc.push ⟨k,v⟩

@[inline, inherit_doc TreeMap.fromArray]
def fromArray (l : Array (α × β)) : TreeMap α β cmp :=
  l.foldl (fun t e => t.insert e.1 e.2) ∅

@[inline, inherit_doc TreeMap.mergeBy]
def mergeBy (mergeFn : α → β → β → β) (t₁ t₂ : TreeMap α β cmp) : TreeMap α β cmp :=
  ⟨DTreeMap.Const.mergeBy mergeFn t₁.inner t₂.inner⟩

variable {γ : Type w} in
def filterMap (f : (a : α) → β → Option γ) (m : TreeMap α β cmp) : TreeMap α γ cmp :=
  ⟨m.inner.filterMap f⟩

variable {γ : Type w} in
@[inline]
def map (f : α → β → γ) (t : TreeMap α β cmp) : TreeMap α γ cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨t.inner.map f⟩

def filter (f : α → β → Bool) (m : TreeMap α β cmp) : TreeMap α β cmp :=
  ⟨m.inner.filter f⟩

instance : Membership α (TreeMap α β cmp) where
  mem m a := m.contains a

instance {m : TreeMap α β cmp} {a : α} : Decidable (a ∈ m) :=
  show Decidable (m.contains a) from inferInstance

instance : Inhabited (TreeMap α β cmp) := ⟨empty⟩

-- /-- Folds the given function over the mappings in the tree in ascending order. -/
-- @[specialize]
-- def foldlM {m δ} [Monad m] (f : δ → α → β → m δ) (init : δ) (t : TreeMap α β cmp) : m δ :=
--   t.inner.foldlM f init

-- universe w in
-- @[inline] def foldl {γ : Type w}
--     (f : γ → α → β → γ) (init : γ) (b : TreeMap α β cmp) : γ :=
--   b.inner.foldl f init

-- /-- Applies the given function to the mappings in the tree in ascending order. -/
-- @[inline]
-- def forM {m} [Monad m] (f : α → β → m PUnit) (t : TreeMap α β cmp) : m PUnit :=
--   t.inner.forM f

instance : Repr (TreeMap α β cmp) where
  reprPrec _ _ := Format.nil

end TreeMap

end Std
