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

@[inline]
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

@[inline]
def get! (l : TreeMap α β cmp) (a : α) [Inhabited β]  : β :=
  DTreeMap.Const.get! l.inner a

@[inline, inherit_doc DTreeMap.get?]
def find? (t : TreeMap α β cmp) (a : α) : Option β :=
  DTreeMap.Const.get? t.inner a

@[inline]
def find! (l : TreeMap α β cmp) (a : α) [Inhabited β]  : β :=
  DTreeMap.Const.get! l.inner a

@[inline]
def findD (l : TreeMap α β cmp) (a : α) (fallback : β) : β :=
  DTreeMap.Const.getD l.inner a fallback

instance : Membership α (TreeMap α β cmp) where
  mem m a := m.contains a

instance {m : TreeMap α β cmp} {a : α} : Decidable (a ∈ m) :=
  show Decidable (m.contains a) from inferInstance

universe w in
@[inline] def forIn {m : Type w → Type w} [Monad m]
    {γ : Type w} (f : α → β → γ → m (ForInStep γ)) (init : γ) (b : TreeMap α β cmp) : m γ :=
  b.inner.forIn (fun a b c => f a b c) init

universe w in
instance {m : Type w → Type w} : ForIn m (TreeMap α β cmp) (α × β) where
  forIn m init f := m.forIn (fun a b acc => f ⟨a, b⟩ acc) init

@[inline] def any (l : TreeMap α β cmp) (p : α → β → Bool) : Bool :=
  l.inner.any p
universe w in
@[inline] def foldl {γ : Type w}
    (f : γ → α → β → γ) (init : γ) (b : TreeMap α β cmp) : γ :=
  b.inner.foldl f init

instance : Repr (TreeMap α β cmp) where
  reprPrec _ _ := Format.nil

instance : Inhabited (TreeMap α β cmp) := ⟨empty⟩

instance : Repr (TreeMap α β cmp) where
  reprPrec _ _ := Format.nil

/-- Returns a `List` of the key/value pairs in order. -/
@[specialize] def toList (t : TreeMap α β cmp) : List (α × β) :=
  Std.DTreeMap.Internal.Impl.Const.toList t.inner.inner

/-- Returns a `Array` of the key/value pairs in order. -/
@[specialize] def toArray (t : TreeMap α β cmp) : Array (α × β) :=
  t.foldl (init := ∅) fun acc k v => acc.push ⟨k,v⟩

@[inline] def fromArray (l : Array (α × β)) (cmp : α → α → Ordering) : TreeMap α β cmp :=
  l.foldl (fun t e => t.insert e.1 e.2) ∅

@[inline] def fromList (l : List (α × β)) (cmp : α → α → Ordering) : TreeMap α β cmp :=
  l.foldl (fun r p => r.insert p.1 p.2) ∅

/-- Merges the maps `t₁` and `t₂`, if a key `a : α` exists in both,
then use `mergeFn a b₁ b₂` to produce the new merged value. -/
def mergeBy (mergeFn : α → β → β → β) (t₁ t₂ : TreeMap α β cmp) : TreeMap α β cmp :=
  t₂.foldl (init := t₁) fun t₁ a b₂ =>
    t₁.insert a <|
      match t₁.find? a with
      | some b₁ => mergeFn a b₁ b₂
      | none => b₂

universe w in
variable {γ : Type w} in
def filterMap (f : α → β → Option γ) (m : TreeMap α β cmp) : TreeMap α γ cmp :=
  m.foldl (fun r k v => match f k v with
    | none => r
    | some b => r.insert k b) {}

def filter (f : α → β → Bool) (m : TreeMap α β cmp) : TreeMap α β cmp :=
  m.foldl (fun r k v => if f k v then r.insert k v else r) ∅

end TreeMap

end Std
