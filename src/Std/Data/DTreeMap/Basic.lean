/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Std.Data.DTreeMap.Internal.WF
import Std.Data.DTreeMap.Raw

/-!
# Dependent tree maps

This file develops the type `Std.Data.DTreeMap` of dependent tree maps.

Lemmas about the operations on `Std.Data.DTreeMap` are available in the
module `Std.Data.DTreeMap.Lemmas`.

See the module `Std.Data.DTreeMap.Raw` for a variant of this type which is safe to use in
nested inductive types.
-/

set_option autoImplicit false
set_option linter.missingDocs true

universe u v

variable {α : Type u} {β : α → Type v} {cmp : α → α → Ordering}

namespace Std

/--
Dependent tree maps.

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
if any is present. The `get` operations of the _dependent_ tree map additionally require a
`LawfulEqOrd` instance to ensure that `cmp a b = .eq` always implies `a = b`, and therefore their
respective value types are equal.

To avoid expensive copies, users should make sure that the tree map is used linearly to avoid
expensive copies.

Internally, the tree maps are represented as weight-balanced trees.

These tree maps contain a bundled well-formedness invariant, which means that they cannot
be used in nested inductive types. For these use cases, `Std.Data.DTreeMap.Raw` and
`Std.Data.DTreeMap.Raw.WF` unbundle the invariant from the tree map. When in doubt, prefer
`DTreeMap` over `DTreeMap.Raw`.
-/
structure DTreeMap (α : Type u) (β : α → Type v) (cmp : α → α → Ordering) where
  /-- Internal implementation detail of the tree map. -/
  inner : DTreeMap.Internal.Impl α β
  /-- Internal implementation detail of the tree map. -/
  wf : letI : Ord α := ⟨cmp⟩; inner.WF

namespace DTreeMap

@[inline, inherit_doc Raw.empty]
def empty : DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨Internal.Impl.empty, .empty⟩

instance : EmptyCollection (DTreeMap α β cmp) := ⟨empty⟩

@[inline, inherit_doc Raw.isEmpty]
def isEmpty (t : DTreeMap α β cmp) : Bool :=
  t.inner.isEmpty

@[inline, inherit_doc Raw.isSingleton]
def isSingleton (t : DTreeMap α β cmp) : Bool :=
  t.inner.isSingleton

@[inline, inherit_doc Raw.insert]
def insert (l : DTreeMap α β cmp) (a : α) (b : β a) : DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨(l.inner.insert a b l.wf.balanced).impl, .insert l.wf⟩

@[inline, inherit_doc Raw.contains]
def contains (l : DTreeMap α β cmp) (a : α) : Bool :=
  letI : Ord α := ⟨cmp⟩; l.inner.contains a

@[inline, inherit_doc Raw.size]
def size (t : DTreeMap α β cmp) : Nat :=
  letI : Ord α := ⟨cmp⟩; t.inner.size

@[inline, inherit_doc Raw.erase]
def erase (l : DTreeMap α β cmp) (a : α) : DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨(l.inner.erase a l.wf.balanced).impl, .erase l.wf⟩

@[inline, inherit_doc Raw.containsThenInsert]
def containsThenInsert (t : DTreeMap α β cmp) (a : α) (b : β a) : Bool × DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩
  let p := t.inner.containsThenInsert a b t.wf.balanced
  (p.1, ⟨p.2.impl, t.wf.containsThenInsert⟩)

@[inline, inherit_doc Raw.insertIfNew]
def insertIfNew (t : DTreeMap α β cmp) (a : α) (b : β a) : DTreeMap α β cmp :=
    letI : Ord α := ⟨cmp⟩; ⟨(t.inner.insertIfNew a b t.wf.balanced).impl, t.wf.insertIfNew⟩

@[inline, inherit_doc Raw.containsThenInsertIfNew]
def containsThenInsertIfNew (t : DTreeMap α β cmp) (a : α) (b : β a) :
    Bool × DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩
  let p := t.inner.containsThenInsertIfNew a b t.wf.balanced
  (p.1, ⟨p.2.impl, t.wf.containsThenInsertIfNew⟩)

@[inline, inherit_doc Raw.get?]
def get? [LawfulEqCmp cmp] (t : DTreeMap α β cmp) (a : α) : Option (β a) :=
  letI : Ord α := ⟨cmp⟩; t.inner.get? a

@[inline, inherit_doc Raw.get]
def get [LawfulEqCmp cmp] (l : DTreeMap α β cmp) (a : α) (h : l.contains a) : β a :=
  letI : Ord α := ⟨cmp⟩; l.inner.get a h

@[inline, inherit_doc Raw.get!]
def get! [LawfulEqCmp cmp] (l : DTreeMap α β cmp) (a : α) [Inhabited (β a)]  : β a :=
  letI : Ord α := ⟨cmp⟩; l.inner.get! a

@[inline, inherit_doc Raw.getD]
def getD [LawfulEqCmp cmp] (l : DTreeMap α β cmp) (a : α) (fallback : β a) : β a :=
  letI : Ord α := ⟨cmp⟩; l.inner.getD a fallback

namespace Const
open Internal (Impl)

variable {β : Type v}

@[inline, inherit_doc Raw.Const.get?]
def get? (t : DTreeMap α (fun _ => β) cmp) (a : α) : Option β :=
  letI : Ord α := ⟨cmp⟩
  Impl.Const.get? a t.inner

@[inline]
def get (l : DTreeMap α (fun _ => β) cmp) (a : α) (h : l.contains a) : β :=
  letI : Ord α := ⟨cmp⟩
  Impl.Const.get a l.inner h

@[inline]
def get! (l : DTreeMap α (fun _ => β) cmp) (a : α) [Inhabited β] : β :=
  letI : Ord α := ⟨cmp⟩
  Impl.Const.get! a l.inner

@[inline]
def getD (l : DTreeMap α (fun _ => β) cmp) (a : α) (fallback : β) : β :=
  letI : Ord α := ⟨cmp⟩
  Impl.Const.getD a l.inner fallback

end Const

universe w

@[inline, inherit_doc Raw.forM]
def forM {m} [Monad m] (f : (a : α) → β a → m PUnit) (t : DTreeMap α β cmp) : m PUnit :=
  t.inner.forM f

@[inline, inherit_doc Raw.forIn]
def forIn {m : Type w → Type w} [Monad m]
    {γ : Type w} (f : (a : α) → β a → γ → m (ForInStep γ)) (init : γ) (b : DTreeMap α β cmp) : m γ :=
  b.inner.forIn (fun c a b => f a b c) init

instance {m : Type w → Type w} : ForIn m (DTreeMap α β cmp) ((a : α) × β a) where
  forIn m init f := m.forIn (fun a b acc => f ⟨a, b⟩ acc) init

@[inline, inherit_doc Raw.any]
def any (l : DTreeMap α β cmp) (p : (a : α) → β a → Bool) : Bool := Id.run $ do
  for ⟨a, b⟩ in l do
    if p a b then return true
  return false

@[inline, inherit_doc Raw.all]
def all (l : DTreeMap α β cmp) (p : (a : α) → β a → Bool) : Bool := Id.run $ do
  for ⟨a, b⟩ in l do
    if not <| p a b then return false
  return true

@[inline, inherit_doc Raw.foldlM]
def foldlM {m δ} [Monad m] (f : δ → (a : α) → β a → m δ) (init : δ) (t : DTreeMap α β cmp) : m δ :=
  t.inner.foldlM f init

@[inline, inherit_doc Raw.foldl]
def foldl {γ : Type w}
    (f : γ → (a : α) → β a → γ) (init : γ) (b : DTreeMap α β cmp) : γ :=
  b.inner.foldl f init

@[inline, inherit_doc Raw.toList]
def toList (t : DTreeMap α β cmp) : List ((a : α) × β a) :=
  t.inner.toList

@[inline, inherit_doc Raw.fromList]
def fromList (l : List ((a : α) × β a)) (cmp : α → α → Ordering) : DTreeMap α β cmp :=
  l.foldl (fun r p => r.insert p.1 p.2) ∅

@[inline, inherit_doc Raw.toArray]
def toArray (t : DTreeMap α β cmp) : Array ((a : α) × β a) :=
  t.foldl (init := ∅) fun acc k v => acc.push ⟨k,v⟩

@[inline, inherit_doc fromArray]
def fromArray (l : Array ((a : α) × β a)) (cmp : α → α → Ordering) : DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩
  let impl := Internal.Impl.fromArray l
  ⟨impl.val, sorry⟩

namespace Const

variable {β : Type v}

@[inline, inherit_doc Raw.Const.toList]
def toList (t : DTreeMap α (fun _ => β) cmp) : List (α × β) :=
  Std.DTreeMap.Internal.Impl.Const.toList t.inner

@[inline, inherit_doc Raw.Const.fromList]
def fromList (l : List (α × β)) (cmp : α → α → Ordering) : DTreeMap α (fun _ => β) cmp :=
  l.foldl (fun r p => r.insert p.1 p.2) ∅

@[inline, inherit_doc Raw.Const.toArray]
def toArray (t : DTreeMap α (fun _ => β) cmp) : Array (α × β) :=
  t.foldl (init := ∅) fun acc k v => acc.push ⟨k,v⟩

@[inline, inherit_doc Raw.Const.fromArray]
def fromArray (l : Array (α × β)) (cmp : α → α → Ordering) : DTreeMap α (fun _ => β) cmp :=
  l.foldl (fun t e => t.insert e.1 e.2) ∅

end Const

@[inline, inherit_doc Raw.mergeBy]
def mergeBy [LawfulEqCmp cmp] (mergeFn : (a : α) → β a → β a → β a) (t₁ t₂ : DTreeMap α β cmp) : DTreeMap α β cmp :=
  t₂.foldl (init := t₁) fun t₁ a b₂ =>
    t₁.insert a <|
      match t₁.get? a with
      | some b₁ => mergeFn a b₁ b₂
      | none => b₂

namespace Const

variable {β : Type v}

@[inline, inherit_doc Raw.Const.mergeBy]
def mergeBy (mergeFn : α → β → β → β) (t₁ t₂ : DTreeMap α (fun _ => β) cmp) : DTreeMap α (fun _ => β) cmp :=
  t₂.foldl (init := t₁) fun t₁ a b₂ =>
    t₁.insert a <|
      match get? t₁ a with
      | some b₁ => mergeFn a b₁ b₂
      | none => b₂

end Const

variable {γ : α → Type w} in
def filterMap (f : (a : α) → β a → Option (γ a)) (m : DTreeMap α β cmp) : DTreeMap α γ cmp :=
  m.foldl (fun r k v => match f k v with
    | none => r
    | some b => r.insert k b) {}

variable {γ : α → Type w} in
@[inline]
def map (f : (a : α) → β a → γ a) (t : DTreeMap α β cmp) : DTreeMap α γ cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨t.inner.map f, sorry⟩

def filter (f : (a : α) → β a → Bool) (m : DTreeMap α β cmp) : DTreeMap α β cmp :=
  m.foldl (fun r k v => if f k v then r.insert k v else r) ∅

instance : Membership α (DTreeMap α β cmp) where
  mem m a := m.contains a

instance {m : DTreeMap α β cmp} {a : α} : Decidable (a ∈ m) :=
  show Decidable (m.contains a) from inferInstance

instance : Inhabited (DTreeMap α β cmp) := ⟨empty⟩

instance : Repr (DTreeMap α β cmp) where
  reprPrec _ _ := Format.nil

end DTreeMap

end Std
