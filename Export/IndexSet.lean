/-
Copyright (c) 2026 AlonM. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AlonM
-/
set_option autoImplicit false

universe u

/-!
# Insertion-ordered sets with dense indices

`IndexSet α` numbers distinct values `0, 1, 2, …` in insertion order, the numbering a
`Std.HashMap α Nat` updated with `m.insert x m.size` gives, without a heap allocation per element.
The elements are stored once, in insertion order, in fixed-size chunks, so growing never copies
them as a whole. The hash table is an open-addressing table with linear probing whose slots are
4-byte indices into the elements; it is rebuilt from the elements when it grows, so the old table
is freed before the new one is allocated.

The 4-byte slots limit an `IndexSet` to `maxSize` elements. With 32-bit hashes, as for `Expr`,
the table covers only `2 ^ 32` home slots, so beyond `2 ^ 31` elements probe sequences grow long.
-/

namespace Export

/-- A set that numbers its elements in insertion order. See the module documentation. -/
structure IndexSet (α : Type u) where
  /-- `log2` of the number of elements per chunk. -/
  chunkBits : Nat
  /-- The elements in insertion order, in chunks of `2 ^ chunkBits`. -/
  chunks : Array (Array α)
  /-- The number of elements. -/
  size : Nat
  /--
  The hash table: a power of two number of 4-byte little-endian slots, where `0` is an empty slot
  and `i + 1` refers to the element with index `i`. At most half of the slots are used.
  -/
  slots : ByteArray

namespace IndexSet

variable {α : Type u}

/-- The largest number of elements whose indices fit in a slot. -/
def maxSize : Nat := 2 ^ 32 - 1

/-- `n` empty slots. -/
def zeroSlots (n : Nat) : ByteArray :=
  (4 * n).fold (fun _ _ b => b.push 0) (ByteArray.emptyWithCapacity (4 * n))

/-- An empty set whose elements are stored in chunks of `2 ^ chunkBits`. -/
def empty (chunkBits : Nat := 20) : IndexSet α :=
  ⟨chunkBits, #[], 0, zeroSlots 8⟩

instance : EmptyCollection (IndexSet α) := ⟨empty⟩

instance : Inhabited (IndexSet α) := ⟨empty⟩

/-- The number of slots of a table. -/
@[inline] def numSlots (slots : @& ByteArray) : Nat :=
  slots.size / 4

/-- The value of slot `i`. -/
@[inline] def getSlot (slots : @& ByteArray) (i : Nat) : Nat :=
  let o := 4 * i
  ((slots.get! o).toUInt32 ||| (slots.get! (o + 1)).toUInt32 <<< 8 |||
    (slots.get! (o + 2)).toUInt32 <<< 16 ||| (slots.get! (o + 3)).toUInt32 <<< 24).toNat

/-- Sets slot `i` to `v < 2 ^ 32`. -/
@[inline] def setSlot (slots : ByteArray) (i v : Nat) : ByteArray :=
  let o := 4 * i
  let v := v.toUInt32
  let slots := slots.set! o v.toUInt8
  let slots := slots.set! (o + 1) (v >>> 8).toUInt8
  let slots := slots.set! (o + 2) (v >>> 16).toUInt8
  slots.set! (o + 3) (v >>> 24).toUInt8

/--
The first slot to probe. Mixes the high bits of the hash into the low ones, as `Std.HashMap` does.
-/
@[inline] def homeSlot (hash : UInt64) (mask : Nat) : Nat :=
  let h := hash ^^^ (hash >>> 32)
  ((h ^^^ (h >>> 16)) &&& mask.toUInt64).toNat

/-- The element with index `i < s.size`. -/
@[inline] def get! [Inhabited α] (s : @& IndexSet α) (i : Nat) : α :=
  s.chunks[i >>> s.chunkBits]![i &&& ((1 <<< s.chunkBits) - 1)]!

/-!
The probe loops terminate because at least half of the slots are empty.
-/

/-- The first empty slot at or after `i`. -/
partial def emptySlotFrom (slots : @& ByteArray) (mask i : Nat) : Nat :=
  if getSlot slots i == 0 then i else emptySlotFrom slots mask ((i + 1) &&& mask)

/-- The first slot at or after `i` that is empty or refers to an element equal to `x`. -/
@[specialize] partial def findSlotFrom [BEq α] [Inhabited α] (s : @& IndexSet α) (x : @& α)
    (mask i : Nat) : Nat :=
  let v := getSlot s.slots i
  if v == 0 || s.get! (v - 1) == x then i else findSlotFrom s x mask ((i + 1) &&& mask)

/-- The index of the element equal to `x`, if any. -/
@[specialize] def find? [BEq α] [Hashable α] [Inhabited α] (s : @& IndexSet α) (x : @& α) :
    Option Nat :=
  let mask := numSlots s.slots - 1
  let v := getSlot s.slots (findSlotFrom s x mask (homeSlot (hash x) mask))
  if v == 0 then none else some (v - 1)

/-- Sets the first empty slot of the probe sequence of `hash` to `v`. -/
@[inline] def setEmptySlot (slots : ByteArray) (hash : UInt64) (v : Nat) : ByteArray :=
  let mask := numSlots slots - 1
  setSlot slots (emptySlotFrom slots mask (homeSlot hash mask)) v

/-- A table of `numSlots` slots for the elements in `chunks`. -/
@[specialize] def rebuild [Hashable α] (chunks : @& Array (Array α)) (numSlots : Nat) :
    ByteArray := Id.run do
  let mut slots := zeroSlots numSlots
  let mut idx := 0
  for chunk in chunks do
    for x in chunk do
      idx := idx + 1
      slots := setEmptySlot slots (hash x) idx
  return slots

/--
Adds `x` with index `s.size`. If `x` is already in `s`, `find?` keeps returning its first index.
Panics if `s.size = maxSize`.
-/
@[specialize] def push [Hashable α] (s : IndexSet α) (x : α) : IndexSet α :=
  -- Destructuring keeps `slots` and `chunks` unshared so that they are updated in place.
  let ⟨chunkBits, chunks, size, slots⟩ := s
  if size ≥ maxSize then
    panic! "IndexSet.push: too many elements"
  else
    let n := numSlots slots
    -- When the table grows, `slots` is dead before `rebuild` allocates its replacement.
    let slots := if 2 * (size + 1) > n then rebuild chunks (2 * n) else slots
    let slots := setEmptySlot slots (hash x) (size + 1)
    let chunks :=
      if size &&& ((1 <<< chunkBits) - 1) == 0 then
        chunks.push ((Array.emptyWithCapacity (1 <<< chunkBits)).push x)
      else
        chunks.modify (chunks.size - 1) (·.push x)
    ⟨chunkBits, chunks, size + 1, slots⟩

end IndexSet

end Export
