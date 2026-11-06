import Std.Tactic.BVDecide

def ByteArray.getUInt64BEfrom (bs : ByteArray) (offset : Nat) (h: bs.size - offset ≥ 8) : UInt64 :=
  (bs.get (offset + 0) (by omega)).toUInt64 <<< 0x38 |||
  (bs.get (offset + 1) (by omega)).toUInt64 <<< 0x30 |||
  (bs.get (offset + 2) (by omega)).toUInt64 <<< 0x28 |||
  (bs.get (offset + 3) (by omega)).toUInt64 <<< 0x20 |||
  (bs.get (offset + 4) (by omega)).toUInt64 <<< 0x18 |||
  (bs.get (offset + 5) (by omega)).toUInt64 <<< 0x10 |||
  (bs.get (offset + 6) (by omega)).toUInt64 <<< 0x08 |||
  (bs.get (offset + 7) (by omega)).toUInt64


def UInt64.getBytesBEfrom (i : UInt64) : ByteArray :=
  ⟨#[ (i >>> 0x38).toUInt8
    , (i >>> 0x30).toUInt8
    , (i >>> 0x28).toUInt8
    , (i >>> 0x20).toUInt8
    , (i >>> 0x18).toUInt8
    , (i >>> 0x10).toUInt8
    , (i >>> 0x8).toUInt8
    , (i >>> 0x0).toUInt8
    ]⟩

def ByteArray.getUInt32BEfrom (bs : ByteArray) (offset : Nat) (h: bs.size - offset ≥ 4) : UInt32 :=
  (bs.get (offset + 0) (by omega)).toUInt32 <<< 0x18 |||
  (bs.get (offset + 1) (by omega)).toUInt32 <<< 0x10 |||
  (bs.get (offset + 2) (by omega)).toUInt32 <<< 0x08 |||
  (bs.get (offset + 3) (by omega)).toUInt32

def UInt32.getBytesBEfrom (i : UInt32) : ByteArray :=
  ⟨#[ (i >>> 0x18).toUInt8
    , (i >>> 0x10).toUInt8
    , (i >>> 0x8).toUInt8
    , (i >>> 0x0).toUInt8
    ]⟩

def ByteArray.getUInt16BEfrom (bs : ByteArray) (offset : Nat) (h: bs.size - offset ≥ 2) : UInt16 :=
  (bs.get (offset + 0) (by omega)).toUInt16 <<< 0x08 |||
  (bs.get (offset + 1) (by omega)).toUInt16

def UInt16.getBytesBEfrom (i : UInt16) : ByteArray :=
  ⟨#[ (i >>> 0x8).toUInt8
    , (i >>> 0x0).toUInt8
    ]⟩

--LittleEndian

def ByteArray.getUInt64LEfrom (bs : ByteArray) (offset : Nat) (h: bs.size - offset ≥ 8) : UInt64 :=
  (bs.get (offset + 7) (by omega)).toUInt64 <<< 0x38 |||
  (bs.get (offset + 6) (by omega)).toUInt64 <<< 0x30 |||
  (bs.get (offset + 5) (by omega)).toUInt64 <<< 0x28 |||
  (bs.get (offset + 4) (by omega)).toUInt64 <<< 0x20 |||
  (bs.get (offset + 3) (by omega)).toUInt64 <<< 0x18 |||
  (bs.get (offset + 2) (by omega)).toUInt64 <<< 0x10 |||
  (bs.get (offset + 1) (by omega)).toUInt64 <<< 0x08 |||
  (bs.get (offset + 0) (by omega)).toUInt64

def UInt64.getBytesLEfrom (i : UInt64) : ByteArray :=
  ⟨#[ (i >>> 0x00).toUInt8
    , (i >>> 0x8).toUInt8
    , (i >>> 0x10).toUInt8
    , (i >>> 0x18).toUInt8
    , (i >>> 0x20).toUInt8
    , (i >>> 0x28).toUInt8
    , (i >>> 0x30).toUInt8
    , (i >>> 0x38).toUInt8
    ]⟩

def ByteArray.getUInt32LEfrom (bs : ByteArray) (offset : Nat) (h: bs.size - offset ≥ 4) : UInt32 :=
  (bs.get (offset + 3) (by omega)).toUInt32 <<< 0x18 |||
  (bs.get (offset + 2) (by omega)).toUInt32 <<< 0x10 |||
  (bs.get (offset + 1) (by omega)).toUInt32 <<< 0x08 |||
  (bs.get (offset + 0) (by omega)).toUInt32

def UInt32.getBytesLEfrom (i : UInt32) : ByteArray :=
  ⟨#[ (i >>> 0x00).toUInt8
    , (i >>> 0x8).toUInt8
    , (i >>> 0x10).toUInt8
    , (i >>> 0x18).toUInt8
    ]⟩

def ByteArray.getUInt16LEfrom (bs : ByteArray) (offset : Nat) (h: bs.size - offset ≥ 2) : UInt16 :=
  (bs.get (offset + 1) (by omega)).toUInt16 <<< 0x08 |||
  (bs.get (offset + 0) (by omega)).toUInt16

def UInt16.getBytesLEfrom (i : UInt16) : ByteArray :=
  ⟨#[ (i >>> 0x00).toUInt8
    , (i >>> 0x8).toUInt8
    ]⟩

/- An alternative approach is to define a byte parsing monad, à la:

https://github.com/risc0/risc0-lean4/blob/31c956fc9246bbfc84359021d66ed94972afd86b/R0sy/ByteDeserial.lean

And just have some runtime error possibilities, rather than proof obligations.
-/

def ByteArray.getEntriesFrom
  (bs : ByteArray)
  (offset : Nat)
  (num : Nat)
  (entsize : Nat)
  (entreq : Nat)
  (suffSize : entsize ≥ entreq)
  (spaceAvail : bs.size ≥ offset + num * entsize)
  (toEnt :  (offset₂ : Nat) → (bs.size - offset₂ ≥ entreq) → α)
  : List α := recur num [] (by omega)
  where recur (idx : Nat) acc (h₁ : idx ≤ num) : List α
  := match idx with
    | 0 => acc
    | i + 1 =>
      let ent := toEnt (offset + (i * entsize)) $ by
        have h₂ : num * entsize ≥ i * entsize + entsize := by
          conv => rhs; rw [Nat.mul_comm]
          rw [←Nat.mul_succ]
          conv => rhs; rw [Nat.mul_comm]
          exact Nat.mul_le_mul_right entsize h₁
        omega
      recur i (ent :: acc) (by omega)

structure NByteArray (n : Nat) where
  bytes: ByteArray
  sized: bytes.size = n

def NByteArray.get {n : Nat} (bs : NByteArray n) (m: Nat) (p: m < n) :=
  have size := bs.sized
  bs.bytes.get (m) (by omega)

instance : Repr (NByteArray n) where
  reprPrec nbs := reprPrec $ nbs.bytes.toList.map λbyte ↦
    Nat.toDigits 16 byte.toNat
    |> (λl ↦ if l.length == 1 then '0' :: l else l)
    |> String.ofList

instance : Repr ByteArray where
  reprPrec nbs := reprPrec $ nbs.data.toList.map λbyte ↦
    Nat.toDigits 16 byte.toNat
    |> (λl ↦ if l.length == 1 then '0' :: l else l)
    |> String.ofList

/-

 These are some simple theorems related to Arrays and ByteArrays. They start
 from the function Array.extract.loop, associated with Array.extract:

 https://github.com/leanprover/lean4/blob/6fce8f7d5cd18a4419bca7fd51780c71c9b1cc5a/src/Init/Prelude.lean#L2722

 `Array.extract.loop src i j dst` essentially returns dst if i is 0 or
 j ≥ src.size, and otherwise calls itself as `Array.extract.loop src (i - 1) (j
 + 1) (dst ++ src[j])`.

 Some things it would be nice to prove, since it would give us an instance of

 https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Defs.html#AddCancelMonoid

 ∀{a b: ByteArray}, (a ++ b).size = a.size + b.size
 ∀{a b c: ByteArray}, a ++ b = c ++ b ↔ a = c
 ∀{a b c: ByteArray}, a ++ b = a ++ c ↔ b = c
 ∀{a b c: ByteArray}, (a ++ b) ++ c = a ++ (b ++ c)
 ∀{a: ByteArray}, a ++ ByteArray.empty = a
 ∀{a: ByteArray}, ByteArray.empty ++ a = a

 It would also be good to improve NByteArray extract to take an offset in addition to a length

-/

def NByteArray.extract (bs : ByteArray) (n : Nat) (h : bs.size ≥ n) : NByteArray n :=
  let bytes := bs.extract 0 n
  let proof : bytes.size = n := by
    simp only [bytes, ByteArray.size_extract]
    omega
  ⟨bytes, proof⟩

/-
  Byte-level round-trip facts for the unsigned integer types. Since the
  fixed-width unsigned integers are represented by bitvectors, these are
  discharged by `bv_decide`.
-/

theorem UInt16.ByteArray_size : ∀ i : UInt16, i.getBytesBEfrom.size = 2 := by
  intro i
  simp [UInt16.getBytesBEfrom, ByteArray.size]

theorem UInt8_to_UInt16_round: ∀{i : UInt8}, i.toUInt16.toUInt8 = i := by
  intro i; bv_decide

theorem UInt16_to_UInt8_round: ∀{i : UInt16}, i.toUInt8.toUInt16 = i % 256 := by
  intro i; bv_decide

theorem UInt16.nullShift : ∀{i : UInt16}, i >>> 0 = i := by
  intro i; bv_decide

@[simp]
theorem UInt16.byteCeiling : ∀(i : UInt16), (i >>> 0x8) % (256 : UInt16) = i >>> 0x8 := by
  intro i; bv_decide

theorem UInt16.shiftUnshift : ∀(i  : UInt16), i = (i >>> 0x8 % 256) <<< 0x8 ||| i % 256 := by
  intro i; bv_decide

theorem UInt32.shiftUnshift : ∀(i  : UInt32),
  i = (i >>> 0x18 % 256) <<< 0x18 |||
      (i >>> 0x10 % 256) <<< 0x10 |||
      (i >>> 0x08 % 256) <<< 0x08 |||
      i % 256 := by
  intro i; bv_decide

theorem UInt64.shiftUnshift : ∀(i  : UInt64),
  i = (i >>> 0x38 % 256) <<< 0x38 |||
      (i >>> 0x30 % 256) <<< 0x30 |||
      (i >>> 0x28 % 256) <<< 0x28 |||
      (i >>> 0x20 % 256) <<< 0x20 |||
      (i >>> 0x18 % 256) <<< 0x18 |||
      (i >>> 0x10 % 256) <<< 0x10 |||
      (i >>> 0x08 % 256) <<< 0x08 |||
      i % 256 := by
  intro i; bv_decide

theorem UInt16.ByteArray_roundtrip :
  ∀ i : UInt16, ∀l, i.getBytesBEfrom.getUInt16BEfrom 0 l = i := by
  intro i l
  simp only [UInt16.getBytesBEfrom, ByteArray.getUInt16BEfrom, ByteArray.get]
  simp
  bv_decide
