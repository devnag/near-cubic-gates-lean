import Proof.Supplier.RowPowerNativeEndpoint

/-! The appended P/N blocks denote signed radix digits, including the native
zero convention. Concatenation computes the integer Horner stack directly. -/
namespace NearCubicWires.RepairOrdinary.RowPowerNativeReusable
open LocalBitMultitape RepairRepresentation SignedSortKey RadixSemantics
open Streaming
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem native_resize (w : ℕ) (z : ℤ) (hw : natBitLength z.natAbs≤w) :
    ClockNormalize.resize w (binary (natBitLength z.natAbs) z.natAbs)=binary w z.natAbs := by
  rw [ClockScalarFields.resize_binary w _ (by simpa using hw)]
  rw [binary_value (natBitLength z.natAbs) z.natAbs (Nat.lt_pow_succ_log_self (by decide) _)]

theorem digits_same (sign : Bool) (bits : List Bool) : RowPowerBlock.digits sign sign bits=bits := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simpa [RowPowerBlock.digits,RowPowerBlock.part] using congrArg (List.cons b) ih
theorem digits_other (a b : Bool) (bits : List Bool) (hab : a≠b) :
    RowPowerBlock.digits a b bits=List.replicate bits.length false := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
    cases a <;> cases b <;> simp_all [RowPowerBlock.digits,RowPowerBlock.part,List.replicate_succ]

theorem block_binary (w : ℕ) (z : ℤ) (hw : natBitLength z.natAbs≤w) :
    block w z false=binary w z.toNat ∧ block w z true=binary w (-z).toNat := by
  unfold block
  rw [native_resize w z hw]
  cases z with
  | ofNat n =>
    have hs : decide ((Int.ofNat n)<0)=false := by simp
    rw [hs,digits_same,digits_other true false _ (by decide),binary_length]
    simp [RankCarrier.binary_zero]
  | negSucc n =>
    simp only [Int.negSucc_lt_zero,decide_true,Int.natAbs_negSucc,Int.toNat_negSucc,
      Int.neg_negSucc,Int.toNat_natCast,digits_same]
    rw [digits_other false true _ (by decide),binary_length,RankCarrier.binary_zero]
    trivial

theorem block_value (w : ℕ) (z : ℤ) (hw : natBitLength z.natAbs≤w) :
    (value (block w z false) : ℤ)-(value (block w z true) : ℤ)=z := by
  have hfit : z.natAbs<2^w :=
    (Nat.lt_pow_succ_log_self (by decide : 1<2) z.natAbs).trans_le
      (Nat.pow_le_pow_right (by decide) hw)
  have hb := block_binary w z hw
  have hp : z.toNat≤z.natAbs := by cases z <;> simp
  have hn : (-z).toNat≤z.natAbs := by cases z <;> simp
  rw [hb.1,hb.2,binary_value _ _ (hp.trans_lt hfit),binary_value _ _ (hn.trans_lt hfit)]
  omega

def blocks (w : ℕ) (negative : Bool) (zs : List ℤ) := zs.flatMap (fun z => block w z negative)
def horner (base : ℤ) : List ℤ → ℤ
  | [] => 0
  | z::zs => z+base*horner base zs

theorem blocks_length (w : ℕ) (negative : Bool) (zs : List ℤ) :
    (blocks w negative zs).length=w*zs.length := by
  induction zs with
  | nil => simp [blocks]
  | cons z zs ih =>
    simp only [blocks,List.flatMap_cons,List.length_append,block_length,List.length_cons]
    change w+(blocks w negative zs).length=w*(zs.length+1)
    rw [ih]
    ring

theorem blocks_value (w : ℕ) (zs : List ℤ) (hw : ∀ z∈zs,natBitLength z.natAbs≤w) :
    (value (blocks w false zs) : ℤ)-(value (blocks w true zs) : ℤ)=horner ((2 : ℤ)^w) zs := by
  induction zs with
  | nil => simp [blocks,value,horner]
  | cons z zs ih =>
    have hz := block_value w z (hw z (by simp))
    have ht := ih (fun a ha => hw a (by simp [ha]))
    simp only [blocks,List.flatMap_cons,value_append,block_length,Nat.cast_add,Nat.cast_mul,
      Nat.cast_pow,Nat.cast_ofNat,horner]
    change (value (block w z false) : ℤ)+(2 : ℤ)^w*value (blocks w false zs)-
      ((value (block w z true) : ℤ)+(2 : ℤ)^w*value (blocks w true zs))=_
    rw [show (value (block w z false) : ℤ)+(2 : ℤ)^w*value (blocks w false zs)-
      ((value (block w z true) : ℤ)+(2 : ℤ)^w*value (blocks w true zs))=
      ((value (block w z false) : ℤ)-value (block w z true))+
        (2 : ℤ)^w*((value (blocks w false zs) : ℤ)-value (blocks w true zs)) by ring,hz,ht]

end NearCubicWires.RepairOrdinary.RowPowerNativeReusable
