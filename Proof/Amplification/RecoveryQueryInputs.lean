import Proof.Amplification.RecoveryQueryLayout

/-! Exact prepared operands of the nine-node prefix-query spine. The
separate cold preparation must physically produce this endpoint. -/
namespace NearCubicWires.RepairOrdinary.RecoveryQueryKernel
open LocalBitMultitape RecoveryExecution RecoveryRootRound RepairSource.RecoveryQuery
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def prepared (cap : Nat) (flat : Bool) (payload committed count : Nat)
    (original : Fin 357→List Bool) : Fin 357→List Bool := fun i =>
  if i.val<5 then original i
  else if i=bank 0 2 then ZeroPadding.pad cap (frame (1 : Nat).bits)
  else if i=bank 0 3 then ZeroPadding.pad cap (frame count.bits)
  else if i=bank 2 3 then ZeroPadding.pad cap (frame committed.bits)
  else if i=bank 5 2 then ZeroPadding.pad cap (frame flat.toNat.bits)
  else if i=bank 5 3 then ZeroPadding.pad cap (frame payload.bits)
  else List.replicate cap false

theorem bank_eq (k l : Fin 9) (i j : Fin 39) : bank k i=bank l j ↔ k=l ∧ i=j := by
  constructor
  · intro h
    have hv := congrArg (fun x : Fin 357 => x.val) h
    dsimp [bank] at hv
    have hi := i.isLt
    have hj := j.isLt
    constructor <;> apply Fin.ext <;> omega
  · rintro ⟨rfl,rfl⟩
    rfl

theorem prepared_bank (cap : Nat) (flat : Bool) (payload committed count : Nat)
    (original : Fin 357→List Bool) (k : Fin 9) (i : Fin 39) :
    prepared cap flat payload committed count original (bank k i)=
      if k.val=0 ∧ i.val=2 then ZeroPadding.pad cap (frame (1 : Nat).bits)
      else if k.val=0 ∧ i.val=3 then ZeroPadding.pad cap (frame count.bits)
      else if k.val=2 ∧ i.val=3 then ZeroPadding.pad cap (frame committed.bits)
      else if k.val=5 ∧ i.val=2 then ZeroPadding.pad cap (frame flat.toNat.bits)
      else if k.val=5 ∧ i.val=3 then ZeroPadding.pad cap (frame payload.bits)
      else List.replicate cap false := by
  have hz : ¬(bank k i).val<5 := by dsimp [bank]; omega
  simp only [prepared,hz,if_false,bank_eq]
  simp only [Fin.ext_iff]
  rfl

theorem padded_zero (cap : Nat) (hc : 1 ≤ cap) :
    ZeroPadding.pad cap (frame (0 : Nat).bits)=List.replicate cap false := by
  change [false]++List.replicate (cap-1) false=List.replicate cap false
  rw [show [false]=List.replicate 1 false by rfl,←List.replicate_add]
  congr 1
  omega

def stage (cap : Nat) (flat : Bool) (payload committed count : Nat)
    (original : Fin 357→List Bool) (outs : Fin 9→Fin 39→List Bool) : Nat→Fin 357→List Bool
  | 0 => prepared cap flat payload committed count original
  | k+1 => install (cellSlots ⟨k%9,Nat.mod_lt _ (by decide)⟩)
      (stage cap flat payload committed count original outs k)
      (outs ⟨k%9,Nat.mod_lt _ (by decide)⟩)

theorem stage_bank (cap : Nat) (flat : Bool) (payload committed count : Nat)
    (original : Fin 357→List Bool) (outs : Fin 9→Fin 39→List Bool)
    (n : Nat) (k : Fin 9) (i : Fin 39) (hn : n ≤ k.val) :
    stage cap flat payload committed count original outs n (bank k i)=
      prepared cap flat payload committed count original (bank k i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hmod : n%9=n := Nat.mod_eq_of_lt (by have hk := k.isLt; omega)
    rw [stage,install_above _ _ _ _ (by dsimp [bank]; rw [hmod]; omega)]
    exact ih (by omega)

theorem stage_small (cap : Nat) (flat : Bool) (payload committed count : Nat)
    (original : Fin 357→List Bool) (outs : Fin 9→Fin 39→List Bool)
    (n : Nat) (i : Fin 357) (hi : i.val<5) :
    stage cap flat payload committed count original outs n i=original i := by
  induction n with
  | zero => simp [stage,prepared,hi]
  | succ n ih => rw [stage,install_small _ _ _ i hi,ih]

end
end NearCubicWires.RepairOrdinary.RecoveryQueryKernel
