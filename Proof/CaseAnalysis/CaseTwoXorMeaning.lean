import Proof.CaseAnalysis.CaseTwoAddressMeaning
import Proof.CaseAnalysis.CaseTwoFixedFoldRun

/-! The checked fixed controller folds exactly the paper's XOR power. This
is the finite-order argument, without importing a symbolic program model. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.FixedFold
open SourceInterfaces RecoveryPipeline
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

private instance : RightCommutative (xor : Bool→Bool→Bool):=⟨by decide⟩
theorem value_range (bit : ℕ→Bool) (n : ℕ) :
    value bit n=((List.range n).map bit).foldl xor false:=by
  induction n with
  | zero=>rfl
  | succ n ih=>
    rw [value,ih,List.range_succ,List.map_append,List.foldl_append]
    rfl
theorem value_xor {arity copies : ℕ} (seed : BoolFunction arity) (point : BitInput (copies*arity))
    (bit : ℕ→Bool) (hb : ∀ block : Fin copies,bit block.val=seed (blockInput point block)) :
    value bit copies=xorPower seed copies point:=by
  have hrange : (List.range copies).map bit=
      (List.finRange copies).map (fun block : Fin copies=>seed (blockInput point block)):=by
    rw [←List.map_coe_finRange_eq_range,List.map_map]
    exact List.map_congr_left (fun block _=>hb block)
  have hu : ((Finset.univ : Finset (Fin copies)).toList).Perm (List.finRange copies):=
    (List.perm_ext_iff_of_nodup (Finset.nodup_toList _) (List.nodup_finRange copies)).mpr (by intro b;simp)
  have hp:=(hu.map (fun block : Fin copies=>seed (blockInput point block))).symm
  rw [value_range,hrange,hp.foldl_eq false,xorPower,List.foldl_map]
theorem block_field {arity copies target : ℕ} (point : BitInput target) (block : Fin copies) :
    blockInput (AddressWindow.field point 0 (copies*arity)) block=
      AddressWindow.field point (block.val*arity) arity:=by
  funext i
  simp only [blockInput,AddressWindow.field,Nat.zero_add]
theorem padded_xor {arity copies target : ℕ} (seed : BoolFunction arity) (point : BitInput target)
    (hfit : copies*arity≤target) (bit : ℕ→Bool)
    (hb : ∀ block : Fin copies,bit block.val=seed (AddressWindow.field point (block.val*arity) arity)) :
    value bit copies=padCore (xorPower seed copies) hfit point:=by
  have hv:=value_xor seed (AddressWindow.field point 0 (copies*arity)) bit (by
    intro block
    rw [block_field point]
    exact hb block)
  have hi : (fun i : Fin (copies*arity)=>point ((finSplitEquiv hfit) (.inl i)))=
      AddressWindow.field point 0 (copies*arity):=by
    funext i
    have hbnd : i.val<target:=i.isLt.trans_le hfit
    simp [finSplitEquiv,AddressWindow.field,AddressWindow.read,hbnd]
    apply congrArg point
    apply Fin.ext
    rfl
  rw [padCore,hi]
  exact hv

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.FixedFold
