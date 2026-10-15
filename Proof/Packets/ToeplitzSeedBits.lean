import Proof.Supplier.SupplierWalkBridge
import Proof.MachineModel.OrdinarySignedSortKey

/-! Literal bit addresses of the original Toeplitz walk encoding. The padding
coordinate is the low part of finProdFinEquiv, so physical decoding must discard
its low bits before splitting lower/upper/translation fields. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Completion.ToeplitzSeedBits
open NearCubicWires NearCubicWires.SupplierWalkBridge NearCubicWires.SupplierToeplitzCore
open NearCubicWires.SourceInterfaces NearCubicWires.RepairOrdinary

def padding (rank : Nat):=2*toeplitzWalkSideBits rank-toeplitzSeedBits rank
def vertexCode (rank : Nat) (v : MargulisVertex (2^toeplitzWalkSideBits rank)):=
  v.2.val+2^toeplitzWalkSideBits rank*v.1.val
def seedCode (rank : Nat) (v : MargulisVertex (2^toeplitzWalkSideBits rank)):=vertexCode rank v/2^padding rank

theorem finEquiv_symm_val {n : Nat} [NeZero n] (x : ZMod n) :
    ((ZMod.finEquiv n).symm x).val=x.val := by
  cases n with
  | zero => exact False.elim (NeZero.ne 0 rfl)
  | succ n => rfl

theorem lower_value (rank : Nat) (v : MargulisVertex (2^toeplitzWalkSideBits rank)) (i : Fin rank):
    (toeplitzWalkEncoding rank v).1.1.1 i=
      ((seedCode rank v/2^i.val%2 : Nat) : ZMod 2):=by
  apply Fin.ext
  simp [toeplitzWalkEncoding,toeplitzSeedBitEquiv,binaryFunctionFinEquiv,seedCode,vertexCode,padding,finProdFinEquiv,finFunctionFinEquiv]
  simp only [finEquiv_symm_val]
  rfl

theorem upper_value (rank : Nat) (v : MargulisVertex (2^toeplitzWalkSideBits rank)) (i : Fin (rank-1)):
    (toeplitzWalkEncoding rank v).1.1.2 i=
      ((seedCode rank v/2^(rank+i.val)%2 : Nat) : ZMod 2):=by
  apply Fin.ext
  simp [toeplitzWalkEncoding,toeplitzSeedBitEquiv,binaryFunctionFinEquiv,seedCode,vertexCode,padding,finProdFinEquiv,finFunctionFinEquiv]
  simp only [finEquiv_symm_val]
  rfl

theorem translation_value (rank : Nat) (v : MargulisVertex (2^toeplitzWalkSideBits rank)) (i : Fin rank):
    (toeplitzWalkEncoding rank v).1.2 i=
      ((seedCode rank v/2^(rank+(rank-1)+i.val)%2 : Nat) : ZMod 2):=by
  apply Fin.ext
  simp [toeplitzWalkEncoding,toeplitzSeedBitEquiv,binaryFunctionFinEquiv,seedCode,vertexCode,padding,finProdFinEquiv,finFunctionFinEquiv]
  simp only [finEquiv_symm_val]
  rfl

end Completion.ToeplitzSeedBits
