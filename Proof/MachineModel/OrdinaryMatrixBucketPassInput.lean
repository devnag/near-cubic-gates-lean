import Proof.MachineModel.OrdinaryMatrixBucketGatePass

/-! Literal matching of the produced34-tape bank with the cold37-tape
whole bucket pass. The only three additional fields are the retained rank
stream, retained Gates sentinel, and fresh rewind-log tape. -/
namespace NearCubicWires.RepairOrdinary.MatrixBucketPassInput
open LocalBitMultitape MatrixScoreBatch MatrixBatchBucketEndpoints MatrixScoreWeight
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def bank (r : Request) (unused : Fin 3 → List Bool) (i : Fin 34) : List Bool :=
  if i=22 then ZeroPadding.pad (MatrixScoreReusableRanks.D r) (UnaryTemplate.tape r.Buckets)
  else if i=28 then unused 0 else if i=29 then unused 1 else if i=30 then unused 2
  else MatrixBucketScalars.data (MatrixScoreReusableRanks.D r) (H r) r.M (r.bucketSize+1) r.Buckets 6 i
noncomputable def fields (r : Request) (unused : Fin 3 → List Bool) : Fin 37 → List Bool :=
  Fin.addCases (m := 34) (n := 3) (motive := fun _ => List Bool) (bank r unused)
    ![MatrixBatchGateNativeLoop.output r,UnaryTemplate.tape r.Gates,[]]

theorem first_fields (r : Request) (unused : Fin 3 → List Bool) (i : Fin 16) :
    MatrixBucketGatePass.input r unused (i.castAdd 21)=fields r unused (i.castAdd 21) := by
  let D := MatrixScoreReusableRanks.D r
  have hD := MatrixBucketCallBounds.workspace_fit r
  have h1 : 1≤D := by dsimp [D]; omega
  have h2 : 2*H r+1≤D := by dsimp [D]; omega
  have h4 : 4*H r+1≤D := by dsimp [D]; omega
  have h6 : 6*H r+6≤D := by dsimp [D]; omega
  have h8 : 8*H r+3≤D := by dsimp [D]; omega
  have hret : 4*H r+3≤D := by dsimp [D]; omega
  simp only [MatrixBucketGatePass.input,MatrixBucketGateBootstrap.input,MatrixBucketGateBootstrap.target,
    MatrixBucketGateNativeLoop.cfg_tapes,MatrixBucketGateNativeLoop.cold,Nat.zero_mul]
  fin_cases i <;>
    simp [Fin.addCases,Function.update,zeros,fields,bank,MatrixBucketGatePrepare.data,MatrixBucketGatePrepare.native_core,
      MatrixBucketGatePrepare.core,MatrixBucketScalars.data,MatrixBucketWorkspace.output,
      scalar]
  all_goals first
    | exact MatrixBucketBankNative.pad_zeros D 0 (Nat.zero_le _)
    | exact MatrixBucketBankNative.pad_zeros D 1 h1
    | exact MatrixBucketBankNative.pad_zeros D (2*H r+1) h2
    | exact MatrixBucketBankNative.pad_zeros D (4*H r+1) h4
    | exact MatrixBucketBankNative.pad_zeros D (6*H r+6) h6
    | exact MatrixBucketBankNative.pad_zeros D (8*H r+3) h8
    | exact MatrixBucketBankNative.pad_zeros D (24*H r+14) hD

theorem last_fields (r : Request) (unused : Fin 3 → List Bool) (i : Fin 21) :
    MatrixBucketGatePass.input r unused (i.natAdd 16)=fields r unused (i.natAdd 16) := by
  let D := MatrixScoreReusableRanks.D r
  have hD := MatrixBucketCallBounds.workspace_fit r
  have h1 : 1≤D := by dsimp [D]; omega
  have h2 : 2*H r+1≤D := by dsimp [D]; omega
  have h4 : 4*H r+1≤D := by dsimp [D]; omega
  have h6 : 6*H r+6≤D := by dsimp [D]; omega
  have h8 : 8*H r+3≤D := by dsimp [D]; omega
  have hret : 4*H r+3≤D := by dsimp [D]; omega
  simp only [MatrixBucketGatePass.input,MatrixBucketGateBootstrap.input,MatrixBucketGateBootstrap.target,
    MatrixBucketGateNativeLoop.cfg_tapes,MatrixBucketGateNativeLoop.cold,Nat.zero_mul]
  fin_cases i <;>
    simp [Fin.addCases,Function.update,zeros,fields,bank,MatrixBucketGatePrepare.data,MatrixBucketGatePrepare.native_core,
      MatrixBucketGatePrepare.core,MatrixBucketGatePrepare.extra,MatrixBucketScalars.data,MatrixBucketWorkspace.output,
      scalar]
  all_goals first
    | exact MatrixBucketBankNative.pad_zeros D 0 (Nat.zero_le _)
    | exact MatrixBucketBankNative.pad_zeros D 1 h1
    | exact MatrixBucketBankNative.pad_zeros D (2*H r+1) h2
    | exact MatrixBucketBankNative.pad_zeros D (4*H r+1) h4
    | exact MatrixBucketBankNative.pad_zeros D (6*H r+6) h6
    | exact MatrixBucketBankNative.pad_zeros D (8*H r+3) h8
    | exact MatrixBucketBankNative.pad_zeros D (24*H r+14) hD
    | exact MatrixBucketBankNative.pad_zeros D (4*H r+3) hret
    | exact MatrixBucketBankNative.pad_zeros D D (Nat.le_refl _)

theorem input_fields (r : Request) (unused : Fin 3 → List Bool) :
    MatrixBucketGatePass.input r unused=fields r unused := by
  funext i
  exact Fin.addCases (m := 16) (n := 21)
    (motive := fun j => MatrixBucketGatePass.input r unused j=fields r unused j)
    (first_fields r unused) (last_fields r unused) i

theorem bank_fields (r : Request) (out : Fin 34 → List Bool)
    (hfields : ∀ i : Fin 34,i≠22 → i≠28 → i≠29 → i≠30 → out i=
      MatrixBucketScalars.data (MatrixScoreReusableRanks.D r) (H r) r.M (r.bucketSize+1) r.Buckets 6 i)
    (h22 : out 22=ZeroPadding.pad (MatrixScoreReusableRanks.D r) (UnaryTemplate.tape r.Buckets)) :
    out=bank r ![out 28,out 29,out 30] := by
  funext i
  by_cases h : i=22
  · subst i; simpa [bank] using h22
  by_cases h28 : i=28
  · subst i; simp [bank]
  by_cases h29 : i=29
  · subst i; simp [bank]
  by_cases h30 : i=30
  · subst i; simp [bank]
  simpa [bank,h,h28,h29,h30] using hfields i h h28 h29 h30

end NearCubicWires.RepairOrdinary.MatrixBucketPassInput
