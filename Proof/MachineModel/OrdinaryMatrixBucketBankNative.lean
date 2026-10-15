import Proof.MachineModel.OrdinaryMatrixBatchBucketBank
import Proof.MachineModel.OrdinaryKeyBuckets

/-! The produced scalar bank is exactly the ordinary bucket machine's
native entry storage, with finite paid zero padding on every work tape. -/
namespace NearCubicWires.RepairOrdinary.MatrixBucketBankNative
open LocalBitMultitape SignedSortKey MatrixScoreWeight
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem config_tapes {s : ℕ} (q : Fin s) (H M B count D : ℕ) :
    (KeyBucketLoop.config q H 0 B 0 [] [] [] false [] [] M M 0 D D 1 count).tapes=
      ![frame (binary H 0),frame (binary H B),[],List.replicate (2*H+1) false,
        frame (binary H 0),[false],[false],List.replicate (6*H+6) false,[],[],[],
        List.replicate (4*H+1) false,List.replicate (8*H+3) false,List.replicate (2*H+1) false,
        List.replicate (24*H+14) false,[],frame (binary M 0),frame (binary M 0),frame (binary M 0),
        List.replicate D false,List.replicate D false,List.replicate (4*H+3) false,UnaryTemplate.tape count] := by
  funext i
  fin_cases i <;> rfl

theorem pad_zeros (D n : ℕ) (hn : n ≤ D) :
    ZeroPadding.pad D (List.replicate n false)=List.replicate D false := by
  simp [ZeroPadding.pad,Nat.add_sub_of_le hn]

theorem cold_tapes {s : ℕ} (q : Fin s) (D H M B count : ℕ) (hD : 24*H+14 ≤ D) :
    (ZeroPadding.config (fun _ : Fin 23 => D)
      (KeyBucketLoop.config q H 0 B 0 [] [] [] false [] [] M M 0 D D 1 count)).tapes=
      fun i : Fin 23 => if i=22 then ZeroPadding.pad D (UnaryTemplate.tape count)
        else MatrixBucketScalars.data D H M B count 6 (i.castAdd 11) := by
  simp only [ZeroPadding.config,config_tapes]
  have h1 : 1 ≤ D := by omega
  have h2 : 2*H+1 ≤ D := by omega
  have h4 : 4*H+1 ≤ D := by omega
  have h6 : 6*H+6 ≤ D := by omega
  have h8 : 8*H+3 ≤ D := by omega
  have hret : 4*H+3 ≤ D := by omega
  funext i
  fin_cases i <;> simp [MatrixBucketScalars.data,MatrixBucketWorkspace.output,scalar,
    pad_zeros D (2*H+1) h2,pad_zeros D (4*H+1) h4,
    pad_zeros D (6*H+6) h6,pad_zeros D (8*H+3) h8,pad_zeros D (24*H+14) hD,
    pad_zeros D (4*H+3) hret,pad_zeros D D (Nat.le_refl _)]
  all_goals first | exact pad_zeros D 0 (Nat.zero_le _) | exact pad_zeros D 1 h1

end NearCubicWires.RepairOrdinary.MatrixBucketBankNative
