import Proof.MachineModel.NativeFanout
import Proof.MachineModel.Runs
import Proof.MachineModel.OrdinaryMatrixBucketRootPower

/-! The same initialization pass can reload the erased bank on every row.
Padding transport changes neither the physical heads nor the linear fuel. -/
namespace NearCubicWires.ExtIncidence.NativeFanout
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def caps (k m D : ℕ) : Fin (k+(m+1)+1)→ℕ:=
  Fin.addCases (Fin.addCases (fun _ : Fin k=>0)
    (Fin.addCases (fun _ : Fin m=>D) (fun _ : Fin 1=>0))) (fun _ : Fin 1=>D+1)
def reusableInput {k m : ℕ} (data : Fin k→List Bool) (D : ℕ) : Fin (k+(m+1)+1)→List Bool:=
  Fin.addCases (Fin.addCases data (Fin.addCases (fun _ : Fin m=>List.replicate D false)
    (fun _ : Fin 1=>List.replicate D true))) (fun _ : Fin 1=>List.replicate (D+1) false)

theorem reusable {k m : ℕ} (select : Fin m→Option (Fin k)) (data : Fin k→List Bool)
    (D : ℕ) (hD : ∀ i,(data i).length ≤ D) :
    Step (machine select) (2*D+4) (fun _=>0) (reusableInput data D)
      (fun _=>0) (output select data D):=by
  obtain ⟨r,hr,ht,hh,_hs⟩:=ready select data D hD
  have run:=Step.of_run hr (funext hh) ht
  have padded:=run.pad (caps k m D)
  have hi : (fun i=>ZeroPadding.pad (caps k m D i) (input data D i))=reusableInput data D:=by
    funext i
    refine Fin.addCases (m:=k+(m+1)) (n:=1) (fun j=>?_) (fun j=>?_) i
    · refine Fin.addCases (m:=k) (n:=m+1) (fun a=>?_) (fun a=>?_) j
      · simp only [caps,input,reusableInput,Fin.addCases_left,ZeroPadding.pad_zero]
      · refine Fin.addCases (m:=m) (n:=1) (fun a=>?_) (fun a=>?_) a <;>
          simp [caps,input,reusableInput,ZeroPadding.pad]
    · simp [caps,input,reusableInput,ZeroPadding.pad]
  have ho : (fun i=>ZeroPadding.pad (caps k m D i) (output select data D i))=output select data D:=by
    funext i
    refine Fin.addCases (m:=k+(m+1)) (n:=1) (fun j=>?_) (fun j=>?_) i
    · refine Fin.addCases (m:=k) (n:=m+1) (fun a=>?_) (fun a=>?_) j
      · simp only [caps,output,Fin.addCases_left,ZeroPadding.pad_zero]
      · refine Fin.addCases (m:=m) (n:=1) (fun a=>?_) (fun a=>?_) a
        · simp only [caps,output,Fin.addCases_left,Fin.addCases_right]
          exact MatrixBucketRootPower.pad_pad D D _ le_rfl
        · simp only [caps,output,Fin.addCases_left,Fin.addCases_right,ZeroPadding.pad_zero]
    · simp [caps,output,ZeroPadding.pad]
  rw [hi,ho] at padded
  exact padded

end NearCubicWires.ExtIncidence.NativeFanout
