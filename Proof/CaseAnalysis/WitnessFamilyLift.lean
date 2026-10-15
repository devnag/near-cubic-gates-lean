import Proof.CaseAnalysis.WitnessFamilyMeaning

/-! Generic retained-tape lifting keeps the enclosing source state count
opaque while proving the three exact unused-bank projections. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ColdFamilyLift
open LocalBitMultitape RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine (E : ℕ) {t s : ℕ} (p : Machine t s):=
  TapeEmbedding.machine FamilyCold.Call.extra (TapeEmbedding.machine (FamilyCapacity.Call.extra E) (TapeEmbedding.machine 1 p))
def receipt (E : ℕ) {t s : ℕ} (bits : List Bool) (r : ExecutionReceipt t s):=
  TapeEmbedding.receipt (fun _ : Fin FamilyCold.Call.extra=>0) (fun _=>[])
    (TapeEmbedding.receipt (fun _ : Fin (FamilyCapacity.Call.extra E)=>0) (fun _=>[])
      (TapeEmbedding.receipt (fun _ : Fin 1=>0) (fun _=>frame bits) r))
def old (E : ℕ) {t : ℕ} (i : Fin t):=
  FamilyCold.Call.old (FamilyCapacity.Call.old E (i.castAdd 1))

theorem heads_old (E : ℕ) {t s : ℕ} (bits : List Bool) (r : ExecutionReceipt t s) (i : Fin t) :
    (receipt E bits r).final.heads (old E i)=r.final.heads i:=by
  simp only [receipt,old,FamilyCold.Call.old,FamilyCapacity.Call.old,TapeEmbedding.receipt_heads_old]
theorem tapes_old (E : ℕ) {t s : ℕ} (bits : List Bool) (r : ExecutionReceipt t s) (i : Fin t) :
    (receipt E bits r).final.tapes (old E i)=r.final.tapes i:=by
  simp only [receipt,old,FamilyCold.Call.old,FamilyCapacity.Call.old,TapeEmbedding.receipt_tapes_old]

theorem heads_new (E : ℕ) {t s : ℕ} (bits : List Bool) (r : ExecutionReceipt t s) (i : Fin 3243) :
    (receipt E bits r).final.heads (i.natAdd (t+1+FamilyCapacity.Call.extra E))=0:=by
  simp only [receipt,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_right]
theorem tapes_new (E : ℕ) {t s : ℕ} (bits : List Bool) (r : ExecutionReceipt t s) (i : Fin 3243) :
    (receipt E bits r).final.tapes (i.natAdd (t+1+FamilyCapacity.Call.extra E))=[]:=by
  simp only [receipt,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_right]

theorem run_lift (E : ℕ) {t s : ℕ} (p : Machine t s) (fuel : ℕ) (data : Fin t→List Bool)
    (bits : List Bool) (r : ExecutionReceipt t s) (hr : run p fuel data=some r) :
    run (machine E p) fuel (FamilyFromPolicy.input E
      (Fin.addCases (m:=t) (n:=1) (motive:=fun _=>List Bool) data (fun _=>frame bits)))=
      some (receipt E bits r):=by
  have one:=TapeEmbedding.run_embed p (fun _ : Fin 1=>0) (fun _=>frame bits) _ _ r hr
  rw [StreamPrepare.embed_initial] at one
  have two:=TapeEmbedding.run_embed (TapeEmbedding.machine 1 p)
    (fun _ : Fin (FamilyCapacity.Call.extra E)=>0) (fun _=>[]) _ _ _ one
  rw [StreamPrepare.embed_initial] at two
  have three:=TapeEmbedding.run_embed (TapeEmbedding.machine (FamilyCapacity.Call.extra E) (TapeEmbedding.machine 1 p))
    (fun _ : Fin FamilyCold.Call.extra=>0) (fun _=>[]) _ _ _ two
  rw [StreamPrepare.embed_initial] at three
  exact three

end NearCubicWires.RepairOrdinary.CloseoutWitness.ColdFamilyLift
