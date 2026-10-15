import Proof.MachineModel.CleanPorts

/-! The reusable occurrence-loop state has one source bank, twelve named
ports and the paid masked-return log. No source output is supplied as input. -/
namespace NearCubicWires.ExtDecompositionBatch
open LocalBitMultitape RepairOrdinary RepairRepresentation ExecutableInterfaces
open RepairOrdinary.DecompositionSource RepairOrdinary.RecoveryRootRound SupplierPipeline
open RepairOrdinary.CloseoutRowsCircuitBottom
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
variable (a : DecompositionAlgorithm)

def loopHeads (pos : ℕ) (c1 c2 c3 : List Bool) : Fin (T a) → ℕ :=
  Fin.addCases (fun _=>0) ![pos,c1.length,c2.length,c3.length,0,0,0,0,0,0,1,0]
def loopTapes (C q : ℕ) (source c1 c2 c3 : List Bool) : Fin (T a) → List Bool :=
  Fin.addCases (fun _=>List.replicate C false)
    ![source,c1,c2,c3,[],[],[],List.replicate C false,List.replicate C true,
      List.replicate (C+1) false,UnaryTemplate.tape q,[]]
def loopInH (pos : ℕ) (c1 c2 c3 : List Bool) : Fin (CT a) → ℕ :=
  Fin.addCases (loopHeads a pos c1 c2 c3) (fun _=>0)
def loopInA (C q : ℕ) (source c1 c2 c3 : List Bool) : Fin (CT a) → List Bool :=
  loggedTapes a C (loopTapes a C q source c1 c2 c3)

theorem body_state (C q : ℕ) (g : SupportedNormalizedGate q) (pre rest c1 c2 c3 : List Bool)
    (K : Fin (SB a) → List Bool) (KH : Fin (SB a) → ℕ) :
    let source:=pre++frame (nativeWord g)++rest
    let H:=loopHeads a pre.length c1 c2 c3
    let A:=loopTapes a C q source c1 c2 c3
    let OH:=tailHeads a g c1 c2 c3 (sourceHeads a pre.length (frame (nativeWord g)).length H KH)
    let OA:=tailTapes a C g c1 c2 c3 (sourceTapes a C (nativeWord g) source A K)
    clearedHeads a OH=loopInH a (pre.length+(frame (nativeWord g)).length)
      (c1++natWord (children a g).length) (c2++(children a g).flatMap exactWord)
      (c3++List.replicate (children a g).length true) ∧
    clearedTapes a C OA=loopInA a C q source
      (c1++natWord (children a g).length) (c2++(children a g).flatMap exactWord)
      (c3++List.replicate (children a g).length true) := by
  dsimp only
  let H:=loopHeads a pre.length c1 c2 c3
  let A:=loopTapes a C q (pre++frame (nativeWord g)++rest) c1 c2 c3
  let SH:=sourceHeads a pre.length (frame (nativeWord g)).length H KH
  let SA:=sourceTapes a C (nativeWord g) (pre++frame (nativeWord g)++rest) A K
  let OH:=tailHeads a g c1 c2 c3 SH
  let OA:=tailTapes a C g c1 c2 c3 SA
  have live (j : Fin 12) :
      clearedHeads a OH ((ex a j).castAdd 1)=
        loopInH a (pre.length+(frame (nativeWord g)).length)
          (c1++natWord (children a g).length) (c2++(children a g).flatMap exactWord)
          (c3++List.replicate (children a g).length true) ((ex a j).castAdd 1) ∧
      clearedTapes a C OA ((ex a j).castAdd 1)=
        loopInA a C q (pre++frame (nativeWord g)++rest)
          (c1++natWord (children a g).length) (c2++(children a g).flatMap exactWord)
          (c3++List.replicate (children a g).length true) ((ex a j).castAdd 1) := by
    obtain ⟨ch,ct⟩:=cleared_extra a C OH OA j
    obtain ⟨th,tt⟩:=tail_ports a C q g c1 c2 c3 SH SA j
    rw [ch,ct]
    change OH (ex a j)=_ at th
    change OA (ex a j)=_ at tt
    rw [th,tt]
    have special:=source_special a C pre.length (frame (nativeWord g)).length
      (nativeWord g) (pre++frame (nativeWord g)++rest) H A KH K
    have sh0:SH (ex a 0)=pre.length+(frame (nativeWord g)).length:=special.1
    have st0:SA (ex a 0)=pre++frame (nativeWord g)++rest:=special.2.1
    have sh (j : Fin 12) (h0 : j.val≠0) (h7 : j.val≠7) : SH (ex a j)=H (ex a j):=
      source_extra_heads a _ _ H KH j h0 h7
    have st (j : Fin 12) (h0 : j.val≠0) (h7 : j.val≠7) : SA (ex a j)=A (ex a j):=
      source_extra_tapes a C _ _ A K j h0 h7
    fin_cases j <;>
      norm_num only [Fin.reduceFinMk,tailPortHeads,tailPortTapes]
    all_goals simp only [loopInH,loopInA,loggedTapes,loopHeads,loopTapes,
      Fin.addCases_left,ex,Fin.addCases_right]
    · exact ⟨sh0,st0⟩
    · exact ⟨rfl,rfl⟩
    · exact ⟨rfl,rfl⟩
    · exact ⟨rfl,rfl⟩
    · exact ⟨(sh 4 (by decide) (by decide)).trans (by simp [H,loopHeads,ex]),
        (st 4 (by decide) (by decide)).trans (by simp [A,loopTapes,ex])⟩
    · exact ⟨(sh 5 (by decide) (by decide)).trans (by simp [H,loopHeads,ex]),
        (st 5 (by decide) (by decide)).trans (by simp [A,loopTapes,ex])⟩
    · exact ⟨(sh 6 (by decide) (by decide)).trans (by simp [H,loopHeads,ex]),
        (st 6 (by decide) (by decide)).trans (by simp [A,loopTapes,ex])⟩
    · exact ⟨rfl,rfl⟩
    · exact ⟨rfl,rfl⟩
    · exact ⟨rfl,rfl⟩
    · exact ⟨rfl,rfl⟩
    · exact ⟨(sh 11 (by decide) (by decide)).trans (by simp [H,loopHeads,ex]),
        (st 11 (by decide) (by decide)).trans (by simp [A,loopTapes,ex])⟩
  constructor
  · funext i
    refine Fin.addCases (m:=T a) (n:=1) (fun j=>?_) (fun j=>?_) i
    · refine Fin.addCases (m:=SB a) (n:=12) (fun k=>?_) (fun k=>?_) j
      · simp only [loopInH,loopHeads,Fin.addCases_left]
        change clearedHeads a OH ((bk a k).castAdd 1)=0
        exact (cleared_bank a C OH OA k).1
      · exact (live k).1
    · have hj:j=0:=Fin.eq_zero j
      subst hj
      simpa only [loopInH,Fin.addCases_right] using (cleared_log a C OH OA).1
  · funext i
    refine Fin.addCases (m:=T a) (n:=1) (fun j=>?_) (fun j=>?_) i
    · refine Fin.addCases (m:=SB a) (n:=12) (fun k=>?_) (fun k=>?_) j
      · simp only [loopInA,loggedTapes,loopTapes,Fin.addCases_left]
        change clearedTapes a C OA ((bk a k).castAdd 1)=List.replicate C false
        exact (cleared_bank a C OH OA k).2
      · exact (live k).2
    · have hj:j=0:=Fin.eq_zero j
      subst hj
      simpa only [loopInA,loggedTapes,Fin.addCases_right] using (cleared_log a C OH OA).2

end NearCubicWires.ExtDecompositionBatch
