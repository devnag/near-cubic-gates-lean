import Proof.CaseAnalysis.RowsPacketOptional

/-! The actual outer family loop consumes every polynomial packet once,
including empty polynomials, and rewinds its literal family driver. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsFamilyLoop
open LocalBitMultitape CloseoutRowsBankPacket CloseoutRowsPreparationBounds
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem flatMap_index {α β : Type} (xs : List α) (default : α) (f : α→List β) :
    (List.range xs.length).flatMap (fun j=>f (xs.getD j default))=xs.flatMap f := by
  have he : (List.range xs.length).map (fun j=>xs.getD j default)=xs := by
    apply List.ext_getElem
    · simp
    · intro i _ hi
      simp only [List.getElem_map,List.getElem_range]
      exact List.getD_eq_getElem xs default hi
  rw [←List.flatMap_map,he]

theorem split_word {α β : Type} (xs : List α) (default : α) (f : α→List β)
    (j : ℕ) (hj : j<xs.length) :
    xs.flatMap f=(xs.take j).flatMap f++f (xs.getD j default)++(xs.drop (j+1)).flatMap f := by
  have h:=congrArg (List.flatMap f) (List.take_append_drop (j+1) xs)
  rw [List.take_succ_eq_append_getElem hj] at h
  simpa only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    List.getD_eq_getElem xs default hj] using h.symm

theorem next_word {α β : Type} (xs : List α) (default : α) (f : α→List β)
    (j : ℕ) (hj : j<xs.length) :
    ((xs.take (j+1)).flatMap f).length=
      ((xs.take j).flatMap f).length+(f (xs.getD j default)).length := by
  simp only [List.take_succ_eq_append_getElem hj,List.flatMap_append,List.flatMap_cons,
    List.flatMap_nil,List.append_nil,List.length_append,List.getD_eq_getElem xs default hj]

noncomputable def machine := CloseoutRowsDegreeLoop.machine CloseoutRowsPacketOptional.machine
noncomputable def stream {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F Q w C : ℕ) (bank : List (List (List Bool))) :=
  bank.flatMap (CloseoutRowsPacketOptional.packet gs p F Q w C)
noncomputable def entry {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F Q w C : ℕ) (bank : List (List (List Bool))) (pre tail : List Bool)
    (j : ℕ) (out : List Bool) :=
  (⟨CloseoutRowsPacketOptional.machine.start,
    heads out (pre.length+(stream gs p F Q w C (bank.take j)).length),
    tapes C out (pre++stream gs p F Q w C bank++tail)⟩ : Configuration 114 _)
def budget (N Q C : ℕ) := N*(CloseoutRowsPacketOptional.cost Q C+3)+3

theorem family_run {l r : ℕ} (gs : List (ExactThresholdGate (l+r)))
    (p F Q w : ℕ) (bank : List (List (List Bool))) (out pre tail : List Bool)
    (hl : ∀ rows∈bank,∀ row∈rows,row.length=gs.length)
    (hw : ∀ rows∈bank,rows.length<2^w)
    (hQp : Q≤p) (hp : RowTupleFixedCapacity.width gs Q≤p)
    (hF : RowCommonBounds.capacity gs (gs.length*Q) p≤F) :
    let C:=capacity (l+r) p F w gs.length Q
    let result:=out++(bank.flatMap (CloseoutRowsSharedDigits.cuts gs Q w)).flatMap (MatrixScoreBatch.cutWord p)
    ∃ actual,runFrom machine (budget bank.length Q C)
      (RepeatMachine.cfg 0 (entry gs p F Q w C bank pre tail 0 out) bank.length 1)=some actual ∧
      actual.final=RepeatMachine.cfg 3
        (entry gs p F Q w C bank pre tail bank.length result) bank.length 1 ∧
      actual.steps≤budget bank.length Q C := by
  dsimp only
  let C:=capacity (l+r) p F w gs.length Q
  let f:=CloseoutRowsPacketOptional.packet gs p F Q w C
  let emit:=fun j=>(CloseoutRowsSharedDigits.cuts gs Q w (bank.getD j [])).flatMap (MatrixScoreBatch.cutWord p)
  have supplier : ∀ j<bank.length,∀ acc,∃ actual,
      runFrom CloseoutRowsPacketOptional.machine (CloseoutRowsPacketOptional.cost Q C)
        (entry gs p F Q w C bank pre tail j acc)=some actual ∧
      actual.final.heads=(entry gs p F Q w C bank pre tail (j+1) (acc++emit j)).heads ∧
      actual.final.tapes=(entry gs p F Q w C bank pre tail (j+1) (acc++emit j)).tapes ∧
      actual.steps≤CloseoutRowsPacketOptional.cost Q C := by
    intro j hj acc
    have hmem : bank.getD j []∈bank := by
      rw [List.getD_eq_getElem bank [] hj]
      exact List.getElem_mem hj
    let packetPre:=pre++(bank.take j).flatMap f
    let packetTail:=(bank.drop (j+1)).flatMap f++tail
    obtain ⟨a,ha,ah,atape,asteps⟩:=CloseoutRowsPacketOptional.optional_run gs p F Q w
      (bank.getD j []) acc packetPre packetTail (hl _ hmem) (hw _ hmem) hQp hp hF
    have hs : packetPre++f (bank.getD j [])++packetTail=pre++stream gs p F Q w C bank++tail := by
      rw [stream,split_word bank [] f j hj]
      simp only [packetPre,packetTail,List.append_assoc]
    have hinput :
        (⟨CloseoutRowsPacketOptional.machine.start,heads acc packetPre.length,
          tapes C acc (packetPre++f (bank.getD j [])++packetTail)⟩ : Configuration 114 _)=
        entry gs p F Q w C bank pre tail j acc := by
      rw [hs]
      apply configuration_ext
      · rfl
      · simp only [packetPre,List.length_append,entry,stream,f]
      · rfl
    rw [hinput] at ha
    refine ⟨a,ha,?_,?_,asteps⟩
    · rw [ah]
      change heads (acc++emit j) (packetPre.length+(f (bank.getD j [])).length)=
        heads (acc++emit j) (pre.length+((bank.take (j+1)).flatMap f).length)
      rw [next_word bank [] f j hj]
      simp only [packetPre,List.length_append,Nat.add_assoc]
    · rw [atape]
      change tapes C (acc++emit j) (packetPre++f (bank.getD j [])++packetTail)=_
      rw [hs]
      rfl
  obtain ⟨actual,ha,hf,ht⟩:=CloseoutRowsDegreeLoop.loop_run CloseoutRowsPacketOptional.machine
    (entry gs p F Q w C bank pre tail) emit (CloseoutRowsPacketOptional.cost Q C) bank.length
    (by intro j hj acc; rfl) supplier out
  have hout : (List.range bank.length).flatMap emit=
      (bank.flatMap (CloseoutRowsSharedDigits.cuts gs Q w)).flatMap (MatrixScoreBatch.cutWord p) := by
    rw [List.flatMap_assoc]
    simpa only [emit] using flatMap_index bank []
      (fun rows=>(CloseoutRowsSharedDigits.cuts gs Q w rows).flatMap (MatrixScoreBatch.cutWord p))
  rw [hout] at hf
  exact ⟨actual,ha,hf,ht⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsFamilyLoop
