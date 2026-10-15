import Proof.Amplification.RecoveryValuationCountReturn

/-! Finite physical controller for a capped serialized valuation list:
parse the count, scan those rows, and write the final acceptance bit. -/
namespace NearCubicWires.RepairOrdinary.RecoveryValuationCount
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryValuationStream
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev graphSizes : Fin 4 → Nat := ![5,Fintype.card (RepeatMachine.Control (Fintype.card (RecoveryCalls.Control RecoveryValuationStream.sizes))),2,2]
noncomputable def programs : (j : Fin 4) → Machine 10 (graphSizes j)
  | ⟨0,_⟩=>countMachine
  | ⟨1,_⟩=>loopMachine
  | ⟨2,_⟩=>flagMachine true
  | ⟨3,_⟩=>flagMachine false
  | ⟨n+4,h⟩=>False.elim (by omega)
def stage (bit : Bool) : Fin 4 := if bit then 2 else 3
noncomputable def next (j : Fin 4) (q : Fin (graphSizes j)) (_ : Fin 10 → Bool) : Option (Fin 4) :=
  if j.val=0 then if q.val=3 then some 1 else some 3 else
  if j.val=1 then some (stage (decide (q.val=(RepeatMachine.phaseCode (Fintype.card (RecoveryCalls.Control RecoveryValuationStream.sizes)) 3).val))) else none
noncomputable abbrev machine := RecoveryCalls.machine graphSizes programs 0 next

def limit (width cap : Nat) := cap*(budget width+6)+12
noncomputable def flagStart {s : Nat} (c : Configuration 10 s) (bit : Bool) :=
  controlConfig (RecoveryCalls.code graphSizes (stage bit))
    (RecoveryCalls.restarted (programs (stage bit)) c.heads c.tapes)
noncomputable def finished {s : Nat} (c : Configuration 10 s) (bit : Bool) :=
  RecoveryCalls.stopped graphSizes c.heads (Function.update c.tapes 7 [bit])

theorem flag_tail {s : Nat} (c : Configuration 10 s) (old bit : Bool)
    (hh : c.heads 7=0) (ht : c.tapes 7=[old]) :
    ∃ n,n≤2 ∧ Timed machine n (flagStart c bit) (finished c bit) := by
  obtain ⟨r,hr,hf,_⟩ := flag_run c old bit hh ht
  cases bit with
  | false =>
    obtain ⟨n,hn,h⟩ := stop_receipt graphSizes programs 0 next 3 _ _ r hr (by rfl)
    rw [hf] at h
    exact ⟨n,hn,h⟩
  | true =>
    obtain ⟨n,hn,h⟩ := stop_receipt graphSizes programs 0 next 2 _ _ r hr (by rfl)
    rw [hf] at h
    exact ⟨n,hn,h⟩

theorem readList_count_none (width cap : Nat) (word : List Bool) (h : readCount cap word=none) :
    readList cap (readEntry width) word=none := by rw [readList,h]; rfl

theorem readList_count_some (width cap count : Nat) (word rest : List Bool)
    (h : readCount cap word=some (count,rest)) :
    readList cap (readEntry width) word=readMany (readEntry width) count rest := by rw [readList,h]; rfl

theorem count_cursor (d : Data) (width cap count : Nat) (pre word rest : List Bool)
    (hi : d.index.length=width) (hw : d.width=width) (hb : d.row.length≤2*(width+1)+1)
    (hs : d.source=pre++frame word) (hp : d.pos=pre.length)
    (hc : readCount cap word=some (count,rest)) :
    RecoveryValuationTable.Inv width ⟨counted d count,rest⟩ := by
  obtain ⟨_,he⟩ := RecoveryCertificateCount.readCount_some cap count word rest hc
  refine ⟨hw,hi,hb,pre++Streaming.marks (List.replicate count true++[false]),?_,?_⟩
  · change d.source=(pre++Streaming.marks (List.replicate count true++[false]))++frame rest
    rw [List.append_assoc,←Streaming.frame_append]
    rw [hs,he]
    simp only [List.append_assoc,List.singleton_append]
  · change d.pos+2*count+2=_
    simp [hp,Streaming.marks_length,Nat.add_assoc]

end NearCubicWires.RepairOrdinary.RecoveryValuationCount
