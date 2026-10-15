import Proof.Amplification.RecoveryRowStructureSmallGate

/-! Complete ordinary zero and singleton structural branches. Each branch
executes its code/payload test, the actual count classifier and the physical
final conjunction, with both composition returns included. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowStructure
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem stream_join {s t : Nat} (p : Machine 52 s) (q : Machine 52 t)
    (d middle out : Data) (capacity firstTime lastTime : Nat)
    (hfirst : ∃ r,runFrom p firstTime (cfg d capacity p.start)=some r ∧
      r.final=cfg middle capacity r.final.control ∧ r.steps=firstTime)
    (hlast : ∃ r,runFrom q lastTime (cfg middle capacity q.start)=some r ∧
      r.final=cfg out capacity r.final.control ∧ r.steps=lastTime) :
    ∃ r,runFrom (Composition.machine p q) (firstTime+1+lastTime)
        (cfg d capacity (Composition.machine p q).start)=some r ∧
      r.final=cfg out capacity r.final.control ∧ r.steps=firstTime+1+lastTime := by
  obtain ⟨first,hr0,hf0,hs0⟩ := hfirst
  obtain ⟨last,hr1,hf1,hs1⟩ := hlast
  have hstart : Composition.restart first.final q.start=cfg middle capacity q.start := by
    rw [hf0]
    rfl
  have hnext : runFrom q lastTime (Composition.restart first.final q.start)=some last := by
    rw [hstart]
    exact hr1
  have h := Composition.run_join p q firstTime lastTime _ first last hr0 hnext
  refine ⟨Composition.joinedReceipt first last,h,?_,?_⟩
  · change Composition.rightConfig _ last.final=cfg out capacity _
    rw [hf1]
    rfl
  · change first.steps+1+last.steps=firstTime+1+lastTime
    rw [hs0,hs1]

noncomputable def zeroCore := Composition.machine codePredMachine countKindMachine
noncomputable def zeroMachine := Composition.machine zeroCore (smallGate false)
def zeroTime (d : Data) := (4*d.code.length+4)+1+RecoveryRowKind.time d.count+1+1
def zeroOutput (d : Data) :=
  setValid (countClassified (codePredicted d)) (decide (value d.code=0 ∧ value d.count=0))

noncomputable def oneCore := Composition.machine payloadMachine countKindMachine
noncomputable def oneMachine := Composition.machine oneCore (smallGate true)
def oneTime (d : Data) (child : List Bool) := (8*child.length+20)+1+RecoveryRowKind.time d.count+1+1
def oneOutput (d : Data) (child : List Bool) :=
  setValid (countClassified (payloadCompared d child)) (decide (value child=value d.state.bits ∧ value d.count=1))

theorem zero_run (d : Data) (capacity : Nat) (word : List Bool) (hd : d.Valid word) :
    ∃ r,runFrom zeroMachine (zeroTime d) (cfg d capacity zeroMachine.start)=some r ∧
      r.final=cfg (zeroOutput d) capacity r.final.control ∧ r.steps=zeroTime d ∧
      (zeroOutput d).Valid word := by
  obtain ⟨first,hr0,hf0,hs0,hv0⟩ := code_pred_run d capacity word hd
  obtain ⟨second,hr1,hf1,hs1,hv1⟩ := count_kind_run (codePredicted d) capacity word hv0
  have hcore := stream_join codePredMachine countKindMachine d (codePredicted d)
    (countClassified (codePredicted d)) capacity (4*d.code.length+4) (RecoveryRowKind.time d.count)
    ⟨first,hr0,hf0,hs0⟩ ⟨second,hr1,hf1,hs1⟩
  obtain ⟨last,hr2,hf2,hs2⟩ := small_gate_run false (countClassified (codePredicted d)) capacity
  have he : smallGateBit false (countClassified (codePredicted d)).valid
      ((countClassified (codePredicted d)).flags 0) ((countClassified (codePredicted d)).flags 1)=
      decide (value d.code=0 ∧ value d.count=0) := by
    simp [smallGateBit,countClassified,codePredicted,setValid,setCode,setCount,setFlag]
  have hfinal : last.final=cfg (zeroOutput d) capacity last.final.control := by
    rw [hf2]
    change cfg (setValid (countClassified (codePredicted d)) _) capacity 1=cfg (zeroOutput d) capacity 1
    rw [he]
    rfl
  obtain ⟨r,hr,hf,hs⟩ := stream_join zeroCore (smallGate false) d (countClassified (codePredicted d))
    (zeroOutput d) capacity ((4*d.code.length+4)+1+RecoveryRowKind.time d.count) 1 hcore ⟨last,hr2,hfinal,hs2⟩
  exact ⟨r,hr,hf,hs,hv1⟩

theorem one_run (d : Data) (capacity : Nat) (child word : List Bool) (hd : d.Valid word)
    (hw : child.length=d.state.bits.length) (hc : d.state.fields 0=frame child) :
    ∃ r,runFrom oneMachine (oneTime d child) (cfg d capacity oneMachine.start)=some r ∧
      r.final=cfg (oneOutput d child) capacity r.final.control ∧ r.steps=oneTime d child ∧
      (oneOutput d child).Valid word := by
  obtain ⟨first,hr0,hf0,hs0,hv0⟩ := payload_run d capacity child word hd hw hc
  obtain ⟨second,hr1,hf1,hs1,hv1⟩ := count_kind_run (payloadCompared d child) capacity word hv0
  have hcore := stream_join payloadMachine countKindMachine d (payloadCompared d child)
    (countClassified (payloadCompared d child)) capacity (8*child.length+20) (RecoveryRowKind.time d.count)
    ⟨first,hr0,hf0,hs0⟩ ⟨second,hr1,hf1,hs1⟩
  obtain ⟨last,hr2,hf2,hs2⟩ := small_gate_run true (countClassified (payloadCompared d child)) capacity
  have he : smallGateBit true (countClassified (payloadCompared d child)).valid
      ((countClassified (payloadCompared d child)).flags 0) ((countClassified (payloadCompared d child)).flags 1)=
      decide (value child=value d.state.bits ∧ value d.count=1) := by
    simp [smallGateBit,countClassified,payloadCompared,setValid,setCount,setFlag]
    rfl
  have hfinal : last.final=cfg (oneOutput d child) capacity last.final.control := by
    rw [hf2]
    change cfg (setValid (countClassified (payloadCompared d child)) _) capacity 1=cfg (oneOutput d child) capacity 1
    rw [he]
    rfl
  obtain ⟨r,hr,hf,hs⟩ := stream_join oneCore (smallGate true) d (countClassified (payloadCompared d child))
    (oneOutput d child) capacity ((8*child.length+20)+1+RecoveryRowKind.time d.count) 1 hcore ⟨last,hr2,hfinal,hs2⟩
  exact ⟨r,hr,hf,hs,hv1⟩

end NearCubicWires.RepairOrdinary.RecoveryRowStructure
