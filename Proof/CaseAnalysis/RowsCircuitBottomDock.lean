import Proof.CaseAnalysis.RowsCircuitGateErase

/-! The original counted bottom traversal runs at the frozen full-circuit
ports. Its existing canonical stream is aliased, and its output prefix and
actual count template remain exact physical fields. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottomDock
open LocalBitMultitape RecoveryRootRound CloseoutRowsCircuit
open CloseoutRowsCircuitBottomLoop
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def localHeads (position memberPos : ℕ) (out : List Bool) (D W : ℕ) : Fin 1060 → ℕ :=
  Fin.addCases (m:=1059) (n:=1) (CloseoutRowsCircuitBottom.heads position memberPos out D W) (fun _=>1)
def localTapes (C core n : ℕ) (out source members : List Bool) (D W : ℕ) (flag : Bool) :
    Fin 1060 → List Bool :=
  Fin.addCases (m:=1059) (n:=1) (CloseoutRowsCircuitBottom.data C core [] out source members D W flag)
    (fun _=>UnaryTemplate.tape n)
noncomputable def machine (threshold : Bool):=
  RecoveryFocus.machine bottomSlots (CloseoutRowsCircuitBottomLoop.machine threshold)

theorem bottoms_run (threshold : Bool) (C core : ℕ) (words : List (List Bool))
    (out members : List Bool) (D W : ℕ) (flag : Bool)
    (H : Fin 1703 → ℕ) (A : Fin 1703 → List Bool)
    (hin : ∀ bits∈words,2*bits.length+1 ≤ C)
    (hcap : ∀ bits∈words,2*CloseoutRowsGateMeasured.budget bits+4 ≤ C)
    (hh : ∀ i,H (bottomSlots i)=localHeads 0 1 out D W i)
    (ht : ∀ i,A (bottomSlots i)=localTapes C core words.length out (words.flatMap frame) members D W flag i) :
    ∃ r,runFrom (machine threshold) (CloseoutRowsCircuitBottomLoop.budget C words.length)
        ⟨(machine threshold).start,H,A⟩=some r ∧
      r.steps ≤ CloseoutRowsCircuitBottomLoop.budget C words.length ∧
      (∀ i,r.final.heads (bottomSlots i)=localHeads (words.flatMap frame).length (1+2*words.length)
        (out++(List.range words.length).flatMap (outputs threshold core 1 members words))
        (descriptions core words D words.length) (wires threshold core 1 members words W words.length) i) ∧
      (∀ i,r.final.tapes (bottomSlots i)=localTapes C core words.length
        (out++(List.range words.length).flatMap (outputs threshold core 1 members words))
        (words.flatMap frame) members (descriptions core words D words.length)
        (wires threshold core 1 members words W words.length) (validity core flag words words.length) i) ∧
      (∀ i,(∀ j,bottomSlots j≠i) → r.final.heads i=H i ∧ r.final.tapes i=A i):=by
  obtain ⟨base,hb,bf,bs⟩:=CloseoutRowsCircuitBottomLoop.bottoms_run threshold C core 1 flag words out [] [] members D W hin hcap
  obtain ⟨localRun,lr,lf,ls⟩:=CloseoutRowsCircuitBottomLoop.template_run (CloseoutRowsCircuitBottom.round threshold)
    _ words.length _ _ base hb bf
  have startH:∀ i,(templateCfg 0 (entry threshold C core 1 flag words [] [] members D W 0 out)
      words.length 1).heads i=localHeads 0 1 out D W i:=by
    intro i
    simp only [templateCfg,controlConfig,TapeEmbedding.config,entry,CloseoutRowsCircuitBottom.cfg,
      List.take_zero,List.flatMap_nil,List.length_nil,Nat.mul_zero,Nat.add_zero,
      descriptions,wires,total,List.range_zero,List.map_nil,List.sum_nil,localHeads]
  have startT:∀ i,(templateCfg 0 (entry threshold C core 1 flag words [] [] members D W 0 out)
      words.length 1).tapes i=localTapes C core words.length out (words.flatMap frame) members D W flag i:=by
    intro i
    simp only [templateCfg,controlConfig,TapeEmbedding.config,entry,CloseoutRowsCircuitBottom.cfg,
      List.nil_append,List.append_nil,descriptions,wires,total,List.range_zero,List.map_nil,List.sum_nil,
      Nat.add_zero,validity,List.all_nil,Bool.and_true,localTapes]
  obtain ⟨r,hr,_rf,rs,rh,rt,keep⟩:=RecoveryFocus.dock bottomSlots bottom_injective
    (CloseoutRowsCircuitBottomLoop.machine threshold) _ H A _
    (fun i=>(hh i).trans (startH i).symm) (fun i=>(ht i).trans (startT i).symm) localRun lr
  refine ⟨r,hr,by omega,?_,?_,keep⟩
  · intro i
    rw [rh,lf]
    simp only [templateCfg,controlConfig,TapeEmbedding.config,entry,CloseoutRowsCircuitBottom.cfg,
      List.take_length,List.length_nil,Nat.zero_add,localHeads]
  · intro i
    rw [rt,lf]
    simp only [templateCfg,controlConfig,TapeEmbedding.config,entry,CloseoutRowsCircuitBottom.cfg,
      List.nil_append,List.append_nil,localTapes]

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottomDock
