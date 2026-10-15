import Proof.CaseAnalysis.RowsSupportLoop
import Proof.CaseAnalysis.RowsCircuitBottomDock
import Proof.CaseAnalysis.RowsCircuitBottomTemplate
import Proof.CaseAnalysis.RowsCircuitLayout

/-! The retained-support loop uses the same actual bottom-count template at
full circuit port624. The only new public port is1703; old ports are unchanged. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Dock
open LocalBitMultitape RadixSemantics RepairSource.VerifierDecoding
open CloseoutRowsCircuitBottomLoop CloseoutRowsCircuitBottom CloseoutRowsSupportStream
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (i : Fin 1061) : Fin 1704:=
  if i.val=1059 then 1703 else if i.val=1060 then 624 else
    if i.val=1052 then 297 else ⟨639+i.val,by omega⟩
theorem slots_val (i : Fin 1061) : (slots i).val=
    if i.val=1059 then 1703 else if i.val=1060 then 624 else if i.val=1052 then 297 else 639+i.val:=by
  unfold slots
  split_ifs <;> rfl
theorem slots_injective : Function.Injective slots:=by
  intro i j h
  have hv:=congrArg Fin.val h
  rw [slots_val,slots_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega
theorem old_slot (i : Fin 1059) : slots (i.castAdd 2)=
    (CloseoutRowsCircuit.bottomSlots (i.castAdd 1)).castAdd 1:=by
  apply Fin.ext
  rw [slots_val]
  simp only [Fin.val_castAdd]
  rw [CloseoutRowsCircuit.bottom_val]
  simp only [Fin.val_castAdd,if_neg (show i.val≠1059 by omega),if_neg (show i.val≠1060 by omega)]
theorem output_slot : slots 1059=1703:=rfl
theorem count_slot : slots 1060=624:=rfl

def localHeads (pos memberPos : ℕ) (native supports : List Bool) (D W : ℕ) : Fin 1061 → ℕ:=
  Fin.addCases (m:=1060) (n:=1) (extend (heads pos memberPos native D W) supports.length) (fun _=>1)
def localTapes (C core count : ℕ) (native supports source members : List Bool) (D W : ℕ) (flag : Bool) :
    Fin 1061 → List Bool:=
  Fin.addCases (m:=1060) (n:=1) (extend (data C core [] native source members D W flag) supports)
    (fun _=>UnaryTemplate.tape count)
noncomputable def machine (threshold : Bool):=RecoveryFocus.machine slots (loop threshold)

theorem loop_run (threshold : Bool) (C core : ℕ) (words : List (List Bool))
    (native supports members : List Bool) (D W : ℕ) (flag : Bool)
    (H : Fin 1704 → ℕ) (A : Fin 1704 → List Bool)
    (hin : ∀ bits∈words,2*bits.length+1≤C)
    (hcap : ∀ bits∈words,2*CloseoutRowsGateMeasured.budget bits+4≤C)
    (hh : ∀ i,H (slots i)=localHeads 0 1 native supports D W i)
    (ht : ∀ i,A (slots i)=localTapes C core words.length native supports (words.flatMap frame) members D W flag i) :
    ∃ r,runFrom (machine threshold) (CloseoutRowsSupportStream.budget C core words.length)
        ⟨(machine threshold).start,H,A⟩=some r ∧
      r.steps≤CloseoutRowsSupportStream.budget C core words.length ∧
      (∀ i,r.final.heads (slots i)=localHeads (words.flatMap frame).length (1+2*words.length)
        (native++(List.range words.length).flatMap (outputs threshold core 1 members words))
        (supportPrefix threshold core 1 members words supports words.length)
        (descriptions core words D words.length) (CloseoutRowsCircuitBottomLoop.wires threshold core 1 members words W words.length) i) ∧
      (∀ i,r.final.tapes (slots i)=localTapes C core words.length
        (native++(List.range words.length).flatMap (outputs threshold core 1 members words))
        (supportPrefix threshold core 1 members words supports words.length) (words.flatMap frame) members
        (descriptions core words D words.length) (CloseoutRowsCircuitBottomLoop.wires threshold core 1 members words W words.length)
        (validity core flag words words.length) i) ∧
      (∀ i,(∀ j,slots j≠i) → r.final.heads i=H i ∧ r.final.tapes i=A i) := by
  obtain ⟨base,hb,bf,bs⟩:=CloseoutRowsSupportStream.loop_run threshold C core 1 flag words native supports
    [] [] members D W hin hcap
  obtain ⟨actual,ar,af,as⟩:=template_run (CloseoutRowsSupportStream.round threshold) _ words.length _ _ base hb bf
  have startH:∀ i,(templateCfg 0
      (CloseoutRowsSupportStream.entry threshold C core 1 flag words supports [] [] members D W 0 native)
      words.length 1).heads i=localHeads 0 1 native supports D W i:=by
    intro i
    simp only [templateCfg,controlConfig,TapeEmbedding.config,CloseoutRowsSupportStream.entry,
      List.take_zero,List.flatMap_nil,List.length_nil,Nat.mul_zero,Nat.add_zero,
      descriptions,CloseoutRowsCircuitBottomLoop.wires,total,List.range_zero,List.map_nil,List.sum_nil,
      supportPrefix,List.append_nil,localHeads]
  have startT:∀ i,(templateCfg 0
      (CloseoutRowsSupportStream.entry threshold C core 1 flag words supports [] [] members D W 0 native)
      words.length 1).tapes i=localTapes C core words.length native supports (words.flatMap frame) members D W flag i:=by
    intro i
    simp only [templateCfg,controlConfig,TapeEmbedding.config,CloseoutRowsSupportStream.entry,
      List.nil_append,List.append_nil,descriptions,CloseoutRowsCircuitBottomLoop.wires,total,List.range_zero,
      List.map_nil,List.sum_nil,Nat.add_zero,validity,List.all_nil,Bool.and_true,
      supportPrefix,List.flatMap_nil,localTapes]
  obtain ⟨r,hr,_rf,rs,rh,rt,keep⟩:=RecoveryFocus.dock slots slots_injective
    (loop threshold) _ H A _ (fun i=>(hh i).trans (startH i).symm)
    (fun i=>(ht i).trans (startT i).symm) actual ar
  refine ⟨r,hr,by omega,?_,?_,keep⟩
  · intro i
    rw [rh,af]
    simp only [templateCfg,controlConfig,TapeEmbedding.config,CloseoutRowsSupportStream.entry,
      List.take_length,List.length_nil,Nat.zero_add,localHeads]
  · intro i
    rw [rt,af]
    simp only [templateCfg,controlConfig,TapeEmbedding.config,CloseoutRowsSupportStream.entry,
      List.nil_append,List.append_nil,localTapes]

end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Dock
