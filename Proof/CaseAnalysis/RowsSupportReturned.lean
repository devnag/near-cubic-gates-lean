import Proof.CaseAnalysis.RowsSupportDock
import Proof.CaseAnalysis.RowsCircuitBottomReturned

/-! Return the unchanged private circuit heads after support retention.
The existing paid return worker leaves the new support append cursor intact. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Dock
open LocalBitMultitape RadixSemantics ExtDecompositionBatch
open CloseoutRowsCircuitBottomLoop CloseoutRowsSupportStream
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def oldIndex : Fin 1060 → Fin 1061:=
  Fin.addCases (m:=1059) (n:=1) (fun i=>i.castAdd 2) (fun _=>1060)
theorem old_slots (i : Fin 1060) : slots (oldIndex i)=
    (CloseoutRowsCircuit.bottomSlots i).castAdd 1:=by
  refine Fin.addCases (m:=1059) (n:=1) ?_ ?_ i
  · intro j
    simpa only [oldIndex,Fin.addCases_left] using old_slot j
  · intro j
    have hj:j=0:=Fin.eq_zero j
    subst j
    rfl
theorem old_heads (p m : ℕ) (native supports : List Bool) (D W : ℕ) (i : Fin 1060) :
    localHeads p m native supports D W (oldIndex i)=
      CloseoutRowsCircuitBottomDock.localHeads p m native D W i:=by
  refine Fin.addCases (m:=1059) (n:=1) ?_ ?_ i
  · intro j
    simp only [oldIndex,Fin.addCases_left]
    change localHeads p m native supports D W ((j.castAdd 1).castAdd 1)=_
    simp only [localHeads,extend,CloseoutRowsCircuitBottomDock.localHeads,Fin.addCases_left]
  · intro j
    have hj:j=0:=Fin.eq_zero j
    subst j
    rfl
theorem old_tapes (C q n : ℕ) (native supports source members : List Bool) (D W : ℕ) (flag : Bool)
    (i : Fin 1060) : localTapes C q n native supports source members D W flag (oldIndex i)=
      CloseoutRowsCircuitBottomDock.localTapes C q n native source members D W flag i:=by
  refine Fin.addCases (m:=1059) (n:=1) ?_ ?_ i
  · intro j
    simp only [oldIndex,Fin.addCases_left]
    change localTapes C q n native supports source members D W flag ((j.castAdd 1).castAdd 1)=_
    simp only [localTapes,extend,CloseoutRowsCircuitBottomDock.localTapes,Fin.addCases_left]
  · intro j
    have hj:j=0:=Fin.eq_zero j
    subst j
    rfl
theorem outside_old (i : Fin 1703) (hi : ∀ j,CloseoutRowsCircuit.bottomSlots j≠i) :
    ∀ j,slots j≠i.castAdd 1:=by
  intro j he
  by_cases h59:j.val=1059
  · have hv:=congrArg Fin.val he
    rw [slots_val,if_pos h59] at hv
    simp only [Fin.val_castAdd] at hv
    omega
  by_cases h60:j.val=1060
  · have hj:j=(1060 : Fin 1061):=Fin.ext h60
    subst j
    have h:CloseoutRowsCircuit.bottomSlots 1059=i:=
      (Fin.castAdd_injective _ _) he
    exact hi 1059 h
  · let k : Fin 1059:=⟨j.val,by omega⟩
    have hj:j=k.castAdd 2:=Fin.ext rfl
    rw [hj,old_slot] at he
    exact hi (k.castAdd 1) ((Fin.castAdd_injective _ _) he)

theorem full_eta {α : Type} (F : Fin 1704 → α) :
    Fin.addCases (m:=1703) (n:=1) (fun i=>F (i.castAdd 1)) (fun _=>F 1703)=F := by
  funext i
  refine Fin.addCases (m:=1703) (n:=1) ?_ ?_ i
  · intro j
    simp only [Fin.addCases_left]
  · intro j
    have hj:j=0:=Fin.eq_zero j
    subst j
    rfl

noncomputable def returned (threshold : Bool):=Composition.machine (machine threshold)
  (TapeEmbedding.machine 1 CloseoutRowsCircuitReturnHeads.machine)
def returnBudget (C q n : ℕ):=CloseoutRowsSupportStream.budget C q n+1+(10*C+14)

theorem returned_run (threshold : Bool) (C core : ℕ) (words : List (List Bool))
    (native supports members : List Bool) (D W : ℕ) (flag : Bool)
    (H : Fin 1704 → ℕ) (A : Fin 1704 → List Bool)
    (hin : ∀ bits∈words,2*bits.length+1≤C)
    (hcap : ∀ bits∈words,2*CloseoutRowsGateMeasured.budget bits+4≤C)
    (hc : 1≤C)
    (bounds : descriptions core words D words.length≤C ∧
      wires threshold core 1 members words W words.length≤C ∧
      (words.flatMap frame).length≤C ∧ 1+2*words.length≤C)
    (hh : ∀ i,H (slots i)=localHeads 0 1 native supports D W i)
    (ht : ∀ i,A (slots i)=localTapes C core words.length native supports (words.flatMap frame) members D W flag i)
    (hz : ∀ i,(∀ j,CloseoutRowsCircuit.bottomSlots j≠i) → H (i.castAdd 1)=0) :
    ∃ r,runFrom (returned threshold) (returnBudget C core words.length)
      ⟨(returned threshold).start,H,A⟩=some r ∧ r.steps≤returnBudget C core words.length ∧
      r.final.heads=Fin.addCases (m:=1703) (n:=1)
        (CloseoutRowsCircuitColdEntry.heads (native++(List.range words.length).flatMap (outputs threshold core 1 members words)))
        (fun _=>(supportPrefix threshold core 1 members words supports words.length).length) ∧
      (∀ i,r.final.tapes ((CloseoutRowsCircuit.bottomSlots i).castAdd 1)=
        CloseoutRowsCircuitBottomDock.localTapes C core words.length
          (native++(List.range words.length).flatMap (outputs threshold core 1 members words))
          (words.flatMap frame) members (descriptions core words D words.length)
          (wires threshold core 1 members words W words.length) (validity core flag words words.length) i) ∧
      r.final.tapes 1703=supportPrefix threshold core 1 members words supports words.length ∧
      (∀ i,(∀ j,CloseoutRowsCircuit.bottomSlots j≠i) → r.final.tapes (i.castAdd 1)=A (i.castAdd 1)) := by
  obtain ⟨base,hbase,_bs,bh,bt,keep⟩:=loop_run threshold C core words native supports members D W flag H A hin hcap hh ht
  let pH:=fun i : Fin 1703=>base.final.heads (i.castAdd 1)
  let pA:=fun i : Fin 1703=>base.final.tapes (i.castAdd 1)
  have ph (i : Fin 1060) : pH (CloseoutRowsCircuit.bottomSlots i)=
      CloseoutRowsCircuitBottomDock.localHeads (words.flatMap frame).length (1+2*words.length)
        (native++(List.range words.length).flatMap (outputs threshold core 1 members words))
        (descriptions core words D words.length) (wires threshold core 1 members words W words.length) i:=by
    change base.final.heads ((CloseoutRowsCircuit.bottomSlots i).castAdd 1)=_
    rw [←old_slots,bh]
    exact old_heads _ _ _ _ _ _ i
  have pt (i : Fin 1060) : pA (CloseoutRowsCircuit.bottomSlots i)=
      CloseoutRowsCircuitBottomDock.localTapes C core words.length
        (native++(List.range words.length).flatMap (outputs threshold core 1 members words))
        (words.flatMap frame) members (descriptions core words D words.length)
        (wires threshold core 1 members words W words.length) (validity core flag words words.length) i:=by
    change base.final.tapes ((CloseoutRowsCircuit.bottomSlots i).castAdd 1)=_
    rw [←old_slots,bt]
    exact old_tapes _ _ _ _ _ _ _ _ _ _ i
  obtain ⟨last,hl,lh,lt,_ls⟩:=CloseoutRowsCircuitReturnHeads.return_run C pH pA
    ⟨(ph 1050).trans_le bounds.1,(ph 1051).trans_le bounds.2.1,
      (ph 1052).trans_le bounds.2.2.1,(ph 1053).trans_le bounds.2.2.2,(ph 1059).trans_le hc⟩
    (ph 1055) (ph 1056) (pt 1055) (pt 1056)
  have tail:=((ExtDecompositionBatch.Step.of_run hl lh lt).embed
    (fun _ : Fin 1=>base.final.heads 1703) (fun _ : Fin 1=>base.final.tapes 1703)).congr_in
      (full_eta base.final.heads) (full_eta base.final.tapes)
  obtain ⟨r,hr,rh,rt,rs⟩:=(ExtDecompositionBatch.Step.of_run hbase rfl rfl).seq tail
  have oldHeads:=CloseoutRowsCircuitBottomReturned.returned_heads pH _ _ _ _ _ ph
    (fun i hi=>((keep (i.castAdd 1) (outside_old i hi)).1).trans (hz i hi))
  have supportHead:base.final.heads 1703=
      (supportPrefix threshold core 1 members words supports words.length).length:=bh 1059
  refine ⟨r,hr,rs,?_,?_,?_,?_⟩
  · rw [rh,oldHeads,supportHead]
  · intro i
    rw [rt]
    simp only [Fin.addCases_left]
    exact pt i
  · rw [rt]
    exact bt 1059
  · intro i hi
    rw [rt]
    simp only [Fin.addCases_left]
    exact (keep (i.castAdd 1) (outside_old i hi)).2

end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Dock
