import Proof.SourceAssembly.SourceTopNative
import Proof.CaseAnalysis.RowsSupportTyped

/- Execute the original compact-circuit parser and native supplier. A one-bit
paid boot handles its arity sentinel; recorded execution rewinds the actual
native append cursor without a separately supplied length driver. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace SourceAssemblyCircuitNative
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open RecoveryExecution SupplierPipeline CanonicalWitnessCodec RadixSemantics
open PacketProduction
noncomputable section
attribute [local irreducible] CloseoutRowsSupportStream.Threshold.machine CloseoutRowsSupportStream.Threshold.program

theorem empty_heads (i : Fin 1704) :
    CloseoutRowsSupportStream.Threshold.heads [] [] i=(if i.val=1674 then 1 else 0) := by
  refine Fin.addCases (m:=1703) (n:=1) (fun j=>?_) (fun j=>?_) i
  · simp only [CloseoutRowsSupportStream.Threshold.heads,Fin.addCases_left,Fin.val_castAdd,
      CloseoutRowsCircuitColdEntry.heads,CloseoutRowsCircuit.heads,List.length_nil]
    by_cases h : j=1688
    · subst j; decide
    · simp [h]
  · simp [CloseoutRowsSupportStream.Threshold.heads]

def boot : Machine 1705 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun _ _=>some ⟨1,(fun i=>if i.val=1704 then some true else none),
    (fun i=>if i.val=1674 ∨ i.val=1704 then .right else .stay)⟩
def bootHeads : Fin 1705→Nat :=
  fun i=>Fin.addCases (m:=1704) (n:=1) (motive:=fun _=>Nat) (CloseoutRowsSupportStream.Threshold.heads [] []) (fun _=>1) i

theorem boot_run (A : Fin 1704→List Bool) :
    Step boot 1 (fun _=>0) (Fin.addCases (m:=1704) (n:=1) (motive:=fun _=>List Bool) A (fun _ : Fin 1=>[]))
      bootHeads (Fin.addCases (m:=1704) (n:=1) (motive:=fun _=>List Bool) A (fun _ : Fin 1=>[true])) := by
  have hs : step boot (initialConfiguration boot (Fin.addCases (m:=1704) (n:=1) (motive:=fun _=>List Bool) A (fun _ : Fin 1=>[])))=
      some (⟨1,bootHeads,Fin.addCases (m:=1704) (n:=1) (motive:=fun _=>List Bool) A (fun _ : Fin 1=>[true])⟩ : Configuration 1705 2) := by
    simp [step,boot,initialConfiguration]
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m:=1704) (n:=1) (fun j=>?_) (fun j=>?_) i
      · have hj:=j.isLt
        simp only [applyAction,Fin.val_castAdd,bootHeads,Fin.addCases_left,
          empty_heads]
        by_cases h : j.val=1674 <;> simp [h,HeadMove.apply,show j.val≠1704 by omega]
      · have hj : j.val=0 := by omega
        simp only [applyAction,bootHeads,Fin.addCases_right,Fin.val_natAdd,hj]
        simp [HeadMove.apply]
    · funext i
      refine Fin.addCases (m:=1704) (n:=1) (fun j=>?_) (fun j=>?_) i
      · have hj:=j.isLt
        simp [applyAction,show j.val≠1704 by omega]
      · have hj : j.val=0 := by omega
        simp only [applyAction,Fin.addCases_right,Fin.val_natAdd,hj]
        simp [writeTapeBit]
  obtain ⟨r,hr,hf,_⟩:=(Timed.single (by rfl) hs).run (by rfl)
  exact Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)

def machine := Composition.machine boot (Rewind.machine CloseoutRowsSupportStream.Threshold.machine)
def input (P q W L : Nat) (bits : List Bool) : Fin 1705→List Bool :=
  Fin.addCases (m:=1704) (n:=1) (motive:=fun _=>List Bool) (CloseoutRowsSupportStream.Threshold.input P q W L bits [] []) (fun _ : Fin 1=>[])
def budget (P q : Nat) (bits : List Bool) := 2*CloseoutRowsSupportStream.circuitBudget P q bits.length+5

theorem threshold_run {q : Nat} (c : NormalizedThresholdThresholdCircuit q)
    (P W L : Nat) (bits : List Bool)
    (hcap : CloseoutRowsCircuitCapacity.capacity bits.length ≤ P)
    (hd : decodeNormalizedThresholdThresholdCircuit q (value bits)=some c)
    (hW : c.wireCount ≤ W) (hL : c.descriptionBits ≤ L) :
    ∃ A, Step machine (budget P q bits) (fun _=>0) (input P q W L bits) (fun _=>0) A ∧
      A 1688=thrWord c ∧ A 1=frame bits ∧ A 1694=List.replicate P true ∧
      A 1703=CloseoutRowsSupportStream.supportWord (List.ofFn (fun i=>c.bottom (retainedTopIndex c i))) := by
  obtain ⟨typed,native⟩:=CloseoutRowsCircuitMeaning.threshold_typed c W L bits hd
  have hp:=typed.mpr ⟨hW,hL⟩
  obtain ⟨f,hf,hfs,_fh,_flag,_rh,raw,_dh,drv,good⟩:=
    CloseoutRowsSupportStream.Threshold.cold_run P q W L bits [] [] hcap
  obtain ⟨_heads,word,_arity,_driver,_W,_L,_raw,support,_bound⟩:=good hp
  obtain ⟨r,hr,rf,_⟩:=Rewind.recorded_run CloseoutRowsSupportStream.Threshold.machine
    (CloseoutRowsSupportStream.circuitBudget P q bits.length) _ f hf 1 (by
      intro i
      dsimp only
      rw [empty_heads]
      split <;> omega)
  have last : Step (Rewind.machine CloseoutRowsSupportStream.Threshold.machine)
      (2*CloseoutRowsSupportStream.circuitBudget P q bits.length+3) bootHeads
      (Fin.addCases (m:=1704) (n:=1) (motive:=fun _=>List Bool) (CloseoutRowsSupportStream.Threshold.input P q W L bits [] []) (fun _ : Fin 1=>[true]))
      (fun _=>0) r.final.tapes := by
    apply (Step.of_run hr ?_ rfl).enlarge (by omega)
    rw [rf]
    funext i
    refine Fin.addCases (m:=1704) (n:=1) (fun _=>?_) (fun _=>?_) i <;>
      simp [Rewind.finished,Rewind.config]
  have all:=(boot_run (CloseoutRowsSupportStream.Threshold.input P q W L bits [] [])).seq last
  refine ⟨r.final.tapes,?_,?_,?_,?_,?_⟩
  · have ht : 1+1+(2*CloseoutRowsSupportStream.circuitBudget P q bits.length+3)=budget P q bits := by
      unfold budget
      omega
    rw [ht] at all
    exact all
  · rw [rf]
    change f.final.tapes 1688=thrWord c
    rw [word,List.nil_append,native]
    rfl
  · rw [rf]
    exact raw
  · rw [rf]
    exact drv

  · rw [rf]
    change f.final.tapes 1703=_
    rw [support,List.nil_append,CloseoutRowsSupportStream.Threshold.support_typed c bits hd]

end
end SourceAssemblyCircuitNative
