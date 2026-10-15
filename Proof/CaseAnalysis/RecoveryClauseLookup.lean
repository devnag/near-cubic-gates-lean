import Proof.CaseAnalysis.RecoveryQueryListOutputRun
import Proof.Amplification.RecoveryPCPAddressLookup

/-! Directly reuse the existing generic framed-field lookup on the actual
unary query references. No address decoder or alternate reference order is
introduced; the literal's paid unary index drives the selected field. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedClauseLookup
open LocalBitMultitape RepairRepresentation RepairSource.VerifierDecoding
open RepairSource.ProjectionNormalization RecoveryBoundedSelectorLoop
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def fields (refs : List ℕ):=refs.map (fun r=>List.replicate r true)
theorem stream_fields (refs : List ℕ) : FieldList.stream (fields refs)=sourceWord refs := by
  induction refs with
  | nil=>rfl
  | cons ref refs ih=>
    change frame (List.replicate ref true)++FieldList.stream (fields refs)=
      frame (List.replicate ref true)++sourceWord refs
    rw [ih]

noncomputable def machine:=RepairSource.RecoveryPCPAddressLookup.machine
def rawBudget (before : List ℕ) (node : ℕ):=(sourceWord before).length+3*before.length+2*node+7
def budget (before : List ℕ) (node : ℕ):=2*rawBudget before node+2
def caps (C : ℕ) : Fin 5→ℕ:=![0,C,C,C,0]
def source (before : List ℕ) (node : ℕ) (tail : List Bool):=sourceWord before++frame (List.replicate node true)++tail
def input (before : List ℕ) (node C L : ℕ) (tail : List Bool) : Fin 5→List Bool:=
  ![source before node tail,List.replicate C false,ZeroPadding.pad C (CompareMachine.word before.length),
    List.replicate C false,List.replicate L false]
def output (before : List ℕ) (node C L : ℕ) (tail : List Bool) : Fin 5→List Bool:=
  ![source before node tail,ZeroPadding.pad C (sourceWord before),ZeroPadding.pad C (CompareMachine.word before.length),
    ZeroPadding.pad C (frame (List.replicate node true)),List.replicate L false]

theorem raw_budget (before : List ℕ) (node : ℕ) :
    RepairSource.RecoveryPCPAddressLookup.rawBudget (fields before) (List.replicate node true)=rawBudget before node := by
  unfold RepairSource.RecoveryPCPAddressLookup.rawBudget rawBudget
  rw [stream_fields]
  simp only [fields,List.length_map,List.length_replicate]

theorem input_pad (before : List ℕ) (node C L : ℕ) (tail : List Bool) :
    ZeroPadding.config (caps C) (initialConfiguration machine
      (Fin.addCases (m:=4) (n:=1) (motive:=fun _=>List Bool)
        (RepairSource.RecoveryPCPAddressLookup.input (fields before) (List.replicate node true) tail)
        (fun _=>List.replicate L false)))=initialConfiguration machine (input before node C L tail) := by
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    fin_cases i
    · change ZeroPadding.pad 0 (FieldList.stream (fields before)++frame (List.replicate node true)++tail)=source before node tail
      rw [ZeroPadding.pad_zero,stream_fields]
      rfl
    · rfl
    · change ZeroPadding.pad C (CompareMachine.word (fields before).length)=ZeroPadding.pad C (CompareMachine.word before.length)
      simp only [fields,List.length_map]
    · rfl
    · exact ZeroPadding.pad_zero _

theorem output_pad (before : List ℕ) (node C L : ℕ) (tail : List Bool) :
    (fun i=>ZeroPadding.pad (caps C i)
      ((Fin.addCases (m:=4) (n:=1) (motive:=fun _=>List Bool)
        (RepairSource.RecoveryPCPAddressLookup.output (fields before) (List.replicate node true) tail)
        (fun _=>List.replicate L false)) i))=output before node C L tail := by
  funext i
  fin_cases i
  · change ZeroPadding.pad 0 (FieldList.stream (fields before)++frame (List.replicate node true)++tail)=source before node tail
    rw [ZeroPadding.pad_zero,stream_fields]
    rfl
  · change ZeroPadding.pad C (FieldList.stream (fields before))=ZeroPadding.pad C (sourceWord before)
    rw [stream_fields]
  · change ZeroPadding.pad C (CompareMachine.word (fields before).length)=ZeroPadding.pad C (CompareMachine.word before.length)
    simp only [fields,List.length_map]
  · rfl
  · exact ZeroPadding.pad_zero _

theorem lookup_ready (before : List ℕ) (node C L : ℕ) (tail : List Bool) (hL : rawBudget before node ≤ L) :
    ClockJoin.ReadyRun machine (budget before node) (input before node C L tail) (output before node C L tail) := by
  obtain ⟨p,pr,pt,ph,ps⟩:=RepairSource.RecoveryPCPAddressLookup.ready_run (fields before) (List.replicate node true) tail L
  rw [RepairSource.RecoveryPCPAddressLookup.budget,raw_budget] at pr ps
  rw [raw_budget,max_eq_left hL] at pt
  obtain ⟨r,hr,rf,rs,_⟩:=ZeroPadding.run_config machine (caps C) _ _ p pr
  change runFrom machine (budget before node)
    (ZeroPadding.config (caps C) (initialConfiguration machine
      (Fin.addCases (m:=4) (n:=1) (motive:=fun _=>List Bool)
        (RepairSource.RecoveryPCPAddressLookup.input (fields before) (List.replicate node true) tail)
        (fun _=>List.replicate L false))))=some r at hr
  rw [input_pad] at hr
  refine ⟨r,hr,?_,?_,rs.le.trans ps⟩
  · rw [rf]
    change (fun i=>ZeroPadding.pad (caps C i) (p.final.tapes i))=_
    rw [pt,output_pad]
  · intro i
    rw [rf]
    exact ph i

end NearCubicWires.RepairOrdinary.RecoveryBoundedClauseLookup
