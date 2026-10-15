import Proof.PCP.ProjectionDimensionTemplate
import Proof.PCP.PCPOuter
import Proof.PCP.VerifierDecodingCompare

/-! The original successor-template printer on already paid grammar backing.
The physically written final false sentinel is absorbed by that same backing. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRecoveryGrammarDriverReady
open LocalBitMultitape RepairSource.ProjectionNormalization RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (B n : ℕ) : Fin 3 → List Bool :=
  ![ZeroPadding.pad B (List.replicate n true),List.replicate B false,List.replicate B false]
def output (B n : ℕ) : Fin 3 → List Bool :=
  ![ZeroPadding.pad B (List.replicate n true),ZeroPadding.pad B (CompareMachine.word (n+1)),List.replicate B false]

theorem template_pad (B n : ℕ) (h : n+3 ≤ B) :
    ZeroPadding.pad B (UnaryTemplate.tape (n+1))=ZeroPadding.pad B (CompareMachine.word (n+1)) := by
  simp only [ZeroPadding.pad,UnaryTemplate.tape,CompareMachine.word,List.length_cons,
    List.length_append,List.length_replicate,List.cons_append,List.append_assoc]
  congr 2
  have hb:B-(n+1+1)=(B-(n+1+1+1))+1:=by omega
  rw [hb,List.replicate_succ]
  rfl

theorem ready (B n : ℕ) (h : n+3 ≤ B) :
    ClockJoin.ReadyRun (DimensionTemplate.machine true) (2*n+8) (input B n) (output B n) := by
  obtain ⟨base,hbase,bt,bh,bs⟩:=DimensionTemplate.ready true n
  obtain ⟨result,hr,rf,rs,_⟩:=ZeroPadding.run_config (DimensionTemplate.machine true) (fun _=>B) _ _ base hbase
  have start:ZeroPadding.config (fun _ : Fin 3=>B)
      (initialConfiguration (DimensionTemplate.machine true) (DimensionTemplate.input n))=
      initialConfiguration (DimensionTemplate.machine true) (input B n):=by
    apply configuration_ext
    · rfl
    · rfl
    · funext i;fin_cases i <;> simp [ZeroPadding.config,initialConfiguration,DimensionTemplate.input,input,ZeroPadding.pad]
  change runFrom _ _ (ZeroPadding.config _ (initialConfiguration _ _))=_ at hr
  rw [start] at hr
  refine ⟨result,hr,?_,?_,rs.le.trans bs⟩
  · rw [rf]
    change (fun i=>ZeroPadding.pad B (base.final.tapes i))=output B n
    rw [bt]
    funext i;fin_cases i
    · rfl
    · exact template_pad B n h
    · change ZeroPadding.pad B (List.replicate (n+3) false)=List.replicate B false
      simp only [ZeroPadding.pad,List.length_replicate,←List.replicate_add,Nat.add_sub_of_le h]
  · rw [rf]
    exact bh

end NearCubicWires.RepairOrdinary.CloseoutRecoveryGrammarDriverReady
