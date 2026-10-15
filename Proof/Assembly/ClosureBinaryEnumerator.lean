import Proof.MachineModel.ClosureLiveEnumeration
import Proof.MachineModel.OrdinaryFramedIncrement
import Proof.CaseAnalysis.RowsDegreeLoop
import Proof.MachineModel.Runs

/-! Runtime binary enumeration around a reusable physical callback. Only the
callback machine and two fixed tape slots enter the machine description.
The width, iteration count, assignment, workspace and emitted words enter
only the runtime configurations and receipt specification. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.BinaryEnumerator
open LocalBitMultitape RepairOrdinary RecoveryExecution ExtDecompositionBatch
open RepairSource.VerifierDecoding RecoveryRootRound CanonicalRecoveryLanguage

noncomputable def heads {t : Nat} (slots : Fin 2 → Fin t)
    (ambient : List Bool → Fin t → Nat) (out : List Bool) :=
  dockH slots (ambient out) (fun _ => 0)

noncomputable def bank {t : Nat} (slots : Fin 2 → Fin t)
    (ambient : List Bool → Fin t → List Bool) (K cap j : Nat) (out : List Bool) :=
  install slots (ambient out)
    ![frame (SignedSortKey.binary K j), List.replicate cap false]

noncomputable def increment {t : Nat} (slots : Fin 2 → Fin t) :=
  RecoveryFocus.machine slots FramedIncrement.machine

noncomputable def body {t s : Nat} (callback : Machine t s) (slots : Fin 2 → Fin t) :=
  Composition.machine callback (increment slots)

theorem increment_step {t : Nat} (slots : Fin 2 → Fin t) (hi : Function.Injective slots)
    (ambientH : List Bool → Fin t → Nat) (ambientT : List Bool → Fin t → List Bool)
    (K cap j : Nat) (out : List Bool) (hj : j+1 < 2^K) (hc : 2*K ≤ cap) :
    Step (increment slots) (4*K+2) (heads slots ambientH out)
      (bank slots ambientT K cap j out) (heads slots ambientH out)
      (bank slots ambientT K cap (j+1) out) := by
  obtain ⟨r,hr,hw,hl,hh,_,_⟩ := FramedIncrement.increment_run K j cap hj hc
  have hinput : Fin.addCases (m:=1) (n:=1) (motive:=fun _=>List Bool)
      (fun _=>frame (SignedSortKey.binary K j)) (fun _=>List.replicate cap false) =
      ![frame (SignedSortKey.binary K j),List.replicate cap false] := by
    funext i; fin_cases i <;> rfl
  rw [hinput] at hr
  have hlocal : Step FramedIncrement.machine (4*K+2) (fun _=>0)
      ![frame (SignedSortKey.binary K j),List.replicate cap false] (fun _=>0)
      ![frame (SignedSortKey.binary K (j+1)),List.replicate cap false] := by
    apply Step.of_run hr
    · funext i; exact hh i
    · funext i; fin_cases i
      · exact hw
      · exact hl
  exact hlocal.focus slots hi (ambientH out) (ambientT out)

def emitted (K : Nat) (emit : BitInput K → List Bool) (count : Nat) :=
  (List.range count).flatMap (fun j => emit (bitInputOfCode K j))

theorem emitted_all (K : Nat) (emit : BitInput K → List Bool) :
    emitted K emit (2^K) = (LiveEnumeration.binary K).flatMap emit := by
  rw [LiveEnumeration.binary_word_order]
  simp only [emitted,allBitInputs,List.flatMap_map]

noncomputable def entry {t s : Nat} (callback : Machine t s) (slots : Fin 2 → Fin t)
    (ambientH : List Bool → Fin t → Nat) (ambientT : List Bool → Fin t → List Bool)
    (K cap j : Nat) (out : List Bool) : Configuration t (s+5) :=
  ⟨(body callback slots).start,heads slots ambientH out,bank slots ambientT K cap j out⟩

theorem body_step {t s : Nat} (callback : Machine t s) (slots : Fin 2 → Fin t)
    (hi : Function.Injective slots)
    (ambientH : List Bool → Fin t → Nat) (ambientT : List Bool → Fin t → List Bool)
    (K cap j cost : Nat) (emit : BitInput K → List Bool) (out : List Bool)
    (hj : j+1 < 2^K) (hc : 2*K ≤ cap)
    (hcallback : Step callback cost (heads slots ambientH out) (bank slots ambientT K cap j out)
      (heads slots ambientH (out ++ emit (bitInputOfCode K j)))
      (bank slots ambientT K cap j (out ++ emit (bitInputOfCode K j)))) :
    Step (body callback slots) (cost+1+(4*K+2))
      (heads slots ambientH out) (bank slots ambientT K cap j out)
      (heads slots ambientH (out ++ emit (bitInputOfCode K j)))
      (bank slots ambientT K cap (j+1) (out ++ emit (bitInputOfCode K j))) :=
  hcallback.seq (increment_step slots hi ambientH ambientT K cap j _ hj hc)

noncomputable def loop {t s : Nat} (callback : Machine t s) (slots : Fin 2 → Fin t) :=
  CloseoutRowsDegreeLoop.machine (body callback slots)

theorem loop_step {t s : Nat} (callback : Machine t s) (slots : Fin 2 → Fin t)
    (hi : Function.Injective slots)
    (ambientH : List Bool → Fin t → Nat) (ambientT : List Bool → Fin t → List Bool)
    (K cap cost total : Nat) (emit : BitInput K → List Bool) (out : List Bool)
    (htotal : total < 2^K) (hc : 2*K ≤ cap)
    (hcallback : ∀ j < total, ∀ pre,
      Step callback cost (heads slots ambientH pre) (bank slots ambientT K cap j pre)
        (heads slots ambientH (pre ++ emit (bitInputOfCode K j)))
        (bank slots ambientT K cap j (pre ++ emit (bitInputOfCode K j)))) :
    Step (loop callback slots) (total*(cost+4*K+6)+3)
      (Fin.addCases (heads slots ambientH out) (fun _ : Fin 1 => 1))
      (Fin.addCases (bank slots ambientT K cap 0 out) (fun _ : Fin 1 => CompareMachine.word total))
      (Fin.addCases (heads slots ambientH (out ++ emitted K emit total)) (fun _ : Fin 1 => 1))
      (Fin.addCases (bank slots ambientT K cap total (out ++ emitted K emit total))
        (fun _ : Fin 1 => CompareMachine.word total)) := by
  obtain ⟨r,hr,hf,_⟩ := CloseoutRowsDegreeLoop.loop_run (body callback slots)
    (entry callback slots ambientH ambientT K cap) (fun j=>emit (bitInputOfCode K j))
    (cost+1+(4*K+2)) total (by intros; rfl) (by
      intro j hj pre
      exact body_step callback slots hi ambientH ambientT K cap j cost emit pre
        (by omega) hc (hcallback j hj pre)) out
  have h := Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)
  have hcost : cost+1+(4*K+2)+3=cost+4*K+6 := by omega
  simpa only [loop,entry,emitted,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,hcost] using h

noncomputable def machine {t s : Nat} (callback : Machine t s) (slots : Fin 2 → Fin t) :=
  Composition.machine (loop callback slots) (TapeEmbedding.machine 1 callback)

def budget (K cost : Nat) := (2^K-1)*(cost+4*K+6)+cost+4

theorem enumerate_step {t s : Nat} (callback : Machine t s) (slots : Fin 2 → Fin t)
    (hi : Function.Injective slots)
    (ambientH : List Bool → Fin t → Nat) (ambientT : List Bool → Fin t → List Bool)
    (K cap cost : Nat) (emit : BitInput K → List Bool) (out : List Bool) (hc : 2*K ≤ cap)
    (hcallback : ∀ j < 2^K, ∀ pre,
      Step callback cost (heads slots ambientH pre) (bank slots ambientT K cap j pre)
        (heads slots ambientH (pre ++ emit (bitInputOfCode K j)))
        (bank slots ambientT K cap j (pre ++ emit (bitInputOfCode K j)))) :
    Step (machine callback slots) (budget K cost)
      (Fin.addCases (heads slots ambientH out) (fun _ : Fin 1 => 1))
      (Fin.addCases (bank slots ambientT K cap 0 out) (fun _ : Fin 1 => CompareMachine.word (2^K-1)))
      (Fin.addCases (heads slots ambientH (out ++ (LiveEnumeration.binary K).flatMap emit))
        (fun _ : Fin 1 => 1))
      (Fin.addCases (bank slots ambientT K cap (2^K-1)
        (out ++ (LiveEnumeration.binary K).flatMap emit))
        (fun _ : Fin 1 => CompareMachine.word (2^K-1))) := by
  have hp := Nat.two_pow_pos K
  have htotal : 2^K-1 < 2^K := by omega
  have first := loop_step callback slots hi ambientH ambientT K cap cost (2^K-1) emit out
    htotal hc (by intro j hj pre; exact hcallback j (by omega) pre)
  have last := (hcallback (2^K-1) htotal (out ++ emitted K emit (2^K-1))).embed
    (fun _ : Fin 1 => 1) (fun _ : Fin 1 => CompareMachine.word (2^K-1))
  have hall := first.seq last
  have he : emitted K emit (2^K-1) ++ emit (bitInputOfCode K (2^K-1)) =
      (LiveEnumeration.binary K).flatMap emit := by
    calc
      _ = emitted K emit ((2^K-1)+1) := by
        simp only [emitted,List.range_succ,List.flatMap_append,List.flatMap_cons,
          List.flatMap_nil,List.append_nil]
      _ = emitted K emit (2^K) := by rw [show 2^K-1+1=2^K by omega]
      _ = _ := emitted_all K emit
  have hb : (2^K-1)*(cost+4*K+6)+3+1+cost=budget K cost := by unfold budget; omega
  simpa only [machine,hb,List.append_assoc,he] using hall

end NearCubicWires.P1Closure.BinaryEnumerator
