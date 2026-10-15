import Proof.SourceAssembly.SourceThresholdGate

/- Paid exact THR TOP field: retained native n header, n alternating signed
unit weights, strict target0, and the ordinary outer frame terminator. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace SourceAssemblyThresholdTop
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open RecoveryRootRound CloseoutRowsEstimatorParity RepairSource.VerifierDecoding RecoveryExecution
noncomputable section

def H (out : Fin 2→List Bool) (i : Fin 6):=if i=2 then (out 0).length else if i=3 then (out 1).length else if i=4 then 1 else 0
def A (n C : Nat) (flag : Bool) (out : Fin 2→List Bool) (i : Fin 6):=
  if i=0 then frame (natWord n) else if i=1 then [flag] else if i=2 then out 0 else if i=3 then out 1 else
  if i=4 then CompareMachine.word n else List.replicate C false
def input (n C : Nat) (i : Fin 6):=if i=1 then [] else A n C false (fun _=>[]) i
def inputHeads:=H (fun _=>[])
def prefixOut (n : Nat) : Fin 2→List Bool:=![Fragment.word false (natWord n),[]]
def loopOut (n : Nat):=Alternating.emittedPrefix Alternating.thresholdStrokes n (prefixOut n)
def finalOut (n : Nat):=fun i=>loopOut n i++Gate.ending i

def boot : Machine 6 2 where
  descriptionBits:=0
  start:=0
  halted:=fun s=>s.val==1
  rule:=fun _ _=>some ⟨1,(fun i=>if i=1 then some false else none),fun _=>.stay⟩
def prefixSlots : Fin 3→Fin 6:=![0,2,5]
def loopSlots : Fin 4→Fin 6:=![1,2,3,4]
def finishSlots : Fin 3→Fin 6:=![1,2,3]
def header:=RecoveryFocus.machine prefixSlots (Fragment.reusable false)
def loop:=RecoveryFocus.machine loopSlots (Alternating.machine Alternating.thresholdStrokes)
def finish:=RecoveryFocus.machine finishSlots (Glyph.machine Gate.finishStrokes)
def machine:=Composition.machine boot (Composition.machine header (Composition.machine loop finish))
def budget (n : Nat):=4*(natWord n).length+21*n+29

theorem boot_run (n C : Nat) : Step boot 1 inputHeads (input n C) inputHeads (A n C false (fun _=>[])) := by
  have hs : step boot (RecoveryCalls.restarted boot inputHeads (input n C))=
      some (⟨1,inputHeads,A n C false (fun _=>[])⟩ : Configuration 6 2) := by
    simp [step,boot,RecoveryCalls.restarted]
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;>rfl
    · funext i;fin_cases i <;>simp [applyAction,input,A,H,inputHeads,writeTapeBit]
  obtain ⟨r,hr,hf,_⟩:=(Timed.single (by rfl) hs).run (by rfl)
  exact Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)

theorem header_run (n C : Nat) (hC : 2*(natWord n).length+1≤C) :
    Step header (4*(natWord n).length+4) inputHeads (A n C false (fun _=>[]))
      (H (prefixOut n)) (A n C false (prefixOut n)) := by
  have h:=Gate.fragment_run false (natWord n) [] [] C hC
  simp only [List.append_nil,List.nil_append,List.length_nil] at h
  refine CloseoutRowsEstimator.SubstitutionDock.run _ prefixSlots (by decide) _ _ _ _ _ _ _ _ h ?_ ?_ ?_ ?_ ?_ ?_
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i hi;fin_cases i <;>first | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl) | exact False.elim (hi 2 rfl) | rfl
  · intro i hi;fin_cases i <;>first | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl) | exact False.elim (hi 2 rfl) | rfl

theorem loop_run (n C : Nat) : Step loop (21*n+3) (H (prefixOut n)) (A n C false (prefixOut n))
    (H (loopOut n)) (A n C (Alternating.flag n) (loopOut n)) := by
  have h:=Alternating.alternating_run Alternating.thresholdStrokes [] n (prefixOut n)
  have hc : n*(2*Alternating.thresholdStrokes.length+5)+3=21*n+3:=by simp [Alternating.thresholdStrokes];omega
  rw [hc] at h
  refine CloseoutRowsEstimator.SubstitutionDock.run _ loopSlots (by decide) _ _ _ _ _ _ _ _ h ?_ ?_ ?_ ?_ ?_ ?_
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i hi;fin_cases i <;>first | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl) | exact False.elim (hi 2 rfl) | exact False.elim (hi 3 rfl) | rfl
  · intro i hi;fin_cases i <;>first | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl) | exact False.elim (hi 2 rfl) | exact False.elim (hi 3 rfl) | rfl

theorem finish_run (n C : Nat) : Step finish 18 (H (loopOut n)) (A n C (Alternating.flag n) (loopOut n))
    (H (finalOut n)) (A n C (Alternating.flag n) (finalOut n)) := by
  have h:=Glyph.word_run Gate.finishStrokes (Alternating.flag n) [Alternating.flag n] 0 (loopOut n) rfl
  have hb (i : Fin 2) : Glyph.word Gate.finishStrokes (Alternating.flag n) i=Gate.ending i:=congrFun (Gate.finish_bytes _) i
  simp only [hb] at h
  refine CloseoutRowsEstimator.SubstitutionDock.run _ finishSlots (by decide) _ _ _ _ _ _ _ _ h ?_ ?_ ?_ ?_ ?_ ?_
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i hi;fin_cases i <;>first | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl) | exact False.elim (hi 2 rfl) | rfl
  · intro i hi;fin_cases i <;>first | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl) | exact False.elim (hi 2 rfl) | rfl

def payload (n : Nat):=natWord n++(List.range n).flatMap (fun j=>[Alternating.flag j,true,false,true])++bitWeight false

theorem final_exact (n : Nat) : finalOut n 0=frame (payload n) := by
  have hw (j : Nat) : Glyph.word Alternating.thresholdStrokes (Alternating.flag j) 0=
      Fragment.body [Alternating.flag j,true,false,true]:=congrFun (Alternating.threshold_bytes _) 0
  simp only [finalOut,loopOut,Alternating.emittedPrefix,prefixOut,Matrix.cons_val_zero,hw,
    Gate.ending,payload,Fragment.frame_eq,Fragment.word,Bool.false_eq_true,ite_false,List.append_nil,
    Fragment.body,List.flatMap_append,List.flatMap_assoc,List.append_assoc]

theorem run (n C : Nat) (hC : 2*(natWord n).length+1≤C) :
    Step machine (budget n) inputHeads (input n C) (H (finalOut n)) (A n C (Alternating.flag n) (finalOut n)) := by
  exact ((boot_run n C).seq ((header_run n C hC).seq ((loop_run n C).seq (finish_run n C)))).enlarge
    (by unfold budget;omega)

end
end SourceAssemblyThresholdTop
