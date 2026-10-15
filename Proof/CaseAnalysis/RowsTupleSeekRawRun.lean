import Proof.CaseAnalysis.RowsTupleSeekRawLoop
import Proof.MachineModel.Encoding

namespace NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek.RawLoop
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem remaining {t s : ℕ} (p : Machine t s) (cost Q : ℕ)
    (H : ℕ → Fin t → ℕ) (A : ℕ → Fin t → List Bool)
    (supplier : ∀ j < Q,Step p cost (H j) (A j) (H (j+1)) (A (j+1)))
    (j n : ℕ) (hn : j+n=Q) (pre tail : List Bool) :
    ∃ time ≤ n*(cost+4)+1,Timed (loop p) time
      (entry p 0 (H j) (A j) pre.length (pre++List.replicate n true++false::tail))
      (final (s:=s) (H (j+n)) (A (j+n)) (pre.length+n) (pre++List.replicate n true++false::tail)) := by
  induction n generalizing j pre with
  | zero=>
    refine ⟨1,by simp,?_⟩
    simpa using probe p (H j) (A j) pre tail false
  | succ n ih=>
    let index := pre++true::(List.replicate n true++false::tail)
    obtain ⟨a,ha,tr⟩ := round (supplier j (by omega)) pre.length index
    obtain ⟨b,hb,tb⟩ := ih (j+1) (by omega) (pre++[true])
    have begin := probe p (H j) (A j) pre (List.replicate n true++false::tail) true
    have same : (pre++[true])++List.replicate n true++false::tail=index := by
      simp [index,List.append_assoc]
    rw [same] at tb
    simp only [List.length_append,List.length_singleton] at tb
    have all := begin.trans (tr.trans tb)
    refine ⟨1+(a+b),by nlinarith,?_⟩
    have he : j+1+n=j+(n+1) := by omega
    simpa only [index,List.replicate_succ,List.cons_append,List.append_assoc,he,Nat.add_assoc,
      show 1+n=n+1 by omega] using all

theorem raw_run {t s : ℕ} (p : Machine t s) (cost Q : ℕ)
    (H : ℕ → Fin t → ℕ) (A : ℕ → Fin t → List Bool)
    (supplier : ∀ j < Q,Step p cost (H j) (A j) (H (j+1)) (A (j+1)))
    (pre tail : List Bool) :
    Step (machine p) (Q*(cost+4)+5)
      (heads (H 0) pre.length) (data (A 0) (pre++ExtIncidence.block Q++tail))
      (heads (H Q) (pre.length+(ExtIncidence.block Q).length)) (data (A Q) (pre++ExtIncidence.block Q++tail)) := by
  obtain ⟨time,ht,tr⟩ := remaining p cost Q H A supplier 0 Q (by omega) (pre++[true]) tail
  simp only [Nat.zero_add,List.length_append,List.length_singleton] at tr
  have source : (pre++[true])++List.replicate Q true++false::tail=pre++ExtIncidence.block Q++tail := by
    simp [ExtIncidence.block,List.replicate_succ,List.append_assoc]
  rw [source] at tr
  obtain ⟨r,hr,rf,_⟩ := tr.run (by simp [loop,final,RecoveryCalls.machine,RecoveryCalls.stopped])
  have hrun := (Step.of_run hr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)).enlarge ht
  have first := advance_run (H 0) (A 0) pre.length (pre++ExtIncidence.block Q++tail)
  have last := advance_run (H Q) (A Q) (pre.length+1+Q) (pre++ExtIncidence.block Q++tail)
  have whole := (first.seq hrun).seq last
  have timeEq : 1+1+(Q*(cost+4)+1)+1+1=Q*(cost+4)+5 := by omega
  have posEq : pre.length+1+Q+1=pre.length+(ExtIncidence.block Q).length := by
    rw [ExtIncidence.block_length];omega
  simpa only [machine,timeEq,posEq] using whole

end NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek.RawLoop
