import Proof.MachineModel.NativeState
import Proof.CaseAnalysis.RowsFamilyLoop

/-! The original raw polynomial family executes with one retained native
bank and one literal outer driver, including empty polynomials/families. -/
namespace NearCubicWires.ExtIncidence.NativeFamily
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch NativeFanoutLayout
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rawWord {B : ℕ} (ms : List (List (Fin B))):=stream (rawIndices ms)
def emit {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) (Q w : ℕ)
    (ms : List (List (Fin gs.length))):=
  (CloseoutRowsSharedDigits.cuts gs Q w (rawRows ms)).flatMap
    (MatrixScoreBatch.cutWord (NativeWidth.width gs Q))
def cost {n : ℕ} (gs : List (ExactThresholdGate n)) (Q w : ℕ) :
    List (List (List (Fin gs.length)))→ℕ
  | []=>0
  | ms::ps=>max (NativeRound.budget gs Q w (rawIndices ms)) (cost gs Q w ps)

theorem member_cost {n : ℕ} (gs : List (ExactThresholdGate n)) (Q w : ℕ)
    (ps : List (List (List (Fin gs.length)))) (ms : List (List (Fin gs.length))) (hm : ms∈ps) :
    NativeRound.budget gs Q w (rawIndices ms) ≤ cost gs Q w ps:=by
  induction ps with
  | nil=>simp at hm
  | cons p ps ih=>
    rcases List.mem_cons.mp hm with rfl | hm
    · exact Nat.le_max_left _ _
    · exact (ih hm).trans (Nat.le_max_right _ _)

noncomputable def machine:=CloseoutRowsDegreeLoop.machine NativeRound.machine
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) (Q w : ℕ)
    (ps : List (List (List (Fin gs.length)))):=ps.length*(cost gs Q w ps+3)+3
noncomputable def entry {n : ℕ} (gs : List (ExactThresholdGate n)) (Q w : ℕ)
    (ps : List (List (List (Fin gs.length)))) (pre tail : List Bool)
    (H : Fin 277→ℕ) (A : Fin 277→List Bool) (j : ℕ) (out : List Bool):=
    (⟨NativeRound.machine.start,
      NativeState.heads H (pre.length+((ps.take j).flatMap rawWord).length) out,
      NativeState.tapes A (NativeMaster.words gs Q w) (NativeMeasured.capacity gs Q w)
        (pre++ps.flatMap rawWord++tail) out⟩ : Configuration 277 _)

theorem family_run {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) (Q w : ℕ)
    (ps : List (List (List (Fin gs.length)))) (out pre tail : List Bool)
    (hw : ∀ ms∈ps,ms.length < 2^w) (hQ : 1 ≤ Q) (H : Fin 277→ℕ) (A : Fin 277→List Bool)
    (mh : ∀ j,H (sources j)=0) (ma : ∀ j,A (sources j)=NativeMaster.words gs Q w j) :
    ∃ actual,runFrom machine (budget gs Q w ps)
      (RepeatMachine.cfg 0 (entry gs Q w ps pre tail H A 0 out) ps.length 1)=some actual ∧
      actual.final=RepeatMachine.cfg 3
        (entry gs Q w ps pre tail H A ps.length (out++ps.flatMap (emit gs Q w))) ps.length 1 ∧
      actual.steps ≤ budget gs Q w ps:=by
  let packet:=fun j=>ps.getD j []
  let output:=fun j=>emit gs Q w (packet j)
  have supplier : ∀ j<ps.length,∀ acc,∃ actual,
      runFrom NativeRound.machine (cost gs Q w ps) (entry gs Q w ps pre tail H A j acc)=some actual ∧
      actual.final.heads=(entry gs Q w ps pre tail H A (j+1) (acc++output j)).heads ∧
      actual.final.tapes=(entry gs Q w ps pre tail H A (j+1) (acc++output j)).tapes ∧
      actual.steps ≤ cost gs Q w ps:=by
    intro j hj acc
    have hm : packet j∈ps:=by
      dsimp only [packet]
      rw [List.getD_eq_getElem ps [] hj]
      exact List.getElem_mem hj
    let before:=pre++(ps.take j).flatMap rawWord
    let after:=(ps.drop (j+1)).flatMap rawWord++tail
    have hs : before++rawWord (packet j)++after=pre++ps.flatMap rawWord++tail:=by
      rw [CloseoutRowsFamilyLoop.split_word ps [] rawWord j hj]
      simp only [before,after,packet,List.append_assoc]
    have hp : before.length=pre.length+((ps.take j).flatMap rawWord).length:=List.length_append
    have hn : before.length+(rawWord (packet j)).length=
        pre.length+((ps.take (j+1)).flatMap rawWord).length:=by
      dsimp only [packet]
      rw [CloseoutRowsFamilyLoop.next_word ps [] rawWord j hj,hp]
      omega
    have run:=NativeState.round_step gs (packet j) Q w acc before after (hw _ hm) hQ H A mh ma
    dsimp only at run
    change Step NativeRound.machine _ (NativeState.heads H before.length acc)
      (NativeState.tapes A _ _ (before++rawWord (packet j)++after) acc)
      (NativeState.heads H (before.length+(rawWord (packet j)).length) (acc++output j))
      (NativeState.tapes A _ _ (before++rawWord (packet j)++after) (acc++output j)) at run
    rw [hs,hn,hp] at run
    exact run.enlarge (member_cost gs Q w ps (packet j) hm)
  obtain ⟨actual,run,final,bound⟩:=CloseoutRowsDegreeLoop.loop_run NativeRound.machine
    (entry gs Q w ps pre tail H A) output (cost gs Q w ps) ps.length
    (by intro j hj acc;rfl) supplier out
  have he : (List.range ps.length).flatMap output=ps.flatMap (emit gs Q w):=
    CloseoutRowsFamilyLoop.flatMap_index ps [] (emit gs Q w)
  rw [he] at final
  exact ⟨actual,run,final,bound⟩

end NearCubicWires.ExtIncidence.NativeFamily
