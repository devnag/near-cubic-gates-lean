import Proof.CaseAnalysis.RowsEstimatorDriverPasses

/-! Physically erase the bounded private driver bank, then return all
scratch heads, using only the two retained D words and their existing log. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverClean
open LocalBitMultitape RecoveryExecution RecoveryRootRound StablePartition.Workspace
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem assoc {α : Type} {t : ℕ} (f : Fin t → α) (a b c : α) :
    (Fin.addCases (motive:=fun _=>α) (Fin.addCases (motive:=fun _=>α) f (fun _ : Fin 1 => a)) (![b,c] : Fin 2 → α) : Fin (t+1+2) → α)=
      (Fin.addCases (motive:=fun _=>α) (Fin.addCases (motive:=fun _=>α) f (![a,b] : Fin 2 → α)) (fun _ : Fin 1 => c) : Fin (t+2+1) → α) := by
  funext i
  refine Fin.addCases (m:=t) (n:=3) (fun j => ?_) (fun j => ?_) i
  · change ((Fin.addCases (motive:=fun _=>α) (Fin.addCases (motive:=fun _=>α) f (fun _ : Fin 1 => a)) (![b,c] : Fin 2 → α)) ((j.castAdd 1).castAdd 2) : α)=
      (Fin.addCases (motive:=fun _=>α) (Fin.addCases (motive:=fun _=>α) f (![a,b] : Fin 2 → α)) (fun _ : Fin 1 => c)) ((j.castAdd 2).castAdd 1)
    simp
  · fin_cases j
    · change ((Fin.addCases (motive:=fun _=>α) (Fin.addCases (motive:=fun _=>α) f (fun _ : Fin 1 => a)) (![b,c] : Fin 2 → α)) (((0 : Fin 1).natAdd t).castAdd 2) : α)=
        (Fin.addCases (motive:=fun _=>α) (Fin.addCases (motive:=fun _=>α) f (![a,b] : Fin 2 → α)) (fun _ : Fin 1 => c)) (((0 : Fin 2).natAdd t).castAdd 1)
      simp
    · change ((Fin.addCases (motive:=fun _=>α) (Fin.addCases (motive:=fun _=>α) f (fun _ : Fin 1 => a)) (![b,c] : Fin 2 → α)) ((0 : Fin 2).natAdd (t+1)) : α)=
        (Fin.addCases (motive:=fun _=>α) (Fin.addCases (motive:=fun _=>α) f (![a,b] : Fin 2 → α)) (fun _ : Fin 1 => c)) (((1 : Fin 2).natAdd t).castAdd 1)
      simp
    · change ((Fin.addCases (motive:=fun _=>α) (Fin.addCases (motive:=fun _=>α) f (fun _ : Fin 1 => a)) (![b,c] : Fin 2 → α)) ((1 : Fin 2).natAdd (t+1)) : α)=
        (Fin.addCases (motive:=fun _=>α) (Fin.addCases (motive:=fun _=>α) f (![a,b] : Fin 2 → α)) (fun _ : Fin 1 => c)) ((0 : Fin 1).natAdd (t+2))
      simp

theorem same {α : Type} (a : α) : (![a,a] : Fin 2 → α)=fun _ => a := by
  funext i
  fin_cases i <;> rfl

theorem heads_bridge (t D pos : ℕ) (data : Fin t → List Bool) :
    DriverSweep.heads t pos=(DriverReturnMany.cfg 0 D pos data).heads := by
  unfold DriverSweep.heads DriverReturnMany.cfg Rewind.config DriverReturnMany.heads
  simpa only [same] using
    assoc (fun _ : Fin t => pos) 0 0 0

theorem words_bridge {t : ℕ} (D pos : ℕ) (data : Fin t → List Bool) :
    DriverSweep.words D pos data=
      (DriverReturnMany.cfg 0 D pos (fun i => overlay (List.replicate pos false) (data i))).tapes := by
  unfold DriverSweep.words RecoveryScratchErase.tapes DriverSweep.extra
    DriverReturnMany.cfg Rewind.config DriverReturnMany.words
  simpa only [same] using
    assoc (fun i => overlay (List.replicate pos false) (data i))
      (List.replicate D true) (List.replicate D true) (List.replicate (D+1) false)

noncomputable def machine (t K : ℕ) :=
  Composition.machine (DriverPasses.forward t K) (DriverPasses.back t K)

theorem run {t : ℕ} (D K : ℕ) (data : Fin t → List Bool)
    (bound : ∀ i,(data i).length≤K*D) : ∃ r,
    LocalBitMultitape.run (machine t K) (K*(5*D+10)+1) (DriverSweep.words D 0 data)=some r ∧
      r.final.tapes=DriverSweep.words D (K*D) (fun _ : Fin t => []) ∧
      (∀ i,r.final.heads i=0) ∧ r.steps=K*(5*D+10)+1 := by
  obtain ⟨first,hf,fh,ft,fs⟩ := DriverPasses.forward_run D K data
  let erased := fun _ : Fin t => List.replicate (K*D) false
  have he : (fun i => overlay (List.replicate (K*D) false) (data i))=erased := by
    funext i
    simp [overlay,List.drop_eq_nil_of_le (bound i),erased]
  obtain ⟨last,hl,lh,lt,ls⟩ := DriverPasses.back_run D K (K*D) erased
  have dock : Composition.restart first.final (DriverPasses.back t K).start=
      DriverIterate.cfg (DriverReturnMany.machine t) K
        (DriverReturnMany.cfg 0 D (K*D) erased).heads (DriverReturnMany.cfg 0 D (K*D) erased).tapes := by
    apply configuration_ext
    · rfl
    · change first.final.heads=(DriverReturnMany.cfg 0 D (K*D) erased).heads
      rw [fh]
      exact heads_bridge t D (K*D) erased
    · change first.final.tapes=(DriverReturnMany.cfg 0 D (K*D) erased).tapes
      rw [ft,words_bridge,he]
  rw [← dock] at hl
  have hj := Composition.run_join (DriverPasses.forward t K) (DriverPasses.back t K) _ _ _ first last hf hl
  have ht : K*(3*D+5)+1+K*(2*D+5)=K*(5*D+10)+1 := by ring
  rw [ht] at hj
  have inputHeads : DriverSweep.heads t 0=fun _ => 0 := by
    funext i
    refine Fin.addCases (m:=t+1) (n:=2) (fun j => ?_) (fun j => ?_) i
    · refine Fin.addCases (m:=t) (n:=1) (fun j => ?_) (fun j => ?_) j <;> simp [DriverSweep.heads]
    · simp [DriverSweep.heads]
  have inputEq : Composition.leftConfig (DriverIterate.states 4 K)
      (DriverIterate.cfg (DriverSweep.round t) K (DriverSweep.heads t 0) (DriverSweep.words D 0 data))=
      initialConfiguration (machine t K) (DriverSweep.words D 0 data) := by
    apply configuration_ext
    · rfl
    · exact inputHeads
    · rfl
  rw [inputEq] at hj
  refine ⟨Composition.joinedReceipt first last,hj,?_,?_,?_⟩
  · change last.final.tapes=_
    rw [lt,words_bridge]
    simp [erased,overlay]
  · intro i
    change last.final.heads i=0
    rw [lh,show K*D-K*(D+1)=0 by rw [Nat.mul_add];omega]
    rw [← heads_bridge t D 0 erased,inputHeads]
  · change first.steps+1+last.steps=_
    rw [fs,ls,ht]

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverClean
