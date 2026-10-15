import Proof.Supplier.EquationRowCutsForward

/-! Count actual right moves of an append-only output, then execute the
standard rewind. The retained unary count is the actual output head, not a
separately assumed or reconstructed length. -/
namespace NearCubicWires.RepairOrdinary.AppendOutputLength
open LocalBitMultitape RecoveryExecution
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def record {t s : ℕ} (p : Machine t s) (target : Fin t) : Machine (t+1) (s+2) :=
  { CursorRestore.machine p target with
    halted := fun q => Fin.addCases p.halted (fun _ : Fin 2 => true) q }

theorem recording_timed {t s space n : ℕ} {p : Machine t s} {c d : Configuration t s}
    (hp : Prefix p space n c d) (target : Fin t) (forward : CursorRestore.NoLeft p target) (count : ℕ) :
    ∃ delta,delta ≤ n ∧ d.heads target=c.heads target+delta ∧
      Timed (record p target) n (Rewind.recording c count) (Rewind.recording d (count+delta)) := by
  induction hp generalizing count with
  | refl c _ =>
    exact ⟨0,by omega,by omega,by simpa using Timed.refl (record p target) (Rewind.recording c count)⟩
  | @step n c d e _ hn hs _ ih =>
    obtain ⟨first,hfirst,hd,hstep⟩ := CursorRestore.record_step p target forward c d count hn hs
    obtain ⟨rest,hrest,he,ht⟩ := ih (count+first)
    refine ⟨first+rest,by omega,by omega,?_⟩
    have hstep' : step (record p target) (Rewind.recording c count)=some (Rewind.recording d (count+first)) := hstep
    have h := Timed.step (by simp [record,Rewind.recording,Rewind.config,hn]) hstep' ht
    simpa only [Nat.add_assoc] using h

def input {t : ℕ} (a : Fin t → List Bool) : Fin (t+1) → List Bool :=
  fun i => Fin.addCases (m := t) (n := 1) (motive := fun _ => List Bool) a (fun _ => []) i

theorem record_run {t s : ℕ} (p : Machine t s) (target : Fin t) (forward : CursorRestore.NoLeft p target)
    (fuel : ℕ) (a : Fin t → List Bool) (source : ExecutionReceipt t s) (hr : run p fuel a=some source) :
    ∃ r,run (record p target) source.steps (input a)=some r ∧
      r.final=Rewind.recording source.final (source.final.heads target) ∧ r.steps=source.steps := by
  obtain ⟨hp,hh⟩ := prefix_of_run p fuel (initialConfiguration p a) source hr
  obtain ⟨delta,_hd,hhead,ht⟩ := recording_timed hp target forward 0
  have he : delta=source.final.heads target := by simpa only [initialConfiguration,Nat.zero_add] using hhead.symm
  simp only [Nat.zero_add,he] at ht
  obtain ⟨r,hRun,hFinal,hSteps⟩ := ht.run (by simp [record,Rewind.recording,Rewind.config,hh])
  have hi : Rewind.recording (initialConfiguration p a) 0=initialConfiguration (record p target) (input a) := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      all_goals simp [Rewind.recording, Rewind.config, initialConfiguration]
    · rfl
  rw [hi] at hRun
  exact ⟨r,hRun,hFinal,hSteps⟩

def machine {t s : ℕ} (p : Machine t s) (target : Fin t) := Rewind.machine (record p target)

theorem length_run {t s : ℕ} (p : Machine t s) (target : Fin t) (forward : CursorRestore.NoLeft p target)
    (fuel : ℕ) (a : Fin t → List Bool) (source : ExecutionReceipt t s) (hr : run p fuel a=some source) :
    ∃ r,run (machine p target) (2*source.steps+2) (input (input a))=some r ∧
      (∀ i : Fin t,r.final.tapes ((i.castAdd 1).castAdd 1)=source.final.tapes i) ∧
      r.final.tapes (((0 : Fin 1).natAdd t).castAdd 1)=List.replicate (source.final.heads target) true ∧
      (∀ i,r.final.heads i=0) ∧ r.steps=2*source.steps+2 := by
  obtain ⟨recorded,hrecord,rf,rs⟩ := record_run p target forward fuel a source hr
  obtain ⟨r,hRun,rt,_rlog,rh,rsteps,_⟩ := Rewind.Workspace.reset_workspace (record p target)
    source.steps (input a) recorded hrecord 0
  have hi : (Fin.addCases (m := t+1) (n := 1) (motive := fun _ => List Bool)
      (input a) (fun _ => List.replicate 0 false))=input (input a) := rfl
  rw [hi,rs] at hRun
  refine ⟨r,hRun,?_,?_,rh,by omega⟩
  · intro i
    have h := rt (i.castAdd 1)
    rw [rf] at h
    simpa only [Rewind.recording,Rewind.config,Fin.addCases_left] using h
  · have h := rt ((0 : Fin 1).natAdd t)
    rw [rf] at h
    simpa only [Rewind.recording,Rewind.config,Fin.addCases_right] using h

end NearCubicWires.RepairOrdinary.AppendOutputLength
