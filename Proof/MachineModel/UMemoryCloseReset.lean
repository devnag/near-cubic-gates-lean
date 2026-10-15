import Proof.MachineModel.UMemoryCloseDelimiter

/-! One paid output-only reset encloses the complete emission prefix.
Its unary recording tape and the twenty raw-checker workspace tapes start
blank. Every other original tape and cursor retains the emitted endpoint. -/
namespace NearCubicWires.RepairOrdinary.UMemoryClose
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def oldSlot {t : ℕ} (i : Fin t) : Fin ((t+1)+20) := (i.castAdd 1).castAdd 20
def scratchSlot (t : ℕ) (i : Fin 20) : Fin ((t+1)+20) := i.natAdd (t+1)
def resultSlot (t : ℕ) : Fin ((t+1)+20) := scratchSlot t 18
def selected {t : ℕ} (event : Fin t) (i : Fin t) : Bool := decide (i=event)

def resetPrefix {t s : ℕ} (p : Machine t s) (event flag : Fin t) : Machine ((t+1)+20) ((s+2)+2) :=
  TapeEmbedding.machine 20 (MaskedReset.machine (emissionPrefix p event flag) (selected event))

def resetEntry {t s : ℕ} (c : Configuration t s) : Configuration ((t+1)+20) ((s+2)+2) :=
  TapeEmbedding.config (fun _ : Fin 20 => 0) (fun _ : Fin 20 => [])
    (Rewind.recording (Composition.leftConfig 2 c) 0)

def resetEndpoint {t s : ℕ} (event flag : Fin t) (c : Configuration t s) (steps : ℕ) :
    Configuration ((t+1)+20) ((s+2)+2) :=
  TapeEmbedding.config (fun _ : Fin 20 => 0) (fun _ : Fin 20 => [])
    (SelectiveReset.finished (s := s+2) (fun i => if selected event i then 0 else c.heads i)
      (delimited event flag c).tapes (steps+2))

theorem reset_prefix_run {t s : ℕ} (p : Machine t s) (event flag : Fin t)
    (fuel : ℕ) (c : Configuration t s) (r : ExecutionReceipt t s)
    (hr : runFrom p fuel c=some r) (hstart : c.heads event=0) :
    ∃ result,runFrom (resetPrefix p event flag) (2*r.steps+6) (resetEntry c)=some result ∧
      result.final=resetEndpoint event flag r.final r.steps ∧ result.steps=2*r.steps+6 := by
  obtain ⟨base,hbase,hbf,hbs⟩ := emission_prefix_run p event flag fuel c r hr
  have hhead : ∀ i, selected event i=true → base.final.heads i ≤ base.steps := by
    intro i hi
    have he : i=event := of_decide_eq_true hi
    subst i
    have hb := SelectiveReset.prefix_head
      (prefix_of_run (emissionPrefix p event flag) (fuel+2) (Composition.leftConfig 2 c) base hbase).1 event
    change base.final.heads event ≤ c.heads event+base.steps at hb
    simpa only [hstart,Nat.zero_add] using hb
  obtain ⟨reset,hrs,hrf,hrsteps,_⟩ := MaskedReset.reset_run (emissionPrefix p event flag)
    (selected event) (fuel+2) (Composition.leftConfig 2 c) base hbase hhead
  have he := TapeEmbedding.run_embed (MaskedReset.machine (emissionPrefix p event flag) (selected event))
    (fun _ : Fin 20 => 0) (fun _ : Fin 20 => []) _ _ reset hrs
  refine ⟨TapeEmbedding.receipt (fun _ : Fin 20 => 0) (fun _ : Fin 20 => []) reset,?_,?_,?_⟩
  · have htime : 2*base.steps+2=2*r.steps+6 := by omega
    rw [htime] at he
    exact he
  · change TapeEmbedding.config _ _ reset.final=resetEndpoint event flag r.final r.steps
    rw [hrf,hbf,hbs]
    rfl
  · change reset.steps=2*r.steps+6
    omega

@[simp] theorem reset_old_heads {t s : ℕ} (event flag i : Fin t) (c : Configuration t s) (steps : ℕ) :
    (resetEndpoint event flag c steps).heads (oldSlot i)=if i=event then 0 else c.heads i := by
  simp [resetEndpoint,oldSlot,TapeEmbedding.config,SelectiveReset.finished,Rewind.config,selected]

@[simp] theorem reset_old_tapes {t s : ℕ} (event flag i : Fin t) (c : Configuration t s) (steps : ℕ) :
    (resetEndpoint event flag c steps).tapes (oldSlot i)=(delimited event flag c).tapes i := by
  simp [resetEndpoint,oldSlot,TapeEmbedding.config,SelectiveReset.finished,Rewind.config]

@[simp] theorem reset_scratch_heads {t s : ℕ} (event flag : Fin t) (i : Fin 20)
    (c : Configuration t s) (steps : ℕ) :
    (resetEndpoint event flag c steps).heads (scratchSlot t i)=0 := by
  simp [resetEndpoint,scratchSlot,TapeEmbedding.config]

@[simp] theorem reset_scratch_tapes {t s : ℕ} (event flag : Fin t) (i : Fin 20)
    (c : Configuration t s) (steps : ℕ) :
    (resetEndpoint event flag c steps).tapes (scratchSlot t i)=[] := by
  simp [resetEndpoint,scratchSlot,TapeEmbedding.config]

theorem reset_flag {t s : ℕ} (event flag : Fin t) (c : Configuration t s) (steps : ℕ)
    (hne : event ≠ flag) :
    (resetEndpoint event flag c steps).scanned (oldSlot flag)=c.scanned flag := by
  simp only [Configuration.scanned,reset_old_heads,Ne.symm hne,↓reduceIte,reset_old_tapes]
  rw [delimited_other event flag flag c (Ne.symm hne)]

end NearCubicWires.RepairOrdinary.UMemoryClose
