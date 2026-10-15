import Proof.MachineModel.OrdinaryAmplifierReplayPayload

/-! Execute an arbitrary selected ordinary source, pay its trace-derived
head reset, then frame its exact amplifier-schema output on a fresh bank. -/
namespace NearCubicWires.RepairOrdinary.AmplifierReplay.Dock
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def slots {t : ℕ} (out : Fin t) (i : Fin 28) : Fin (t+1+27) :=
  Fin.addCases (m:=1) (n:=27) (motive:=fun _ => Fin (t+1+27))
    (fun _ => (out.castAdd 1).castAdd 27) (fun j => j.natAdd (t+1)) i
def output (t : ℕ) : Fin (t+1+27) := (26 : Fin 27).natAdd (t+1)

theorem slots_injective {t : ℕ} (out : Fin t) : Function.Injective (slots out) := by
  intro i j h
  revert h
  refine Fin.addCases (m:=1) (n:=27) (fun a => ?_) (fun a => ?_) i <;>
    refine Fin.addCases (m:=1) (n:=27) (fun b => ?_) (fun b => ?_) j
  · intro _; fin_cases a; fin_cases b; rfl
  · intro h
    have hv := congrArg Fin.val h
    simp only [slots,Fin.addCases_left,Fin.addCases_right,Fin.val_castAdd,Fin.val_natAdd] at hv
    omega
  · intro h
    have hv := congrArg Fin.val h
    simp only [slots,Fin.addCases_left,Fin.addCases_right,Fin.val_castAdd,Fin.val_natAdd] at hv
    omega
  · intro h
    have hv := congrArg Fin.val h
    simp only [slots,Fin.addCases_right,Fin.val_natAdd] at hv
    have he : a=b := Fin.ext (by omega)
    rw [he]

def reset {t s : ℕ} (p : Machine t s) := TapeEmbedding.machine 27 (Rewind.machine p)
def post {t : ℕ} (out : Fin t) := RecoveryFocus.machine (slots out) Payload.machine
def machine {t s : ℕ} (p : Machine t s) (out : Fin t) := Composition.machine (reset p) (post out)
def input {t : ℕ} (data : Fin t→List Bool) : Fin (t+1+27)→List Bool :=
  Fin.addCases (motive:=fun _ : Fin (t+1+27) => List Bool)
    (Fin.addCases (motive:=fun _ : Fin (t+1) => List Bool) data (fun _ : Fin 1 => []))
    (fun _ : Fin 27 => [])
def budget (b n : ℕ) (table : List Bool) := 2*b+2+1+Payload.budget n table

theorem bank_heads {t s : ℕ} (out : Fin t) (c : Configuration (t+1) s)
    (hh : ∀ i,c.heads i=0) :
    ∀ j,(TapeEmbedding.config (fun _ : Fin 27 => 0) (fun _ : Fin 27 => []) c).heads (slots out j)=0 := by
  intro j
  refine Fin.addCases (m:=1) (n:=27) (fun i => ?_) (fun i => ?_) j
  · simpa only [slots,Fin.addCases_left,TapeEmbedding.config] using hh (out.castAdd 1)
  · simp only [slots,Fin.addCases_right,TapeEmbedding.config]

theorem bank_tapes {t s : ℕ} (out : Fin t) (c : Configuration (t+1) s)
    (word : List Bool) (ht : c.tapes (out.castAdd 1)=word) :
    ∀ j,(TapeEmbedding.config (fun _ : Fin 27 => 0) (fun _ : Fin 27 => []) c).tapes (slots out j)=
      Prepare.input word j := by
  intro j
  refine Fin.addCases (m:=1) (n:=27) (fun i => ?_) (fun i => ?_) j
  · fin_cases i
    simp only [slots,Fin.addCases_left,TapeEmbedding.config,Fin.addCases_left]
    change c.tapes (out.castAdd 1)=word
    exact ht
  · simp only [slots,Fin.addCases_right,TapeEmbedding.config]
    have hne : (i.natAdd 1 : Fin 28)≠0 := by
      intro h
      have hv := congrArg Fin.val h
      change 1+i.val=0 at hv
      omega
    change []=(if i.natAdd 1=0 then word else [])
    rw [if_neg hne]

theorem dock_run {t s : ℕ} (p : Machine t s) (out : Fin t) (data : Fin t→List Bool)
    (b n : ℕ) (table : List Bool) (hlen : table.length=2^n)
    (source : ExecutionReceipt t s) (hr : run p b data=some source)
    (hout : source.final.tapes out=frame n.bits++table) :
    ∃ r,run (machine p out) (budget b n table) (input data)=some r ∧
      r.final.tapes (output t)=frame (frame n.bits++table) ∧ r.steps ≤ budget b n table := by
  have hs := runFrom_steps_le p b _ source hr
  obtain ⟨base,hb,ht,hh,hsteps,_⟩ := Rewind.reset_run p b data source hr
  have hbound : 2*source.steps+2 ≤ 2*b+2 := by omega
  have hm := run_moreFuel (Rewind.machine p) (2*source.steps+2)
    (2*b+2-(2*source.steps+2)) _ base hb
  rw [Nat.add_sub_of_le hbound] at hm
  have he := TapeEmbedding.run_embed (Rewind.machine p) (fun _ : Fin 27 => 0)
    (fun _ : Fin 27 => []) _ _ base hm
  let first := TapeEmbedding.receipt (fun _ : Fin 27 => 0) (fun _ : Fin 27 => []) base
  obtain ⟨last,hl,houtLast,hstepsLast⟩ := Payload.focused_run (slots out) (slots_injective out)
    first.final.heads first.final.tapes n table hlen
    (bank_heads out base.final hh) (bank_tapes out base.final _ ((ht out).trans hout))
  have hj := Composition.run_join (reset p) (post out) _ _ _ first last he hl
  have hi : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 27 => 0)
      (fun _ : Fin 27 => []) (initialConfiguration (Rewind.machine p)
        (Fin.addCases data (fun _ : Fin 1 => []))))=
      initialConfiguration (machine p out) (input data) := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m:=t+1) (n:=27) (fun j => ?_) (fun j => ?_) i <;>
        simp [Composition.leftConfig,TapeEmbedding.config,initialConfiguration,Fin.addCases]
    · rfl
  rw [hi] at hj
  refine ⟨Composition.joinedReceipt first last,hj,houtLast,?_⟩
  change base.steps+1+last.steps ≤ _
  unfold budget
  omega

end
end NearCubicWires.RepairOrdinary.AmplifierReplay.Dock
