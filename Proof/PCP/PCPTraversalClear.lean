import Proof.PCP.PCPTraversalBounds
import Proof.Amplification.RecoveryRowLookupTapes

/-! The traversal's physical scratch sweeps. The measured capacity driver
and the reset log are retained explicitly; arbitrary inactive source and
stack cursors keep their positions. These are executions of `clear` in the
fixed controller, not free replacement of dirty tape contents. -/
namespace NearCubicWires.RepairOrdinary.PCPTraversal
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem extend_injective {t : ℕ} (slot : Fin t → Fin 128) (last : Fin 128)
    (hi : Function.Injective slot) (hl : ∀ j,slot j≠last) :
    Function.Injective (Fin.addCases slot (fun _ : Fin 1 => last)) := by
  intro x y
  refine Fin.addCases (m:=t) (n:=1) (fun a => ?_) (fun a => ?_) x
  · refine Fin.addCases (m:=t) (n:=1) (fun b => ?_) (fun b => ?_) y
    · intro h
      simp only [Fin.addCases_left] at h
      rw [hi h]
    · intro h
      simp only [Fin.addCases_left,Fin.addCases_right] at h
      exact False.elim (hl a h)
  · refine Fin.addCases (m:=t) (n:=1) (fun b => ?_) (fun b => ?_) y
    · intro h
      simp only [Fin.addCases_left,Fin.addCases_right] at h
      exact False.elim (hl b h.symm)
    · intro _
      have h : a=b := Subsingleton.elim _ _
      rw [h]

theorem eraseSlots_injective {t : ℕ} (slot : Fin t → Fin 128)
    (hi : Function.Injective slot) (hd : ∀ j,slot j≠28) (hl : ∀ j,slot j≠127) :
    Function.Injective (eraseSlots slot) := by
  apply extend_injective _ _ (extend_injective slot 28 hi hd)
  intro j
  refine Fin.addCases (m:=t) (n:=1) (fun i => ?_) (fun i => ?_) j
  · simpa only [Fin.addCases_left] using hl i
  · simp only [Fin.addCases_right]
    decide

def clearedLocal (t cap log : ℕ) : Fin (t+1+1) → List Bool :=
  Fin.addCases (Fin.addCases (fun _ : Fin t => List.replicate cap false)
    (fun _ : Fin 1 => List.replicate cap true))
    (fun _ : Fin 1 => List.replicate (max log (cap+1)) false)
noncomputable def cleared {t : ℕ} (slot : Fin t → Fin 128) (cap log : ℕ)
    (ambient : Fin 128 → List Bool) : Fin 128 → List Bool :=
  install (eraseSlots slot) ambient (clearedLocal t cap log)

theorem cleared_slot {t : ℕ} (slot : Fin t → Fin 128)
    (hi : Function.Injective slot) (hd : ∀ j,slot j≠28) (hl : ∀ j,slot j≠127)
    (cap log : ℕ) (ambient : Fin 128 → List Bool) (j : Fin t) :
    cleared slot cap log ambient (slot j)=List.replicate cap false := by
  have h := install_slot (eraseSlots slot) (eraseSlots_injective slot hi hd hl)
    ambient (clearedLocal t cap log) ((j.castAdd 1).castAdd 1)
  change install (eraseSlots slot) ambient (clearedLocal t cap log) _=_
  simpa only [eraseSlots,clearedLocal,Fin.addCases_left] using h

theorem cleared_driver {t : ℕ} (slot : Fin t → Fin 128)
    (hi : Function.Injective slot) (hd : ∀ j,slot j≠28) (hl : ∀ j,slot j≠127)
    (cap log : ℕ) (ambient : Fin 128 → List Bool) :
    cleared slot cap log ambient 28=List.replicate cap true := by
  have h := install_slot (eraseSlots slot) (eraseSlots_injective slot hi hd hl)
    ambient (clearedLocal t cap log) (((0 : Fin 1).natAdd t).castAdd 1)
  change install (eraseSlots slot) ambient (clearedLocal t cap log) _=_
  simpa only [eraseSlots,clearedLocal,Fin.addCases_left,Fin.addCases_right] using h

theorem cleared_log {t : ℕ} (slot : Fin t → Fin 128)
    (hi : Function.Injective slot) (hd : ∀ j,slot j≠28) (hl : ∀ j,slot j≠127)
    (cap log : ℕ) (ambient : Fin 128 → List Bool) :
    cleared slot cap log ambient 127=List.replicate (max log (cap+1)) false := by
  have h := install_slot (eraseSlots slot) (eraseSlots_injective slot hi hd hl)
    ambient (clearedLocal t cap log) ((0 : Fin 1).natAdd (t+1))
  change install (eraseSlots slot) ambient (clearedLocal t cap log) _=_
  simpa only [eraseSlots,clearedLocal,Fin.addCases_right] using h

theorem cleared_other {t : ℕ} (slot : Fin t → Fin 128)
    (cap log : ℕ) (ambient : Fin 128 → List Bool) (i : Fin 128)
    (hi : ∀ j,slot j≠i) (hd : 28≠i) (hl : 127≠i) :
    cleared slot cap log ambient i=ambient i := by
  apply install_other
  intro j
  refine Fin.addCases (m:=t+1) (n:=1) (fun a => ?_) (fun a => ?_) j
  · refine Fin.addCases (m:=t) (n:=1) (fun b => ?_) (fun b => ?_) a
    · simpa only [eraseSlots,Fin.addCases_left] using hi b
    · simpa only [eraseSlots,Fin.addCases_left,Fin.addCases_right] using hd
  · simpa only [eraseSlots,Fin.addCases_right] using hl

theorem clear_run {t : ℕ} (slot : Fin t → Fin 128)
    (hi : Function.Injective slot) (hd : ∀ j,slot j≠28) (hl : ∀ j,slot j≠127)
    (cap log : ℕ) (heads : Fin 128 → ℕ) (ambient : Fin 128 → List Bool)
    (hb : ∀ j,(ambient (slot j)).length≤cap)
    (hdriver : ambient 28=List.replicate cap true)
    (hlog : ambient 127=List.replicate log false)
    (hh : ∀ j,heads (slot j)=0) (hhd : heads 28=0) (hhl : heads 127=0) :
    ∃ r,runFrom (clear slot).2 (2*cap+4) ⟨(clear slot).2.start,heads,ambient⟩=some r ∧
      r.final.heads=heads ∧ r.final.tapes=cleared slot cap log ambient ∧ r.steps=2*cap+4 := by
  have h := RecoveryScratchErase.erase_ready cap log (fun j => ambient (slot j)) hb
  apply h.focus_at (eraseSlots slot) (eraseSlots_injective slot hi hd hl) heads ambient
  · intro j
    refine Fin.addCases (m:=t+1) (n:=1) (fun a => ?_) (fun a => ?_) j
    · refine Fin.addCases (m:=t) (n:=1) (fun b => ?_) (fun b => ?_) a
      · simp only [eraseSlots,Fin.addCases_left]
      · simpa only [eraseSlots,Fin.addCases_left,Fin.addCases_right] using hdriver
    · simpa only [eraseSlots,Fin.addCases_right] using hlog
  · intro j
    refine Fin.addCases (m:=t+1) (n:=1) (fun a => ?_) (fun a => ?_) j
    · refine Fin.addCases (m:=t) (n:=1) (fun b => ?_) (fun b => ?_) a
      · simpa only [eraseSlots,Fin.addCases_left] using hh b
      · simpa only [eraseSlots,Fin.addCases_left,Fin.addCases_right] using hhd
    · simpa only [eraseSlots,Fin.addCases_right] using hhl

end NearCubicWires.RepairOrdinary.PCPTraversal
