import Proof.Circuits.DecompositionAtomReset

/-! The reusable caller erases its actual127 scratch tapes simultaneously,
using an outside-bank unary driver. Source, count and append cursors survive;
the erase log retains its explicitly paid zero tail. -/
namespace NearCubicWires.RepairOrdinary.DecompositionAtomReuse
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def scratchSlots (i : Fin 175) : Fin 179 :=
  ⟨i.val+1,by omega⟩
def eraseSlots (i : Fin 177) : Fin 179 :=
  Fin.addCases (m:=176) (n:=1) (motive:=fun _ => Fin 179)
    (Fin.addCases (m:=175) (n:=1) (motive:=fun _ => Fin 179)
      scratchSlots (fun _ : Fin 1 => 177)) (fun _ : Fin 1 => 178) i
noncomputable def eraseMachine := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 175)
noncomputable def erased (capacity log : ℕ) (ambient : Fin 179 → List Bool) :=
  install eraseSlots ambient (PCPTraversal.clearedLocal 175 capacity log)

theorem eraseSlots_injective : Function.Injective eraseSlots := by decide

theorem erase_run (capacity log : ℕ) (heads : Fin 179 → ℕ) (ambient : Fin 179 → List Bool)
    (hb : ∀ j,(ambient (scratchSlots j)).length ≤ capacity)
    (hd : ambient 177=List.replicate capacity true)
    (hl : ambient 178=List.replicate log false)
    (hh : ∀ j,heads (scratchSlots j)=0) (hhd : heads 177=0) (hhl : heads 178=0) :
    ∃ r,runFrom eraseMachine (2*capacity+4) ⟨eraseMachine.start,heads,ambient⟩=some r ∧
      r.final.heads=heads ∧ r.final.tapes=erased capacity log ambient ∧ r.steps=2*capacity+4 := by
  have h := RecoveryScratchErase.erase_ready capacity log (fun j => ambient (scratchSlots j)) hb
  apply h.focus_at eraseSlots eraseSlots_injective heads ambient
  · intro j
    refine Fin.addCases (m:=176) (n:=1) (fun a => ?_) (fun a => ?_) j
    · refine Fin.addCases (m:=175) (n:=1) (fun b => ?_) (fun b => ?_) a
      · simp only [eraseSlots,Fin.addCases_left]
      · simpa only [eraseSlots,Fin.addCases_left,Fin.addCases_right] using hd
    · simpa only [eraseSlots,Fin.addCases_right] using hl
  · intro j
    refine Fin.addCases (m:=176) (n:=1) (fun a => ?_) (fun a => ?_) j
    · refine Fin.addCases (m:=175) (n:=1) (fun b => ?_) (fun b => ?_) a
      · simpa only [eraseSlots,Fin.addCases_left] using hh b
      · simpa only [eraseSlots,Fin.addCases_left,Fin.addCases_right] using hhd
    · simpa only [eraseSlots,Fin.addCases_right] using hhl

theorem erased_slot (capacity log : ℕ) (ambient : Fin 179 → List Bool) (j : Fin 175) :
    erased capacity log ambient (scratchSlots j)=List.replicate capacity false := by
  have h := install_slot eraseSlots eraseSlots_injective ambient
    (PCPTraversal.clearedLocal 175 capacity log) ((j.castAdd 1).castAdd 1)
  simpa only [erased,eraseSlots,PCPTraversal.clearedLocal,Fin.addCases_left] using h

theorem erased_driver (capacity log : ℕ) (ambient : Fin 179 → List Bool) :
    erased capacity log ambient 177=List.replicate capacity true := by
  have h := install_slot eraseSlots eraseSlots_injective ambient
    (PCPTraversal.clearedLocal 175 capacity log) (((0 : Fin 1).natAdd 175).castAdd 1)
  simpa only [erased,eraseSlots,PCPTraversal.clearedLocal,Fin.addCases_left,Fin.addCases_right] using h

theorem erased_log (capacity log : ℕ) (ambient : Fin 179 → List Bool) :
    erased capacity log ambient 178=List.replicate (max log (capacity+1)) false := by
  have h := install_slot eraseSlots eraseSlots_injective ambient
    (PCPTraversal.clearedLocal 175 capacity log) ((0 : Fin 1).natAdd 176)
  simpa only [erased,eraseSlots,PCPTraversal.clearedLocal,Fin.addCases_right] using h

theorem erased_live (capacity log : ℕ) (ambient : Fin 179 → List Bool)
    (i : Fin 179) (hi : i=0 ∨ i=176) : erased capacity log ambient i=ambient i := by
  apply install_other
  intro j
  refine Fin.addCases (m:=176) (n:=1) (fun a => ?_) (fun a => ?_) j
  · refine Fin.addCases (m:=175) (n:=1) (fun b => ?_) (fun b => ?_) a
    · simp only [eraseSlots,Fin.addCases_left]
      intro he
      have hv := congrArg Fin.val he
      have hib := b.isLt
      simp only [scratchSlots] at hv
      rcases hi with hi|hi <;> subst i <;> omega
    · simp only [eraseSlots,Fin.addCases_left,Fin.addCases_right]
      rcases hi with hi|hi <;> subst i <;> decide
  · simp only [eraseSlots,Fin.addCases_right]
    rcases hi with hi|hi <;> subst i <;> decide

end NearCubicWires.RepairOrdinary.DecompositionAtomReuse
