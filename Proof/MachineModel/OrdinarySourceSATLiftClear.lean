import Proof.MachineModel.OrdinarySourceSATLiftLayout

/-! One physical sweep prepares every reused arithmetic/printing/copy tape.
The borrowed source query is untouched, and the external capacity survives. -/
namespace NearCubicWires.RepairSource.OrdinarySourceSATLift.Kernel
open LocalBitMultitape RepairOrdinary RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def Bounded (cap : ℕ) (tapes : Fin 156 → List Bool) : Prop :=
  ∀ i, 3 ≤ i.val → (tapes i).length ≤ cap

def cleared (cap : ℕ) (source : List Bool) : Fin 156 → List Bool := fun i =>
  if i.val = 0 then source else if i.val = 1 then List.replicate cap true
  else if i.val = 2 then List.replicate (cap+1) false else List.replicate cap false

theorem erased_zero (j : Fin 155) : eraseSlots j ≠ (0 : Fin 156) := by
  refine Fin.addCases (m := 154) (n := 1) (fun a => ?_) (fun a => ?_) j
  · refine Fin.addCases (m := 153) (n := 1) (fun b => ?_) (fun b => ?_) a
    · intro h
      have hv := congrArg (fun x : Fin 156 => x.val) h
      simp [eraseSlots,workSlot] at hv
    · simp [eraseSlots]
  · simp [eraseSlots]

theorem clear_run (cap log : ℕ) (ambient : Fin 156 → List Bool)
    (hb : Bounded cap ambient) (hd : ambient 1 = List.replicate cap true)
    (hl : ambient 2 = List.replicate log false) (hz : log ≤ cap+1) :
    ReadyRun (call 0).2 (2*cap+4) ambient (cleared cap (ambient 0)) := by
  have h := (RecoveryScratchErase.erase_ready cap log (fun i => ambient (workSlot i))
    (fun i => hb (workSlot i) (by simp [workSlot]))).focus eraseSlots erase_injective ambient (by
      intro j
      refine Fin.addCases (m := 154) (n := 1) (fun a => ?_) (fun a => ?_) j
      · refine Fin.addCases (m := 153) (n := 1) (fun b => ?_) (fun b => ?_) a
        · simp [eraseSlots]
        · simpa [eraseSlots] using hd
      · simpa [eraseSlots] using hl)
  let result : Fin 155 → List Bool := Fin.addCases (m := 154) (n := 1)
    (motive := fun _ => List Bool)
    (Fin.addCases (m := 153) (n := 1) (motive := fun _ => List Bool)
      (fun _ => List.replicate cap false) (fun _ => List.replicate cap true))
    (fun _ => List.replicate (max log (cap+1)) false)
  have hout : install eraseSlots ambient result = cleared cap (ambient 0) := by
    funext i
    match i with
    | ⟨0,_⟩ =>
      exact install_other _ _ _ _ erased_zero
    | ⟨1,_⟩ =>
      have he := install_slot eraseSlots erase_injective ambient result
        (((0 : Fin 1).natAdd 153).castAdd 1)
      simp only [eraseSlots,result,Fin.addCases_left,Fin.addCases_right] at he
      exact he
    | ⟨2,_⟩ =>
      have he := install_slot eraseSlots erase_injective ambient result ((0 : Fin 1).natAdd 154)
      simp only [eraseSlots,result,Fin.addCases_right] at he
      exact he.trans (by rw [max_eq_right hz]; rfl)
    | ⟨n+3,hn⟩ =>
      let j : Fin 153 := ⟨n,by omega⟩
      have he := install_slot eraseSlots erase_injective ambient result ((j.castAdd 1).castAdd 1)
      have hi : eraseSlots ((j.castAdd 1).castAdd 1) = (⟨n+3,hn⟩ : Fin 156) := by
        apply Fin.ext
        simp only [eraseSlots,Fin.addCases_left]
        dsimp [workSlot,j]
        omega
      rw [hi] at he
      simpa [result,cleared,show n+3≠0 by omega,show n+3≠1 by omega,show n+3≠2 by omega] using he
  change ReadyRun (call 0).2 (2*cap+4) ambient (install eraseSlots ambient result) at h
  rw [hout] at h
  exact h

theorem cleared_bounded (cap : ℕ) (source : List Bool) : Bounded cap (cleared cap source) := by
  intro i hi
  simp [cleared,show i.val≠0 by omega,show i.val≠1 by omega,show i.val≠2 by omega]

theorem install_bounded {t : ℕ} (slot : Fin t → Fin 156)
    (cap : ℕ) (ambient : Fin 156 → List Bool) (output : Fin t → List Bool)
    (ha : Bounded cap ambient) (ho : ∀ i,(output i).length ≤ cap) :
    Bounded cap (install slot ambient output) := by
  intro i hi
  cases hp : RecoveryFocus.pick slot i with
  | none => simpa [install,hp] using ha i hi
  | some j => simpa [install,hp] using ho j

end NearCubicWires.RepairSource.OrdinarySourceSATLift.Kernel
