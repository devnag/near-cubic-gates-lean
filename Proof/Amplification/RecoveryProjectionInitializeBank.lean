import Proof.Amplification.RecoveryProjectionNormalizedRows

/-! One actual unary sweep allocates all 28 evaluator tapes and the shared
copy log. Source fields and the already produced R/Q drivers are retained. -/
namespace NearCubicWires.RepairSource.RecoveryProjectionInitialize
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def eraseSlots (i : Fin 31) : Fin 36 :=
  ⟨if i.val<28 then i.val else if i.val=28 then 30 else if i.val=29 then 32 else 33,
    by split_ifs <;> omega⟩
theorem erase_injective : Function.Injective eraseSlots := by
  intro a b h; apply Fin.ext
  have hv:=congrArg (fun i : Fin 36=>i.val) h
  dsimp only [eraseSlots] at hv
  split_ifs at hv <;> have ha:=a.isLt <;> have hb:=b.isLt <;> omega

def cold (cap R Q : Nat) (source : List Bool) (i : Fin 36) :=
  if i.val=28 then source else if i.val=32 then List.replicate cap true
  else if i.val=34 then VerifierDecoding.CompareMachine.word R
  else if i.val=35 then VerifierDecoding.CompareMachine.word Q else []
def erased (cap R Q : Nat) (source : List Bool) (i : Fin 36) :=
  if i.val=28 then source else if i.val=32 then List.replicate cap true
  else if i.val=34 then VerifierDecoding.CompareMachine.word R
  else if i.val=35 then VerifierDecoding.CompareMachine.word Q
  else if i.val=33 then List.replicate (cap+1) false
  else if i.val=29 ∨ i.val=31 then [] else List.replicate cap false
noncomputable def eraseMachine := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 29)

theorem erase_ready (cap R Q : Nat) (source : List Bool) :
    ClockJoin.ReadyRun eraseMachine (2*cap+4) (cold cap R Q source) (erased cap R Q source) := by
  classical
  have h := (RecoveryScratchErase.erase_ready cap 0 (fun _ : Fin 29=>[]) (by simp)).focus
    eraseSlots erase_injective (cold cap R Q source) (by
      intro i
      refine Fin.addCases (m:=30) (n:=1) (fun x=>?_) (fun x=>?_) i
      · refine Fin.addCases (m:=29) (n:=1) (fun j=>?_) (fun j=>?_) x
        · simp only [eraseSlots,Fin.val_castAdd,cold]
          have hj:=j.isLt
          split_ifs <;> simp_all
        · fin_cases j; rfl
      · fin_cases x; rfl)
  have he : install eraseSlots (cold cap R Q source)
      (fun i=>Fin.addCases (m:=30) (n:=1)
        (fun j=>Fin.addCases (m:=29) (n:=1) (fun _=>List.replicate cap false)
          (fun _=>List.replicate cap true) j)
        (fun _=>List.replicate (max 0 (cap+1)) false) i)=erased cap R Q source := by
    funext i
    by_cases hi : i.val<28
    · let j : Fin 29 := ⟨i.val,by omega⟩
      have he : i=eraseSlots ((j.castAdd 1).castAdd 1) := by
        apply Fin.ext
        simp only [eraseSlots,Fin.val_castAdd,j,hi,ite_true]
      rw [he,install_slot _ erase_injective]
      simp only [Fin.addCases_left]
      simp only [erased,eraseSlots,Fin.val_castAdd,j,hi,ite_true]
      split_ifs <;> first | rfl | omega
    by_cases h30 : i.val=30
    · have he : i=eraseSlots 28 := Fin.ext h30
      rw [he,install_slot _ erase_injective]
      rfl
    by_cases h32 : i.val=32
    · have he : i=eraseSlots 29 := Fin.ext h32
      rw [he,install_slot _ erase_injective]
      rfl
    by_cases h33 : i.val=33
    · have he : i=eraseSlots 30 := Fin.ext h33
      rw [he,install_slot _ erase_injective]
      change List.replicate (max 0 (cap+1)) false=List.replicate (cap+1) false
      simp only [Nat.zero_max]
    have hn : ∀ j,eraseSlots j≠i := by
      intro j h; have hv:=congrArg (fun k : Fin 36=>k.val) h; have hj:=j.isLt
      dsimp only [eraseSlots] at hv
      split_ifs at hv <;> omega
    rw [install_other _ _ _ _ hn]
    have cases : i.val=28 ∨ i.val=29 ∨ i.val=31 ∨ i.val=34 ∨ i.val=35 := by have ht:=i.isLt; omega
    rcases cases with h28|h29|h31|h34|h35
    all_goals simp_all [cold,erased]
  rw [he] at h
  obtain ⟨r,hr,ht,hh,hs⟩ := h
  exact ⟨r,hr,ht,hh,hs.le⟩

end NearCubicWires.RepairSource.RecoveryProjectionInitialize
