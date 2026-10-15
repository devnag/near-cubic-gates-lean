import Proof.Amplification.RecoveryProjectionFieldEval
import Proof.Amplification.RecoveryProjectionEmitBit

/-! The actual source-field loop clears all 28 evaluator tapes with its
preserved unary capacity driver. External source/randomness/output cursors
are outside the executed sweep and retain their positions. -/
namespace NearCubicWires.RepairSource.RecoveryProjectionField
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def bankSlots (i : Fin 28) : Fin 34 := i.castAdd 6
def eraseSlots (i : Fin 30) : Fin 34 :=
  if h : i.val<28 then ⟨i.val,by omega⟩ else ⟨i.val+4,by have hi:=i.isLt; omega⟩
theorem erase_injective : Function.Injective eraseSlots := by
  intro a b h; apply Fin.ext
  have hv:=congrArg Fin.val h
  simp only [eraseSlots] at hv
  split at hv <;> split at hv <;> dsimp at hv <;> omega
noncomputable def eraseMachine := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 28)

theorem erase_bank (i : Fin 28) : eraseSlots ((i.castAdd 1).castAdd 1)=bankSlots i := by
  simp only [eraseSlots,Fin.val_castAdd,i.isLt,↓reduceDIte]
  rfl

theorem erase_run (cap log : Nat) (hs : Fin 34→Nat) (data : Fin 34→List Bool)
    (hb : ∀ j,(data (bankSlots j)).length ≤ cap) (hh : ∀ j,hs (bankSlots j)=0)
    (hd : data 32=List.replicate cap true) (hhd : hs 32=0)
    (hl : data 33=List.replicate log false) (hhl : hs 33=0) : ∃ r,
    runFrom eraseMachine (2*cap+4) ⟨eraseMachine.start,hs,data⟩=some r ∧
      r.final.heads=hs ∧ (∀ j,r.final.tapes (bankSlots j)=List.replicate cap false) ∧
      (∀ i : Fin 34,28 ≤ i.val → i.val<32 → r.final.tapes i=data i) ∧
      r.final.tapes 32=List.replicate cap true ∧
      r.final.tapes 33=List.replicate (max log (cap+1)) false ∧ r.steps=2*cap+4 := by
  obtain ⟨base,hr,ht,bh,bs⟩ := RecoveryScratchErase.erase_ready cap log (fun j=>data (bankSlots j)) hb
  obtain ⟨r,hrr,_hcontrol,rsteps,rh,rt,other⟩ := RecoveryFocus.dock eraseSlots erase_injective
    (RecoveryScratchErase.resetMachine 28) _ hs data _
    (by
      intro j
      refine Fin.addCases (m:=29) (n:=1) (fun k=>?_) (fun k=>?_) j
      · refine Fin.addCases (m:=28) (n:=1) (fun i=>?_) (fun i=>?_) k
        · simpa only [erase_bank,initialConfiguration] using hh i
        · fin_cases i; exact hhd
      · fin_cases k; exact hhl)
    (by
      intro j
      refine Fin.addCases (m:=29) (n:=1) (fun k=>?_) (fun k=>?_) j
      · refine Fin.addCases (m:=28) (n:=1) (fun i=>?_) (fun i=>?_) k
        · simp only [erase_bank,initialConfiguration,Fin.addCases_left]
        · fin_cases i; exact hd
      · fin_cases k; exact hl) base hr
  refine ⟨r,hrr,?_,?_,?_,?_,?_,rsteps.trans bs⟩
  · funext i
    by_cases hi : i.val<28
    · let j : Fin 28 := ⟨i.val,hi⟩
      have he : bankSlots j=i := Fin.ext rfl
      have hlocal := (rh ((j.castAdd 1).castAdd 1)).trans (bh _)
      rw [erase_bank,he] at hlocal
      exact hlocal.trans (hh j |>.symm)
    by_cases h32 : i=32
    · subst i; exact ((rh 28).trans (bh 28)).trans hhd.symm
    by_cases h33 : i=33
    · subst i; exact ((rh 29).trans (bh 29)).trans hhl.symm
    have hn : ∀ j,eraseSlots j≠i := by
      intro j h; have hv:=congrArg Fin.val h; have hj:=j.isLt; have hi':=i.isLt
      have hi32 : i.val≠32 := fun he=>h32 (Fin.ext he)
      have hi33 : i.val≠33 := fun he=>h33 (Fin.ext he)
      simp only [eraseSlots] at hv
      split at hv <;> dsimp at hv <;> omega
    exact (other i hn).1
  · intro j
    have hlocal := (rt ((j.castAdd 1).castAdd 1)).trans (congrFun ht ((j.castAdd 1).castAdd 1))
    simpa only [erase_bank,Fin.addCases_left] using hlocal
  · intro i hi htop
    have hn : ∀ j,eraseSlots j≠i := by
      intro j h; have hv:=congrArg Fin.val h; have hj:=j.isLt
      simp only [eraseSlots] at hv
      split at hv <;> dsimp at hv <;> omega
    exact (other i hn).2
  · exact (rt 28).trans (congrFun ht 28)
  · exact (rt 29).trans (congrFun ht 29)

end NearCubicWires.RepairSource.RecoveryProjectionField
