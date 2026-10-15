import Proof.Amplification.RecoveryBoundedNativeFoldLoop

/-! Emit the original conjunction seed, then physically erase the completed
literal address counter into the already paid reverse-fold workspace. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedNativeUnaryPhase
open LocalBitMultitape RepairRepresentation RecoveryRootRound Composition
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def trueBits := natWord 0++natWord 1++natWord 0
def writeSlot : Fin 1→Fin 34:=fun _=>20
def eraseSlots : Fin 3→Fin 34:=![1,22,23]
noncomputable def first:=RecoveryFocus.machine writeSlot (HierarchyFixedWord.raw trueBits)
noncomputable def second:=RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 1)
noncomputable def machine:=Composition.machine first second
abbrev heads:=RecoveryBoundedNativeLiteralStep.heads
def data (index acc C : ℕ) (flag : Bool) (out stack : List Bool):=
  RecoveryBoundedNativeLiteralStep.data index acc C flag out stack 0
noncomputable def entry (index acc C : ℕ) (flag : Bool) (out stack : List Bool):=
  (⟨machine.start,heads out stack,data index acc C flag out stack⟩ : Configuration 34 _)

private theorem output_install (index acc C : ℕ) (flag : Bool) (out stack : List Bool) :
    install writeSlot (data index acc C flag out stack) (fun _=>out++trueBits)=
      data index acc C flag (out++trueBits) stack := by
  apply HierarchyWidth.install_eq writeSlot (by decide)
  · intro j; fin_cases j; rfl
  · intro i hi
    have h:=hi 0
    fin_cases i
    all_goals first | exact False.elim (h rfl) |
      simp [data,RecoveryBoundedNativeLiteralStep.data,RecoveryBoundedNativeLiteralStack.data,
        RecoveryBoundedNativeLiteral.data,PCPPNativeClauseBank.data,Fin.addCases]

theorem write_run (index acc C : ℕ) (flag : Bool) (out stack : List Bool) :
    ∃ r, runFrom first trueBits.length
      ⟨first.start,heads out stack,data index acc C flag out stack⟩=some r ∧
      r.final.heads=heads (out++trueBits) stack ∧
      r.final.tapes=data index acc C flag (out++trueBits) stack ∧ r.steps=trueBits.length := by
  obtain ⟨a,ha,af,as⟩:=RepairSource.ProjectionNormalization.Constants.write_run trueBits out
  obtain ⟨r,hr,_,rs,rh,rt,rkeep⟩:=RecoveryFocus.dock writeSlot (by decide) (HierarchyFixedWord.raw trueBits) _
    (heads out stack) (data index acc C flag out stack)
    (RepairSource.ProjectionNormalization.Constants.cfg trueBits out 0 (by omega))
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; change out=out++trueBits.take 0; simp) a ha
  refine ⟨r,hr,?_,?_,rs.trans as⟩
  · funext i
    by_cases hs : ∃ j,writeSlot j=i
    · obtain ⟨j,rfl⟩:=hs
      rw [rh j,af]
      fin_cases j
      change out.length+trueBits.length=(out++trueBits).length
      simp
    · rw [(rkeep i (by simpa using hs)).1]
      have h : i≠20 := by intro he; apply hs; exact ⟨0,he.symm⟩
      fin_cases i
      all_goals first | exact False.elim (h rfl) |
        simp [heads,RecoveryBoundedNativeLiteralStack.heads,RecoveryBoundedNativeLiteral.heads,
          PCPPNativeClauseBank.heads,Fin.addCases]
  · have he:=HierarchyWidth.install_eq writeSlot (by decide) (data index acc C flag out stack)
      r.final.tapes (fun _=>out++trueBits)
      (by intro j; rw [rt j,af]; simp [RepairSource.ProjectionNormalization.Constants.cfg])
      (by intro i hi; exact (rkeep i hi).2)
    rw [output_install] at he
    exact he.symm

private theorem erase_ready (index C : ℕ) (hi : index ≤ C) :
    ReadyRun (RecoveryScratchErase.resetMachine 1) (2*C+4)
      ![List.replicate index true,List.replicate C true,List.replicate (C+1) false]
      ![List.replicate C false,List.replicate C true,List.replicate (C+1) false] := by
  have h:=RecoveryScratchErase.erase_ready C (C+1) (fun _ : Fin 1=>List.replicate index true)
    (by intro j; simpa using hi)
  have hin : (Fin.addCases (m:=2) (n:=1) (motive:=fun _=>List Bool)
      (Fin.addCases (m:=1) (n:=1) (motive:=fun _=>List Bool)
        (fun _=>List.replicate index true) (fun _=>List.replicate C true))
      (fun _=>List.replicate (C+1) false))=
      ![List.replicate index true,List.replicate C true,List.replicate (C+1) false] := by
    funext i; fin_cases i <;> rfl
  have hout : (Fin.addCases (m:=2) (n:=1) (motive:=fun _=>List Bool)
      (Fin.addCases (m:=1) (n:=1) (motive:=fun _=>List Bool)
        (fun _=>List.replicate C false) (fun _=>List.replicate C true))
      (fun _=>List.replicate (max (C+1) (C+1)) false))=
      ![List.replicate C false,List.replicate C true,List.replicate (C+1) false] := by
    simp only [max_self]
    funext i; fin_cases i <;> rfl
  rw [hin,hout] at h
  exact h

private theorem erase_install (index acc C : ℕ) (flag : Bool) (out stack : List Bool) :
    install eraseSlots (data index acc C flag out stack)
      ![List.replicate C false,List.replicate C true,List.replicate (C+1) false]=
      RecoveryBoundedNativeFold.data 0 acc C flag out stack [] := by
  apply HierarchyWidth.install_eq eraseSlots (by decide)
  · intro j; fin_cases j <;> rfl
  · intro i hi
    have h:=hi 0
    fin_cases i
    all_goals first | exact False.elim (h rfl) |
      simp [data,RecoveryBoundedNativeLiteralStep.data,RecoveryBoundedNativeLiteralStack.data,
        RecoveryBoundedNativeLiteral.data,PCPPNativeClauseBank.data,RecoveryBoundedNativeLiteral.values,
        RecoveryBoundedNativeFold.data,RecoveryBoundedNativeFold.oldData,RecoveryBoundedNativeFold.values,Fin.addCases]

theorem phase_run (index acc C : ℕ) (flag : Bool) (out stack : List Bool) (hi : index ≤ C) :
    ∃ r, runFrom machine (trueBits.length+1+(2*C+4)) (entry index acc C flag out stack)=some r ∧
      r.steps=trueBits.length+1+(2*C+4) ∧
      r.final.heads=RecoveryBoundedNativeFold.heads (out++trueBits) stack.length ∧
      r.final.tapes=RecoveryBoundedNativeFold.data 0 acc C flag (out++trueBits) stack [] := by
  obtain ⟨a,ha,ah,atapes,as⟩:=write_run index acc C flag out stack
  obtain ⟨b,hb,bh,bt,bs⟩:=(erase_ready index C hi).focus_at eraseSlots (by decide)
    (heads (out++trueBits) stack) (data index acc C flag (out++trueBits) stack)
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [erase_install] at bt
  have hb' : runFrom second (2*C+4) (restart a.final second.start)=some b := by
    change runFrom second _ ⟨second.start,a.final.heads,a.final.tapes⟩=some b
    rw [ah,atapes]; exact hb
  have full:=Composition.run_join first second _ _ _ a b ha hb'
  refine ⟨joinedReceipt a b,full,?_,?_,bt⟩
  · change a.steps+1+b.steps=_
    omega
  · rw [show (joinedReceipt a b).final.heads=b.final.heads from rfl,bh]
    funext i
    fin_cases i <;>
      simp [heads,RecoveryBoundedNativeLiteralStack.heads,RecoveryBoundedNativeLiteral.heads,
        RecoveryBoundedNativeFold.heads,Fin.addCases]

end NearCubicWires.RepairOrdinary.RecoveryBoundedNativeUnaryPhase
