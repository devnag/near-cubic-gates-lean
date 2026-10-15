import Proof.CaseAnalysis.RecoveryFixedFinishBounds
import Proof.CaseAnalysis.RecoveryCountDriver

/-! The retained projector and original full randomness driver are reused
after a count case. Only randomness is rewritten and the driver moves once. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedFixedRestart
open LocalBitMultitape Composition RecoveryRootRound SourceInterfaces RepairSource CanonicalRecoveryLanguage
open RecoveryBoundedRowRandomReset (outerSlots outer_injective)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extra (P : Fin 37→List Bool) (total : ℕ) : Fin 38→List Bool:=
  Fin.addCases (m:=37) (n:=1) P (fun _=>VerifierDecoding.CompareMachine.word total)
def data (S : ℕ) (A : Fin 78→List Bool) (P : Fin 37→List Bool) (total : ℕ):=
  RecoveryBoundedFixedContinue.data S A (extra P total)

theorem data_slot (S total : ℕ) (A : Fin 78→List Bool) (P : Fin 37→List Bool) (j : Fin 37) :
    data S A P total (outerSlots j)=P j := by
  change RecoveryBoundedFixedContinue.data S A (extra P total) ((j.castAdd 1).natAdd 78)=P j
  simp only [RecoveryBoundedFixedContinue.data,Fin.addCases_right,extra,Fin.addCases_left]

theorem install_projector (S total : ℕ) (A : Fin 78→List Bool) (P Q : Fin 37→List Bool) :
    install outerSlots (data S A P total) Q=data S A Q total := by
  apply HierarchyWidth.install_eq outerSlots outer_injective
  · intro j
    exact data_slot S total A Q j
  · intro i hi
    revert hi
    refine Fin.addCases (m:=78) (n:=38) ?_ ?_ i
    · intro j _
      simp only [data,RecoveryBoundedFixedContinue.data,Fin.addCases_left]
    · intro j
      refine Fin.addCases (m:=37) (n:=1) ?_ ?_ j
      · intro k hk
        exact False.elim (hk k rfl)
      · intro k _
        simp only [data,RecoveryBoundedFixedContinue.data,Fin.addCases_right,extra]

def heads (out stack : List Bool):=RecoveryBoundedFixedContinue.heads out stack RecoveryBoundedFixedFinish.extraHeads
def nextHeads (out stack : List Bool):=RecoveryBoundedRows.startHeads
  (RecoveryBoundedRows.heads (RecoveryBoundedRowAfter.heads out stack))

theorem heads_slot (out stack : List Bool) (j : Fin 37) : heads out stack (outerSlots j)=0 := by
  change RecoveryBoundedFixedContinue.heads out stack RecoveryBoundedFixedFinish.extraHeads ((j.castAdd 1).natAdd 78)=0
  simp only [RecoveryBoundedFixedContinue.heads,Fin.addCases_right,RecoveryBoundedFixedFinish.extraHeads]
  apply if_neg
  intro he
  have hv:=congrArg Fin.val he
  change j.val=37 at hv
  omega

theorem next_heads (out stack : List Bool) :
    Function.update (heads out stack) 115 (heads out stack 115+1)=nextHeads out stack := by
  funext i
  fin_cases i <;> rfl

noncomputable def machine:=Composition.machine RecoveryBoundedRowRandomReset.machine RecoveryBoundedCountDriver.machine

theorem run (p : RawProjectionPCP) (R Q k B S total : ℕ) (out stack : List Bool) (A : Fin 78→List Bool) :
    ∃ r,runFrom machine (4*R+6)
      ⟨machine.start,heads out stack,data S A (RecoveryBoundedRowProjection.bank p R Q (bitInputOfCode R k) B) total⟩=some r ∧
      r.steps≤4*R+6 ∧ r.final.heads=nextHeads out stack ∧
      r.final.tapes=data S A (RecoveryBoundedRowProjection.bank p R Q (bitInputOfCode R 0) B) total := by
  obtain ⟨a,ar,ah,aT,as⟩:=RecoveryBoundedRowRandomReset.run p R Q k B (heads out stack)
    (data S A (RecoveryBoundedRowProjection.bank p R Q (bitInputOfCode R k) B) total)
    (heads_slot out stack) (data_slot S total A _)
  rw [install_projector] at aT
  obtain ⟨b,br,bs,bh,bt⟩:=RecoveryBoundedCountDriver.run (heads out stack)
    (data S A (RecoveryBoundedRowProjection.bank p R Q (bitInputOfCode R 0) B) total)
  have br' : runFrom RecoveryBoundedCountDriver.machine 1
      (restart a.final RecoveryBoundedCountDriver.machine.start)=some b := by
    change runFrom _ _ ⟨_,a.final.heads,a.final.tapes⟩=some b
    rw [ah,aT]
    exact br
  obtain ⟨r,rr,rs,rh,rt⟩:=RecoveryBoundedRows.Whole.join RecoveryBoundedRowRandomReset.machine RecoveryBoundedCountDriver.machine
    (heads out stack) (data S A (RecoveryBoundedRowProjection.bank p R Q (bitInputOfCode R k) B) total)
    (4*R+4) 1 a b ar br'
  refine ⟨r,?_,?_,?_,rt.trans bt⟩
  · simpa only [machine,RecoveryBoundedRows.Whole.machine,show 4*R+4+1+1=4*R+6 by omega] using rr
  · rw [rs]
    omega
  · exact rh.trans (bh.trans (next_heads out stack))

end NearCubicWires.RepairOrdinary.RecoveryBoundedFixedRestart
