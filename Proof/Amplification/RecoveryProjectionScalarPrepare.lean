import Proof.Amplification.RecoveryProjectionScalarDimensions
import Proof.Amplification.RecoveryProjectionInitialize

/-! Full scalar-to-row preparation. The only initial data are the original
binary R/Q fields and query source bytes. Actual unary parsing, polynomial
capacity generation, allocation, randomness writes and head moves are paid. -/
namespace NearCubicWires.RepairSource.RecoveryProjectionScalar
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def coreSlots (i : Fin 36) : Fin 69 := i.castAdd 33
theorem core_injective : Function.Injective coreSlots := by
  intro a b h; exact Fin.ext (congrArg (fun i : Fin 69=>i.val) h)
noncomputable def initializeMachine := RecoveryFocus.machine coreSlots RecoveryProjectionInitialize.machine
noncomputable def prepareMachine (C : Nat) := Composition.machine (machine C) initializeMachine
def prepareBudget (C : Nat) (rBits qBits : List Bool) :=
  budget C rBits qBits+1+(2*(C*(value rBits+1)^4)+4*value rBits+15)

theorem prepare_run (C : Nat) (rBits qBits source : List Bool)
    (hc : 2*value rBits+3≤C*(value rBits+1)^4) : ∃ r,
    run (prepareMachine C) (prepareBudget C rBits qBits) (input rBits qBits source)=some r ∧
      (∀ i,r.final.heads (coreSlots i)=
        (RecoveryProjectionRows.cfg 0 (C*(value rBits+1)^4) (value rBits) source
          (List.replicate (value rBits) false) [] [] 0 (value qBits) 1).heads i) ∧
      (∀ i,r.final.tapes (coreSlots i)=
        (RecoveryProjectionRows.cfg 0 (C*(value rBits+1)^4) (value rBits) source
          (List.replicate (value rBits) false) [] [] 0 (value qBits) 1).tapes i) ∧
      r.steps≤prepareBudget C rBits qBits := by
  obtain ⟨dim,hDim,hSource,hCap,hR,hQ,hBlank,h33⟩ := dimensions_ready C rBits qBits source
  obtain ⟨first,hfirst,ft,fh,fs⟩ := hDim
  have hcore : ∀ i,first.final.tapes (coreSlots i)=
      RecoveryProjectionInitialize.cold (C*(value rBits+1)^4) (value rBits) (value qBits) source i := by
    intro i
    rw [ft]
    refine Fin.addCases (m:=32) (n:=4) (fun j=>?_) (fun j=>?_) i
    · by_cases hj : j.val=28
      · have he : j=28 := Fin.ext hj
        subst j
        exact hSource
      · change dim (j.castAdd 37)=_
        rw [hBlank j hj]
        have ht:=j.isLt
        simp only [RecoveryProjectionInitialize.cold,Fin.val_castAdd,hj,ite_false]
        split_ifs <;> first | rfl | omega
    · fin_cases j
      · exact hCap
      · exact h33
      · exact hR
      · exact hQ
  obtain ⟨base,hbase,bh,bt,bs⟩ := RecoveryProjectionInitialize.initialize_run
    (C*(value rBits+1)^4) (value rBits) (value qBits) source hc
  obtain ⟨last,hlast,_hcontrol,lastSteps,lastHeads,lastTapes,_other⟩ := RecoveryFocus.dock coreSlots core_injective
    RecoveryProjectionInitialize.machine _ first.final.heads first.final.tapes _
    (by intro i; exact fh (coreSlots i)) hcore base hbase
  have hall := Composition.run_join (machine C) initializeMachine _ _ _ first last hfirst hlast
  refine ⟨_,hall,?_,?_,?_⟩
  · intro i
    change last.final.heads (coreSlots i)=_
    rw [lastHeads,bh]
  · intro i
    change last.final.tapes (coreSlots i)=_
    rw [lastTapes,bt]
  · change first.steps+1+last.steps≤_
    unfold prepareBudget
    omega

end NearCubicWires.RepairSource.RecoveryProjectionScalar
