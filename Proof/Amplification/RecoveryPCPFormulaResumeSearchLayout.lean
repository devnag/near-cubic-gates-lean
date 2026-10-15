import Proof.Amplification.RecoveryPCPFormulaResumeSearchCount

/-! Archive the physically generated proof count outside the formula bank
before its rows and serializer run. The five original source fields remain
the complete external input. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeSearch
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open SourceInterfaces VerifierDecoding ProjectionNormalization CanonicalRecoveryLanguage
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def scalarSlots (i : Fin 66) : Fin 788 := i.castAdd 722
def countSlots : Fin 4→Fin 788 := ![58,785,786,787]
def formulaSlots (i : Fin 716) : Fin 788 := (RecoveryPCPFormulaResumeCold.formulaSlots i).castAdd 3
theorem scalar_injective : Function.Injective scalarSlots := by
  intro i j h; exact Fin.ext (congrArg (fun i : Fin 788=>i.val) h)
theorem count_injective : Function.Injective countSlots := by decide
theorem formula_injective : Function.Injective formulaSlots := by
  intro i j h
  apply RecoveryPCPFormulaResumeCold.formula_injective
  exact Fin.ext (congrArg (fun i : Fin 788=>i.val) h)
noncomputable def first := RecoveryFocus.machine scalarSlots RecoveryPCPFormulaResumeColdScalars.machine
noncomputable def countMachine := RecoveryFocus.machine countSlots RecoveryPCPFormulaResumeSearchCount.machine
noncomputable def counted := Composition.machine first countMachine
noncomputable def last := RecoveryFocus.machine formulaSlots RecoveryPCPFormulaResumeSerialize.machine
noncomputable def machine := Composition.machine counted last
noncomputable def input (p : RawProjectionPCP) (R Q : Nat) : Fin 788→List Bool :=
  Fin.addCases (m:=785) (n:=3) (motive:=fun _=>List Bool) (RecoveryPCPFormulaResumeCold.input p R Q) (fun _=>[])

theorem scalar_input (p : RawProjectionPCP) (R Q : Nat) (i : Fin 66) :
    input p R Q (scalarSlots i)=RecoveryPCPFormulaResumeColdScalars.input R.bits Q.bits i := by
  have he : scalarSlots i=(RecoveryPCPFormulaResumeCold.scalarSlots i).castAdd 3 := Fin.ext rfl
  rw [he]
  simp only [input,Fin.addCases_left]
  exact RecoveryPCPFormulaResumeCold.scalar_input p R Q i

theorem scalar_old (p : RawProjectionPCP) (R Q : Nat) (out : Fin 66→List Bool) (j : Fin 785) :
    install scalarSlots (input p R Q) out (j.castAdd 3)=
      install RecoveryPCPFormulaResumeCold.scalarSlots (RecoveryPCPFormulaResumeCold.input p R Q) out j := by
  classical
  by_cases hj : ∃ i,RecoveryPCPFormulaResumeCold.scalarSlots i=j
  · obtain ⟨i,hi⟩ := hj
    subst j
    have he : (RecoveryPCPFormulaResumeCold.scalarSlots i).castAdd 3=scalarSlots i := Fin.ext rfl
    rw [he,install_slot scalarSlots scalar_injective,
      install_slot RecoveryPCPFormulaResumeCold.scalarSlots RecoveryPCPFormulaResumeCold.scalar_injective]
  · rw [install_other _ _ _ _ (by
      intro i hi
      apply hj
      exact ⟨i,Fin.ext (congrArg (fun i : Fin 788=>i.val) hi)⟩),
      install_other _ _ _ _ (by intro i hi; exact hj ⟨i,hi⟩)]
    simp only [input,Fin.addCases_left]

theorem scalar_fresh (p : RawProjectionPCP) (R Q : Nat) (out : Fin 66→List Bool) (i : Fin 3) :
    install scalarSlots (input p R Q) out (i.natAdd 785)=[] := by
  rw [install_other _ _ _ _ (by
    intro j h
    have hv:=congrArg (fun i : Fin 788=>i.val) h
    have hj:=j.isLt
    change j.val=785+i.val at hv
    omega)]
  simp only [input,Fin.addCases_right]

end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeSearch
