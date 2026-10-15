import Proof.CaseAnalysis.WitnessFamilyCount
import Proof.CaseAnalysis.ScheduleClauseWidth

/-! The actual native arity supplies every short common mode dimension:
binary R for exact sum arity, logScale R and the numerator R^3. All copies,
templates, arithmetic and head resets are existing paid ordinary workers. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ModeDimensions
open LocalBitMultitape RecoveryRootRound RepairRepresentation RepairSource
open ProjectionNormalization CloseoutSchedule VerifierDecoding SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def binarySlots (i : Fin 10) : Fin 47:=i.castAdd 37
def logSlots (i : Fin (Clause.tapes 1)) : Fin 47:=
  ⟨if i.val=0 then 2 else 10+i.val,by dsimp [Clause.tapes] at *;split_ifs <;> omega⟩
def powerSlots (i : Fin (DimensionPower.tapes 3)) : Fin 47:=
  ⟨if i.val=0 then 3 else 38+i.val,by dsimp [DimensionPower.tapes] at *;split_ifs <;> omega⟩
def binaryProgram:=RecoveryFocus.machine binarySlots MatrixDimensionBinary.resetMachine
def logarithm:=RecoveryFocus.machine logSlots (Clause.machine 1)
def power:=RecoveryFocus.machine powerSlots (DimensionPower.machine 3 1)
def first:=Composition.machine binaryProgram logarithm
def machine:=Composition.machine first power
def input (R : ℕ) (i : Fin 47) : List Bool:=if i.val=0 then List.replicate R true else []
def budget (R : ℕ):=(16*R^2+72*R+32)+1+Clause.budget 1 R+1+DimensionPower.cost 1 R 3

theorem binary_injective : Function.Injective binarySlots:=by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 47=>k.val) h)
theorem log_injective : Function.Injective logSlots:=by
  intro i j h
  have hv:=congrArg (fun k : Fin 47=>k.val) h
  dsimp only [logSlots] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega
theorem power_injective : Function.Injective powerSlots:=by
  intro i j h
  have hv:=congrArg (fun k : Fin 47=>k.val) h
  dsimp only [powerSlots] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega
theorem binary_outside (i : Fin 47) (hi : 10 ≤ i.val) : ∀ j,binarySlots j≠i:=by
  intro j h
  have hv:=congrArg (fun k : Fin 47=>k.val) h
  change j.val=i.val at hv
  omega
theorem log_outside (i : Fin 47) (hi : i.val<10 ∧ i.val≠2 ∨ 38 ≤ i.val) : ∀ j,logSlots j≠i:=by
  intro j h
  have hv:=congrArg (fun k : Fin 47=>k.val) h
  have hj:j.val<28:=j.isLt
  dsimp only [logSlots] at hv
  split_ifs at hv <;> rcases hi with hi|hi <;> omega
theorem power_outside (i : Fin 47) (hi : i.val<38 ∧ i.val≠3) : ∀ j,powerSlots j≠i:=by
  intro j h
  have hv:=congrArg (fun k : Fin 47=>k.val) h
  dsimp only [powerSlots] at hv
  split_ifs at hv <;> omega

theorem dimensions_run (R : ℕ) (hR : 0<R) : ∃ output,
    ClockJoin.ReadyRun machine (budget R) (input R) output ∧
      output 1=List.replicate R true ∧ output 3=UnaryTemplate.tape R ∧
      output 5=frame (binary (natBitLength R) R) ∧
      output 8=CompareMachine.word (natBitLength R) ∧
      output 36=CompareMachine.word (logScale R) ∧ output 45=List.replicate (R^3) true:=by
  obtain ⟨b,hb,b1,b2,b3,b5,b8,bh,bs⟩:=MatrixDimensionBinary.reset_run R hR
  have br:ClockJoin.ReadyRun MatrixDimensionBinary.resetMachine (16*R^2+72*R+32)
      (MatrixDimensionBinary.resetInput R) b.final.tapes:=⟨b,hb,rfl,bh,bs⟩
  have hbf:=br.focus binarySlots binary_injective (input R) (by intro i;fin_cases i <;> rfl)
  let afterBinary:=install binarySlots (input R) b.final.tapes
  have binaryValue (i : Fin 10) : afterBinary (binarySlots i)=b.final.tapes i:=
    install_slot _ binary_injective _ _ _
  have binaryBlank (i : Fin 47) (hi : 10 ≤ i.val) : afterBinary i=[]:=by
    rw [show afterBinary=install binarySlots _ _ by rfl,install_other _ _ _ _ (binary_outside i hi)]
    simp only [input,if_neg (show i.val≠0 by omega)]
  obtain ⟨lo,hl,_,ll⟩:=Clause.clause_run 1 R (by decide)
  have hlf:=hl.focus logSlots log_injective afterBinary (by
    intro i
    by_cases h0:i.val=0
    · have he:i=⟨0,by decide⟩:=Fin.ext h0
      rw [he]
      exact (binaryValue 2).trans b2
    rw [Clause.input,if_neg h0]
    exact binaryBlank _ (by simp only [logSlots,if_neg h0];omega))
  let afterLog:=install logSlots afterBinary lo
  have logKeep (i : Fin 47) (hi : i.val<10 ∧ i.val≠2 ∨ 38 ≤ i.val) :
      afterLog i=afterBinary i:=install_other _ _ _ _ (log_outside i hi)
  obtain ⟨po,hp,pt,pv⟩:=DimensionPower.power_run 3 1 R
  have hpf:=hp.focus powerSlots power_injective afterLog (by
    intro i
    by_cases h0:i.val=0
    · have he:i=⟨0,by decide⟩:=Fin.ext h0
      rw [he]
      exact (logKeep 3 (Or.inl ⟨by decide,by decide⟩)).trans ((binaryValue 3).trans b3)
    rw [DimensionPower.input,if_neg h0]
    rw [logKeep _ (Or.inr (by simp only [powerSlots,if_neg h0];omega))]
    exact binaryBlank _ (by simp only [powerSlots,if_neg h0];omega))
  have hall:=ClockJoin.join first power _ _ _ _ _
    (ClockJoin.join binaryProgram logarithm _ _ _ _ _ hbf hlf) hpf
  refine ⟨_,hall,?_,?_,?_,?_,?_,?_⟩
  · rw [install_other _ _ _ _ (power_outside _ ⟨by decide,by decide⟩),
      logKeep _ (Or.inl ⟨by decide,by decide⟩)]
    exact (binaryValue 1).trans b1
  · change install powerSlots afterLog po (powerSlots ⟨0,by decide⟩)=_
    rw [install_slot _ power_injective]
    exact pt
  · rw [install_other _ _ _ _ (power_outside _ ⟨by decide,by decide⟩),
      logKeep _ (Or.inl ⟨by decide,by decide⟩)]
    exact (binaryValue 5).trans b5
  · rw [install_other _ _ _ _ (power_outside _ ⟨by decide,by decide⟩),
      logKeep _ (Or.inl ⟨by decide,by decide⟩)]
    exact (binaryValue 8).trans b8
  · rw [install_other _ _ _ _ (power_outside _ ⟨by decide,by decide⟩)]
    change install logSlots afterBinary lo (logSlots (Clause.widthSlot 1))=_
    rw [install_slot _ log_injective,ll]
    simp only [CloseoutLanguage.clauseWidth,pow_one,logScale]
  · change install powerSlots afterLog po (powerSlots (DimensionPower.valueSlot 3 3 le_rfl))=_
    rw [install_slot _ power_injective,pv,one_mul]

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.ModeDimensions
