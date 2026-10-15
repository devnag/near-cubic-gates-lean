import Proof.MachineModel.OrdinaryMatrixBatchNativeWidth

/-! A retained positive unary dimension becomes its common-width native
binary word through actual copy, binary generation and paid widening. -/
namespace NearCubicWires.RepairOrdinary.MatrixNativeDimension
open LocalBitMultitape RecoveryRootRound CompetitorRationalProducts SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def copySlots : Fin 5 → Fin 18 := ![1,2,3,4,5]
def binarySlots : Fin 10 → Fin 18 := ![2,6,7,8,9,10,11,12,13,14]
def scalarSlots : Fin 5 → Fin 18 := ![0,10,15,16,17]
noncomputable def copy := RecoveryFocus.machine copySlots MatrixTemplateCopy.resetMachine
noncomputable def binaryMachine := RecoveryFocus.machine binarySlots MatrixDimensionBinary.resetMachine
noncomputable def scalar := RecoveryFocus.machine scalarSlots ClockNormalize.machine
noncomputable def tail := Composition.machine binaryMachine scalar
noncomputable def machine := Composition.machine copy tail
def input (M n : ℕ) : Fin 18 → List Bool := fun i =>
  if i=0 then List.replicate M true else if i=1 then UnaryTemplate.tape n else []
def budget (M n : ℕ) := 16*n^2+76*n+4*M+50

theorem dimension_run (M n : ℕ) (hn : 0<n) (hfit : n<2^M) :
    ∃ out,ClockJoin.ReadyRun machine (budget M n) (input M n) out ∧
      out 0=List.replicate M true ∧ out 1=UnaryTemplate.tape n ∧ out 15=frame (binary M n) := by
  obtain ⟨copied,hc,c0,c1,_,_,ch,cs⟩ := MatrixTemplateCopy.reset_run n
  have cr : ClockJoin.ReadyRun MatrixTemplateCopy.resetMachine (4*n+12)
      (MatrixTemplateCopy.resetInput n) copied.final.tapes := ⟨copied,hc,rfl,ch,cs.le⟩
  let stage0 := install copySlots (input M n) copied.final.tapes
  have hcopy := bounded_focus copySlots (by decide) _ _ _ cr (input M n)
    (by intro i; fin_cases i <;> rfl)
  have c2 : stage0 2=List.replicate n true := (install_slot copySlots (by decide) _ _ 1).trans c1
  have c1' : stage0 1=UnaryTemplate.tape n := (install_slot copySlots (by decide) _ _ 0).trans c0
  have c0' : stage0 0=List.replicate M true := install_other copySlots _ _ 0 (by decide)
  have fresh0 (i : Fin 18) (hi : 6 ≤ i.val) : stage0 i=[] := by
    have h0 : i≠0 := by intro h; subst i; omega
    have h1 : i≠1 := by intro h; subst i; omega
    apply (install_other copySlots _ _ i ?_).trans (by simp [input,h0,h1])
    intro j h
    fin_cases j <;> have hv := congrArg Fin.val h <;> simp [copySlots] at hv <;> omega
  obtain ⟨converted,hb,_,_,_,b5,_,bh,bs⟩ := MatrixDimensionBinary.reset_run n hn
  have br : ClockJoin.ReadyRun MatrixDimensionBinary.resetMachine (16*n^2+72*n+32)
      (MatrixDimensionBinary.resetInput n) converted.final.tapes := ⟨converted,hb,rfl,bh,bs⟩
  have bi : ∀ i,stage0 (binarySlots i)=MatrixDimensionBinary.resetInput n i := by
    intro i; fin_cases i
    · exact c2
    all_goals exact fresh0 _ (by decide)
  let stage1 := install binarySlots stage0 converted.final.tapes
  have hbinary := bounded_focus binarySlots (by decide) _ _ _ br stage0 bi
  have b10 : stage1 10=frame (binary (natBitLength n) n) := (install_slot binarySlots (by decide) _ _ 5).trans b5
  have b0 : stage1 0=List.replicate M true := (install_other binarySlots _ _ 0 (by decide)).trans c0'
  have b1 : stage1 1=UnaryTemplate.tape n := (install_other binarySlots _ _ 1 (by decide)).trans c1'
  have fresh1 (i : Fin 18) (hi : 15 ≤ i.val) : stage1 i=[] := by
    apply (install_other binarySlots _ _ i ?_).trans (fresh0 i (by omega))
    intro j h
    fin_cases j <;> have hv := congrArg Fin.val h <;> simp [binarySlots] at hv <;> omega
  have hwidth : natBitLength n≤M := by
    have h := Nat.log_lt_of_lt_pow (by omega : n≠0) hfit
    change Nat.log 2 n+1≤M
    omega
  obtain ⟨widened,hw,w0,_,w2,_,_,wh,ws⟩ := ClockScalarFields.scalar_run M (binary (natBitLength n) n)
    (by simpa only [binary_length] using hwidth)
  have hv := binary_value (natBitLength n) n (Nat.lt_pow_succ_log_self (by decide : 1<2) n)
  rw [hv] at w2
  have wr : ClockJoin.ReadyRun ClockNormalize.machine (4*M+4)
      (ClockNormalize.input M (binary (natBitLength n) n)) widened.final.tapes := ⟨widened,hw,rfl,wh,ws.le⟩
  have wi : ∀ i,stage1 (scalarSlots i)=ClockNormalize.input M (binary (natBitLength n) n) i := by
    intro i; fin_cases i
    · exact b0
    · exact b10
    all_goals exact fresh1 _ (by decide)
  let out := install scalarSlots stage1 widened.final.tapes
  have hscalar := bounded_focus scalarSlots (by decide) _ _ _ wr stage1 wi
  have ht := ClockJoin.join binaryMachine scalar _ _ _ _ _ hbinary hscalar
  have whole := ClockJoin.join copy tail _ _ _ _ _ hcopy ht
  have htime : (4*n+12)+1+((16*n^2+72*n+32)+1+(4*M+4))=budget M n := by unfold budget; omega
  rw [htime] at whole
  exact ⟨out,whole,(install_slot scalarSlots (by decide) _ _ 0).trans w0,
    (install_other scalarSlots _ _ 1 (by decide)).trans b1,(install_slot scalarSlots (by decide) _ _ 2).trans w2⟩

end NearCubicWires.RepairOrdinary.MatrixNativeDimension
