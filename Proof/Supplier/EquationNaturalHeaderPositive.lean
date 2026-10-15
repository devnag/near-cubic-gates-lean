import Proof.MachineModel.OrdinaryMatrixNativeDimension
import Proof.MachineModel.OrdinaryMatrixNaturalHeader

/-! Physical raw-unary to canonical natWord header, for a positive runtime
dimension. The value and its bit-width are produced by the existing count
program before the source-compatible header writer is called. -/
namespace NearCubicWires.RepairOrdinary.EquationNaturalHeader
open LocalBitMultitape RecoveryRootRound CompetitorRationalProducts SignedSortKey
open RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def binarySlots (i : Fin 10) : Fin 16 := i.castAdd 6
def widthSlots : Fin 5 → Fin 16 := ![8,10,11,12,13]
def headerSlots : Fin 4 → Fin 16 := ![5,10,14,15]
noncomputable def first := RecoveryFocus.machine binarySlots MatrixDimensionBinary.resetMachine
noncomputable def width := RecoveryFocus.machine widthSlots MatrixTemplateCopy.resetMachine
noncomputable def last := RecoveryFocus.machine headerSlots MatrixNaturalHeader.resetMachine
noncomputable def tail := Composition.machine width last
noncomputable def positive := Composition.machine first tail
def input (n : ℕ) : Fin 16 → List Bool := fun i => if i=0 then List.replicate n true else []
def budget (n : ℕ) := 16*n^2+72*n+10*natBitLength n+52

theorem positive_ready (n : ℕ) (hn : 0<n) :
    ∃ out,ClockJoin.ReadyRun positive (budget n) (input n) out ∧
      out 1=List.replicate n true ∧ out 14=natWord n := by
  obtain ⟨converted,hb,b1,_,_,b5,b8,bh,bs⟩ := MatrixDimensionBinary.reset_run n hn
  have br : ClockJoin.ReadyRun MatrixDimensionBinary.resetMachine (16*n^2+72*n+32)
      (MatrixDimensionBinary.resetInput n) converted.final.tapes := ⟨converted,hb,rfl,bh,bs⟩
  let a := install binarySlots (input n) converted.final.tapes
  have hfirst := bounded_focus binarySlots (by decide) _ _ _ br (input n)
    (by intro i; fin_cases i <;> rfl)
  have a1 : a 1=List.replicate n true := (install_slot binarySlots (by decide) _ _ 1).trans b1
  have a5 : a 5=frame (binary (natBitLength n) n) := (install_slot binarySlots (by decide) _ _ 5).trans b5
  have a8 : a 8=RepairSource.VerifierDecoding.CompareMachine.word (natBitLength n) :=
    (install_slot binarySlots (by decide) _ _ 8).trans b8
  have fresh (i : Fin 16) (hi : 10 ≤ i.val) : a i=[] := by
    apply (install_other binarySlots _ _ i ?_).trans ?_
    · intro j h
      have hv := congrArg Fin.val h
      have hj := j.isLt
      simp only [binarySlots,Fin.val_castAdd] at hv
      omega
    · simp [input,show i≠0 from by intro he; subst i; omega]
  obtain ⟨copied,hc,c1,_,_,ch,cs⟩ := MatrixTemplateCopy.word_run (natBitLength n)
  have cr : ClockJoin.ReadyRun MatrixTemplateCopy.resetMachine (4*natBitLength n+12)
      (MatrixTemplateCopy.wordInput (natBitLength n)) copied.final.tapes := ⟨copied,hc,rfl,ch,cs.le⟩
  let b := install widthSlots a copied.final.tapes
  have hi : ∀ i,a (widthSlots i)=MatrixTemplateCopy.wordInput (natBitLength n) i := by
    intro i; fin_cases i
    · exact a8
    all_goals exact fresh _ (by decide)
  have hwidth := bounded_focus widthSlots (by decide) _ _ _ cr a hi
  have b1' : b 1=List.replicate n true := (install_other widthSlots _ _ 1 (by decide)).trans a1
  have b5' : b 5=frame (binary (natBitLength n) n) := (install_other widthSlots _ _ 5 (by decide)).trans a5
  have b10 : b 10=List.replicate (natBitLength n) true := (install_slot widthSlots (by decide) _ _ 1).trans c1
  have b14 : b 14=[] := (install_other widthSlots _ _ 14 (by decide)).trans (fresh 14 (by decide))
  have b15 : b 15=[] := (install_other widthSlots _ _ 15 (by decide)).trans (fresh 15 (by decide))
  obtain ⟨printed,hp,_,_,p2,ph,ps⟩ := MatrixNaturalHeader.natural_run n
  have pr : ClockJoin.ReadyRun MatrixNaturalHeader.resetMachine (6*natBitLength n+6)
      (MatrixNaturalHeader.resetInput (binary (natBitLength n) n)) printed.final.tapes :=
    ⟨printed,hp,rfl,ph,ps.le⟩
  have pi : ∀ i,b (headerSlots i)=MatrixNaturalHeader.resetInput (binary (natBitLength n) n) i := by
    intro i; fin_cases i
    · exact b5'
    · simpa [headerSlots,MatrixNaturalHeader.resetInput,MatrixNaturalHeader.input,Fin.addCases] using b10
    · exact b14
    · exact b15
  let out := install headerSlots b printed.final.tapes
  have hlast := bounded_focus headerSlots (by decide) _ _ _ pr b pi
  have ht := ClockJoin.join width last _ _ _ _ _ hwidth hlast
  have hall := ClockJoin.join first tail _ _ _ _ _ hfirst ht
  have he : (16*n^2+72*n+32)+1+((4*natBitLength n+12)+1+(6*natBitLength n+6))=budget n := by
    unfold budget
    omega
  rw [he] at hall
  exact ⟨out,hall,(install_other headerSlots _ _ 1 (by decide)).trans b1',
    (install_slot headerSlots (by decide) _ _ 2).trans p2⟩

end NearCubicWires.RepairOrdinary.EquationNaturalHeader
