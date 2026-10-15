import Proof.Hierarchy.CompetitorOddRowSliceRow
import Proof.PCP.PCPUnarySplit

/-! Paid half-row dimensions from the retained U sentinel and raw Q.
All work starts blank. U/2 and H=Q*(U/2) are actual machine outputs. -/
namespace NearCubicWires.RepairOrdinary.CompetitorOddRowSlice
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def halfBytes (u q : ℕ) := q*(u/2)
def input (u q : ℕ) (source : List Bool) : Fin 21 → List Bool := fun i =>
  if i=1 then source else if i=3 then UnaryTemplate.tape u else if i=4 then List.replicate q true else []
def uSlots : Fin 5 → Fin 21 := ![3,5,6,7,8]
def splitSlots : Fin 4 → Fin 21 := ![5,9,10,11]
def halfSlots : Fin 5 → Fin 21 := ![10,12,13,14,15]
def productSlots : Fin 4 → Fin 21 := ![4,14,16,17]
def byteSlots : Fin 5 → Fin 21 := ![16,18,19,0,20]
noncomputable def uProgram := RecoveryFocus.machine uSlots MatrixTemplateCopy.resetMachine
noncomputable def splitProgram := RecoveryFocus.machine splitSlots PCPUnarySplit.machine
noncomputable def halfProgram := RecoveryFocus.machine halfSlots MatrixRawDimension.resetMachine
noncomputable def productProgram := RecoveryFocus.machine productSlots ClockUnaryProduct.machine
noncomputable def byteProgram := RecoveryFocus.machine byteSlots MatrixRawDimension.resetMachine
noncomputable def prepareProgram := Composition.machine uProgram
  (Composition.machine splitProgram (Composition.machine halfProgram (Composition.machine productProgram byteProgram)))
def prepareBudget (u q : ℕ) := 6*u+4*(u/2)+4*halfBytes u q+WilliamsUnaryProduct.budget q (u/2)+36

theorem prepare_run (u q : ℕ) (source : List Bool) :
    ∃ out,ClockJoin.ReadyRun prepareProgram (prepareBudget u q) (input u q source) out ∧
      out 0=UnaryTemplate.tape (halfBytes u q) ∧ out 1=source ∧ out 2=[] ∧
      out 3=UnaryTemplate.tape u ∧ out 4=List.replicate q true := by
  obtain ⟨ucopy,hur,hu0,hu1,_,_,huh,hus⟩ := MatrixTemplateCopy.reset_run u
  have uReady : ClockJoin.ReadyRun MatrixTemplateCopy.resetMachine (4*u+12)
      (MatrixTemplateCopy.resetInput u) ucopy.final.tapes := ⟨ucopy,hur,rfl,huh,hus.le⟩
  let first := install uSlots (input u q source) ucopy.final.tapes
  have hfirst := CompetitorRationalProducts.bounded_focus uSlots (by decide) _ _ _ uReady (input u q source)
    (by intro i; fin_cases i <;> rfl)
  let splitOutput : Fin 4 → List Bool :=
    ![List.replicate u true,List.replicate ((u+1)/2) true,List.replicate (u/2) true,List.replicate (u+1) false]
  have hsplit : ∀ i,first (splitSlots i)=![List.replicate u true,[],[],[]] i := by
    intro i
    fin_cases i
    · exact (install_slot uSlots (by decide) _ ucopy.final.tapes 1).trans hu1
    · exact install_other uSlots _ _ 9 (by decide)
    · exact install_other uSlots _ _ 10 (by decide)
    · exact install_other uSlots _ _ 11 (by decide)
  let second := install splitSlots first splitOutput
  have hsecond := CompetitorRationalProducts.bounded_focus splitSlots (by decide) _ _ _ (PCPUnarySplit.split_run u) first hsplit
  obtain ⟨halved,hhr,_,_,hh3,hhh,hhs⟩ := MatrixRawDimension.reset_run (u/2)
  have halfReady : ClockJoin.ReadyRun MatrixRawDimension.resetMachine (4*(u/2)+8)
      (MatrixRawDimension.resetInput (u/2)) halved.final.tapes := ⟨halved,hhr,rfl,hhh,hhs.le⟩
  have hhalf : ∀ i,second (halfSlots i)=MatrixRawDimension.resetInput (u/2) i := by
    intro i
    fin_cases i
    · exact install_slot splitSlots (by decide) first splitOutput 2
    · exact (install_other splitSlots _ _ 12 (by decide)).trans (install_other uSlots _ _ 12 (by decide))
    · exact (install_other splitSlots _ _ 13 (by decide)).trans (install_other uSlots _ _ 13 (by decide))
    · exact (install_other splitSlots _ _ 14 (by decide)).trans (install_other uSlots _ _ 14 (by decide))
    · exact (install_other splitSlots _ _ 15 (by decide)).trans (install_other uSlots _ _ 15 (by decide))
  let third := install halfSlots second halved.final.tapes
  have hthird := CompetitorRationalProducts.bounded_focus halfSlots (by decide) _ _ _ halfReady second hhalf
  have hproduct : ∀ i,third (productSlots i)=WilliamsUnaryProduct.input q (u/2) i := by
    intro i
    fin_cases i
    · exact (install_other halfSlots _ _ 4 (by decide)).trans
        ((install_other splitSlots _ _ 4 (by decide)).trans (install_other uSlots _ _ 4 (by decide)))
    · exact (install_slot halfSlots (by decide) second halved.final.tapes 3).trans hh3
    · exact (install_other halfSlots _ _ 16 (by decide)).trans
        ((install_other splitSlots _ _ 16 (by decide)).trans (install_other uSlots _ _ 16 (by decide)))
    · exact (install_other halfSlots _ _ 17 (by decide)).trans
        ((install_other splitSlots _ _ 17 (by decide)).trans (install_other uSlots _ _ 17 (by decide)))
  have productReady : ClockJoin.ReadyRun ClockUnaryProduct.machine (WilliamsUnaryProduct.budget q (u/2))
      (WilliamsUnaryProduct.input q (u/2)) (WilliamsUnaryProduct.output q (u/2)) := by
    obtain ⟨r,hr,ht,hh,hs⟩ := WilliamsUnaryProduct.product_ready q (u/2)
    exact ⟨r,hr,ht,hh,hs.le⟩
  let fourth := install productSlots third (WilliamsUnaryProduct.output q (u/2))
  have hfourth := CompetitorRationalProducts.bounded_focus productSlots (by decide) _ _ _ productReady third hproduct
  obtain ⟨bytes,hbr,_,_,hb3,hbh,hbs⟩ := MatrixRawDimension.reset_run (halfBytes u q)
  have byteReady : ClockJoin.ReadyRun MatrixRawDimension.resetMachine (4*halfBytes u q+8)
      (MatrixRawDimension.resetInput (halfBytes u q)) bytes.final.tapes := ⟨bytes,hbr,rfl,hbh,hbs.le⟩
  have hbyte : ∀ i,fourth (byteSlots i)=MatrixRawDimension.resetInput (halfBytes u q) i := by
    intro i
    fin_cases i
    · exact install_slot productSlots (by decide) third (WilliamsUnaryProduct.output q (u/2)) 2
    all_goals first
      | exact (install_other productSlots _ _ 18 (by decide)).trans ((install_other halfSlots _ _ 18 (by decide)).trans
          ((install_other splitSlots _ _ 18 (by decide)).trans (install_other uSlots _ _ 18 (by decide))))
      | exact (install_other productSlots _ _ 19 (by decide)).trans ((install_other halfSlots _ _ 19 (by decide)).trans
          ((install_other splitSlots _ _ 19 (by decide)).trans (install_other uSlots _ _ 19 (by decide))))
      | exact (install_other productSlots _ _ 0 (by decide)).trans ((install_other halfSlots _ _ 0 (by decide)).trans
          ((install_other splitSlots _ _ 0 (by decide)).trans (install_other uSlots _ _ 0 (by decide))))
      | exact (install_other productSlots _ _ 20 (by decide)).trans ((install_other halfSlots _ _ 20 (by decide)).trans
          ((install_other splitSlots _ _ 20 (by decide)).trans (install_other uSlots _ _ 20 (by decide))))
  let out := install byteSlots fourth bytes.final.tapes
  have hfifth := CompetitorRationalProducts.bounded_focus byteSlots (by decide) _ _ _ byteReady fourth hbyte
  have hlast := ClockJoin.join productProgram byteProgram _ _ _ _ _ hfourth hfifth
  have hhalfLast := ClockJoin.join halfProgram (Composition.machine productProgram byteProgram) _ _ _ _ _ hthird hlast
  have hsplitLast := ClockJoin.join splitProgram (Composition.machine halfProgram (Composition.machine productProgram byteProgram))
    _ _ _ _ _ hsecond hhalfLast
  have hall := ClockJoin.join uProgram
    (Composition.machine splitProgram (Composition.machine halfProgram (Composition.machine productProgram byteProgram)))
    _ _ _ _ _ hfirst hsplitLast
  have htime : (4*u+12)+1+((2*u+4)+1+((4*(u/2)+8)+1+
      (WilliamsUnaryProduct.budget q (u/2)+1+(4*halfBytes u q+8))))=prepareBudget u q := by
    unfold prepareBudget
    omega
  rw [htime] at hall
  have keep (i : Fin 21) (hb : ∀ j,byteSlots j≠i) (hp : ∀ j,productSlots j≠i)
      (hh : ∀ j,halfSlots j≠i) (hs : ∀ j,splitSlots j≠i) : out i=first i :=
    (install_other byteSlots fourth bytes.final.tapes i hb).trans
      ((install_other productSlots third _ i hp).trans
        ((install_other halfSlots second _ i hh).trans (install_other splitSlots first _ i hs)))
  refine ⟨out,hall,(install_slot byteSlots (by decide) fourth bytes.final.tapes 3).trans hb3,?_,?_,?_,?_⟩
  · exact (keep 1 (by decide) (by decide) (by decide) (by decide)).trans (install_other uSlots _ _ 1 (by decide))
  · exact (keep 2 (by decide) (by decide) (by decide) (by decide)).trans (install_other uSlots _ _ 2 (by decide))
  · exact (keep 3 (by decide) (by decide) (by decide) (by decide)).trans
      ((install_slot uSlots (by decide) _ ucopy.final.tapes 0).trans hu0)
  · exact (install_other byteSlots fourth bytes.final.tapes 4 (by decide)).trans
      (install_slot productSlots (by decide) third (WilliamsUnaryProduct.output q (u/2)) 0)

end NearCubicWires.RepairOrdinary.CompetitorOddRowSlice
