import Proof.MachineModel.OrdinaryMatrixBucketSize

/-! Execute the remaining canonical quotient and successor. The output
is the literal bucket count, preserving the previously produced B. -/
namespace NearCubicWires.RepairOrdinary.MatrixBucketCount
open LocalBitMultitape RecoveryRootRound CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def divideSlots : Fin 4 → Fin 28 := ![7,20,22,23]
def copySlots : Fin 5 → Fin 28 := ![22,24,25,26,27]
def incrementSlots : Fin 1 → Fin 28 := fun _ => 26
noncomputable def divide := RecoveryFocus.machine divideSlots MatrixBucketDivide.machine
noncomputable def copy := RecoveryFocus.machine copySlots MatrixRawDimension.resetMachine
noncomputable def increment := RecoveryFocus.machine incrementSlots MatrixBucketDimensions.Increment.machine
noncomputable def tail := Composition.machine copy increment
noncomputable def machine := Composition.machine divide tail
def value (U B : ℕ) := (2*U)/B+1
def budget (U B : ℕ) := (8*(2*U)+6)+1+((4*((2*U)/B)+8)+1+(2*((2*U)/B)+5))

theorem count_run (U B : ℕ) (hB : 0<B) (ambient : Fin 28 → List Bool)
    (h7 : ambient 7=List.replicate (2*U) true) (h20 : ambient 20=UnaryTemplate.tape B)
    (fresh : ∀ i : Fin 28,22 ≤ i.val → ambient i=[]) :
    ∃ out,ClockJoin.ReadyRun machine (budget U B) ambient out ∧
      (∀ i : Fin 22,out (i.castAdd 6)=ambient (i.castAdd 6)) ∧
      out 24=List.replicate ((2*U)/B) true ∧ out 25=List.replicate ((2*U)/B) true ∧
      out 26=UnaryTemplate.tape (value U B) := by
  obtain ⟨divided,hd,d0,d1,d2,dh,ds⟩ := MatrixBucketDivide.divide_run (2*U) B hB
  have ready : ClockJoin.ReadyRun MatrixBucketDivide.machine (8*(2*U)+6)
      (MatrixBucketDivide.resetInput (2*U) B) divided.final.tapes := ⟨divided,hd,rfl,dh,ds⟩
  have hi : ∀ i,ambient (divideSlots i)=MatrixBucketDivide.resetInput (2*U) B i := by
    intro i; fin_cases i
    · exact h7
    · exact h20
    all_goals exact fresh _ (by decide)
  let stage := install divideSlots ambient divided.final.tapes
  have hp := bounded_focus divideSlots (by decide) _ _ _ ready ambient hi
  have localT (i : Fin 4) : stage (divideSlots i)=divided.final.tapes i := install_slot divideSlots (by decide) _ _ i
  have old (i : Fin 22) : stage (i.castAdd 6)=ambient (i.castAdd 6) := by
    by_cases h7' : i=7
    · subst i; exact (localT 0).trans (d0.trans h7.symm)
    by_cases h20' : i=20
    · subst i; exact (localT 1).trans (d1.trans h20.symm)
    apply install_other
    intro j h
    fin_cases j <;> have hv := congrArg Fin.val h <;> simp [divideSlots] at hv <;> omega
  have untouched (i : Fin 28) (hi : 24 ≤ i.val) : stage i=[] := by
    apply (install_other divideSlots _ _ i ?_).trans (fresh i (by omega))
    intro j h
    fin_cases j <;> have hv := congrArg Fin.val h <;> simp [divideSlots] at hv <;> omega
  obtain ⟨copied,hc,c1,c2,c3,ch,cs⟩ := MatrixRawDimension.reset_run ((2*U)/B)
  have cr : ClockJoin.ReadyRun MatrixRawDimension.resetMachine (4*((2*U)/B)+8)
      (MatrixRawDimension.resetInput ((2*U)/B)) copied.final.tapes := ⟨copied,hc,rfl,ch,cs.le⟩
  have ci : ∀ i,stage (copySlots i)=MatrixRawDimension.resetInput ((2*U)/B) i := by
    intro i; fin_cases i
    · exact (localT 2).trans d2
    all_goals exact untouched _ (by decide)
  let stage1 := install copySlots stage copied.final.tapes
  have hcopy := bounded_focus copySlots (by decide) _ _ _ cr stage ci
  have s26 : stage1 26=UnaryTemplate.tape ((2*U)/B) := (install_slot copySlots (by decide) _ _ 3).trans c3
  have old1 (i : Fin 22) : stage1 (i.castAdd 6)=ambient (i.castAdd 6) := by
    apply (install_other copySlots _ _ (i.castAdd 6) ?_).trans (old i)
    intro j h
    fin_cases j <;> have hv := congrArg Fin.val h <;> simp [copySlots] at hv <;> omega
  obtain ⟨base,hb,bt,bh,bs⟩ := MatrixBucketDimensions.Increment.increment_run ((2*U)/B)
  have ir : ClockJoin.ReadyRun MatrixBucketDimensions.Increment.machine (2*((2*U)/B)+5)
      (fun _ => UnaryTemplate.tape ((2*U)/B)) (fun _ => UnaryTemplate.tape (value U B)) :=
    ⟨base,hb,bt,bh,bs.le⟩
  let out := install incrementSlots stage1 (fun _ => UnaryTemplate.tape (value U B))
  have hinc := bounded_focus incrementSlots (by decide) _ _ _ ir stage1 (by intro i; exact s26)
  have ht := ClockJoin.join copy increment _ _ _ _ _ hcopy hinc
  have whole := ClockJoin.join divide tail _ _ _ _ _ hp ht
  refine ⟨out,whole,?_,?_,?_,install_slot incrementSlots (by decide) _ _ 0⟩
  · intro i
    apply (install_other incrementSlots _ _ (i.castAdd 6) ?_).trans (old1 i)
    intro j h
    have hv := congrArg Fin.val h
    dsimp [incrementSlots] at hv
    omega
  · exact (install_other incrementSlots _ _ 24 (by decide)).trans
      ((install_slot copySlots (by decide) _ _ 1).trans c1)
  · exact (install_other incrementSlots _ _ 25 (by decide)).trans
      ((install_slot copySlots (by decide) _ _ 2).trans c2)

end NearCubicWires.RepairOrdinary.MatrixBucketCount
