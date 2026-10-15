import Proof.PCP.ProjectionDimensionTemplate

/-! The same fixed finite program evaluates C*(n+1)^D from a raw unary n
and blank scratch, then produces its binary value and unary bit length. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.DimensionPolynomial
open LocalBitMultitape RepairOrdinary RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (D : ℕ) := 14+2*D
def templateSlots (D : ℕ) : Fin 3 → Fin (tapes D) := fun i => ⟨i.val,by dsimp [tapes]; omega⟩
def powerSlots (D : ℕ) : Fin (DimensionPower.tapes D) → Fin (tapes D) :=
  fun i => if i.val=0 then ⟨1,by dsimp [tapes]; omega⟩ else ⟨2+i.val,by have := i.isLt; dsimp [tapes,DimensionPower.tapes] at *; omega⟩
def binarySlots (D : ℕ) : Fin 10 → Fin (tapes D) :=
  fun i => if i.val=0 then ⟨3+2*D,by dsimp [tapes]; omega⟩ else ⟨4+2*D+i.val,by dsimp [tapes]; omega⟩
theorem template_injective (D : ℕ) : Function.Injective (templateSlots D) := by
  intro a b h
  have hv := congrArg (fun i : Fin (tapes D) => i.val) h
  exact Fin.ext hv
theorem power_injective (D : ℕ) : Function.Injective (powerSlots D) := by
  intro a b h
  apply Fin.ext
  have hv := congrArg Fin.val h
  dsimp only [powerSlots] at hv
  split_ifs at hv <;> dsimp at hv <;> omega
theorem binary_injective (D : ℕ) : Function.Injective (binarySlots D) := by
  intro a b h
  apply Fin.ext
  have hv := congrArg Fin.val h
  dsimp only [binarySlots] at hv
  split_ifs at hv <;> dsimp at hv <;> omega

def input (D n : ℕ) : Fin (tapes D) → List Bool := fun i => if i.val=0 then List.replicate n true else []
noncomputable def templateProgram (D : ℕ) := RecoveryFocus.machine (templateSlots D) (DimensionTemplate.machine true)
noncomputable def powerProgram (D C : ℕ) := RecoveryFocus.machine (powerSlots D) (DimensionPower.machine D C)
noncomputable def binaryProgram (D : ℕ) := RecoveryFocus.machine (binarySlots D) MatrixDimensionBinary.resetMachine
noncomputable def machine (D C : ℕ) := Composition.machine
  (Composition.machine (templateProgram D) (powerProgram D C)) (binaryProgram D)
def value (D C n : ℕ) := C*(n+1)^D
def budget (D C n : ℕ) := (2*n+8)+1+DimensionPower.cost C (n+1) D+1+
  (16*(value D C n)^2+72*value D C n+32)
def rawSlot (D : ℕ) : Fin (tapes D) := binarySlots D 1
def bitsSlot (D : ℕ) : Fin (tapes D) := binarySlots D 5
def widthSlot (D : ℕ) : Fin (tapes D) := binarySlots D 8

theorem polynomial_run (D C n : ℕ) (hc : 0<C) : ∃ out,
    ClockJoin.ReadyRun (machine D C) (budget D C n) (input D n) out ∧
      out ⟨0,by simp [tapes]⟩=List.replicate n true ∧
      out (rawSlot D)=List.replicate (value D C n) true ∧
      out (bitsSlot D)=frame (binary (natBitLength (value D C n)) (value D C n)) ∧
      out (widthSlot D)=RepairSource.VerifierDecoding.CompareMachine.word (natBitLength (value D C n)) := by
  let middle := install (templateSlots D) (input D n) (DimensionTemplate.output true n)
  have ht := (DimensionTemplate.ready true n).focus (templateSlots D) (template_injective D) (input D n)
    (by intro i; fin_cases i <;> rfl)
  change ClockJoin.ReadyRun (templateProgram D) (2*n+8) (input D n) middle at ht
  have middle_source : middle ⟨0,by simp [tapes]⟩=List.replicate n true := by
    change install (templateSlots D) _ _ (templateSlots D 0)=_
    rw [install_slot _ (template_injective D)]
    rfl
  have middle_template : middle (powerSlots D ⟨0,by simp [DimensionPower.tapes]⟩)=UnaryTemplate.tape (n+1) := by
    change install (templateSlots D) _ _ (templateSlots D 1)=_
    rw [install_slot _ (template_injective D)]
    rfl
  have middle_blank (i : Fin (tapes D)) (hi : 3 ≤ i.val) : middle i=[] := by
    dsimp only [middle]
    rw [install_other _ _ _ _ (by
      intro j he; have hv := congrArg Fin.val he; dsimp [templateSlots] at hv; omega)]
    simp [input,show i.val≠0 by omega]
  obtain ⟨powerOut,hp,hpt,hpv⟩ := DimensionPower.power_run D C (n+1)
  have hpower := hp.focus (powerSlots D) (power_injective D) middle (by
    intro i
    by_cases hi : i.val=0
    · have he : i=⟨0,by simp [DimensionPower.tapes]⟩ := Fin.ext hi
      subst i
      exact middle_template
    · rw [DimensionPower.input,if_neg hi]
      exact middle_blank _ (by simp [powerSlots,hi]; omega))
  let afterPower := install (powerSlots D) middle powerOut
  change ClockJoin.ReadyRun (powerProgram D C) (DimensionPower.cost C (n+1) D) middle afterPower at hpower
  have power_source : afterPower ⟨0,by simp [tapes]⟩=List.replicate n true := by
    dsimp only [afterPower]
    rw [install_other _ _ _ _ (by
      intro i he; have hv := congrArg Fin.val he
      dsimp [powerSlots] at hv; split_ifs at hv; dsimp at hv; omega)]
    exact middle_source
  have power_value : afterPower (binarySlots D 0)=List.replicate (value D C n) true := by
    have he : binarySlots D 0=powerSlots D (DimensionPower.valueSlot D D le_rfl) := by
      apply Fin.ext
      simp [binarySlots,powerSlots,DimensionPower.valueSlot]
      omega
    rw [he]
    change install (powerSlots D) middle powerOut _=_
    rw [install_slot _ (power_injective D)]
    exact hpv
  have power_blank (i : Fin (tapes D)) (hi : 5+2*D ≤ i.val) : afterPower i=[] := by
    dsimp only [afterPower]
    rw [install_other _ _ _ _ (by
      intro j he; have hv := congrArg Fin.val he; have hj := j.isLt
      dsimp [powerSlots,DimensionPower.tapes] at hv hj
      split_ifs at hv <;> dsimp at hv <;> omega)]
    exact middle_blank i (by omega)
  have hpos : 0<value D C n := by dsimp [value]; positivity
  obtain ⟨r,hr,hraw,_,_,hbits,hwidth,hh,hs⟩ := MatrixDimensionBinary.reset_run (value D C n) hpos
  have hb : ClockJoin.ReadyRun MatrixDimensionBinary.resetMachine
      (16*(value D C n)^2+72*value D C n+32)
      (MatrixDimensionBinary.resetInput (value D C n)) r.final.tapes := ⟨r,hr,rfl,hh,hs⟩
  have hbinary := hb.focus (binarySlots D) (binary_injective D) afterPower (by
    intro i; fin_cases i
    · exact power_value
    all_goals exact power_blank _ (by simp [binarySlots]; omega))
  have hfinal := ClockJoin.join _ _ _ _ _ _ _
    (ClockJoin.join _ _ _ _ _ _ _ ht hpower) hbinary
  refine ⟨_,hfinal,?_,?_,?_,?_⟩
  · rw [install_other _ _ _ _ (by
      intro i he; have hv := congrArg Fin.val he
      dsimp [binarySlots] at hv; split_ifs at hv <;> dsimp at hv <;> omega)]
    exact power_source
  · rw [rawSlot,install_slot _ (binary_injective D)]
    exact hraw
  · rw [bitsSlot,install_slot _ (binary_injective D)]
    exact hbits
  · rw [widthSlot,install_slot _ (binary_injective D)]
    exact hwidth

end NearCubicWires.RepairSource.ProjectionNormalization.DimensionPolynomial
