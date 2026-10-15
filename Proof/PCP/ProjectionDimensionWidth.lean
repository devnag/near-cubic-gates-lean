import Proof.PCP.ProjectionDimensionPolynomial
import Proof.MachineModel.UWalkUnary

/-! From the physical unary dyadic exponent e, evaluate the small factor
and form R=e+bitLength(C*(e+1)^p), retaining e and producing binary R. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.DimensionWidth
open LocalBitMultitape RepairOrdinary RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def base (D : ℕ) := DimensionPolynomial.tapes D
def tapes (D : ℕ) := base D+13
def old (D : ℕ) (i : Fin (base D)) : Fin (tapes D) := i.castAdd 13
def fresh (D : ℕ) (i : Fin 13) : Fin (tapes D) := i.natAdd (base D)
def copySlots (D : ℕ) : Fin 3 → Fin (tapes D) :=
  ![old D (DimensionPolynomial.widthSlot D),fresh D 0,fresh D 1]
def sumSlots (D : ℕ) : Fin 4 → Fin (tapes D) :=
  ![old D ⟨0,by simp [base,DimensionPolynomial.tapes]⟩,fresh D 0,fresh D 2,fresh D 3]
def binarySlots (D : ℕ) : Fin 10 → Fin (tapes D) :=
  fun i => if i.val=0 then fresh D 2 else fresh D ⟨3+i.val,by omega⟩
theorem old_injective (D : ℕ) : Function.Injective (old D) := by
  intro a b h; exact Fin.ext (congrArg (fun i : Fin (tapes D) => i.val) h)
theorem copy_injective (D : ℕ) : Function.Injective (copySlots D) := by
  intro a b h; apply Fin.ext
  have hv := congrArg Fin.val h
  have hb : (DimensionPolynomial.widthSlot D).val < base D := (DimensionPolynomial.widthSlot D).isLt
  fin_cases a <;> fin_cases b <;> simp [copySlots,old,fresh] at hv ⊢ <;> omega
theorem sum_injective (D : ℕ) : Function.Injective (sumSlots D) := by
  intro a b h; apply Fin.ext
  have hv := congrArg Fin.val h
  have hb : 1 ≤ base D := by simp [base,DimensionPolynomial.tapes]; omega
  fin_cases a <;> fin_cases b <;> simp [sumSlots,old,fresh] at hv ⊢ <;> omega
theorem binary_injective (D : ℕ) : Function.Injective (binarySlots D) := by
  intro a b h; apply Fin.ext
  have hv := congrArg Fin.val h
  dsimp [binarySlots,fresh] at hv
  split_ifs at hv <;> dsimp at hv <;> omega

def input (D e : ℕ) : Fin (tapes D) → List Bool := fun i => if i.val=0 then List.replicate e true else []
def amount (D C e : ℕ) := e+natBitLength (DimensionPolynomial.value D C e)
noncomputable def polynomialProgram (D C : ℕ) := RecoveryFocus.machine (old D) (DimensionPolynomial.machine D C)
noncomputable def copyProgram (D : ℕ) := RecoveryFocus.machine (copySlots D) (UWalkUnary.machine false false)
noncomputable def sumProgram (D : ℕ) := RecoveryFocus.machine (sumSlots D) ClockUnarySum.machine
noncomputable def binaryProgram (D : ℕ) := RecoveryFocus.machine (binarySlots D) MatrixDimensionBinary.resetMachine
noncomputable def machine (D C : ℕ) := Composition.machine
  (Composition.machine (Composition.machine (polynomialProgram D C) (copyProgram D)) (sumProgram D)) (binaryProgram D)
def budget (D C e : ℕ) := DimensionPolynomial.budget D C e+1+
  (2*natBitLength (DimensionPolynomial.value D C e)+6)+1+(2*amount D C e+6)+1+
  (16*(amount D C e)^2+72*amount D C e+32)
def rawSlot (D : ℕ) := binarySlots D 1
def bitsSlot (D : ℕ) := binarySlots D 5

theorem width_run (D C e : ℕ) (hc : 0<C) : ∃ out,
    ClockJoin.ReadyRun (machine D C) (budget D C e) (input D e) out ∧
      out (old D ⟨0,by simp [base,DimensionPolynomial.tapes]⟩)=List.replicate e true ∧
      out (rawSlot D)=List.replicate (amount D C e) true ∧
      out (bitsSlot D)=frame (binary (natBitLength (amount D C e)) (amount D C e)) := by
  let a := DimensionPolynomial.value D C e
  let l := natBitLength a
  obtain ⟨polyOut,hpoly,he,_,_,hl⟩ := DimensionPolynomial.polynomial_run D C e hc
  have hp := hpoly.focus (old D) (old_injective D) (input D e) (by intro i; rfl)
  let p := install (old D) (input D e) polyOut
  change ClockJoin.ReadyRun (polynomialProgram D C) (DimensionPolynomial.budget D C e) (input D e) p at hp
  have psource : p (old D ⟨0,by simp [base,DimensionPolynomial.tapes]⟩)=List.replicate e true := by
    rw [show p=install (old D) (input D e) polyOut by rfl,install_slot _ (old_injective D)]
    exact he
  have pwidth : p (copySlots D 0)=UWalkUnary.source 0 l := by
    change install (old D) (input D e) polyOut (old D (DimensionPolynomial.widthSlot D))=_
    rw [install_slot _ (old_injective D),hl]
    simp [UWalkUnary.source,ZeroPadding.pad,l,a]
  have pblank (i : Fin 13) : p (fresh D i)=[] := by
    dsimp only [p]
    rw [install_other _ _ _ _ (by
      intro j hj; have hv := congrArg Fin.val hj; dsimp [old,fresh] at hv; omega)]
    have hb : 1 ≤ base D := by simp [base,DimensionPolynomial.tapes]; omega
    simp [input,fresh,show base D≠0 by omega]
  have hc0 := (UWalkUnary.ready false false 0 l).focus (copySlots D) (copy_injective D) p (by
    intro i; fin_cases i
    · exact pwidth
    · exact pblank 0
    · exact pblank 1)
  let c := install (copySlots D) p (UWalkUnary.result false false 0 l)
  change ClockJoin.ReadyRun (copyProgram D) (2*l+6) p c at hc0
  have csource : c (sumSlots D 0)=List.replicate e true := by
    dsimp only [c]
    rw [install_other _ _ _ _ (by
      intro i hi; have hv := congrArg Fin.val hi
      fin_cases i <;> simp [copySlots,sumSlots,old,fresh,DimensionPolynomial.widthSlot,
        DimensionPolynomial.binarySlots,base,DimensionPolynomial.tapes] at hv)]
    exact psource
  have clength : c (sumSlots D 1)=List.replicate l true := by
    change install (copySlots D) p _ (copySlots D 1)=_
    rw [install_slot _ (copy_injective D)]
    rfl
  have cblank (i : Fin 13) (hi : 2 ≤ i.val) : c (fresh D i)=[] := by
    dsimp only [c]
    rw [install_other _ _ _ _ (by
      intro j hj; have hv := congrArg Fin.val hj
      have hw : (DimensionPolynomial.widthSlot D).val < base D := (DimensionPolynomial.widthSlot D).isLt
      fin_cases j <;> simp [copySlots,old,fresh] at hv <;> omega)]
    exact pblank i
  have hsum := (ClockUnarySum.sum_ready e l).focus (sumSlots D) (sum_injective D) c (by
    intro i; fin_cases i
    · exact csource
    · exact clength
    · exact cblank 2 (by decide)
    · exact cblank 3 (by decide))
  let s := install (sumSlots D) c
    ![List.replicate e true,List.replicate l true,List.replicate (e+l) true,List.replicate (e+l+2) false]
  change ClockJoin.ReadyRun (sumProgram D) (2*amount D C e+6) c s at hsum
  have ssource : s (sumSlots D 0)=List.replicate e true := by
    change install (sumSlots D) c _ (sumSlots D 0)=_
    rw [install_slot _ (sum_injective D)]
    rfl
  have svalue : s (binarySlots D 0)=List.replicate (amount D C e) true := by
    change install (sumSlots D) c _ (sumSlots D 2)=_
    rw [install_slot _ (sum_injective D)]
    rfl
  have sblank (i : Fin 13) (hi : 4 ≤ i.val) : s (fresh D i)=[] := by
    dsimp only [s]
    rw [install_other _ _ _ _ (by
      intro j hj; have hv := congrArg Fin.val hj
      have hb : 1 ≤ base D := by simp [base,DimensionPolynomial.tapes]; omega
      fin_cases j <;> simp [sumSlots,old,fresh] at hv <;> omega)]
    exact cblank i (by omega)
  have hpos : 0<amount D C e := by dsimp [amount,natBitLength]; omega
  obtain ⟨r,hr,hraw,_,_,hbits,_,hh,hs⟩ := MatrixDimensionBinary.reset_run (amount D C e) hpos
  have hb : ClockJoin.ReadyRun MatrixDimensionBinary.resetMachine
      (16*(amount D C e)^2+72*amount D C e+32)
      (MatrixDimensionBinary.resetInput (amount D C e)) r.final.tapes := ⟨r,hr,rfl,hh,hs⟩
  have hbin := hb.focus (binarySlots D) (binary_injective D) s (by
    intro i; fin_cases i
    · exact svalue
    all_goals exact sblank _ (by decide))
  refine ⟨_,ClockJoin.join _ _ _ _ _ _ _
    (ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ hp hc0) hsum) hbin,?_,?_,?_⟩
  · rw [install_other _ _ _ _ (by
      intro i hi; have hv := congrArg Fin.val hi
      have hb : 1 ≤ base D := by simp [base,DimensionPolynomial.tapes]; omega
      dsimp [binarySlots,old,fresh] at hv
      split_ifs at hv <;> dsimp at hv <;> omega)]
    exact ssource
  · rw [rawSlot,install_slot _ (binary_injective D)]
    exact hraw
  · rw [bitsSlot,install_slot _ (binary_injective D)]
    exact hbits

end NearCubicWires.RepairSource.ProjectionNormalization.DimensionWidth
