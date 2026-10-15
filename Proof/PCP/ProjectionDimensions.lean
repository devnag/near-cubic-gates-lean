import Proof.PCP.ProjectionDimensionWidth
import Proof.PCP.ProjectionDimensionDyadic

/-! Actual production of both adopted PCP dimensions. Unary intermediates
are fixed polynomials in the dyadic exponent; no proof envelope is expanded. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.DimensionProducer
open LocalBitMultitape RepairOrdinary RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (p q : ℕ) := DimensionWidth.tapes p+DimensionPolynomial.tapes q
def old (p q : ℕ) (i : Fin (DimensionWidth.tapes p)) : Fin (tapes p q) := i.castAdd (DimensionPolynomial.tapes q)
def querySlots (p q : ℕ) : Fin (DimensionPolynomial.tapes q) → Fin (tapes p q) :=
  fun i => if i.val=0 then old p q (DimensionWidth.rawSlot p)
    else ⟨DimensionWidth.tapes p+(i.val-1),by dsimp [tapes]; have := i.isLt; omega⟩
theorem old_injective (p q : ℕ) : Function.Injective (old p q) := by
  intro a b h; exact Fin.ext (congrArg (fun i : Fin (tapes p q) => i.val) h)
theorem query_injective (p q : ℕ) : Function.Injective (querySlots p q) := by
  intro a b h; apply Fin.ext
  have hv := congrArg Fin.val h
  have hr := (DimensionWidth.rawSlot p).isLt
  dsimp only [querySlots,old] at hv
  split_ifs at hv <;> dsimp at hv <;> omega

def input (p q e : ℕ) : Fin (tapes p q) → List Bool := fun i => if i.val=0 then List.replicate e true else []
noncomputable def widthProgram (p q C : ℕ) := RecoveryFocus.machine (old p q) (DimensionWidth.machine p C)
noncomputable def queryProgram (p q C : ℕ) := RecoveryFocus.machine (querySlots p q) (DimensionPolynomial.machine q C)
noncomputable def machine (p q C : ℕ) := Composition.machine (widthProgram p q C) (queryProgram p q C)
def budget (p q C e : ℕ) := DimensionWidth.budget p C e+1+
  DimensionPolynomial.budget q C (DimensionWidth.amount p C e)
def R (p C e : ℕ) := DimensionWidth.amount p C e
def Q (p q C e : ℕ) := DimensionPolynomial.value q C (R p C e)
def rawR (p q : ℕ) := old p q (DimensionWidth.rawSlot p)
def bitsR (p q : ℕ) := old p q (DimensionWidth.bitsSlot p)
def rawQ (p q : ℕ) := querySlots p q (DimensionPolynomial.rawSlot q)
def bitsQ (p q : ℕ) := querySlots p q (DimensionPolynomial.bitsSlot q)

theorem dimensions_run (p q C e : ℕ) (hc : 0<C) : ∃ out,
    ClockJoin.ReadyRun (machine p q C) (budget p q C e) (input p q e) out ∧
      out (rawR p q)=List.replicate (R p C e) true ∧
      out (bitsR p q)=frame (binary (natBitLength (R p C e)) (R p C e)) ∧
      out (rawQ p q)=List.replicate (Q p q C e) true ∧
      out (bitsQ p q)=frame (binary (natBitLength (Q p q C e)) (Q p q C e)) := by
  obtain ⟨wout,hw,_,hraw,hbits⟩ := DimensionWidth.width_run p C e hc
  have hwidth := hw.focus (old p q) (old_injective p q) (input p q e) (by intro i; rfl)
  let middle := install (old p q) (input p q e) wout
  have hmraw : middle (querySlots p q ⟨0,by simp [DimensionPolynomial.tapes]⟩)=List.replicate (R p C e) true := by
    change install (old p q) (input p q e) wout (old p q (DimensionWidth.rawSlot p))=_
    rw [install_slot _ (old_injective p q)]
    exact hraw
  have hmblank (i : Fin (DimensionPolynomial.tapes q)) (hi : i.val≠0) : middle (querySlots p q i)=[] := by
    dsimp only [middle]
    rw [install_other _ _ _ _ (by
      intro j hj; have hv := congrArg Fin.val hj; have hbound := j.isLt
      simp only [querySlots,hi,if_false,old,Fin.val_castAdd] at hv
      omega)]
    have hf : 1 ≤ DimensionWidth.tapes p := by simp [DimensionWidth.tapes,DimensionWidth.base,DimensionPolynomial.tapes]
    simp [input,querySlots,hi,show DimensionWidth.tapes p≠0 by omega]
  obtain ⟨qout,hq,hretain,hqraw,hqbits,_⟩ := DimensionPolynomial.polynomial_run q C (R p C e) hc
  have hquery := hq.focus (querySlots p q) (query_injective p q) middle (by
    intro i
    by_cases hi : i.val=0
    · have he : i=⟨0,by simp [DimensionPolynomial.tapes]⟩ := Fin.ext hi
      subst i
      exact hmraw
    · rw [DimensionPolynomial.input,if_neg hi]
      exact hmblank i hi)
  refine ⟨_,ClockJoin.join _ _ _ _ _ _ _ hwidth hquery,?_,?_,?_,?_⟩
  · change install (querySlots p q) middle qout (querySlots p q ⟨0,by simp [DimensionPolynomial.tapes]⟩)=_
    rw [install_slot _ (query_injective p q)]
    exact hretain
  · rw [install_other _ _ _ _ (by
      intro i hi; have hv := congrArg Fin.val hi
      have hbound := (DimensionWidth.bitsSlot p).isLt
      dsimp [querySlots,bitsR,old] at hv
      split_ifs at hv
      · simp [DimensionWidth.rawSlot,DimensionWidth.bitsSlot,DimensionWidth.binarySlots,DimensionWidth.fresh] at hv
      · dsimp at hv; omega)]
    change install (old p q) (input p q e) wout (old p q (DimensionWidth.bitsSlot p))=_
    rw [install_slot _ (old_injective p q)]
    exact hbits
  · rw [rawQ,install_slot _ (query_injective p q)]
    exact hqraw
  · rw [bitsQ,install_slot _ (query_injective p q)]
    exact hqbits

end NearCubicWires.RepairSource.ProjectionNormalization.DimensionProducer
