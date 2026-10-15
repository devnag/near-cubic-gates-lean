import Proof.MachineModel.OrdinaryMatrixBatchRetainedFields

/-! Actual key-width and endpoint preparation from the retained score
width, coordinate width and canonical native B. -/
namespace NearCubicWires.RepairOrdinary.MatrixBucketEndpoints
open LocalBitMultitape RecoveryRootRound CompetitorRationalProducts SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sumSlots : Fin 4 → Fin 16 := ![0,1,3,4]
def wideSlots : Fin 5 → Fin 16 := ![3,2,5,6,7]
def keyZeroSlots : Fin 5 → Fin 16 := ![3,8,9,10,11]
def idZeroSlots : Fin 5 → Fin 16 := ![1,12,13,14,15]
noncomputable def sum := RecoveryFocus.machine sumSlots ClockUnarySum.machine
noncomputable def wide := RecoveryFocus.machine wideSlots ClockNormalize.machine
noncomputable def keyZero := RecoveryFocus.machine keyZeroSlots ClockNormalize.machine
noncomputable def idZero := RecoveryFocus.machine idZeroSlots ClockNormalize.machine
noncomputable def zeros := Composition.machine keyZero idZero
noncomputable def tail := Composition.machine wide zeros
noncomputable def machine := Composition.machine sum tail
def input (W M B : ℕ) : Fin 16 → List Bool := fun i =>
  if i=0 then List.replicate W true else if i=1 then List.replicate M true else if i=2 then frame (binary M B) else []
def budget (W M : ℕ) := 10*(W+M)+4*M+21

theorem endpoints_run (W M B : ℕ) (hB : B<2^M) :
    ∃ out,ClockJoin.ReadyRun machine (budget W M) (input W M B) out ∧
      out 0=List.replicate W true ∧ out 1=List.replicate M true ∧ out 2=frame (binary M B) ∧
      out 3=List.replicate (W+M) true ∧ out 5=frame (binary (W+M) B) ∧
      out 9=frame (binary (W+M) 0) ∧ out 13=frame (binary M 0) := by
  let sumOut : Fin 4 → List Bool := ![List.replicate W true,List.replicate M true,List.replicate (W+M) true,List.replicate (W+M+2) false]
  let stage0 := install sumSlots (input W M B) sumOut
  have hs := bounded_focus sumSlots (by decide) _ _ _ (ClockUnarySum.sum_ready W M) (input W M B)
    (by intro i; fin_cases i <;> rfl)
  obtain ⟨widened,hw,w0,w1,w2,_,_,wh,ws⟩ := ClockScalarFields.scalar_run (W+M) (binary M B) (by simp)
  rw [binary_value M B hB] at w2
  have wr : ClockJoin.ReadyRun ClockNormalize.machine (4*(W+M)+4) (ClockNormalize.input (W+M) (binary M B)) widened.final.tapes :=
    ⟨widened,hw,rfl,wh,ws.le⟩
  have wi : ∀ i,stage0 (wideSlots i)=ClockNormalize.input (W+M) (binary M B) i := by
    intro i; fin_cases i
    · exact install_slot sumSlots (by decide) _ _ 2
    all_goals exact install_other sumSlots _ _ _ (by decide)
  let stage1 := install wideSlots stage0 widened.final.tapes
  have hwiden := bounded_focus wideSlots (by decide) _ _ _ wr stage0 wi
  obtain ⟨keyed,hk,k0,_,k2,_,_,kh,ks⟩ := ClockScalarFields.zero_run (W+M)
  have kr : ClockJoin.ReadyRun ClockNormalize.machine (4*(W+M)+4) (ClockScalarFields.zeroInput (W+M)) keyed.final.tapes :=
    ⟨keyed,hk,rfl,kh,ks.le⟩
  have ki : ∀ i,stage1 (keyZeroSlots i)=ClockScalarFields.zeroInput (W+M) i := by
    intro i; fin_cases i
    · exact (install_slot wideSlots (by decide) _ _ 0).trans w0
    all_goals exact (install_other wideSlots _ _ _ (by decide)).trans (install_other sumSlots _ _ _ (by decide))
  let stage2 := install keyZeroSlots stage1 keyed.final.tapes
  have hkey := bounded_focus keyZeroSlots (by decide) _ _ _ kr stage1 ki
  obtain ⟨ided,hi,i0,_,i2,_,_,ih,is⟩ := ClockScalarFields.zero_run M
  have ir : ClockJoin.ReadyRun ClockNormalize.machine (4*M+4) (ClockScalarFields.zeroInput M) ided.final.tapes :=
    ⟨ided,hi,rfl,ih,is.le⟩
  have ii : ∀ i,stage2 (idZeroSlots i)=ClockScalarFields.zeroInput M i := by
    intro i; fin_cases i
    · exact (install_other keyZeroSlots _ _ 1 (by decide)).trans
        ((install_other wideSlots _ _ 1 (by decide)).trans (install_slot sumSlots (by decide) _ _ 1))
    all_goals
      exact (install_other keyZeroSlots _ _ _ (by decide)).trans
        ((install_other wideSlots _ _ _ (by decide)).trans (install_other sumSlots _ _ _ (by decide)))
  let out := install idZeroSlots stage2 ided.final.tapes
  have hid := bounded_focus idZeroSlots (by decide) _ _ _ ir stage2 ii
  have hz := ClockJoin.join keyZero idZero _ _ _ _ _ hkey hid
  have ht := ClockJoin.join wide zeros _ _ _ _ _ hwiden hz
  have whole := ClockJoin.join sum tail _ _ _ _ _ hs ht
  have htime : (2*(W+M)+6)+1+((4*(W+M)+4)+1+((4*(W+M)+4)+1+(4*M+4)))=budget W M := by
    unfold budget
    omega
  rw [htime] at whole
  refine ⟨out,whole,?_,(install_slot idZeroSlots (by decide) _ _ 0).trans i0,?_,?_,?_,?_,
    (install_slot idZeroSlots (by decide) _ _ 2).trans i2⟩
  · exact (install_other idZeroSlots _ _ 0 (by decide)).trans ((install_other keyZeroSlots _ _ 0 (by decide)).trans
      ((install_other wideSlots _ _ 0 (by decide)).trans (install_slot sumSlots (by decide) _ _ 0)))
  · exact (install_other idZeroSlots _ _ 2 (by decide)).trans ((install_other keyZeroSlots _ _ 2 (by decide)).trans
      ((install_slot wideSlots (by decide) _ _ 1).trans w1))
  · exact (install_other idZeroSlots _ _ 3 (by decide)).trans ((install_slot keyZeroSlots (by decide) _ _ 0).trans k0)
  · exact (install_other idZeroSlots _ _ 5 (by decide)).trans ((install_other keyZeroSlots _ _ 5 (by decide)).trans
      ((install_slot wideSlots (by decide) _ _ 2).trans w2))
  · exact (install_other idZeroSlots _ _ 9 (by decide)).trans ((install_slot keyZeroSlots (by decide) _ _ 2).trans k2)

end NearCubicWires.RepairOrdinary.MatrixBucketEndpoints
