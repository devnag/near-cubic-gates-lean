import Proof.MachineModel.OrdinarySourceSATLiftRequestCodec
import Proof.MachineModel.OrdinarySourceSATLiftRequestMoves

namespace NearCubicWires.RepairSource.OrdinarySourceSATLift.Request
open LocalBitMultitape RepairOrdinary ProjectionNormalization OrdinaryOracleCompose
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (D : ℕ) := DimensionPolynomial.tapes D+3
def inputSlot (D : ℕ) : Fin (tapes D) := ⟨0,by simp [tapes,DimensionPolynomial.tapes]⟩
def logSlot (D : ℕ) : Fin (tapes D) := ⟨1,by simp [tapes,DimensionPolynomial.tapes]⟩
def outSlot (D : ℕ) : Fin (tapes D) := ⟨2,by simp [tapes,DimensionPolynomial.tapes]⟩
def powerSlot (D : ℕ) (i : Fin (DimensionPolynomial.tapes D)) : Fin (tapes D) :=
  ⟨3+i.val,by dsimp [tapes]; omega⟩
def nSlot (D : ℕ) : Fin (tapes D) := powerSlot D ⟨0,by simp [DimensionPolynomial.tapes]⟩
def bSlot (D : ℕ) : Fin (tapes D) := powerSlot D (PCPSerializerCapacity.Power.outputSlot D)
def copySlots (D : ℕ) : Fin 3 → Fin (tapes D) := ![inputSlot D,nSlot D,logSlot D]
def scaleSlots (D : ℕ) (which : Bool) : Fin 2 → Fin (tapes D) :=
  ![if which then bSlot D else nSlot D,outSlot D]

theorem power_injective (D : ℕ) : Function.Injective (powerSlot D) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  dsimp [powerSlot] at hv
  omega

theorem power_ne_out (D : ℕ) (i : Fin (DimensionPolynomial.tapes D)) : powerSlot D i≠outSlot D := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [powerSlot,outSlot] at hv
  omega

theorem n_ne_b (D : ℕ) : nSlot D≠bSlot D := by
  intro h
  have hv := congrArg Fin.val ((power_injective D) h)
  dsimp [PCPSerializerCapacity.Power.outputSlot,DimensionPolynomial.binarySlots] at hv
  omega

theorem copy_injective (D : ℕ) : Function.Injective (copySlots D) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [copySlots,inputSlot,nSlot,powerSlot,logSlot]

theorem scale_injective (D : ℕ) (which : Bool) : Function.Injective (scaleSlots D which) := by
  have hn := power_ne_out D ⟨0,by simp [DimensionPolynomial.tapes]⟩
  have hb := power_ne_out D (PCPSerializerCapacity.Power.outputSlot D)
  intro i j h
  cases which <;> fin_cases i <;> fin_cases j <;> simp_all [scaleSlots,nSlot,bSlot]

def ports (D : ℕ) : Ports (tapes D) where
  twoTapes := by simp [tapes,DimensionPolynomial.tapes]
  outputTape := outSlot D
  outputFresh := by simp [outSlot]
  queryTape := outSlot D
  queryFresh := by simp [outSlot]

structure Ready (D n b np bp : ℕ) (out : List Bool)
    (heads : Fin (tapes D) → ℕ) (data : Fin (tapes D) → List Bool) : Prop where
  n_head : heads (nSlot D)=np
  n_data : data (nSlot D)=List.replicate n true
  b_head : heads (bSlot D)=bp
  b_data : data (bSlot D)=List.replicate b true
  out_head : heads (outSlot D)=out.length
  out_data : data (outSlot D)=out

theorem Ready.print {D n b np bp : ℕ} {out bits : List Bool}
    {heads newHeads : Fin (tapes D) → ℕ} {data newData : Fin (tapes D) → List Bool}
    (h : Ready D n b np bp out heads data)
    (hh : newHeads (outSlot D)=(out++bits).length) (ht : newData (outSlot D)=out++bits)
    (other : ∀ i,i≠outSlot D → newHeads i=heads i ∧ newData i=data i) :
    Ready D n b np bp (out++bits) newHeads newData := by
  have hn := other (nSlot D) (power_ne_out D _)
  have hb := other (bSlot D) (power_ne_out D _)
  exact ⟨hn.1.trans h.n_head,hn.2.trans h.n_data,hb.1.trans h.b_head,hb.2.trans h.b_data,hh,ht⟩

end NearCubicWires.RepairSource.OrdinarySourceSATLift.Request
