import Proof.CaseAnalysis.WitnessCoefficientBits
import Proof.PCP.ProjectionDimensionWidth

/-! One exact coefficient-bit policy is physically produced from the
actual source q0 and clause-bit count. The numeric clause count and the
numeric coefficient cap are never materialized. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.CoefficientBits
open LocalBitMultitape RecoveryRootRound RepairSource RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def polySlots (i : Fin (DimensionPolynomial.tapes 1)) : Fin 21:=⟨i.val,by
  have hi:=i.isLt;dsimp only [DimensionPolynomial.tapes] at hi;omega⟩
def copySlots : Fin 3→Fin 21:=![polySlots (DimensionPolynomial.widthSlot 1),17,18]
def sumSlots : Fin 4→Fin 21:=![16,17,19,20]
theorem poly_injective : Function.Injective polySlots:=by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 21=>k.val) h)
theorem copy_injective : Function.Injective copySlots:=by decide
theorem sum_injective : Function.Injective sumSlots:=by decide
def input (q0 clauseBits : ℕ) (i : Fin 21):=
  if i.val=0 then List.replicate q0 true else if i.val=16 then List.replicate clauseBits true else []
def width (delta : ℚ) (copies q0 clauseBits : ℕ):=
  clauseBits+natBitLength (DimensionPolynomial.value 1 (factor delta copies) q0)
noncomputable def poly (delta : ℚ) (copies : ℕ):=
  RecoveryFocus.machine polySlots (DimensionPolynomial.machine 1 (factor delta copies))
noncomputable def copy:=RecoveryFocus.machine copySlots (UWalkUnary.machine false false)
noncomputable def sum:=RecoveryFocus.machine sumSlots ClockUnarySum.machine
noncomputable def first (delta : ℚ) (copies : ℕ):=Composition.machine (poly delta copies) copy
noncomputable def machine (delta : ℚ) (copies : ℕ):=Composition.machine (first delta copies) sum
def budget (delta : ℚ) (copies q0 clauseBits : ℕ):=
  DimensionPolynomial.budget 1 (factor delta copies) q0+1+
    (2*natBitLength (DimensionPolynomial.value 1 (factor delta copies) q0)+6)+1+
      (2*width delta copies q0 clauseBits+6)

theorem policy_run (delta : ℚ) (copies q0 clauseBits : ℕ) : ∃ output,
    ClockJoin.ReadyRun (machine delta copies) (budget delta copies q0 clauseBits)
      (input q0 clauseBits) output ∧
      output 0=List.replicate q0 true ∧ output 16=List.replicate clauseBits true ∧
      output 19=List.replicate
        (natBitLength (CloseoutXor.cap delta q0 copies*max 1 (2*2^clauseBits))) true:=by
  let len:=natBitLength (DimensionPolynomial.value 1 (factor delta copies) q0)
  obtain ⟨p,hp,hq,_,_,hl⟩:=DimensionPolynomial.polynomial_run 1 (factor delta copies) q0
    (factor_positive delta copies)
  have hpoly:=hp.focus polySlots poly_injective (input q0 clauseBits) (by
    intro i
    have hi:i.val<16:=i.isLt
    simp only [polySlots,input,DimensionPolynomial.input]
    split_ifs <;> first | rfl | omega)
  let pbank:=install polySlots (input q0 clauseBits) p
  have old (i : Fin (DimensionPolynomial.tapes 1)) : pbank (polySlots i)=p i:=install_slot _ poly_injective _ _ _
  have fresh (i : Fin 21) (hi : 16 ≤ i.val) : pbank i=input q0 clauseBits i:=by
    apply install_other
    intro j h
    have hj:j.val<16:=j.isLt
    have hv:=congrArg Fin.val h
    change j.val=i.val at hv
    omega
  have hcopy:∀ i,pbank (copySlots i)=![UWalkUnary.source 0 len,[],[]] i:=by
    intro i;fin_cases i
    · change pbank (polySlots (DimensionPolynomial.widthSlot 1))=_
      rw [old,hl]
      change VerifierDecoding.CompareMachine.word len=UWalkUnary.source 0 len
      rw [UWalkUnary.source,ZeroPadding.pad_zero]
    · exact fresh 17 (by decide)
    · exact fresh 18 (by decide)
  have hc:=(UWalkUnary.ready false false 0 len).focus copySlots copy_injective pbank hcopy
  let cbank:=install copySlots pbank (UWalkUnary.result false false 0 len)
  have cleft:cbank 16=List.replicate clauseBits true:=by
    rw [show cbank=install copySlots pbank (UWalkUnary.result false false 0 len) by rfl,
      install_other _ _ _ _ (by decide)]
    exact fresh 16 (by decide)
  have cright:cbank 17=List.replicate len true:=by
    change install copySlots pbank _ (copySlots 1)=_
    rw [install_slot _ copy_injective]
    rfl
  have hsum:∀ i,cbank (sumSlots i)=
      ![List.replicate clauseBits true,List.replicate len true,[],[]] i:=by
    intro i;fin_cases i
    · exact cleft
    · exact cright
    all_goals
      rw [show cbank=install copySlots pbank (UWalkUnary.result false false 0 len) by rfl,
        install_other _ _ _ _ (by decide)]
      exact fresh _ (by decide)
  have hs:=(ClockUnarySum.sum_ready clauseBits len).focus sumSlots sum_injective cbank hsum
  have hall:=ClockJoin.join (first delta copies) sum _ _ _ _ _
    (ClockJoin.join (poly delta copies) copy _ _ _ _ _ hpoly hc) hs
  let output:=install sumSlots cbank
    ![List.replicate clauseBits true,List.replicate len true,
      List.replicate (clauseBits+len) true,List.replicate (clauseBits+len+2) false]
  refine ⟨output,hall,?_,?_,?_⟩
  · rw [show output=install sumSlots cbank _ by rfl,install_other _ _ _ _ (by decide)]
    rw [show cbank=install copySlots pbank _ by rfl,install_other _ _ _ _ (by decide)]
    exact (old ⟨0,by simp [DimensionPolynomial.tapes]⟩).trans hq
  · change install sumSlots cbank _ (sumSlots 0)=_
    rw [install_slot _ sum_injective]
    rfl
  · change install sumSlots cbank _ (sumSlots 2)=_
    rw [install_slot _ sum_injective,exact_bits]
    rfl

end NearCubicWires.RepairOrdinary.CloseoutWitness.CoefficientBits
