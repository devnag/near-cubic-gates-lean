import Proof.Amplification.RecoveryPCPFormulaResumeScalars
import Proof.CaseAnalysis.RecoveryRowRandomReset
import Proof.PCP.ProjectionNormalizationDriverAtoms
import Proof.MachineModel.UWalkUnary

/-! Cold layout for the original projector bank. The four input words are
the original binary dimensions, actual normalized queries and paid B driver.
Scalar outputs dock directly to their original bank cells. -/
namespace NearCubicWires.RepairOrdinary.RecoveryProjectionCold
open LocalBitMultitape RepairSource RecoveryRootRound SourceInterfaces
open VerifierDecoding ProjectionNormalization CanonicalRecoveryLanguage
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def bankSlots (i : Fin 37) : Fin 113 := i.castAdd 76
def scalarSlots (i : Fin 66) : Fin 113 :=
  ⟨if i.val=3 then 34 else if i.val=17 then 32 else if i.val=31 then 35
    else if i.val=64 then 29 else if i.val=61 then 103 else i.val+37,
    by have hi:=i.isLt;split_ifs <;> omega⟩
def eraseSlots (i : Fin 31) : Fin 113 :=
  (RecoveryProjectionInitialize.eraseSlots i).castAdd 77
def backingSlots : Fin 4→Fin 113 := ![31,36,104,105]
def countSlots : Fin 4→Fin 113 := ![103,107,106,108]
def rawRSlots : Fin 3→Fin 113 := ![34,109,110]
def rawQSlots : Fin 3→Fin 113 := ![35,111,112]

theorem scalar_injective : Function.Injective scalarSlots := by
  intro a b h;apply Fin.ext
  have hv:=congrArg (fun i : Fin 113=>i.val) h
  have ha:=a.isLt;have hb:=b.isLt
  dsimp only [scalarSlots] at hv
  split_ifs at hv <;> omega
theorem erase_injective : Function.Injective eraseSlots := by
  intro a b h;apply RecoveryProjectionInitialize.erase_injective
  exact Fin.ext (congrArg (fun i : Fin 113=>i.val) h)
theorem backing_injective : Function.Injective backingSlots := by decide
theorem count_injective : Function.Injective countSlots := by decide
theorem rawR_injective : Function.Injective rawRSlots := by decide
theorem rawQ_injective : Function.Injective rawQSlots := by decide

theorem scalar_outside_low (i : Fin 113) (hi : i.val<37)
    (h29 : i.val≠29) (h32 : i.val≠32) (h34 : i.val≠34) (h35 : i.val≠35) :
    ∀ j,scalarSlots j≠i := by
  intro j h;have hv:=congrArg (fun i : Fin 113=>i.val) h
  dsimp only [scalarSlots] at hv
  split_ifs at hv <;> omega
theorem scalar_outside_high (i : Fin 113) (hi : (104 : ℕ)≤(i : Fin 113).val) :
    ∀ j,scalarSlots j≠i := by
  intro j h;have hv:=congrArg (fun i : Fin 113=>i.val) h
  have hj:=j.isLt
  dsimp only [scalarSlots] at hv
  split_ifs at hv <;> omega

def input (R Q B : ℕ) (queries : List Bool) (i : Fin 113) : List Bool :=
  if i=37 then frame R.bits else if i=65 then frame Q.bits
  else if i=28 then queries else if i=104 then List.replicate B true else []
def beforeBank (R Q : ℕ) (queries : List Bool) (i : Fin 37) : List Bool :=
  if i=28 then queries else if i=29 then frame (List.replicate R false)
  else if i=32 then List.replicate (RecoveryProjectionRows.capacity R) true
  else if i=34 then CompareMachine.word R else if i=35 then CompareMachine.word Q else []
def erasedBank (R Q : ℕ) (queries : List Bool) (i : Fin 37) : List Bool :=
  if i=28 then queries else if i=29 then frame (List.replicate R false)
  else if i=32 then List.replicate (RecoveryProjectionRows.capacity R) true
  else if i=34 then CompareMachine.word R else if i=35 then CompareMachine.word Q
  else if i=33 then List.replicate (RecoveryProjectionRows.capacity R+1) false
  else if i=31 ∨ i=36 then [] else List.replicate (RecoveryProjectionRows.capacity R) false
def readyBank (R Q B : ℕ) (queries : List Bool) (i : Fin 37) : List Bool :=
  if i=31 ∨ i=36 then List.replicate B false else erasedBank R Q queries i

theorem readyBank_original (p : RawProjectionPCP) (R Q B : ℕ) :
    readyBank R Q B (QueryBytes.framedCodes (normalizedRows p R Q).flatten)=
      RecoveryBoundedRowProjection.bank p R Q (bitInputOfCode R 0) B := by
  funext i
  fin_cases i
  all_goals first
    | (change List.replicate B false=ZeroPadding.pad B [];simp [ZeroPadding.pad])
    | (change frame (List.replicate R false)=ZeroPadding.pad 0 (frame (List.ofFn (bitInputOfCode R 0))++[])
       rw [RecoveryBoundedRowRandomReset.zero_word,List.append_nil,ZeroPadding.pad_zero])
    | exact (ZeroPadding.pad_zero _).symm

end NearCubicWires.RepairOrdinary.RecoveryProjectionCold
