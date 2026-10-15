import Proof.CaseAnalysis.CaseTwoCompoundInput
import Proof.CaseAnalysis.CaseTwoOriginalInput

/-! One block starts from the two retained frames and final address. The
compound input is physically copied to a fresh source bank; the original
hierarchy, converted description and address stay outside that bank. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.SourceBlock
open LocalBitMultitape RepairSource RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) (a : PointwisePCPPAlgorithm)
def tapes (k : ℕ):=8+OriginalSource.tapes source a k
def old (k : ℕ) (i : Fin 8) : Fin (tapes source a k):=i.castAdd (OriginalSource.tapes source a k)
def pairSlots (k : ℕ) (i : Fin 6):=old source a k ((![0,1,3,4,5,6] : Fin 6→Fin 8) i)
def sourceSlots (k : ℕ) (j : Fin (OriginalSource.tapes source a k)) : Fin (tapes source a k):=
  if j.val=0 then old source a k 3 else j.natAdd 8
theorem pair_injective (k : ℕ) : Function.Injective (pairSlots source a k):=by
  intro i j he
  have hv:=congrArg Fin.val he
  have hmap : (![0,1,3,4,5,6] : Fin 6→Fin 8) i=![0,1,3,4,5,6] j:=Fin.ext hv
  exact (by decide : Function.Injective (![0,1,3,4,5,6] : Fin 6→Fin 8)) hmap
theorem source_injective (k : ℕ) : Function.Injective (sourceSlots source a k):=by
  intro i j he
  have hv:=congrArg Fin.val he
  apply Fin.ext
  dsimp only [sourceSlots,old] at hv
  split_ifs at hv <;>simp only [Fin.val_castAdd,Fin.val_natAdd] at hv <;>omega
theorem source_away (k : ℕ) (i : Fin 3) : ∀ j,sourceSlots source a k j≠old source a k (i.castAdd 5):=by
  intro j he
  have hv:=congrArg Fin.val he
  have hi:=i.isLt
  dsimp only [sourceSlots,old] at hv
  split_ifs at hv <;>simp only [Fin.val_castAdd,Fin.val_natAdd] at hv <;>omega
def input (k : ℕ) (hierarchy oracle address : List Bool) : Fin (tapes source a k)→List Bool:=fun i=>
  if i.val=0 then frame hierarchy else if i.val=1 then frame oracle else if i.val=2 then frame address else []
def pair (k : ℕ):=RecoveryFocus.machine (pairSlots source a k) CompoundInput.machine
def sourceProgram (k CH Cpad : ℕ) (code : List Bool):=
  RecoveryFocus.machine (sourceSlots source a k) (OriginalSource.machine source a k CH Cpad code)
def machine (k CH Cpad : ℕ) (code : List Bool):=
  Composition.machine (pair source a k) (sourceProgram source a k CH Cpad code)
def cacheSlots (k : ℕ) (j : Fin 19):=sourceSlots source a k
  (OriginalSource.slots source a k (RequestSource.cacheSlots a (SourceCache.cacheSlots a j)))
def requestSlot (k : ℕ):=sourceSlots source a k
  (OriginalSource.slots source a k (RequestSource.cacheSlots a (SourceCache.requestSlot a)))

theorem pair_input (k : ℕ) (hierarchy oracle address : List Bool) (j : Fin 6) :
    input source a k hierarchy oracle address (pairSlots source a k j)=CompoundInput.input hierarchy oracle j:=by
  fin_cases j <;>rfl

theorem source_input (k : ℕ) (hierarchy oracle address : List Bool) (A : Fin 6→List Bool)
    (hword : A 2=frame hierarchy++frame oracle) (j : Fin (OriginalSource.tapes source a k)) :
    install (pairSlots source a k) (input source a k hierarchy oracle address) A (sourceSlots source a k j)=
      OriginalSource.input source a k hierarchy oracle j:=by
  rw [OriginalSource.input_word]
  by_cases hj : j.val=0
  · have he : sourceSlots source a k j=pairSlots source a k 2:=by simp [sourceSlots,hj];rfl
    rw [he,install_slot (pairSlots source a k) (pair_injective source a k),hword]
    simp only [SourceHandoff.sourceTapes,hj,if_true,PCPPNativeInputFields.word]
  · have away : ∀ i,pairSlots source a k i≠sourceSlots source a k j:=by
      intro i he
      have hv:=congrArg Fin.val he
      have hp : (pairSlots source a k i).val<8:=by fin_cases i <;>simp [pairSlots,old]
      simp only [sourceSlots,hj,if_false,Fin.val_natAdd] at hv
      omega
    rw [install_other (pairSlots source a k) _ _ _ away]
    simp only [input,sourceSlots,hj,if_false,Fin.val_natAdd,SourceHandoff.sourceTapes]
    have h1 : 8+j.val≠1:=by omega
    have h2 : 8+j.val≠2:=by omega
    simp [h1,h2]

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.SourceBlock
