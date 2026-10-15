import Proof.CaseAnalysis.RowsEstimatorSubstitutionRepeat
import Proof.CaseAnalysis.RowsOriginalFactor

/-! Each original family index block controls one actual single-cache Cartesian operation. No repeated factor is cancelled. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsOriginalMonomial
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch CloseoutRowsRawAtomSeek CloseoutRowsEstimator
open SubstitutionFactor (data heads)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def Valid (cs : List (List (List ℕ))) (m : List ℕ) : Prop:=∀ i∈m,i<cs.length
def value (cs : List (List (List ℕ))) : (m : List ℕ) → Valid cs m → List (List ℕ) → List (List ℕ)
  | [],_,acc=>acc
  | i::m,h,acc=>value cs m (fun j hj=>h j (by simp [hj])) (CloseoutRowsOriginalFactor.value cs i (h i (by simp)) acc)
def budget (R : ℕ) (cs : List (List (List ℕ))) : (m : List ℕ) → Valid cs m → List (List ℕ) → ℕ
  | [],_,_=>1
  | i::m,h,acc=>CloseoutRowsOriginalFactor.budget R cs i (h i (by simp)) acc+2+
      budget R cs m (fun j hj=>h j (by simp [hj])) (CloseoutRowsOriginalFactor.value cs i (h i (by simp)) acc)
def Fits (C R : ℕ) (cs : List (List (List ℕ))) : (m : List ℕ) → Valid cs m → List (List ℕ) → Prop
  | [],_,_=>True
  | i::m,h,acc=>SubstitutionFactor.Fits C R acc (cs[i]'(h i (by simp))) ∧
      Fits C R cs m (fun j hj=>h j (by simp [hj])) (CloseoutRowsOriginalFactor.value cs i (h i (by simp)) acc)
noncomputable def machine:=SubstitutionRepeat.machine CloseoutRowsOriginalFactor.machine 0

theorem remaining (C R : ℕ) (cs : List (List (List ℕ))) (m : List ℕ) (valid : Valid cs m)
    (pre tail : List Bool) (acc : List (List ℕ)) (hcache : CloseoutRowsOriginalCache.capacity cs ≤ C)
    (hf : Fits C R cs m valid acc) : ∃ time ≤ budget R cs m valid acc,Timed machine time
      (SubstitutionRepeat.entry CloseoutRowsOriginalFactor.machine 0 (heads pre.length)
        (data C (pre++m.flatMap ExtIncidence.block++false::tail) (cacheWord cs) [] (ExtIncidence.stream acc) []))
      (SubstitutionRepeat.final CloseoutRowsOriginalFactor.machine (heads (pre.length+(m.flatMap ExtIncidence.block).length))
        (data C (pre++m.flatMap ExtIncidence.block++false::tail) (cacheWord cs) [] (ExtIncidence.stream (value cs m valid acc)) [])) := by
  unfold machine
  induction m generalizing pre acc with
  | nil=>
    refine ⟨1,Nat.le_refl _,?_⟩
    simpa [value,List.flatMap_nil] using SubstitutionRepeat.stop CloseoutRowsOriginalFactor.machine 0
      (heads pre.length) (data C (pre++false::tail) (cacheWord cs) [] (ExtIncidence.stream acc) [])
      (by exact Streaming.read_append pre tail false)
  | cons i m ih=>
    let hi:=valid i (by simp)
    let validTail : Valid cs m:=fun j hj=>valid j (by simp [hj])
    let next:=CloseoutRowsOriginalFactor.value cs i hi acc
    have raw:=CloseoutRowsOriginalFactor.run C R cs i hi pre (m.flatMap ExtIncidence.block++false::tail) acc hcache hf.1
    obtain ⟨first,hfirst,tr⟩:=SubstitutionRepeat.body CloseoutRowsOriginalFactor.machine 0 _ _ _ _ raw
    obtain ⟨rest,hrest,restTrace⟩:=ih validTail (pre++ExtIncidence.block i) next hf.2
    have probe:=SubstitutionRepeat.probe CloseoutRowsOriginalFactor.machine 0 (heads pre.length)
      (data C (pre++ExtIncidence.block i++(m.flatMap ExtIncidence.block++false::tail))
        (cacheWord cs) [] (ExtIncidence.stream acc) []) (by
          change readTapeBit (pre++ExtIncidence.block i++(m.flatMap ExtIncidence.block++false::tail)) pre.length=true
          simp [ExtIncidence.block,List.replicate_succ,List.append_assoc,Streaming.read_append])
    simp only [List.append_assoc,List.length_append] at tr restTrace probe
    have all:=probe.trans (tr.trans restTrace)
    refine ⟨1+(first+rest),?_,?_⟩
    · change 1+(first+rest) ≤ CloseoutRowsOriginalFactor.budget R cs i hi acc+2+budget R cs m validTail next
      omega
    · simpa only [List.flatMap_cons,List.append_assoc,List.length_append,Nat.add_assoc,value] using all

end NearCubicWires.RepairOrdinary.CloseoutRowsOriginalMonomial
