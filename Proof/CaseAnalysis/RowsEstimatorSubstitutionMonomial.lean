import Proof.CaseAnalysis.RowsEstimatorSubstitutionRepeat
import Proof.CaseAnalysis.RowsEstimatorSubstitutionFactorRun

/-! Each original factor block controls one actual reusable Pair operation. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionMonomial
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch CloseoutRowsRawPairSeek
open SubstitutionFactor (data heads)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def Valid (cs : List Pair) (m : List ℕ) : Prop:=∀ i∈m,i<cs.length
def value (cs : List Pair) : (m : List ℕ) → Valid cs m → List (List ℕ) → List (List ℕ)
  | [],_,acc=>acc
  | i::m,h,acc=>value cs m (fun j hj=>h j (by simp [hj])) (SubstitutionFactor.value cs i (h i (by simp)) acc)
def budget (R : ℕ) (cs : List Pair) : (m : List ℕ) → Valid cs m → List (List ℕ) → ℕ
  | [],_,_=>1
  | i::m,h,acc=>SubstitutionFactor.budget R cs i (h i (by simp)) acc+2+
      budget R cs m (fun j hj=>h j (by simp [hj])) (SubstitutionFactor.value cs i (h i (by simp)) acc)
def Fits (C R : ℕ) (cs : List Pair) : (m : List ℕ) → Valid cs m → List (List ℕ) → Prop
  | [],_,_=>True
  | i::m,h,acc=>SubstitutionFactor.Fits C R acc ((cs[i]'(h i (by simp))).1++(cs[i]'(h i (by simp))).2) ∧
      Fits C R cs m (fun j hj=>h j (by simp [hj])) (SubstitutionFactor.value cs i (h i (by simp)) acc)
noncomputable def machine:=SubstitutionRepeat.machine SubstitutionFactor.machine 0

theorem remaining (C R : ℕ) (cs : List Pair) (m : List ℕ) (valid : Valid cs m)
    (pre tail : List Bool) (acc : List (List ℕ)) (hcache : SubstitutionCache.capacity cs ≤ C)
    (hf : Fits C R cs m valid acc) : ∃ time ≤ budget R cs m valid acc,Timed machine time
      (SubstitutionRepeat.entry SubstitutionFactor.machine 0 (heads pre.length)
        (data C (pre++m.flatMap ExtIncidence.block++false::tail) (cacheWord cs) [] (ExtIncidence.stream acc) []))
      (SubstitutionRepeat.final SubstitutionFactor.machine (heads (pre.length+(m.flatMap ExtIncidence.block).length))
        (data C (pre++m.flatMap ExtIncidence.block++false::tail) (cacheWord cs) [] (ExtIncidence.stream (value cs m valid acc)) [])) := by
  unfold machine
  induction m generalizing pre acc with
  | nil=>
    refine ⟨1,Nat.le_refl _,?_⟩
    simpa [value,List.flatMap_nil] using SubstitutionRepeat.stop SubstitutionFactor.machine 0
      (heads pre.length) (data C (pre++false::tail) (cacheWord cs) [] (ExtIncidence.stream acc) [])
      (by exact Streaming.read_append pre tail false)
  | cons i m ih=>
    let hi:=valid i (by simp)
    let validTail : Valid cs m:=fun j hj=>valid j (by simp [hj])
    let next:=SubstitutionFactor.value cs i hi acc
    have raw:=SubstitutionFactor.run C R cs i hi pre (m.flatMap ExtIncidence.block++false::tail) acc hcache hf.1
    obtain ⟨first,hfirst,tr⟩:=SubstitutionRepeat.body SubstitutionFactor.machine 0 _ _ _ _ raw
    obtain ⟨rest,hrest,restTrace⟩:=ih validTail (pre++ExtIncidence.block i) next hf.2
    have probe:=SubstitutionRepeat.probe SubstitutionFactor.machine 0 (heads pre.length)
      (data C (pre++ExtIncidence.block i++(m.flatMap ExtIncidence.block++false::tail))
        (cacheWord cs) [] (ExtIncidence.stream acc) []) (by
          change readTapeBit (pre++ExtIncidence.block i++(m.flatMap ExtIncidence.block++false::tail)) pre.length=true
          simp [ExtIncidence.block,List.replicate_succ,List.append_assoc,Streaming.read_append])
    simp only [List.append_assoc,List.length_append] at tr restTrace probe
    have all:=probe.trans (tr.trans restTrace)
    refine ⟨1+(first+rest),?_,?_⟩
    · change 1+(first+rest) ≤ SubstitutionFactor.budget R cs i hi acc+2+budget R cs m validTail next
      omega
    · simpa only [List.flatMap_cons,List.append_assoc,List.length_append,Nat.add_assoc,value] using all

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionMonomial
