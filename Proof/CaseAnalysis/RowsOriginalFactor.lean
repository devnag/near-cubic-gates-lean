import Proof.CaseAnalysis.RowsOriginalCache
import Proof.CaseAnalysis.RowsEstimatorSubstitutionFactorRun

/-! One original family factor uses the actual single-cache reader and the
existing Cartesian product, accumulator copy, and logical-length cleanup. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsOriginalFactor
open LocalBitMultitape ExtDecompositionBatch CloseoutRowsRawAtomSeek CloseoutRowsEstimator
open SubstitutionFactor (heads data productMachine accMachine atomMachine copyMachine productClearMachine)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def cacheMachine := RecoveryFocus.machine SubstitutionFactor.cacheSlots CloseoutRowsOriginalCache.machine
noncomputable def machine := Composition.machine
  (Composition.machine (Composition.machine (Composition.machine
    (Composition.machine cacheMachine productMachine) accMachine) atomMachine) copyMachine) productClearMachine
def value (cs : List (List (List ℕ))) (i : ℕ) (hi : i < cs.length) (acc : List (List ℕ)) :=
  CloseoutRowsRawProductLoop.product acc cs[i]
def budget (R : ℕ) (cs : List (List (List ℕ))) (i : ℕ) (hi : i < cs.length) (acc : List (List ℕ)) :=
  CloseoutRowsOriginalCache.budget cs i hi+1+SubstitutionProduct.budget R acc.length+
    1+(2*(ExtIncidence.stream acc).length+2)+1+(2*(ExtIncidence.stream cs[i]).length+2)+
    1+SubstitutionCopy.budget (value cs i hi acc)+1+(2*(ExtIncidence.stream (value cs i hi acc)).length+2)

theorem cache_run (C : ℕ) (cs : List (List (List ℕ))) (i : ℕ) (hi : i < cs.length)
    (pre tail acc : List Bool) (hc : CloseoutRowsOriginalCache.capacity cs ≤ C) :
    Step cacheMachine (CloseoutRowsOriginalCache.budget cs i hi) (heads pre.length)
      (data C (pre++ExtIncidence.block i++tail) (cacheWord cs) [] acc [])
      (heads (pre.length+(ExtIncidence.block i).length))
      (data C (pre++ExtIncidence.block i++tail) (cacheWord cs) (ExtIncidence.stream cs[i]) acc []) := by
  refine SubstitutionDock.run _ _ (by decide) _ _ _ _ _ _ _ _
    (CloseoutRowsOriginalCache.run C cs i hi pre tail hc) ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first
  | (intro j;fin_cases j <;> rfl)
  | (intro j hj;fin_cases j <;> first | rfl | exact False.elim (hj 0 rfl) | exact False.elim (hj 2 rfl))

theorem run (C R : ℕ) (cs : List (List (List ℕ))) (i : ℕ) (hi : i < cs.length)
    (pre tail : List Bool) (acc : List (List ℕ)) (hcache : CloseoutRowsOriginalCache.capacity cs ≤ C)
    (h : SubstitutionFactor.Fits C R acc cs[i]) :
    Step machine (budget R cs i hi acc) (heads pre.length)
      (data C (pre++ExtIncidence.block i++tail) (cacheWord cs) [] (ExtIncidence.stream acc) [])
      (heads (pre.length+(ExtIncidence.block i).length))
      (data C (pre++ExtIncidence.block i++tail) (cacheWord cs) [] (ExtIncidence.stream (value cs i hi acc)) []) := by
  let pos:=pre.length+(ExtIncidence.block i).length
  let source:=pre++ExtIncidence.block i++tail
  have a:=cache_run C cs i hi pre tail (ExtIncidence.stream acc) hcache
  have b:=SubstitutionFactor.product_run C R pos source (cacheWord cs) acc cs[i]
    h.rowCapacity h.monomial h.row h.productTime
  have c:=SubstitutionFactor.acc_run C pos source (cacheWord cs) (ExtIncidence.stream cs[i])
    (ExtIncidence.stream (value cs i hi acc)) acc h.accLength
  have d:=SubstitutionFactor.atom_run C pos source (cacheWord cs) [] (ExtIncidence.stream (value cs i hi acc)) cs[i] h.atomLength
  have e:=SubstitutionFactor.copy_run C pos source (cacheWord cs) (value cs i hi acc) h.copyTime
  have f:=SubstitutionFactor.product_clear_run C pos source (cacheWord cs) []
    (ExtIncidence.stream (value cs i hi acc)) (value cs i hi acc) h.productLength
  exact ((((a.seq b).seq c).seq d).seq e).seq f

end NearCubicWires.RepairOrdinary.CloseoutRowsOriginalFactor
