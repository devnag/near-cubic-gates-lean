import Proof.CaseAnalysis.RowsEstimatorSubstitutionFactorLayout

/-! Execute one actual factor, copy the new accumulator, and retire all
three temporary streams at their logical lengths. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionFactor
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch CloseoutRowsRawPairSeek
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=Composition.machine
  (Composition.machine (Composition.machine (Composition.machine
    (Composition.machine cacheMachine productMachine) accMachine) atomMachine) copyMachine) productClearMachine
def value (cs : List Pair) (i : ℕ) (hi : i<cs.length) (acc : List (List ℕ)):=
  CloseoutRowsRawProductLoop.product acc (cs[i].1++cs[i].2)
def budget (R : ℕ) (cs : List Pair) (i : ℕ) (hi : i<cs.length) (acc : List (List ℕ)):=
  SubstitutionCache.budget cs i hi+1+SubstitutionProduct.budget R acc.length+
    1+(2*(ExtIncidence.stream acc).length+2)+1+(2*(ExtIncidence.stream (cs[i].1++cs[i].2)).length+2)+
    1+SubstitutionCopy.budget (value cs i hi acc)+1+(2*(ExtIncidence.stream (value cs i hi acc)).length+2)
structure Fits (C R : ℕ) (acc atom : List (List ℕ)) : Prop where
  rowCapacity : R ≤ C
  monomial : ∀ l∈acc,(l.flatMap ExtIncidence.block).length+1 ≤ R
  row : ∀ l∈acc,CloseoutRowsRawProductRow.budget l atom ≤ R
  productTime : CloseoutRowsRawProductLoop.budget R acc.length ≤ C
  accLength : (ExtIncidence.stream acc).length ≤ C
  atomLength : (ExtIncidence.stream atom).length ≤ C
  copyTime : CloseoutRowsRawPolynomialAdd.budget (CloseoutRowsRawProductLoop.product acc atom) [] ≤ C
  productLength : (ExtIncidence.stream (CloseoutRowsRawProductLoop.product acc atom)).length ≤ C

theorem run (C R : ℕ) (cs : List Pair) (i : ℕ) (hi : i<cs.length) (pre tail : List Bool)
    (acc : List (List ℕ)) (hcache : SubstitutionCache.capacity cs ≤ C) (h : Fits C R acc (cs[i].1++cs[i].2)) :
    Step machine (budget R cs i hi acc) (heads pre.length)
      (data C (pre++ExtIncidence.block i++tail) (cacheWord cs) [] (ExtIncidence.stream acc) [])
      (heads (pre.length+(ExtIncidence.block i).length))
      (data C (pre++ExtIncidence.block i++tail) (cacheWord cs) [] (ExtIncidence.stream (value cs i hi acc)) []) := by
  let pos:=pre.length+(ExtIncidence.block i).length
  let source:=pre++ExtIncidence.block i++tail
  let atom:=cs[i].1++cs[i].2
  let product:=value cs i hi acc
  have a:=cache_run C cs i hi pre tail (ExtIncidence.stream acc) hcache
  have b:=product_run C R pos source (cacheWord cs) acc atom h.rowCapacity h.monomial h.row h.productTime
  have c:=acc_run C pos source (cacheWord cs) (ExtIncidence.stream atom) (ExtIncidence.stream product) acc h.accLength
  have d:=atom_run C pos source (cacheWord cs) [] (ExtIncidence.stream product) atom h.atomLength
  have e:=copy_run C pos source (cacheWord cs) product h.copyTime
  have f:=product_clear_run C pos source (cacheWord cs) [] (ExtIncidence.stream product) product h.productLength
  exact ((((a.seq b).seq c).seq d).seq e).seq f

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionFactor
