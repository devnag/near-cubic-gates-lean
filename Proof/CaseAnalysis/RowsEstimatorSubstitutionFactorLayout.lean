import Proof.CaseAnalysis.RowsEstimatorSubstitutionDock
import Proof.CaseAnalysis.RowsEstimatorSubstitutionCopy
import Proof.CaseAnalysis.RowsEstimatorSubstitutionProduct

/-! One fixed accumulator bank for each source factor. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionFactor
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (pos : ℕ) : Fin 10 → ℕ:=![pos,0,0,0,0,0,0,0,0,0]
def data (C : ℕ) (source cache atom acc product : List Bool) : Fin 10 → List Bool:=
  ![source,cache,ZeroPadding.pad C atom,ZeroPadding.pad C acc,ZeroPadding.pad C product,[false],
    List.replicate C false,List.replicate C false,List.replicate C false,List.replicate C false]
def cacheSlots : Fin 7 → Fin 10:=![0,1,2,5,6,7,8]
def productSlots : Fin 6 → Fin 10:=![3,2,4,6,7,8]
def accSlots : Fin 2 → Fin 10:=![3,8]
def atomSlots : Fin 2 → Fin 10:=![2,8]
def copySlots : Fin 6 → Fin 10:=![4,9,3,6,7,8]
def productClearSlots : Fin 2 → Fin 10:=![4,8]
noncomputable def cacheMachine:=RecoveryFocus.machine cacheSlots SubstitutionCache.machine
noncomputable def productMachine:=RecoveryFocus.machine productSlots SubstitutionProduct.machine
noncomputable def accMachine:=RecoveryFocus.machine accSlots SubstitutionErase.reset
noncomputable def atomMachine:=RecoveryFocus.machine atomSlots SubstitutionErase.reset
noncomputable def copyMachine:=RecoveryFocus.machine copySlots (SubstitutionCopy.machine true)
noncomputable def productClearMachine:=RecoveryFocus.machine productClearSlots SubstitutionErase.reset

theorem cache_run (C : ℕ) (cs : List CloseoutRowsRawPairSeek.Pair) (i : ℕ) (hi : i<cs.length)
    (pre tail acc : List Bool) (hc : SubstitutionCache.capacity cs ≤ C) :
    Step cacheMachine (SubstitutionCache.budget cs i hi) (heads pre.length)
      (data C (pre++ExtIncidence.block i++tail) (CloseoutRowsRawPairSeek.cacheWord cs) [] acc [])
      (heads (pre.length+(ExtIncidence.block i).length))
      (data C (pre++ExtIncidence.block i++tail) (CloseoutRowsRawPairSeek.cacheWord cs)
        (ExtIncidence.stream (cs[i].1++cs[i].2)) acc []) := by
  refine SubstitutionDock.run _ _ (by decide) _ _ _ _ _ _ _ _ (SubstitutionCache.run C cs i hi pre tail hc)
    ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first
  | (intro j;fin_cases j <;>rfl)
  | (intro j hj;fin_cases j <;> first | rfl | exact False.elim (hj 0 rfl) | exact False.elim (hj 2 rfl))

theorem product_run (C R pos : ℕ) (source cache : List Bool) (acc atom : List (List ℕ))
    (hR : R ≤ C) (hl : ∀ l∈acc,(l.flatMap ExtIncidence.block).length+1 ≤ R)
    (hc : ∀ l∈acc,CloseoutRowsRawProductRow.budget l atom ≤ R)
    (hb : CloseoutRowsRawProductLoop.budget R acc.length ≤ C) :
    Step productMachine (SubstitutionProduct.budget R acc.length) (heads pos)
      (data C source cache (ExtIncidence.stream atom) (ExtIncidence.stream acc) []) (heads pos)
      (data C source cache (ExtIncidence.stream atom) (ExtIncidence.stream acc)
        (ExtIncidence.stream (CloseoutRowsRawProductLoop.product acc atom))) := by
  refine SubstitutionDock.run _ _ (by decide) _ _ _ _ _ _ _ _ (SubstitutionProduct.run C R acc atom hR hl hc hb)
    ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first
  | (intro j;fin_cases j <;>rfl)
  | (intro j hj;fin_cases j <;> first | rfl | exact False.elim (hj 2 rfl))

theorem acc_run (C pos : ℕ) (source cache atom product : List Bool) (acc : List (List ℕ))
    (hc : (ExtIncidence.stream acc).length ≤ C) :
    Step accMachine (2*(ExtIncidence.stream acc).length+2) (heads pos)
      (data C source cache atom (ExtIncidence.stream acc) product) (heads pos)
      (data C source cache atom [] product) := by
  refine SubstitutionDock.run _ _ (by decide) _ _ _ _ _ _ _ _ (SubstitutionErase.reset_run C acc hc)
    ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first
  | (intro j;fin_cases j <;>rfl)
  | (intro j hj;fin_cases j <;> first | rfl | exact False.elim (hj 0 rfl))

theorem atom_run (C pos : ℕ) (source cache acc product : List Bool) (atom : List (List ℕ))
    (hc : (ExtIncidence.stream atom).length ≤ C) :
    Step atomMachine (2*(ExtIncidence.stream atom).length+2) (heads pos)
      (data C source cache (ExtIncidence.stream atom) acc product) (heads pos)
      (data C source cache [] acc product) := by
  refine SubstitutionDock.run _ _ (by decide) _ _ _ _ _ _ _ _ (SubstitutionErase.reset_run C atom hc)
    ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first
  | (intro j;fin_cases j <;>rfl)
  | (intro j hj;fin_cases j <;> first | rfl | exact False.elim (hj 0 rfl))

theorem copy_run (C pos : ℕ) (source cache : List Bool) (product : List (List ℕ))
    (hb : CloseoutRowsRawPolynomialAdd.budget product [] ≤ C) :
    Step copyMachine (SubstitutionCopy.budget product) (heads pos)
      (data C source cache [] [] (ExtIncidence.stream product)) (heads pos)
      (data C source cache [] (ExtIncidence.stream product) (ExtIncidence.stream product)) := by
  refine SubstitutionDock.run _ _ (by decide) _ _ _ _ _ _ _ _ (SubstitutionCopy.run true C product [] (by intro _;rfl) hb)
    ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first
  | (intro j;fin_cases j <;>rfl)
  | (intro j hj;fin_cases j <;> first | rfl | exact False.elim (hj 2 rfl))

theorem product_clear_run (C pos : ℕ) (source cache atom acc : List Bool) (product : List (List ℕ))
    (hc : (ExtIncidence.stream product).length ≤ C) :
    Step productClearMachine (2*(ExtIncidence.stream product).length+2) (heads pos)
      (data C source cache atom acc (ExtIncidence.stream product)) (heads pos)
      (data C source cache atom acc []) := by
  refine SubstitutionDock.run _ _ (by decide) _ _ _ _ _ _ _ _ (SubstitutionErase.reset_run C product hc)
    ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first
  | (intro j;fin_cases j <;>rfl)
  | (intro j hj;fin_cases j <;> first | rfl | exact False.elim (hj 0 rfl))

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionFactor
