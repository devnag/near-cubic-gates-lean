import Proof.CaseAnalysis.RecoveryGrammarPrototypeReady

/-! One canonical reloaded bank is the seam between successive original
grammar atoms. Only graph, actual count, source, stack and paid drivers survive. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarBank
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def base (node B : ℕ) (out stack packet source : List Bool) (i : Fin 78) : List Bool:=
  if i=20 then out else if i=25 then List.replicate node true
  else if i=70 then source else if i=74 then stack else if i=75 then packet
  else if i=76 then List.replicate B true else if i=77 then List.replicate (B+1) false
  else List.replicate B false
def logicalBase (node B : ℕ) (out stack packet source : List Bool):=
  Function.update (base node B out stack packet source) 77 []
def ready (fields : Fin 78→List Bool) (node B : ℕ) (out stack packet source : List Bool):=
  RecoveryBoundedRowReload.loaded fields B (base node B out stack packet source)

theorem base_work (node B : ℕ) (out stack packet source : List Bool) (j : Fin 70) :
    base node B out stack packet source (RecoveryBoundedRowErase.work j)=List.replicate B false := by
  have h:=RecoveryBoundedRowErase.work_spec j
  have h74:=RecoveryBoundedRowErase.work_high j 74 (by decide)
  have h75:=RecoveryBoundedRowErase.work_high j 75 (by decide)
  have h76:=RecoveryBoundedRowErase.work_high j 76 (by decide)
  have h77:=RecoveryBoundedRowErase.work_high j 77 (by decide)
  simp only [base,if_neg h.2.1,if_neg h.2.2.1,if_neg h.2.2.2,
    if_neg h74,if_neg h75,if_neg h76,if_neg h77]

theorem ready_work (fields : Fin 78→List Bool) (node B : ℕ) (out stack packet source : List Bool)
    (j : Fin 70) :
    ready fields node B out stack packet source (RecoveryBoundedRowErase.work j)=
      if RecoveryBoundedRowErase.work j∈RecoveryBoundedRowReload.ports
        then ZeroPadding.pad B (fields (RecoveryBoundedRowErase.work j)) else List.replicate B false := by
  rw [ready,RecoveryBoundedRowReload.loaded_apply,base_work]

theorem ready_kept (fields : Fin 78→List Bool) (node B : ℕ) (out stack packet source : List Bool)
    (i : Fin 78) (hi : i∉RecoveryBoundedRowReload.ports) :
    ready fields node B out stack packet source i=base node B out stack packet source i := by
  rw [ready,RecoveryBoundedRowReload.loaded_apply,if_neg hi]

theorem after_ready (fields : Fin 78→List Bool) (A : Fin 78→List Bool) (ref B : ℕ)
    (out stack packet source : List Bool)
    (h20 : A 20=out) (h70 : A 70=source) (h73 : A 73=List.replicate B false)
    (h75 : A 75=packet) (h76 : A 76=List.replicate B true) (h77 : A 77=List.replicate (B+1) false) :
    RecoveryBoundedGrammarAfter.output fields A ref B stack=
      ready fields (ref+1) B out (RecoveryBoundedAddress.pushed ref stack) packet source := by
  apply congrArg (RecoveryBoundedRowReload.loaded fields B)
  funext i
  fin_cases i <;>
    simp [RecoveryBoundedRowErase.data,RecoveryBoundedGrammarAfter.advanced,base,
      h20,h70,h73,h75,h76,h77]

theorem logical_padding (node B : ℕ) (out stack packet source : List Bool) :
    RecoveryBoundedGrammarWorker.paddedData B (logicalBase node B out stack packet source)=
      base node B out stack packet source := by
  funext i
  fin_cases i <;>
    simp [RecoveryBoundedGrammarWorker.paddedData,RecoveryBoundedGrammarWorker.capacity,
      logicalBase,base,ZeroPadding.pad]

theorem ready20 (fields : Fin 78→List Bool) (node B : ℕ) (out stack packet source : List Bool) :
    ready fields node B out stack packet source 20=out := by
  rw [ready_kept _ _ _ _ _ _ _ _ (by decide)]
  rfl
theorem ready25 (fields : Fin 78→List Bool) (node B : ℕ) (out stack packet source : List Bool) :
    ready fields node B out stack packet source 25=List.replicate node true := by
  rw [ready_kept _ _ _ _ _ _ _ _ (by decide)]
  rfl
theorem ready74 (fields : Fin 78→List Bool) (node B : ℕ) (out stack packet source : List Bool) :
    ready fields node B out stack packet source 74=stack := by
  rw [ready_kept _ _ _ _ _ _ _ _ (by decide)]
  rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarBank
