import Proof.CaseAnalysis.RowsOriginalBranches
import Proof.CaseAnalysis.RowsOriginalSource
import Proof.MachineModel.OrdinaryMatrixBucketRootPower

/-! The source parser's backing may be larger than the product bank.
Only the six shared source ports are padded; product clocks stay unchanged. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsOriginalDock
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (j : Fin 22) : Fin 107:=
  if h10 : j.val=10 then 29 else if h11 : j.val=11 then 41 else if h18 : j.val=18 then 30 else if h19 : j.val=19 then 42
  else if h20 : j.val=20 then 85 else if h21 : j.val=21 then 89
  else if hsmall : j.val<10 then ⟨91+j.val,by omega⟩ else ⟨89+j.val,by omega⟩
theorem injective : Function.Injective slots:=by decide
def privateSlot (j : Fin 16) : Fin 22:=⟨if j.val<10 then j.val else j.val+2,by split_ifs <;>omega⟩
def extra (C : ℕ) (cs : List (List (List ℕ))) (j : Fin 16):=
  CloseoutRowsOriginalBranches.input C cs (fun _=>0) (fun _=>false) (privateSlot j)
def heads : Fin 107→ℕ:=Fin.addCases (m:=91) (n:=16) (motive:=fun _=>ℕ) CloseoutRowsOriginalClassify.heads (fun _=>0)
def data (C : ℕ) (cs : List (List (List ℕ))) (A : Fin 91→List Bool) : Fin 107→List Bool:=
  Fin.addCases (m:=91) (n:=16) (motive:=fun _=>List Bool) A (extra C cs)
def caps (P : ℕ) (j : Fin 22):=if j=10 ∨ j=11 ∨ 18≤j.val then P else 0
def sourceSlots : Fin 6→Fin 91:=![29,41,30,42,85,89]
def sourceWords (P : ℕ) (indices : Fin 2→ℕ) (bits : Fin 4→Bool) : Fin 6→List Bool:=
  ![ZeroPadding.pad P (List.replicate (indices 0) true),ZeroPadding.pad P (List.replicate (indices 1) true),
    ZeroPadding.pad P [bits 0],ZeroPadding.pad P [bits 1],ZeroPadding.pad P [bits 2],ZeroPadding.pad P [bits 3]]

theorem run {s fuel : ℕ} (worker : Machine 22 s) (C P : ℕ) (cs : List (List (List ℕ)))
    (indices : Fin 2→ℕ) (bits : Fin 4→Bool) (A : Fin 91→List Bool)
    (H' : Fin 22→ℕ) (A' : Fin 22→List Bool)
    (h : Step worker fuel (fun _=>0) (CloseoutRowsOriginalBranches.input C cs indices bits) H' A')
    (hc : C≤P) (hs : ∀ j,A (sourceSlots j)=sourceWords P indices bits j) :
    Step (RecoveryFocus.machine slots worker) fuel heads (data C cs A)
      (dockH slots heads H') (install slots (data C cs A) (fun j=>ZeroPadding.pad (caps P j) (A' j))) := by
  have padded:=h.pad (caps P)
  refine padded.dock slots injective heads (data C cs A) (by intro j;fin_cases j <;>rfl) ?_
  intro j;fin_cases j
  all_goals first
  | exact (ZeroPadding.pad_zero _).symm
  | exact (hs 0).trans (MatrixBucketRootPower.pad_pad C P _ hc).symm
  | exact (hs 1).trans (MatrixBucketRootPower.pad_pad C P _ hc).symm
  | exact (hs 2).trans (MatrixBucketRootPower.pad_pad C P _ hc).symm
  | exact (hs 3).trans (MatrixBucketRootPower.pad_pad C P _ hc).symm
  | exact (hs 4).trans (MatrixBucketRootPower.pad_pad C P _ hc).symm
  | exact (hs 5).trans (MatrixBucketRootPower.pad_pad C P _ hc).symm

end NearCubicWires.RepairOrdinary.CloseoutRowsOriginalDock
