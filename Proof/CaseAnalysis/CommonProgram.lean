import Proof.CaseAnalysis.CommonProgramLayout

/-! One finite oracle control graph on every input length. Inactive inputs
print false; live inputs run the original full recovery and its selected
output worker. The Case1 edge performs the paid common-query clear. -/
namespace NearCubicWires.RepairSource.CloseoutCommonProgram
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def liveFlag (p : Parameters) : Fin (tapes p):=prefixSlot p
  (CloseoutCommonPrefix.firstSlots (work p) p.refuter p.k
    (CloseoutRetainedRefuter.old p.refuter (CloseoutSchedule.RefuterPrefix.flagPort (work p))))
def recoveryFlag (p : Parameters) : Fin (tapes p):=lift1 p (flagBank p)
def pieces (p : Parameters) : Fin 6→Piece (tapes p):=
  ![focused (prefixProgram p) (prefixSlot p),
    focused (recovery p) (recoverySlot p),
    ordinary (RecoveryFocus.machine (clearSlot p) (CloseoutCommonQueryClear.machine p.Aq p.Bq)),
    focused (one p) (oneSlot p),
    ordinary (RecoveryFocus.machine (twoSlot p) (two p)),
    ordinary (RecoveryFocus.machine (falseSlot p) (HierarchyFixedWord.machine [false]))]
def next (p : Parameters) (j : Fin 6) (_ : Fin (pieces p j).states)
    (read : Fin (tapes p)→Bool) : Option (Fin 6):=
  if j.val=0 then some (if read (liveFlag p) then 1 else 5)
  else if j.val=1 then some (if read (recoveryFlag p) then 4 else 2)
  else if j.val=2 then some 3 else none
def program (p : Parameters):=(ports p).program (graph (pieces p) 0 (next p))
def input (p : Parameters) (bits : List Bool) (i : Fin (tapes p)):=
  if i.val=0 then frame bits else []

theorem ordinary_input (p : Parameters) (bits : List Bool) :
    (program p).base.inputTapes bits=input p bits:=rfl

theorem shared_query (p : Parameters) : (program p).queryTape=lift0 p (query0 p):=rfl

end
end NearCubicWires.RepairSource.CloseoutCommonProgram
