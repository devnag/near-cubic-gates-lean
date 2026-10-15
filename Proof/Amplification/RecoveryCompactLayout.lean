import Proof.Amplification.RecoveryColdMarkerWhole
import Proof.Amplification.RecoveryCompactCopy

/-! Native cold compact-bank tape layout. The clause/valuation portion
reuses the accepted RawSAT padding equality; lookup and row-reader fields
are assembled around exactly those same original valuation bytes. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdCompact
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryColdView
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def baseTapes (bits word table : List Bool) (i : Fin 52) : List Bool :=
  if h:i.val<42 then RecoveryColdSAT.tapes bits word ⟨i.val,by omega⟩ else
  if i.val=48 then frame table else if i.val=49 then CompareMachine.word (width bits) else []
def baseCaps (bits word : List Bool) (i : Fin 52) : Nat :=
  if h:i.val<42 then RecoveryColdSAT.caps bits word ⟨i.val,by omega⟩ else
  if i.val=51 then 2*width bits+1 else if i.val=48 ∨ i.val=49 then 0 else 1
def baseHeads (i : Fin 52) : Nat := if i.val=49 then 1 else 0

theorem base_layout {s : Nat} (bits word table : List Bool) (q : Fin s) :
    ZeroPadding.config (baseCaps bits word) ⟨q,baseHeads,baseTapes bits word table⟩=
      RecoveryRowStructure.cfg (data bits word table) (2*width bits+1) q := by
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> rfl
  · have ht := congrArg Configuration.tapes (RecoveryColdSAT.native_layout bits word q)
    funext i
    fin_cases i
    case «0» => exact congrFun ht 0
    case «1» => exact congrFun ht 1
    case «2» => exact congrFun ht 2
    case «3» => exact congrFun ht 3
    case «4» => exact congrFun ht 4
    case «5» => exact congrFun ht 5
    case «6» => exact congrFun ht 6
    case «7» => exact congrFun ht 7
    case «8» => exact congrFun ht 8
    case «9» => exact congrFun ht 9
    case «10» => exact congrFun ht 10
    case «11» => exact congrFun ht 11
    case «12» => exact congrFun ht 12
    case «13» => exact congrFun ht 13
    case «14» => exact congrFun ht 14
    case «15» => exact congrFun ht 15
    case «16» => exact congrFun ht 16
    case «17» => exact congrFun ht 17
    case «18» => exact congrFun ht 18
    case «19» => exact congrFun ht 19
    case «20» => exact congrFun ht 20
    case «21» => exact congrFun ht 21
    case «22» => exact congrFun ht 22
    case «23» => exact congrFun ht 23
    case «24» => exact congrFun ht 24
    case «25» => exact congrFun ht 25
    case «26» => exact congrFun ht 26
    case «27» => exact congrFun ht 27
    case «28» => exact congrFun ht 28
    case «29» => exact congrFun ht 29
    case «30» => exact congrFun ht 30
    case «31» => exact congrFun ht 31
    case «32» => exact congrFun ht 32
    case «33» => exact congrFun ht 33
    case «34» => exact congrFun ht 34
    case «35» => exact congrFun ht 35
    case «36» => exact congrFun ht 36
    case «37» => exact congrFun ht 37
    case «38» => exact congrFun ht 38
    case «39» => exact congrFun ht 39
    case «40» => exact congrFun ht 40
    case «41» => exact congrFun ht 41
    all_goals
      simp [ZeroPadding.config,baseCaps,baseTapes,ZeroPadding.pad,
        RecoveryRowStructure.cfg,RecoveryRowStream.Data.cfg,
        RecoveryRowStream.Data.left,RecoveryRowStream.Data.right,
        RecoveryRowLeaf.tapes,RecoveryRowLeaf.extra,data,Fin.addCases]
    all_goals first
      | rfl
      | exact congrArg CompareMachine.word (RecoveryColdHeader.zero_length bits).symm

def lookupTapes (bits table : List Bool) (total : Nat) (i : Fin 16) : List Bool :=
  match i.val with
  | 0=>frame table
  | 5=>CompareMachine.word (width bits)
  | 7 | 8=>frame (RecoveryColdHeader.zeroWord bits)
  | 14=>CompareMachine.word total
  | _=>[]
def lookupCaps (bits : List Bool) (i : Fin 16) : Nat :=
  if i.val=6 ∨ i.val=9 ∨ i.val=10 ∨ i.val=11 then 1 else
  if i.val=12 then 2*width bits+1 else if i.val=13 then 4*width bits+3 else
  if i.val=15 then erase bits else 0

theorem lookup_layout (bits table : List Bool) (total : Nat) :
    (fun i=>ZeroPadding.pad (lookupCaps bits i) (lookupTapes bits table total i))=
      RecoveryRowLookupTable.readyTapes (lookup bits table) total (erase bits) := by
  unfold RecoveryRowLookupTable.readyTapes
  rw [RecoveryRowLookupTable.inputTapes_eq]
  funext i
  fin_cases i <;> simp [lookupCaps,lookupTapes,lookup,ZeroPadding.pad,Fin.addCases]

end NearCubicWires.RepairOrdinary.RecoveryColdCompact
