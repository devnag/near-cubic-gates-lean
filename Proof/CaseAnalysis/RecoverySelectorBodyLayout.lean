import Proof.CaseAnalysis.RecoverySelectorBankPicks

/-! The physical restoration ports of the original selector body. The
shared field index is retained separately from the consumed local copy. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorLoop
open LocalBitMultitape SourceInterfaces RepairRepresentation
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedNative
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def flagCaps (C : ℕ) (i : Fin 41) : ℕ:=if i=29 then C else 0
def restoreSlots : Fin 8→Fin 42:=![1,41,36,29,34,32,22,23]
def lastFlag {n bound : ℕ} (row : Fin (bound+1)) (start base value limit : ℕ)
    (out : List Bool) :=
  ((RecoveryBoundedNativeUnaryLoop.initial (n:=n) row start base out []).iterate value limit).flag
noncomputable def post {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit value C D ref : ℕ) (out skipped tail stack : List Bool)
    (hblock : start+limit ≤ rowWidth n bound) :=
  TapeEmbedding.config (fun _ : Fin 1=>0)
    (fun _=>List.replicate (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) true)
    (ZeroPadding.config (flagCaps C)
      (RecoveryBoundedSelectorJoin.completeState b row start limit value C D ref out [] skipped tail stack hblock))

local macro "selector_head_ports" : tactic =>
  `(tactic| (
      all_goals norm_num only [restoreSlots,post,TapeEmbedding.config,Fin.addCases,ZeroPadding.config]
      all_goals try rfl
      all_goals norm_num only [RecoveryBoundedSelectorJoin.completeState,RecoveryFocus.config,join_pick,
        TapeEmbedding.config,Fin.addCases,RecoveryBoundedSelectorReference.heads]
      all_goals norm_num only [RecoveryBoundedSelectorReset.completeState,TapeEmbedding.config,Fin.addCases,
        RecoveryBoundedSelectorReset.selected,ZeroPadding.config]
      all_goals try rfl
      all_goals norm_num only [RecoveryBoundedReferenceAppend.completeState,TapeEmbedding.config,
        Fin.addCases,ZeroPadding.config]
      all_goals norm_num only [RecoveryBoundedNativeGuarded.completeState,RecoveryFocus.config,guard_pick,
        TapeEmbedding.config,Fin.addCases,PCPPNativeClauseBank.entry,PCPPNativeClauseBank.heads]
      all_goals norm_num only [RecoveryBoundedNativeUnaryJoin.completeState,RecoveryFocus.config,fold_pick]
      all_goals rfl
  ))

local macro "selector_tape_ports" : tactic =>
  `(tactic| (
      all_goals norm_num only [restoreSlots,post,TapeEmbedding.config,Fin.addCases,ZeroPadding.config,flagCaps,
          RecoveryBoundedSelectorRestore.data,ZeroPadding.pad_zero]
      all_goals try rfl
      all_goals norm_num only [RecoveryBoundedSelectorJoin.completeState,RecoveryFocus.config,join_pick,
        TapeEmbedding.config,Fin.addCases,RecoveryBoundedSelectorReference.data]
      all_goals norm_num only [RecoveryBoundedSelectorReset.completeState,TapeEmbedding.config,Fin.addCases,
        ZeroPadding.config,RecoveryBoundedSelectorReset.caps,ZeroPadding.pad_zero]
      all_goals norm_num only [RecoveryBoundedReferenceAppend.completeState,TapeEmbedding.config,
        Fin.addCases,ZeroPadding.config,RecoveryBoundedReferenceAppend.caps,ZeroPadding.pad_zero]
      all_goals norm_num only [RecoveryBoundedNativeGuarded.completeState,RecoveryFocus.config,guard_pick,
        TapeEmbedding.config,Fin.addCases,PCPPNativeClauseBank.entry,PCPPNativeClauseBank.data,
        RecoveryBoundedNativeFold.values]
      all_goals norm_num only [RecoveryBoundedNativeUnaryJoin.completeState,RecoveryFocus.config,fold_pick]
      all_goals try rfl
      all_goals norm_num only [RecoveryBoundedNativeUnaryJoin.finalState,RecoveryBoundedNativeUnaryJoin.foldFinal,
        RecoveryBoundedNativeFoldLoop.configuration,RepairSource.VerifierDecoding.RepeatMachine.cfg,
        controlConfig,TapeEmbedding.config,Fin.addCases,RecoveryBoundedNativeFoldLoop.State.entry,
        RecoveryBoundedNativeFold.entry,RecoveryBoundedNativeFold.data,RecoveryBoundedNativeFold.oldData,
        ZeroPadding.pad,lastFlag]
      all_goals simp
  ))

variable {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit value C D ref : ℕ) (out skipped tail stack : List Bool)
    (hblock : start+limit ≤ rowWidth n bound)

private theorem restore_head_0 :
    (post b row start limit value C D ref out skipped tail stack hblock).heads (restoreSlots 0)=0 := by
  selector_head_ports

private theorem restore_head_1 :
    (post b row start limit value C D ref out skipped tail stack hblock).heads (restoreSlots 1)=0 := by
  selector_head_ports

private theorem restore_head_2 :
    (post b row start limit value C D ref out skipped tail stack hblock).heads (restoreSlots 2)=0 := by
  selector_head_ports

private theorem restore_head_3 :
    (post b row start limit value C D ref out skipped tail stack hblock).heads (restoreSlots 3)=0 := by
  selector_head_ports

private theorem restore_head_4 :
    (post b row start limit value C D ref out skipped tail stack hblock).heads (restoreSlots 4)=0 := by
  selector_head_ports

private theorem restore_head_5 :
    (post b row start limit value C D ref out skipped tail stack hblock).heads (restoreSlots 5)=0 := by
  selector_head_ports

private theorem restore_head_6 :
    (post b row start limit value C D ref out skipped tail stack hblock).heads (restoreSlots 6)=0 := by
  selector_head_ports

private theorem restore_head_7 :
    (post b row start limit value C D ref out skipped tail stack hblock).heads (restoreSlots 7)=0 := by
  selector_head_ports

private theorem restore_tape_0 :
    (post b row start limit value C D ref out skipped tail stack hblock).tapes (restoreSlots 0)=
      RecoveryBoundedSelectorRestore.data (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start)
        ref value C (lastFlag (n:=n) row start b.nodes.length value limit out) 0 0 := by
  selector_tape_ports

private theorem restore_tape_1 :
    (post b row start limit value C D ref out skipped tail stack hblock).tapes (restoreSlots 1)=
      RecoveryBoundedSelectorRestore.data (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start)
        ref value C (lastFlag (n:=n) row start b.nodes.length value limit out) 0 1 := by
  selector_tape_ports

private theorem restore_tape_2 :
    (post b row start limit value C D ref out skipped tail stack hblock).tapes (restoreSlots 2)=
      RecoveryBoundedSelectorRestore.data (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start)
        ref value C (lastFlag (n:=n) row start b.nodes.length value limit out) 0 2 := by
  selector_tape_ports

private theorem restore_tape_3 :
    (post b row start limit value C D ref out skipped tail stack hblock).tapes (restoreSlots 3)=
      RecoveryBoundedSelectorRestore.data (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start)
        ref value C (lastFlag (n:=n) row start b.nodes.length value limit out) 0 3 := by
  selector_tape_ports

private theorem restore_tape_4 :
    (post b row start limit value C D ref out skipped tail stack hblock).tapes (restoreSlots 4)=
      RecoveryBoundedSelectorRestore.data (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start)
        ref value C (lastFlag (n:=n) row start b.nodes.length value limit out) 0 4 := by
  selector_tape_ports

private theorem restore_tape_5 :
    (post b row start limit value C D ref out skipped tail stack hblock).tapes (restoreSlots 5)=
      RecoveryBoundedSelectorRestore.data (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start)
        ref value C (lastFlag (n:=n) row start b.nodes.length value limit out) 0 5 := by
  selector_tape_ports

private theorem restore_tape_6 :
    (post b row start limit value C D ref out skipped tail stack hblock).tapes (restoreSlots 6)=
      RecoveryBoundedSelectorRestore.data (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start)
        ref value C (lastFlag (n:=n) row start b.nodes.length value limit out) 0 6 := by
  selector_tape_ports

private theorem restore_tape_7 :
    (post b row start limit value C D ref out skipped tail stack hblock).tapes (restoreSlots 7)=
      RecoveryBoundedSelectorRestore.data (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start)
        ref value C (lastFlag (n:=n) row start b.nodes.length value limit out) 0 7 := by
  selector_tape_ports

theorem restore_heads {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit value C D ref : ℕ) (out skipped tail stack : List Bool)
    (hblock : start+limit ≤ rowWidth n bound) :
    ∀ j,(post b row start limit value C D ref out skipped tail stack hblock).heads (restoreSlots j)=0 := by
  intro j
  fin_cases j
  · exact restore_head_0 b row start limit value C D ref out skipped tail stack hblock
  · exact restore_head_1 b row start limit value C D ref out skipped tail stack hblock
  · exact restore_head_2 b row start limit value C D ref out skipped tail stack hblock
  · exact restore_head_3 b row start limit value C D ref out skipped tail stack hblock
  · exact restore_head_4 b row start limit value C D ref out skipped tail stack hblock
  · exact restore_head_5 b row start limit value C D ref out skipped tail stack hblock
  · exact restore_head_6 b row start limit value C D ref out skipped tail stack hblock
  · exact restore_head_7 b row start limit value C D ref out skipped tail stack hblock

theorem restore_tapes {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit value C D ref : ℕ) (out skipped tail stack : List Bool)
    (hblock : start+limit ≤ rowWidth n bound) :
    ∀ j,(post b row start limit value C D ref out skipped tail stack hblock).tapes (restoreSlots j)=
      RecoveryBoundedSelectorRestore.data (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start)
        ref value C (lastFlag (n:=n) row start b.nodes.length value limit out) 0 j := by
  intro j
  fin_cases j
  · exact restore_tape_0 b row start limit value C D ref out skipped tail stack hblock
  · exact restore_tape_1 b row start limit value C D ref out skipped tail stack hblock
  · exact restore_tape_2 b row start limit value C D ref out skipped tail stack hblock
  · exact restore_tape_3 b row start limit value C D ref out skipped tail stack hblock
  · exact restore_tape_4 b row start limit value C D ref out skipped tail stack hblock
  · exact restore_tape_5 b row start limit value C D ref out skipped tail stack hblock
  · exact restore_tape_6 b row start limit value C D ref out skipped tail stack hblock
  · exact restore_tape_7 b row start limit value C D ref out skipped tail stack hblock

end NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorLoop
