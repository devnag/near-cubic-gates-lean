import Proof.CaseAnalysis.RecoverySelectorPostPorts

/-! The checked selector body returns the exact reusable bank for its next
value. The cleared inner stack is bounded by the allocated recovery capacity. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorLoop
open LocalBitMultitape SourceInterfaces RepairRepresentation RecoveryRootRound
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedNative
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

local macro "selector_done_heads" : tactic =>
  `(tactic| (
    all_goals norm_num only [doneState,post,TapeEmbedding.config,Fin.addCases,ZeroPadding.config]
    all_goals norm_num only [RecoveryBoundedSelectorJoin.completeState,RecoveryFocus.config,join_pick,
      TapeEmbedding.config,Fin.addCases,RecoveryBoundedSelectorReference.heads]
    all_goals norm_num only [RecoveryBoundedSelectorReset.completeState,TapeEmbedding.config,Fin.addCases,
      RecoveryBoundedSelectorReset.selected,ZeroPadding.config]
    all_goals norm_num only [RecoveryBoundedReferenceAppend.completeState,TapeEmbedding.config,
      Fin.addCases,ZeroPadding.config]
    all_goals norm_num only [RecoveryBoundedNativeGuarded.completeState,RecoveryFocus.config,guard_pick,
      TapeEmbedding.config,Fin.addCases,PCPPNativeClauseBank.entry,PCPPNativeClauseBank.heads]
    all_goals norm_num only [RecoveryBoundedNativeUnaryJoin.completeState,RecoveryFocus.config,fold_pick]
    all_goals try rfl
    all_goals norm_num only [RecoveryBoundedNativeUnaryJoin.finalState,RecoveryBoundedNativeUnaryJoin.foldFinal,
      RecoveryBoundedNativeFoldLoop.configuration,RepairSource.VerifierDecoding.RepeatMachine.cfg,
      controlConfig,TapeEmbedding.config,Fin.addCases,RecoveryBoundedNativeFoldLoop.State.entry,
      RecoveryBoundedNativeFold.entry,RecoveryBoundedNativeFold.heads,PCPPNativeClauseBank.heads]
    all_goals simp only [RecoveryBoundedNativeFoldLoop.stack,RecoveryBoundedNativeUnaryLoop.stackWords,
      List.reverse_nil,List.flatMap_nil,List.nil_append,List.length_nil]
    all_goals rfl
  ))

variable {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit value C D ref : ℕ) (out skipped tail stack : List Bool)
    (hblock : start+limit ≤ rowWidth n bound)
local notation "after" => doneState b row start limit value C D ref out skipped tail stack hblock
local notation "fieldIndex" => RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start
local notation "acc" => RecoveryBoundedSelectorJoin.counter b row start limit value hblock
local notation "nextWord" => nextOut b row start limit value ref out hblock
local notation "saved" => RecoveryBoundedSelectorReference.pushed acc stack

private theorem done_port_0 :
    (after).heads 0=0 ∧ (after).tapes 0=[] := by
  constructor
  · selector_done_heads
  · dsimp only [doneState]
    change install restoreSlots _ _ _=_
    rw [install_other restoreSlots _ _ _ (by decide)]
    rw [post_data,join_data,reset_data,reference_data,guard_data,unary_data]
    change ZeroPadding.pad 0 (install RecoveryBoundedSelectorJoin.slots _ _ _)=_
    rw [install_other RecoveryBoundedSelectorJoin.slots _ _ _ (by decide)]
    change ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0
      (install RecoveryBoundedNativeGuarded.slots _ _ (RecoveryBoundedNativeGuarded.slots 0))))=_
    rw [install_slot RecoveryBoundedNativeGuarded.slots RecoveryBoundedNativeGuarded.slots_injective]
    change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 ([]))))=_
    simp only [ZeroPadding.pad_zero]

private theorem done_port_1 :
    (after).heads 1=0 ∧ (after).tapes 1=ZeroPadding.pad C (List.replicate fieldIndex true) := by
  constructor
  · selector_done_heads
  · dsimp only [doneState]
    change install restoreSlots _ _ (restoreSlots 0)=_
    rw [install_slot restoreSlots (by decide)]
    rfl

private theorem done_port_2 :
    (after).heads 2=0 ∧ (after).tapes 2=List.replicate C false := by
  constructor
  · selector_done_heads
  · dsimp only [doneState]
    change install restoreSlots _ _ _=_
    rw [install_other restoreSlots _ _ _ (by decide)]
    rw [post_data,join_data,reset_data,reference_data,guard_data,unary_data]
    change ZeroPadding.pad 0 (install RecoveryBoundedSelectorJoin.slots _ _ _)=_
    rw [install_other RecoveryBoundedSelectorJoin.slots _ _ _ (by decide)]
    change ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0
      (install RecoveryBoundedNativeGuarded.slots _ _ (RecoveryBoundedNativeGuarded.slots 2))))=_
    rw [install_slot RecoveryBoundedNativeGuarded.slots RecoveryBoundedNativeGuarded.slots_injective]
    change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate C false))))=_
    simp only [ZeroPadding.pad_zero]

private theorem done_port_3 :
    (after).heads 3=0 ∧ (after).tapes 3=List.replicate C false := by
  constructor
  · selector_done_heads
  · dsimp only [doneState]
    change install restoreSlots _ _ _=_
    rw [install_other restoreSlots _ _ _ (by decide)]
    rw [post_data,join_data,reset_data,reference_data,guard_data,unary_data]
    change ZeroPadding.pad 0 (install RecoveryBoundedSelectorJoin.slots _ _ _)=_
    rw [install_other RecoveryBoundedSelectorJoin.slots _ _ _ (by decide)]
    change ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0
      (install RecoveryBoundedNativeGuarded.slots _ _ (RecoveryBoundedNativeGuarded.slots 3))))=_
    rw [install_slot RecoveryBoundedNativeGuarded.slots RecoveryBoundedNativeGuarded.slots_injective]
    change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate C false))))=_
    simp only [ZeroPadding.pad_zero]

private theorem done_port_4 :
    (after).heads 4=0 ∧ (after).tapes 4=List.replicate C false := by
  constructor
  · selector_done_heads
  · dsimp only [doneState]
    change install restoreSlots _ _ _=_
    rw [install_other restoreSlots _ _ _ (by decide)]
    rw [post_data,join_data,reset_data,reference_data,guard_data,unary_data]
    change ZeroPadding.pad 0 (install RecoveryBoundedSelectorJoin.slots _ _ _)=_
    rw [install_other RecoveryBoundedSelectorJoin.slots _ _ _ (by decide)]
    change ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0
      (install RecoveryBoundedNativeGuarded.slots _ _ (RecoveryBoundedNativeGuarded.slots 4))))=_
    rw [install_slot RecoveryBoundedNativeGuarded.slots RecoveryBoundedNativeGuarded.slots_injective]
    change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate C false))))=_
    simp only [ZeroPadding.pad_zero]

private theorem done_port_5 :
    (after).heads 5=0 ∧ (after).tapes 5=List.replicate C false := by
  constructor
  · selector_done_heads
  · dsimp only [doneState]
    change install restoreSlots _ _ _=_
    rw [install_other restoreSlots _ _ _ (by decide)]
    rw [post_data,join_data,reset_data,reference_data,guard_data,unary_data]
    change ZeroPadding.pad 0 (install RecoveryBoundedSelectorJoin.slots _ _ _)=_
    rw [install_other RecoveryBoundedSelectorJoin.slots _ _ _ (by decide)]
    change ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0
      (install RecoveryBoundedNativeGuarded.slots _ _ (RecoveryBoundedNativeGuarded.slots 5))))=_
    rw [install_slot RecoveryBoundedNativeGuarded.slots RecoveryBoundedNativeGuarded.slots_injective]
    change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate C false))))=_
    simp only [ZeroPadding.pad_zero]

private theorem done_port_6 :
    (after).heads 6=0 ∧ (after).tapes 6=List.replicate C false := by
  constructor
  · selector_done_heads
  · dsimp only [doneState]
    change install restoreSlots _ _ _=_
    rw [install_other restoreSlots _ _ _ (by decide)]
    rw [post_data,join_data,reset_data,reference_data,guard_data,unary_data]
    change ZeroPadding.pad 0 (install RecoveryBoundedSelectorJoin.slots _ _ _)=_
    rw [install_other RecoveryBoundedSelectorJoin.slots _ _ _ (by decide)]
    change ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0
      (install RecoveryBoundedNativeGuarded.slots _ _ (RecoveryBoundedNativeGuarded.slots 6))))=_
    rw [install_slot RecoveryBoundedNativeGuarded.slots RecoveryBoundedNativeGuarded.slots_injective]
    change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate C false))))=_
    simp only [ZeroPadding.pad_zero]

private theorem done_port_7 :
    (after).heads 7=0 ∧ (after).tapes 7=List.replicate C false := by
  constructor
  · selector_done_heads
  · dsimp only [doneState]
    change install restoreSlots _ _ _=_
    rw [install_other restoreSlots _ _ _ (by decide)]
    rw [post_data,join_data,reset_data,reference_data,guard_data,unary_data]
    change ZeroPadding.pad 0 (install RecoveryBoundedSelectorJoin.slots _ _ _)=_
    rw [install_other RecoveryBoundedSelectorJoin.slots _ _ _ (by decide)]
    change ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0
      (install RecoveryBoundedNativeGuarded.slots _ _ (RecoveryBoundedNativeGuarded.slots 7))))=_
    rw [install_slot RecoveryBoundedNativeGuarded.slots RecoveryBoundedNativeGuarded.slots_injective]
    change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate C false))))=_
    simp only [ZeroPadding.pad_zero]

private theorem done_port_8 :
    (after).heads 8=0 ∧ (after).tapes 8=List.replicate C false := by
  constructor
  · selector_done_heads
  · dsimp only [doneState]
    change install restoreSlots _ _ _=_
    rw [install_other restoreSlots _ _ _ (by decide)]
    rw [post_data,join_data,reset_data,reference_data,guard_data,unary_data]
    change ZeroPadding.pad 0 (install RecoveryBoundedSelectorJoin.slots _ _ _)=_
    rw [install_other RecoveryBoundedSelectorJoin.slots _ _ _ (by decide)]
    change ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0
      (install RecoveryBoundedNativeGuarded.slots _ _ (RecoveryBoundedNativeGuarded.slots 8))))=_
    rw [install_slot RecoveryBoundedNativeGuarded.slots RecoveryBoundedNativeGuarded.slots_injective]
    change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate C false))))=_
    simp only [ZeroPadding.pad_zero]

private theorem done_port_9 :
    (after).heads 9=0 ∧ (after).tapes 9=List.replicate C false := by
  constructor
  · selector_done_heads
  · dsimp only [doneState]
    change install restoreSlots _ _ _=_
    rw [install_other restoreSlots _ _ _ (by decide)]
    rw [post_data,join_data,reset_data,reference_data,guard_data,unary_data]
    change ZeroPadding.pad 0 (install RecoveryBoundedSelectorJoin.slots _ _ _)=_
    rw [install_other RecoveryBoundedSelectorJoin.slots _ _ _ (by decide)]
    change ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0
      (install RecoveryBoundedNativeGuarded.slots _ _ (RecoveryBoundedNativeGuarded.slots 9))))=_
    rw [install_slot RecoveryBoundedNativeGuarded.slots RecoveryBoundedNativeGuarded.slots_injective]
    change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate C false))))=_
    simp only [ZeroPadding.pad_zero]

private theorem done_port_10 :
    (after).heads 10=0 ∧ (after).tapes 10=List.replicate C false := by
  constructor
  · selector_done_heads
  · dsimp only [doneState]
    change install restoreSlots _ _ _=_
    rw [install_other restoreSlots _ _ _ (by decide)]
    rw [post_data,join_data,reset_data,reference_data,guard_data,unary_data]
    change ZeroPadding.pad 0 (install RecoveryBoundedSelectorJoin.slots _ _ _)=_
    rw [install_other RecoveryBoundedSelectorJoin.slots _ _ _ (by decide)]
    change ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0
      (install RecoveryBoundedNativeGuarded.slots _ _ (RecoveryBoundedNativeGuarded.slots 10))))=_
    rw [install_slot RecoveryBoundedNativeGuarded.slots RecoveryBoundedNativeGuarded.slots_injective]
    change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate C false))))=_
    simp only [ZeroPadding.pad_zero]

private theorem done_port_11 :
    (after).heads 11=0 ∧ (after).tapes 11=List.replicate C false := by
  constructor
  · selector_done_heads
  · dsimp only [doneState]
    change install restoreSlots _ _ _=_
    rw [install_other restoreSlots _ _ _ (by decide)]
    rw [post_data,join_data,reset_data,reference_data,guard_data,unary_data]
    change ZeroPadding.pad 0 (install RecoveryBoundedSelectorJoin.slots _ _ _)=_
    rw [install_other RecoveryBoundedSelectorJoin.slots _ _ _ (by decide)]
    change ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0
      (install RecoveryBoundedNativeGuarded.slots _ _ (RecoveryBoundedNativeGuarded.slots 11))))=_
    rw [install_slot RecoveryBoundedNativeGuarded.slots RecoveryBoundedNativeGuarded.slots_injective]
    change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate C false))))=_
    simp only [ZeroPadding.pad_zero]

private theorem done_port_12 :
    (after).heads 12=0 ∧ (after).tapes 12=List.replicate C false := by
  constructor
  · selector_done_heads
  · dsimp only [doneState]
    change install restoreSlots _ _ _=_
    rw [install_other restoreSlots _ _ _ (by decide)]
    rw [post_data,join_data,reset_data,reference_data,guard_data,unary_data]
    change ZeroPadding.pad 0 (install RecoveryBoundedSelectorJoin.slots _ _ _)=_
    rw [install_other RecoveryBoundedSelectorJoin.slots _ _ _ (by decide)]
    change ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0
      (install RecoveryBoundedNativeGuarded.slots _ _ (RecoveryBoundedNativeGuarded.slots 12))))=_
    rw [install_slot RecoveryBoundedNativeGuarded.slots RecoveryBoundedNativeGuarded.slots_injective]
    change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate C false))))=_
    simp only [ZeroPadding.pad_zero]

private theorem done_port_13 :
    (after).heads 13=0 ∧ (after).tapes 13=List.replicate C false := by
  constructor
  · selector_done_heads
  · dsimp only [doneState]
    change install restoreSlots _ _ _=_
    rw [install_other restoreSlots _ _ _ (by decide)]
    rw [post_data,join_data,reset_data,reference_data,guard_data,unary_data]
    change ZeroPadding.pad 0 (install RecoveryBoundedSelectorJoin.slots _ _ _)=_
    rw [install_other RecoveryBoundedSelectorJoin.slots _ _ _ (by decide)]
    change ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0
      (install RecoveryBoundedNativeGuarded.slots _ _ (RecoveryBoundedNativeGuarded.slots 13))))=_
    rw [install_slot RecoveryBoundedNativeGuarded.slots RecoveryBoundedNativeGuarded.slots_injective]
    change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate C false))))=_
    simp only [ZeroPadding.pad_zero]

private theorem done_port_14 :
    (after).heads 14=0 ∧ (after).tapes 14=List.replicate C false := by
  constructor
  · selector_done_heads
  · dsimp only [doneState]
    change install restoreSlots _ _ _=_
    rw [install_other restoreSlots _ _ _ (by decide)]
    rw [post_data,join_data,reset_data,reference_data,guard_data,unary_data]
    change ZeroPadding.pad 0 (install RecoveryBoundedSelectorJoin.slots _ _ _)=_
    rw [install_other RecoveryBoundedSelectorJoin.slots _ _ _ (by decide)]
    change ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0
      (install RecoveryBoundedNativeGuarded.slots _ _ (RecoveryBoundedNativeGuarded.slots 14))))=_
    rw [install_slot RecoveryBoundedNativeGuarded.slots RecoveryBoundedNativeGuarded.slots_injective]
    change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate C false))))=_
    simp only [ZeroPadding.pad_zero]

private theorem done_port_15 :
    (after).heads 15=0 ∧ (after).tapes 15=List.replicate C false := by
  constructor
  · selector_done_heads
  · dsimp only [doneState]
    change install restoreSlots _ _ _=_
    rw [install_other restoreSlots _ _ _ (by decide)]
    rw [post_data,join_data,reset_data,reference_data,guard_data,unary_data]
    change ZeroPadding.pad 0 (install RecoveryBoundedSelectorJoin.slots _ _ _)=_
    rw [install_other RecoveryBoundedSelectorJoin.slots _ _ _ (by decide)]
    change ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0
      (install RecoveryBoundedNativeGuarded.slots _ _ (RecoveryBoundedNativeGuarded.slots 15))))=_
    rw [install_slot RecoveryBoundedNativeGuarded.slots RecoveryBoundedNativeGuarded.slots_injective]
    change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate C false))))=_
    simp only [ZeroPadding.pad_zero]

private theorem done_port_16 :
    (after).heads 16=0 ∧ (after).tapes 16=List.replicate C false := by
  constructor
  · selector_done_heads
  · dsimp only [doneState]
    change install restoreSlots _ _ _=_
    rw [install_other restoreSlots _ _ _ (by decide)]
    rw [post_data,join_data,reset_data,reference_data,guard_data,unary_data]
    change ZeroPadding.pad 0 (install RecoveryBoundedSelectorJoin.slots _ _ _)=_
    rw [install_other RecoveryBoundedSelectorJoin.slots _ _ _ (by decide)]
    change ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0
      (install RecoveryBoundedNativeGuarded.slots _ _ (RecoveryBoundedNativeGuarded.slots 16))))=_
    rw [install_slot RecoveryBoundedNativeGuarded.slots RecoveryBoundedNativeGuarded.slots_injective]
    change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate C false))))=_
    simp only [ZeroPadding.pad_zero]

private theorem done_port_17 :
    (after).heads 17=0 ∧ (after).tapes 17=List.replicate C false := by
  constructor
  · selector_done_heads
  · dsimp only [doneState]
    change install restoreSlots _ _ _=_
    rw [install_other restoreSlots _ _ _ (by decide)]
    rw [post_data,join_data,reset_data,reference_data,guard_data,unary_data]
    change ZeroPadding.pad 0 (install RecoveryBoundedSelectorJoin.slots _ _ _)=_
    rw [install_other RecoveryBoundedSelectorJoin.slots _ _ _ (by decide)]
    change ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0
      (install RecoveryBoundedNativeGuarded.slots _ _ (RecoveryBoundedNativeGuarded.slots 17))))=_
    rw [install_slot RecoveryBoundedNativeGuarded.slots RecoveryBoundedNativeGuarded.slots_injective]
    change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate C false))))=_
    simp only [ZeroPadding.pad_zero]

private theorem done_port_18 :
    (after).heads 18=0 ∧ (after).tapes 18=List.replicate C false := by
  constructor
  · selector_done_heads
  · dsimp only [doneState]
    change install restoreSlots _ _ _=_
    rw [install_other restoreSlots _ _ _ (by decide)]
    rw [post_data,join_data,reset_data,reference_data,guard_data,unary_data]
    change ZeroPadding.pad 0 (install RecoveryBoundedSelectorJoin.slots _ _ _)=_
    rw [install_other RecoveryBoundedSelectorJoin.slots _ _ _ (by decide)]
    change ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0
      (install RecoveryBoundedNativeGuarded.slots _ _ (RecoveryBoundedNativeGuarded.slots 18))))=_
    rw [install_slot RecoveryBoundedNativeGuarded.slots RecoveryBoundedNativeGuarded.slots_injective]
    change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate C false))))=_
    simp only [ZeroPadding.pad_zero]

private theorem done_port_19 :
    (after).heads 19=0 ∧ (after).tapes 19=List.replicate C false := by
  constructor
  · selector_done_heads
  · dsimp only [doneState]
    change install restoreSlots _ _ _=_
    rw [install_other restoreSlots _ _ _ (by decide)]
    rw [post_data,join_data,reset_data,reference_data,guard_data,unary_data]
    change ZeroPadding.pad 0 (install RecoveryBoundedSelectorJoin.slots _ _ _)=_
    rw [install_other RecoveryBoundedSelectorJoin.slots _ _ _ (by decide)]
    change ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0
      (install RecoveryBoundedNativeGuarded.slots _ _ (RecoveryBoundedNativeGuarded.slots 19))))=_
    rw [install_slot RecoveryBoundedNativeGuarded.slots RecoveryBoundedNativeGuarded.slots_injective]
    change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate C false))))=_
    simp only [ZeroPadding.pad_zero]

private theorem done_port_20 :
    (after).heads 20=(nextWord).length ∧ (after).tapes 20=nextWord := by
  constructor
  · selector_done_heads
  · dsimp only [doneState]
    change install restoreSlots _ _ _=_
    rw [install_other restoreSlots _ _ _ (by decide)]
    rw [post_data,join_data,reset_data,reference_data,guard_data,unary_data]
    change ZeroPadding.pad 0 (install RecoveryBoundedSelectorJoin.slots _ _ _)=_
    rw [install_other RecoveryBoundedSelectorJoin.slots _ _ _ (by decide)]
    change ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0
      (install RecoveryBoundedNativeGuarded.slots _ _ (RecoveryBoundedNativeGuarded.slots 20))))=_
    rw [install_slot RecoveryBoundedNativeGuarded.slots RecoveryBoundedNativeGuarded.slots_injective]
    change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (nextWord))))=_
    simp only [ZeroPadding.pad_zero]

private theorem done_port_21 :
    (after).heads 21=0 ∧ (after).tapes 21=List.replicate C false := by
  constructor
  · selector_done_heads
  · dsimp only [doneState]
    change install restoreSlots _ _ _=_
    rw [install_other restoreSlots _ _ _ (by decide)]
    rw [post_data,join_data,reset_data,reference_data,guard_data,unary_data]
    change ZeroPadding.pad 0 (install RecoveryBoundedSelectorJoin.slots _ _ _)=_
    rw [install_other RecoveryBoundedSelectorJoin.slots _ _ _ (by decide)]
    change ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0
      (install RecoveryBoundedNativeGuarded.slots _ _ (RecoveryBoundedNativeGuarded.slots 21))))=_
    rw [install_slot RecoveryBoundedNativeGuarded.slots RecoveryBoundedNativeGuarded.slots_injective]
    change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate C false))))=_
    simp only [ZeroPadding.pad_zero]

private theorem done_port_22 :
    (after).heads 22=0 ∧ (after).tapes 22=List.replicate C true := by
  constructor
  · selector_done_heads
  · dsimp only [doneState]
    change install restoreSlots _ _ (restoreSlots 6)=_
    rw [install_slot restoreSlots (by decide)]
    rfl

private theorem done_port_23 :
    (after).heads 23=0 ∧ (after).tapes 23=List.replicate (C+1) false := by
  constructor
  · selector_done_heads
  · dsimp only [doneState]
    change install restoreSlots _ _ (restoreSlots 7)=_
    rw [install_slot restoreSlots (by decide)]
    rfl

private theorem done_port_24 :
    (after).heads 24=0 ∧ (after).tapes 24=[] := by
  constructor
  · selector_done_heads
  · dsimp only [doneState]
    change install restoreSlots _ _ _=_
    rw [install_other restoreSlots _ _ _ (by decide)]
    rw [post_data,join_data,reset_data,reference_data,guard_data,unary_data]
    change ZeroPadding.pad 0 (install RecoveryBoundedSelectorJoin.slots _ _ _)=_
    rw [install_other RecoveryBoundedSelectorJoin.slots _ _ _ (by decide)]
    change ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0
      (install RecoveryBoundedNativeGuarded.slots _ _ (RecoveryBoundedNativeGuarded.slots 24))))=_
    rw [install_slot RecoveryBoundedNativeGuarded.slots RecoveryBoundedNativeGuarded.slots_injective]
    change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 ([]))))=_
    simp only [ZeroPadding.pad_zero]

private theorem done_port_25 :
    (after).heads 25=0 ∧ (after).tapes 25=List.replicate (acc+2) true := by
  constructor
  · selector_done_heads
  · dsimp only [doneState]
    change install restoreSlots _ _ _=_
    rw [install_other restoreSlots _ _ _ (by decide)]
    rw [post_data,join_data,reset_data,reference_data,guard_data,unary_data]
    change ZeroPadding.pad 0 (install RecoveryBoundedSelectorJoin.slots _ _ (RecoveryBoundedSelectorJoin.slots 0))=_
    rw [install_slot RecoveryBoundedSelectorJoin.slots (by decide),ZeroPadding.pad_zero]
    rfl

private theorem done_port_26 :
    (after).heads 26=0 ∧ (after).tapes 26=[] := by
  constructor
  · selector_done_heads
  · dsimp only [doneState]
    change install restoreSlots _ _ _=_
    rw [install_other restoreSlots _ _ _ (by decide)]
    rw [post_data,join_data,reset_data,reference_data,guard_data,unary_data]
    change ZeroPadding.pad 0 (install RecoveryBoundedSelectorJoin.slots _ _ _)=_
    rw [install_other RecoveryBoundedSelectorJoin.slots _ _ _ (by decide)]
    change ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0
      (install RecoveryBoundedNativeGuarded.slots _ _ (RecoveryBoundedNativeGuarded.slots 26))))=_
    rw [install_slot RecoveryBoundedNativeGuarded.slots RecoveryBoundedNativeGuarded.slots_injective]
    change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 ([]))))=_
    simp only [ZeroPadding.pad_zero]

private theorem done_port_27 :
    (after).heads 27=0 ∧ (after).tapes 27=[] := by
  constructor
  · selector_done_heads
  · dsimp only [doneState]
    change install restoreSlots _ _ _=_
    rw [install_other restoreSlots _ _ _ (by decide)]
    rw [post_data,join_data,reset_data,reference_data,guard_data,unary_data]
    change ZeroPadding.pad 0 (install RecoveryBoundedSelectorJoin.slots _ _ _)=_
    rw [install_other RecoveryBoundedSelectorJoin.slots _ _ _ (by decide)]
    change ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0
      (install RecoveryBoundedNativeGuarded.slots _ _ (RecoveryBoundedNativeGuarded.slots 27))))=_
    rw [install_slot RecoveryBoundedNativeGuarded.slots RecoveryBoundedNativeGuarded.slots_injective]
    change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 ([]))))=_
    simp only [ZeroPadding.pad_zero]

private theorem done_port_28 :
    (after).heads 28=0 ∧ (after).tapes 28=[] := by
  constructor
  · selector_done_heads
  · dsimp only [doneState]
    change install restoreSlots _ _ _=_
    rw [install_other restoreSlots _ _ _ (by decide)]
    rw [post_data,join_data,reset_data,reference_data,guard_data,unary_data]
    change ZeroPadding.pad 0 (install RecoveryBoundedSelectorJoin.slots _ _ _)=_
    rw [install_other RecoveryBoundedSelectorJoin.slots _ _ _ (by decide)]
    change ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0
      (install RecoveryBoundedNativeGuarded.slots _ _ (RecoveryBoundedNativeGuarded.slots 28))))=_
    rw [install_slot RecoveryBoundedNativeGuarded.slots RecoveryBoundedNativeGuarded.slots_injective]
    change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 ([]))))=_
    simp only [ZeroPadding.pad_zero]

private theorem done_port_29 :
    (after).heads 29=0 ∧ (after).tapes 29=List.replicate C false := by
  constructor
  · selector_done_heads
  · dsimp only [doneState]
    change install restoreSlots _ _ (restoreSlots 3)=_
    rw [install_slot restoreSlots (by decide)]
    rfl

private theorem done_port_30 :
    (after).heads 30=0 ∧ (after).tapes 30=List.replicate C false := by
  constructor
  · selector_done_heads
  · dsimp only [doneState]
    change install restoreSlots _ _ _=_
    rw [install_other restoreSlots _ _ _ (by decide)]
    rw [post_data,join_data,reset_data,reference_data,guard_data,unary_data]
    change ZeroPadding.pad 0 (install RecoveryBoundedSelectorJoin.slots _ _ _)=_
    rw [install_other RecoveryBoundedSelectorJoin.slots _ _ _ (by decide)]
    change ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0
      (install RecoveryBoundedNativeGuarded.slots _ _ (30 : Fin 37))))=_
    rw [install_other RecoveryBoundedNativeGuarded.slots _ _ _ (by decide)]
    rw [show (30 : Fin 37)=(30 : Fin 36).castAdd 1 from rfl,Fin.addCases_left]
    change ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0
      (install RecoveryBoundedNativeUnaryJoin.foldSlots _ _ (RecoveryBoundedNativeUnaryJoin.foldSlots 30))))=_
    rw [install_slot RecoveryBoundedNativeUnaryJoin.foldSlots (by decide)]
    change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad C []))))=_
    simp only [ZeroPadding.pad_zero]
    rfl

private theorem done_port_31 (W : ℕ) (hp : b.nodes.length+3*limit≤W) (hC : 16384*(W+1)^2≤C) :
    (after).heads 31=0 ∧ (after).tapes 31=List.replicate C false := by
  constructor
  · selector_done_heads
  · dsimp only [doneState]
    change install restoreSlots _ _ _=_
    rw [install_other restoreSlots _ _ _ (by decide)]
    rw [post_data,join_data,reset_data,reference_data,guard_data,unary_data]
    change ZeroPadding.pad 0 (install RecoveryBoundedSelectorJoin.slots _ _ _)=_
    rw [install_other RecoveryBoundedSelectorJoin.slots _ _ _ (by decide)]
    change ZeroPadding.pad 0 (ZeroPadding.pad C (ZeroPadding.pad 0
      (install RecoveryBoundedNativeGuarded.slots _ _ (31 : Fin 37))))=_
    rw [install_other RecoveryBoundedNativeGuarded.slots _ _ _ (by decide)]
    rw [show (31 : Fin 37)=(31 : Fin 36).castAdd 1 from rfl,Fin.addCases_left]
    change ZeroPadding.pad 0 (ZeroPadding.pad C (ZeroPadding.pad 0
      (install RecoveryBoundedNativeUnaryJoin.foldSlots _ _ (RecoveryBoundedNativeUnaryJoin.foldSlots 31))))=_
    rw [install_slot RecoveryBoundedNativeUnaryJoin.foldSlots (by decide)]
    let a:=(RecoveryBoundedNativeUnaryLoop.initial (n:=n) row start b.nodes.length out []).iterate value limit
    let z:=(RecoveryBoundedNativeFoldLoop.State.iterate true
      (literalReferences b.nodes.length (unaryItems row start limit value hblock)).reverse
      ⟨a.position,0,0,a.out++RecoveryBoundedNativeUnaryPhase.trueBits⟩).erased
    change ZeroPadding.pad 0 (ZeroPadding.pad C (ZeroPadding.pad 0 (List.replicate z false)))=_
    simp only [ZeroPadding.pad_zero]
    apply pad_erased
    apply unary_erased_bound b.nodes.length _ W C _
    · simpa only [unaryItems,List.length_ofFn] using hp
    · exact hC

private theorem done_port_32 :
    (after).heads 32=0 ∧ (after).tapes 32=List.replicate C false := by
  constructor
  · selector_done_heads
  · dsimp only [doneState]
    change install restoreSlots _ _ (restoreSlots 5)=_
    rw [install_slot restoreSlots (by decide)]
    rfl

private theorem done_port_33 :
    (after).heads 33=0 ∧ (after).tapes 33=List.replicate C false := by
  constructor
  · selector_done_heads
  · dsimp only [doneState]
    change install restoreSlots _ _ _=_
    rw [install_other restoreSlots _ _ _ (by decide)]
    rw [post_data,join_data,reset_data,reference_data,guard_data,unary_data]
    change ZeroPadding.pad 0 (install RecoveryBoundedSelectorJoin.slots _ _ _)=_
    rw [install_other RecoveryBoundedSelectorJoin.slots _ _ _ (by decide)]
    change ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0
      (install RecoveryBoundedNativeGuarded.slots _ _ (33 : Fin 37))))=_
    rw [install_other RecoveryBoundedNativeGuarded.slots _ _ _ (by decide)]
    rw [show (33 : Fin 37)=(33 : Fin 36).castAdd 1 from rfl,Fin.addCases_left]
    change ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0
      (install RecoveryBoundedNativeUnaryJoin.foldSlots _ _ (RecoveryBoundedNativeUnaryJoin.foldSlots 33))))=_
    rw [install_slot RecoveryBoundedNativeUnaryJoin.foldSlots (by decide)]
    change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate C false))))=_
    simp only [ZeroPadding.pad_zero]

private theorem done_port_34 :
    (after).heads 34=0 ∧ (after).tapes 34=List.replicate (value+1) true := by
  constructor
  · selector_done_heads
  · dsimp only [doneState]
    change install restoreSlots _ _ (restoreSlots 4)=_
    rw [install_slot restoreSlots (by decide)]
    rfl

private theorem done_port_35 :
    (after).heads 35=1 ∧ (after).tapes 35=RepairSource.VerifierDecoding.CompareMachine.word limit := by
  constructor
  · selector_done_heads
  · dsimp only [doneState]
    change install restoreSlots _ _ _=_
    rw [install_other restoreSlots _ _ _ (by decide)]
    rw [post_data,join_data,reset_data,reference_data,guard_data,unary_data]
    change ZeroPadding.pad 0 (install RecoveryBoundedSelectorJoin.slots _ _ _)=_
    rw [install_other RecoveryBoundedSelectorJoin.slots _ _ _ (by decide)]
    change ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0
      (install RecoveryBoundedNativeGuarded.slots _ _ (35 : Fin 37))))=_
    rw [install_other RecoveryBoundedNativeGuarded.slots _ _ _ (by decide)]
    rw [show (35 : Fin 37)=(35 : Fin 36).castAdd 1 from rfl,Fin.addCases_left]
    change ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0
      (install RecoveryBoundedNativeUnaryJoin.foldSlots _ _ (RecoveryBoundedNativeUnaryJoin.foldSlots 34))))=_
    rw [install_slot RecoveryBoundedNativeUnaryJoin.foldSlots (by decide)]
    change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (RepairSource.VerifierDecoding.CompareMachine.word (literalReferences b.nodes.length (unaryItems row start limit value hblock)).length))))=_
    simp only [ZeroPadding.pad_zero,RecoveryBoundedNative.references_length,unaryItems,List.length_ofFn]

private theorem done_port_36 :
    (after).heads 36=0 ∧ (after).tapes 36=List.replicate C false := by
  constructor
  · selector_done_heads
  · dsimp only [doneState]
    change install restoreSlots _ _ (restoreSlots 2)=_
    rw [install_slot restoreSlots (by decide)]
    rfl

private theorem done_port_37 :
    (after).heads 37=skipped.length+2*ref+1 ∧ (after).tapes 37=skipped++frame (List.replicate ref true)++tail := by
  constructor
  · selector_done_heads
  · dsimp only [doneState]
    change install restoreSlots _ _ _=_
    rw [install_other restoreSlots _ _ _ (by decide)]
    rw [post_data,join_data,reset_data,reference_data,guard_data,unary_data]
    change ZeroPadding.pad 0 (install RecoveryBoundedSelectorJoin.slots _ _ _)=_
    rw [install_other RecoveryBoundedSelectorJoin.slots _ _ _ (by decide)]
    change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (skipped++frame (List.replicate ref true)++tail)))=_
    simp only [ZeroPadding.pad_zero]

private theorem done_port_38 :
    (after).heads 38=0 ∧ (after).tapes 38=List.replicate C false := by
  constructor
  · selector_done_heads
  · dsimp only [doneState]
    change install restoreSlots _ _ _=_
    rw [install_other restoreSlots _ _ _ (by decide)]
    rw [post_data,join_data,reset_data,reference_data,guard_data,unary_data]
    change ZeroPadding.pad 0 (install RecoveryBoundedSelectorJoin.slots _ _ _)=_
    rw [install_other RecoveryBoundedSelectorJoin.slots _ _ _ (by decide)]
    change (ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate C false)))=_
    simp only [ZeroPadding.pad_zero]

private theorem done_port_39 :
    (after).heads 39=0 ∧ (after).tapes 39=List.replicate D false := by
  constructor
  · selector_done_heads
  · dsimp only [doneState]
    change install restoreSlots _ _ _=_
    rw [install_other restoreSlots _ _ _ (by decide)]
    rw [post_data,join_data,reset_data,reference_data,guard_data,unary_data]
    change ZeroPadding.pad 0 (install RecoveryBoundedSelectorJoin.slots _ _ _)=_
    rw [install_other RecoveryBoundedSelectorJoin.slots _ _ _ (by decide)]
    change (ZeroPadding.pad 0 (List.replicate D false))=_
    simp only [ZeroPadding.pad_zero]

private theorem done_port_40 :
    (after).heads 40=(saved).length ∧ (after).tapes 40=saved := by
  constructor
  · selector_done_heads
  · dsimp only [doneState]
    change install restoreSlots _ _ _=_
    rw [install_other restoreSlots _ _ _ (by decide)]
    rw [post_data,join_data,reset_data,reference_data,guard_data,unary_data]
    change ZeroPadding.pad 0 (install RecoveryBoundedSelectorJoin.slots _ _ (RecoveryBoundedSelectorJoin.slots 1))=_
    rw [install_slot RecoveryBoundedSelectorJoin.slots (by decide),ZeroPadding.pad_zero]
    rfl

private theorem done_port_41 :
    (after).heads 41=0 ∧ (after).tapes 41=List.replicate fieldIndex true := by
  constructor
  · selector_done_heads
  · dsimp only [doneState]
    change install restoreSlots _ _ (restoreSlots 1)=_
    rw [install_slot restoreSlots (by decide)]
    rfl

theorem done_heads (W : ℕ) (hp : b.nodes.length+3*limit≤W) (hC : 16384*(W+1)^2≤C) :
    (after).heads=stateHeads nextWord saved (skipped.length+2*ref+1) := by
  funext i
  fin_cases i
  · exact (done_port_0 b row start limit value C D ref out skipped tail stack hblock).1
  · exact (done_port_1 b row start limit value C D ref out skipped tail stack hblock).1
  · exact (done_port_2 b row start limit value C D ref out skipped tail stack hblock).1
  · exact (done_port_3 b row start limit value C D ref out skipped tail stack hblock).1
  · exact (done_port_4 b row start limit value C D ref out skipped tail stack hblock).1
  · exact (done_port_5 b row start limit value C D ref out skipped tail stack hblock).1
  · exact (done_port_6 b row start limit value C D ref out skipped tail stack hblock).1
  · exact (done_port_7 b row start limit value C D ref out skipped tail stack hblock).1
  · exact (done_port_8 b row start limit value C D ref out skipped tail stack hblock).1
  · exact (done_port_9 b row start limit value C D ref out skipped tail stack hblock).1
  · exact (done_port_10 b row start limit value C D ref out skipped tail stack hblock).1
  · exact (done_port_11 b row start limit value C D ref out skipped tail stack hblock).1
  · exact (done_port_12 b row start limit value C D ref out skipped tail stack hblock).1
  · exact (done_port_13 b row start limit value C D ref out skipped tail stack hblock).1
  · exact (done_port_14 b row start limit value C D ref out skipped tail stack hblock).1
  · exact (done_port_15 b row start limit value C D ref out skipped tail stack hblock).1
  · exact (done_port_16 b row start limit value C D ref out skipped tail stack hblock).1
  · exact (done_port_17 b row start limit value C D ref out skipped tail stack hblock).1
  · exact (done_port_18 b row start limit value C D ref out skipped tail stack hblock).1
  · exact (done_port_19 b row start limit value C D ref out skipped tail stack hblock).1
  · exact (done_port_20 b row start limit value C D ref out skipped tail stack hblock).1
  · exact (done_port_21 b row start limit value C D ref out skipped tail stack hblock).1
  · exact (done_port_22 b row start limit value C D ref out skipped tail stack hblock).1
  · exact (done_port_23 b row start limit value C D ref out skipped tail stack hblock).1
  · exact (done_port_24 b row start limit value C D ref out skipped tail stack hblock).1
  · exact (done_port_25 b row start limit value C D ref out skipped tail stack hblock).1
  · exact (done_port_26 b row start limit value C D ref out skipped tail stack hblock).1
  · exact (done_port_27 b row start limit value C D ref out skipped tail stack hblock).1
  · exact (done_port_28 b row start limit value C D ref out skipped tail stack hblock).1
  · exact (done_port_29 b row start limit value C D ref out skipped tail stack hblock).1
  · exact (done_port_30 b row start limit value C D ref out skipped tail stack hblock).1
  · exact (done_port_31 b row start limit value C D ref out skipped tail stack hblock
      W hp hC).1
  · exact (done_port_32 b row start limit value C D ref out skipped tail stack hblock).1
  · exact (done_port_33 b row start limit value C D ref out skipped tail stack hblock).1
  · exact (done_port_34 b row start limit value C D ref out skipped tail stack hblock).1
  · exact (done_port_35 b row start limit value C D ref out skipped tail stack hblock).1
  · exact (done_port_36 b row start limit value C D ref out skipped tail stack hblock).1
  · exact (done_port_37 b row start limit value C D ref out skipped tail stack hblock).1
  · exact (done_port_38 b row start limit value C D ref out skipped tail stack hblock).1
  · exact (done_port_39 b row start limit value C D ref out skipped tail stack hblock).1
  · exact (done_port_40 b row start limit value C D ref out skipped tail stack hblock).1
  · exact (done_port_41 b row start limit value C D ref out skipped tail stack hblock).1

theorem done_tapes (W : ℕ) (hp : b.nodes.length+3*limit≤W) (hC : 16384*(W+1)^2≤C) :
    (after).tapes=stateData fieldIndex (acc+2) C D (value+1) limit nextWord
      (skipped++frame (List.replicate ref true)++tail) saved := by
  funext i
  fin_cases i
  · exact (done_port_0 b row start limit value C D ref out skipped tail stack hblock).2
  · exact (done_port_1 b row start limit value C D ref out skipped tail stack hblock).2
  · exact (done_port_2 b row start limit value C D ref out skipped tail stack hblock).2
  · exact (done_port_3 b row start limit value C D ref out skipped tail stack hblock).2
  · exact (done_port_4 b row start limit value C D ref out skipped tail stack hblock).2
  · exact (done_port_5 b row start limit value C D ref out skipped tail stack hblock).2
  · exact (done_port_6 b row start limit value C D ref out skipped tail stack hblock).2
  · exact (done_port_7 b row start limit value C D ref out skipped tail stack hblock).2
  · exact (done_port_8 b row start limit value C D ref out skipped tail stack hblock).2
  · exact (done_port_9 b row start limit value C D ref out skipped tail stack hblock).2
  · exact (done_port_10 b row start limit value C D ref out skipped tail stack hblock).2
  · exact (done_port_11 b row start limit value C D ref out skipped tail stack hblock).2
  · exact (done_port_12 b row start limit value C D ref out skipped tail stack hblock).2
  · exact (done_port_13 b row start limit value C D ref out skipped tail stack hblock).2
  · exact (done_port_14 b row start limit value C D ref out skipped tail stack hblock).2
  · exact (done_port_15 b row start limit value C D ref out skipped tail stack hblock).2
  · exact (done_port_16 b row start limit value C D ref out skipped tail stack hblock).2
  · exact (done_port_17 b row start limit value C D ref out skipped tail stack hblock).2
  · exact (done_port_18 b row start limit value C D ref out skipped tail stack hblock).2
  · exact (done_port_19 b row start limit value C D ref out skipped tail stack hblock).2
  · exact (done_port_20 b row start limit value C D ref out skipped tail stack hblock).2
  · exact (done_port_21 b row start limit value C D ref out skipped tail stack hblock).2
  · exact (done_port_22 b row start limit value C D ref out skipped tail stack hblock).2
  · exact (done_port_23 b row start limit value C D ref out skipped tail stack hblock).2
  · exact (done_port_24 b row start limit value C D ref out skipped tail stack hblock).2
  · exact (done_port_25 b row start limit value C D ref out skipped tail stack hblock).2
  · exact (done_port_26 b row start limit value C D ref out skipped tail stack hblock).2
  · exact (done_port_27 b row start limit value C D ref out skipped tail stack hblock).2
  · exact (done_port_28 b row start limit value C D ref out skipped tail stack hblock).2
  · exact (done_port_29 b row start limit value C D ref out skipped tail stack hblock).2
  · exact (done_port_30 b row start limit value C D ref out skipped tail stack hblock).2
  · exact (done_port_31 b row start limit value C D ref out skipped tail stack hblock W hp hC).2
  · exact (done_port_32 b row start limit value C D ref out skipped tail stack hblock).2
  · exact (done_port_33 b row start limit value C D ref out skipped tail stack hblock).2
  · exact (done_port_34 b row start limit value C D ref out skipped tail stack hblock).2
  · exact (done_port_35 b row start limit value C D ref out skipped tail stack hblock).2
  · exact (done_port_36 b row start limit value C D ref out skipped tail stack hblock).2
  · exact (done_port_37 b row start limit value C D ref out skipped tail stack hblock).2
  · exact (done_port_38 b row start limit value C D ref out skipped tail stack hblock).2
  · exact (done_port_39 b row start limit value C D ref out skipped tail stack hblock).2
  · exact (done_port_40 b row start limit value C D ref out skipped tail stack hblock).2
  · exact (done_port_41 b row start limit value C D ref out skipped tail stack hblock).2

end NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorLoop
