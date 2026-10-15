import Proof.Assembly.SelectedFactorization

/-! The actual selected branch as three phases and its retained tail.
All layout and component definitions are transparent; the equality includes
the dependent state count. Sequential execution retains the consecutive banks. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace SelectedBranchPhases
open NearCubicWires NearCubicWires.P1TopDown
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary RecoveryRootRound
open RepairSource RepairSource.CloseoutFinal RepairSource.VerifierDecoding
open CloseoutRowsOriginalSchedule ControllerSelectedContinuation
noncomputable section

variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
  (k r scratch : Nat)

abbrev tapes := WorkspaceSelectedAdmission.originalTapes sources p k+1+1+
  extra sources p k r scratch

def offset := WorkspaceSelectedEntry.size sources k r p.clauseDegree+
  WorkspaceSelectedAdmission.originalTapes sources p k-2

attribute [local irreducible] WorkspaceSelectedAdmission.originalTapes WorkspaceSelectedEntry.size

theorem space : WorkspaceSelectedEntry.size sources k r p.clauseDegree+1155 ≤
    extra sources p k r scratch := by
  dsimp [extra]
  omega

theorem offset_ge : 301 ≤ offset sources p k r := by
  have ht := WorkspaceSelectedEntryReady.old_size sources p k
  have hP : 302 ≤ WorkspaceSelectedEntry.size sources k r p.clauseDegree := by
    unfold WorkspaceSelectedEntry.size
    omega
  dsimp [offset]
  omega

theorem fresh_lt : offset sources p k r+1154 < bodyTapes sources p k r scratch := by
  have ht := WorkspaceSelectedEntryReady.old_size sources p k
  have hspace := space sources p k r scratch
  dsimp [offset,bodyTapes]
  omega

def body : Fin (bodyTapes sources p k r scratch) → Fin (tapes sources p k r scratch) :=
  ControllerSelectedLayout.selectedBody sources p k r (extra sources p k r scratch)
    (space sources p k r scratch)

def driver : Fin (tapes sources p k r scratch) :=
  WorkspaceSelectedEntryReady.driver sources p k r (extra sources p k r scratch)
    (by have := space sources p k r scratch; omega)

def loops := WorkspaceSelectedEntryRepeat.slots (body sources p k r scratch)
  (driver sources p k r scratch)

theorem body_injective : Function.Injective (body sources p k r scratch) :=
  ControllerSelectedLayout.body_injective (WorkspaceSelectedEntryReady.old_size sources p k)
    (by unfold WorkspaceSelectedEntry.size; omega) (space sources p k r scratch)

theorem body_ne_driver (i : Fin (bodyTapes sources p k r scratch)) :
    body sources p k r scratch i ≠ driver sources p k r scratch := by
  intro h
  have hv := congrArg Fin.val h
  exact ControllerSelectedLayout.body_ne_driver _ _ (space sources p k r scratch) i
    (by simpa only [body,driver,ControllerSelectedLayout.selectedBody,
      WorkspaceSelectedEntryReady.driver,Nat.add_assoc] using hv)

def cache (mode : Bool) (j : Fin 19) : Fin (bodyTapes sources p k r scratch) :=
  let c := WorkspaceSelectedEntryReady.cache sources p k mode j
  let P := WorkspaceSelectedEntry.size sources k r p.clauseDegree
  ⟨if c.val<2 then c.val else P+c.val-2, by
    have hc := c.isLt
    have ht := WorkspaceSelectedEntryReady.old_size sources p k
    have hspace := space sources p k r scratch
    change c.val<WorkspaceSelectedAdmission.originalTapes sources p k at hc
    dsimp [bodyTapes]
    split_ifs <;> omega⟩

def phaseEntry (mode : Bool) (ph : Phase) :
    Σ states, Machine (bodyTapes sources p k r scratch) states :=
  match ph with
  | .penalty => ⟨_,CloseoutFinalC10FirstPhaseEntry.machine
      (offset sources p k r) (bodyTapes sources p k r scratch)
      (offset_ge sources p k r) (by have := fresh_lt sources p k r scratch; omega)⟩
  | .moment | .clause => ⟨_,RecoveryFocus.machine (cache sources p k r scratch mode)
      (RecoveryFocus.machine (![14,17,18] : Fin 3 → Fin 19)
        (RecoveryScratchErase.resetMachine 1))⟩

def clause
    (site : Bool → Phase → Σ states, Machine (bodyTapes sources p k r scratch) states)
    (mode : Bool) (ph : Phase) :
    Σ states, Machine (bodyTapes sources p k r scratch) states := by
  let B := bodyTapes sources p k r scratch
  let slots := cache sources p k r scratch mode
  let right := DecompositionCountPosition.move (fun i : Fin B =>
    if i=slots 13 ∨ i=slots 14 then .right else .stay)
  let left := DecompositionCountPosition.move (fun i : Fin B =>
    if i=slots 13 ∨ i=slots 14 then .left else .stay)
  let query := RecoveryFocus.machine slots PCPPQueryClauseReuse.machine
  let advance := RecoveryFocus.machine slots CloseoutFinalC10RequestAtCursor.advance
  let terminalSlots : Fin 4 → Fin B :=
    ![slots 14,⟨offset sources p k r+53,by have := fresh_lt sources p k r scratch; omega⟩,
      slots 1,slots 2]
  let test := RecoveryFocus.machine terminalSlots CloseoutRowsGateArityCheck.machine
  let clear := C10LengthGate.branch (slots 2) (slots 1) (CloseoutRowsOriginalSwitch.stop B)
  let live := Composition.machine right
    (Composition.machine query (Composition.machine left
      (Composition.machine (site mode ph).2
        (Composition.machine right (Composition.machine advance left)))))
  exact ⟨_,Composition.machine test (CloseoutRowsOriginalSwitch.machine clear live (slots 1))⟩

def fold (ph : Phase) : Σ states, Machine (bodyTapes sources p k r scratch) states :=
  ⟨_,CloseoutFinalC10RetainedPhaseFold.machine (offset sources p k r)
    (bodyTapes sources p k r scratch) (offset_ge sources p k r)
    (fresh_lt sources p k r scratch) ph⟩

def phase
    (site : Bool → Phase → Σ states, Machine (bodyTapes sources p k r scratch) states)
    (mode : Bool) (ph : Phase) : Σ states, Machine (tapes sources p k r scratch) states :=
  ⟨_,Composition.machine
    (RecoveryFocus.machine (body sources p k r scratch) (phaseEntry sources p k r scratch mode ph).2)
    (Composition.machine
      (RecoveryFocus.machine (loops sources p k r scratch)
        (RepeatMachine.machine (clause sources p k r scratch site mode ph).2 (fun _ _=>true)))
      (RecoveryFocus.machine (body sources p k r scratch) (fold sources p k r scratch ph).2))⟩

def tail : Σ states, Machine (tapes sources p k r scratch) states :=
  ⟨_,RecoveryFocus.machine (body sources p k r scratch)
    (RecoveryFocus.machine (CloseoutFinalC10RetainedPhaseFold.tailSlots
      (offset sources p k r) (bodyTapes sources p k r scratch)
      (offset_ge sources p k r) (fresh_lt sources p k r scratch))
      (C10TailComposeUniform.tailMachine sources))⟩

theorem tail_eq : tail sources p k r scratch =
    ⟨_,RecoveryFocus.machine (body sources p k r scratch)
      (RecoveryFocus.machine (CloseoutFinalC10RetainedPhaseFold.tailSlots
        (offset sources p k r) (bodyTapes sources p k r scratch)
        (offset_ge sources p k r) (fresh_lt sources p k r scratch))
        (C10TailComposeUniform.tailMachine sources))⟩ := rfl

theorem branch_eq
    (site : Bool → Phase → Σ states, Machine (bodyTapes sources p k r scratch) states)
    (mode : Bool) :
    SelectedEntryFactorization.branch sources p k r scratch site mode =
      ⟨_,Composition.machine (phase sources p k r scratch site mode .penalty).2
        (Composition.machine (phase sources p k r scratch site mode .moment).2
          (Composition.machine (phase sources p k r scratch site mode .clause).2
            (tail sources p k r scratch).2))⟩ := by
  rfl

theorem branch_run
    (site : Bool → Phase → Σ states, Machine (bodyTapes sources p k r scratch) states)
    (mode : Bool) (fuel : Phase → Nat) (tf : Nat)
    (H0 H1 H2 H3 H4 : Fin (tapes sources p k r scratch) → Nat)
    (A0 A1 A2 A3 A4 : Fin (tapes sources p k r scratch) → List Bool)
    (hp : Step (phase sources p k r scratch site mode .penalty).2
      (fuel .penalty) H0 A0 H1 A1)
    (hm : Step (phase sources p k r scratch site mode .moment).2
      (fuel .moment) H1 A1 H2 A2)
    (hc : Step (phase sources p k r scratch site mode .clause).2
      (fuel .clause) H2 A2 H3 A3)
    (ht : Step (tail sources p k r scratch).2 tf H3 A3 H4 A4) :
    Step (SelectedEntryFactorization.branch sources p k r scratch site mode).2
      (fuel .penalty+1+(fuel .moment+1+(fuel .clause+1+tf))) H0 A0 H4 A4 := by
  exact hp.seq (hm.seq (hc.seq ht))

/-- Exact frozen diagnostic, with transparent phase and tail witnesses. -/
theorem factorization :
open NearCubicWires NearCubicWires.P1TopDown NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.SourceInterfaces in
∀ (sources : EightSources) (gamma : Real) (p : Parameters sources gamma)
 (k r scratch : Nat)
 (site : Bool → CloseoutRowsOriginalSchedule.Phase → Σ states,
   Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states) (mode : Bool),
 let tapes := WorkspaceSelectedAdmission.originalTapes sources p k+1+1+
   ControllerSelectedContinuation.extra sources p k r scratch
 ∃ (states : CloseoutRowsOriginalSchedule.Phase → Nat)
   (phase : (ph : CloseoutRowsOriginalSchedule.Phase) → Machine tapes (states ph))
   (ts : Nat) (tail : Machine tapes ts),
 SelectedEntryFactorization.branch sources p k r scratch site mode =
   ⟨_, Composition.machine (phase .penalty)
     (Composition.machine (phase .moment) (Composition.machine (phase .clause) tail))⟩ ∧
 ∀ (fuel : CloseoutRowsOriginalSchedule.Phase → Nat) (tf : Nat)
   (H0 H1 H2 H3 H4 : Fin tapes → Nat) (A0 A1 A2 A3 A4 : Fin tapes → List Bool),
 Step (phase .penalty) (fuel .penalty) H0 A0 H1 A1 →
 Step (phase .moment) (fuel .moment) H1 A1 H2 A2 →
 Step (phase .clause) (fuel .clause) H2 A2 H3 A3 →
 Step tail tf H3 A3 H4 A4 →
 Step (SelectedEntryFactorization.branch sources p k r scratch site mode).2
   (fuel .penalty+1+(fuel .moment+1+(fuel .clause+1+tf))) H0 A0 H4 A4
 := by
  intro sources gamma p k r scratch site mode
  refine ⟨(fun ph => (phase sources p k r scratch site mode ph).1),
    (fun ph => (phase sources p k r scratch site mode ph).2),
    (tail sources p k r scratch).1, (tail sources p k r scratch).2,
    branch_eq sources p k r scratch site mode, ?_⟩
  exact branch_run sources p k r scratch site mode

end
end SelectedBranchPhases
