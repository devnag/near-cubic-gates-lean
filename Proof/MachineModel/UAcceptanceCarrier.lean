import Proof.Foundations.OrdinaryComposition

/-! The final result bit is converted into an accepting or rejecting halted
control by one physical read. Sequential composition pays its own return step.
The construction retains every tape and head of the source endpoint. -/
namespace NearCubicWires.RepairOrdinary.UAcceptanceCarrier
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def answerState (answer : Bool) : Fin 3 := if answer then 1 else 2

def decision {t : ℕ} (resultSlot : Fin t) : Machine t 3 where
  descriptionBits := 0
  start := 0
  halted := fun state => decide (state.val ≠ 0)
  rule := fun state bits => if state.val = 0 then
    some ⟨answerState (bits resultSlot), fun _ => none, fun _ => .stay⟩
    else none

def decisionReceipt {t s : ℕ} (resultSlot : Fin t)
    (c : Configuration t s) : ExecutionReceipt t 3 :=
  ⟨⟨answerState (c.scanned resultSlot), c.heads, c.tapes⟩, 1, c.tapeCells⟩

theorem decision_run {t s : ℕ} (resultSlot : Fin t) (c : Configuration t s) :
    runFrom (decision resultSlot) 1 (Composition.restart c (decision resultSlot).start) =
      some (decisionReceipt resultSlot c) := by
  cases h : c.scanned resultSlot <;>
    simp [runFrom, decision, Composition.restart, step, applyAction,
      Configuration.scanned, HeadMove.apply, decisionReceipt, answerState,
      Configuration.tapeCells] at h ⊢
  all_goals simp_all

def machine {t s : ℕ} (p : Machine t s) (resultSlot : Fin t) : Machine t (s + 3) :=
  Composition.machine p (decision resultSlot)

def accepting (s : ℕ) (state : Fin (s + 3)) : Bool :=
  decide (state = (1 : Fin 3).natAdd s)

def receipt {t s : ℕ} (resultSlot : Fin t)
    (r : ExecutionReceipt t s) : ExecutionReceipt t (s + 3) :=
  Composition.joinedReceipt r (decisionReceipt resultSlot r.final)

theorem runFrom_transfer {t s : ℕ} (p : Machine t s) (resultSlot : Fin t)
    (fuel : ℕ) (c : Configuration t s) (r : ExecutionReceipt t s)
    (hr : runFrom p fuel c = some r) :
    runFrom (machine p resultSlot) (fuel + 2) (Composition.leftConfig 3 c) =
      some (receipt resultSlot r) := by
  exact Composition.run_join p (decision resultSlot) fuel 1 c r
    (decisionReceipt resultSlot r.final) hr (decision_run resultSlot r.final)

theorem run_transfer {t s : ℕ} (p : Machine t s) (resultSlot : Fin t)
    (fuel : ℕ) (input : Fin t → List Bool) (r : ExecutionReceipt t s)
    (hr : run p fuel input = some r) :
    run (machine p resultSlot) (fuel + 2) input = some (receipt resultSlot r) :=
  runFrom_transfer p resultSlot fuel _ r hr

theorem receipt_fields {t s : ℕ} (resultSlot : Fin t) (r : ExecutionReceipt t s) :
    (receipt resultSlot r).final.tapes = r.final.tapes ∧
    (receipt resultSlot r).final.heads = r.final.heads ∧
    (receipt resultSlot r).steps = r.steps + 2 ∧
    (receipt resultSlot r).peakTapeCells = max r.peakTapeCells r.final.tapeCells ∧
    accepting s (receipt resultSlot r).final.control = r.final.scanned resultSlot := by
  refine ⟨rfl, rfl, by simp [receipt, Composition.joinedReceipt, decisionReceipt, Nat.add_assoc],
    rfl, ?_⟩
  cases h : r.final.scanned resultSlot <;>
    simp [receipt, Composition.joinedReceipt, Composition.rightConfig,
      decisionReceipt, accepting, answerState, h]

def verifier {t s : ℕ} (p : Machine t s) (ht : 2 ≤ t)
    (resultSlot : Fin t) : Verifier where
  tapeCount := t
  stateCount := s + 3
  twoTapes := ht
  machine := machine p resultSlot
  accepting := accepting s

theorem inputTapes_eq {t s : ℕ} (p : Machine t s) (ht : 2 ≤ t)
    (resultSlot : Fin t) (input witness : List Bool) :
    (verifier p ht resultSlot).inputTapes input witness =
      (fun i : Fin t => if i.val = 0 then frame input
        else if i.val = 1 then frame witness else []) := rfl

theorem verifier_run {t s : ℕ} (p : Machine t s) (ht : 2 ≤ t)
    (resultSlot : Fin t) (fuel : ℕ) (input witness : List Bool)
    (r : ExecutionReceipt t s)
    (hr : run p fuel ((verifier p ht resultSlot).inputTapes input witness) = some r) :
    run (verifier p ht resultSlot).machine (fuel + 2)
      ((verifier p ht resultSlot).inputTapes input witness) = some (receipt resultSlot r) ∧
    (verifier p ht resultSlot).accepting (receipt resultSlot r).final.control =
      r.final.scanned resultSlot :=
  ⟨run_transfer p resultSlot fuel _ r hr, (receipt_fields resultSlot r).2.2.2.2⟩

theorem acceptsAt_transfer {t s : ℕ} (p : Machine t s) (ht : 2 ≤ t)
    (resultSlot : Fin t) (fuel : ℕ) (input witness : List Bool)
    (r : ExecutionReceipt t s)
    (hr : run p fuel ((verifier p ht resultSlot).inputTapes input witness) = some r) :
    (verifier p ht resultSlot).acceptsAt (fuel + 2) input witness ↔
      r.final.scanned resultSlot = true := by
  obtain ⟨hjoined, haccept⟩ := verifier_run p ht resultSlot fuel input witness r hr
  constructor
  · rintro ⟨r', hr', ha⟩
    have heq : r' = receipt resultSlot r := Option.some.inj (hr'.symm.trans hjoined)
    simpa only [heq, haccept] using ha
  · intro ha
    exact ⟨receipt resultSlot r, hjoined, haccept.trans ha⟩

/-- Successful receipts of the deterministic interpreter agree even when
their supplied fuel differs. This also rules out acceptance at another fuel. -/
theorem run_receipt_unique {t s : ℕ} (p : Machine t s) (input : Fin t → List Bool)
    (f g : ℕ) (r u : ExecutionReceipt t s)
    (hr : run p f input = some r) (hu : run p g input = some u) : r = u := by
  have hr' := run_moreFuel p f g input r hr
  have hu' := run_moreFuel p g f input u hu
  rw [Nat.add_comm g f] at hu'
  exact Option.some.inj (hr'.symm.trans hu')

theorem accepts_transfer {t s : ℕ} (p : Machine t s) (ht : 2 ≤ t)
    (resultSlot : Fin t) (fuel : ℕ) (input witness : List Bool)
    (r : ExecutionReceipt t s)
    (hr : run p fuel ((verifier p ht resultSlot).inputTapes input witness) = some r) :
    (verifier p ht resultSlot).accepts input witness ↔ r.final.scanned resultSlot = true := by
  obtain ⟨hjoined, haccept⟩ := verifier_run p ht resultSlot fuel input witness r hr
  constructor
  · rintro ⟨f, r', hr', ha⟩
    have heq := run_receipt_unique (verifier p ht resultSlot).machine
      ((verifier p ht resultSlot).inputTapes input witness) f (fuel + 2)
      r' (receipt resultSlot r) hr' hjoined
    have ha' : (verifier p ht resultSlot).accepting
        (receipt resultSlot r).final.control = true := heq ▸ ha
    exact haccept.symm.trans ha'
  · intro ha
    exact ⟨fuel + 2, (acceptsAt_transfer p ht resultSlot fuel input witness r hr).2 ha⟩

end NearCubicWires.RepairOrdinary.UAcceptanceCarrier
