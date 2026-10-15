import Proof.Amplification.RecoveryFixedUnpair

/-! Ordinary execution bounds its materialized tape support. This supplies a
coarse polynomial erase length for repeated compact-decoder scalar calls. -/
namespace NearCubicWires.RepairOrdinary.RecoveryTapeSupport
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem write_length (bits : List Bool) (position : Nat) (bit : Bool) :
    (writeTapeBit bits position bit).length = max bits.length (position + 1) := by
  induction position generalizing bits with
  | zero => cases bits <;> simp [writeTapeBit]
  | succ position ih =>
    cases bits <;> simp only [writeTapeBit, List.length_cons, List.length_nil, ih]
    all_goals omega

theorem step_support {t s : Nat} (p : Machine t s) (c d : Configuration t s) (cap position : Nat)
    (hh : ∀ i, c.heads i ≤ position)
    (ht : ∀ i, (c.tapes i).length ≤ max cap (position + 1))
    (hs : step p c = some d) :
    ∀ i, (d.tapes i).length ≤ max cap (position + 1 + 1) := by
  unfold step at hs
  obtain ⟨action, _, he⟩ := Option.map_eq_some_iff.mp hs
  subst d
  intro i
  have hhi := hh i
  have hti := ht i
  simp only [applyAction]
  cases ha : action.write i
  · dsimp only
    omega
  · simp only [write_length]
    omega

theorem run_support {t s : Nat} (p : Machine t s) (fuel : Nat)
    (c : Configuration t s) (r : ExecutionReceipt t s)
    (hr : runFrom p fuel c = some r) (cap position : Nat)
    (hh : ∀ i, c.heads i ≤ position)
    (ht : ∀ i, (c.tapes i).length ≤ max cap (position + 1)) :
    ∀ i, (r.final.tapes i).length ≤ max cap (position + r.steps + 1) := by
  induction fuel generalizing c r position with
  | zero =>
    simp only [runFrom] at hr
    split at hr
    · cases hr
      simpa using ht
    · contradiction
  | succ fuel ih =>
    simp only [runFrom] at hr
    split at hr
    · cases hr
      simpa using ht
    · cases hs : step p c with
      | none => simp [hs] at hr
      | some d =>
        cases htail : runFrom p fuel d with
        | none => simp [hs, htail] at hr
        | some tail =>
          simp only [hs, htail, Option.some.injEq] at hr
          subst r
          have h := ih d tail htail (position + 1) (Rewind.head_bound p c d position hh hs)
            (step_support p c d cap position hh ht hs)
          simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

def capacity (bits : List Bool) := 8192 * (bits.length + 1) ^ 2

theorem fixed_unpair_support (bits : List Bool)
    (r : ExecutionReceipt 21 (Fintype.card (RecoveryCalls.Control RecoveryFixedUnpair.sizes)))
    (hr : run RecoveryFixedUnpair.machine (RecoveryFixedUnpair.budget bits)
      (fun i => if i.val = 0 then frame bits else []) = some r) :
    ∀ i, (r.final.tapes i).length ≤ capacity bits := by
  have hi (i : Fin 21) : ((fun i : Fin 21 => if i.val = 0 then frame bits else []) i).length ≤
      max (2 * bits.length + 1) (0 + 1) := by
    dsimp only
    split <;> simp [frame_length]
  have h := run_support RecoveryFixedUnpair.machine _ _ r hr (2 * bits.length + 1) 0
    (by intro i; exact Nat.zero_le _) hi
  obtain ⟨known, hknown, _, _, _, hbound⟩ := RecoveryFixedUnpair.fixed_unpair_run bits
  have heq : r = known := Option.some.inj (hr.symm.trans hknown)
  have hs : r.steps ≤ RecoveryFixedUnpair.budget bits := by rw [heq]; exact hbound
  intro i
  have hlocal := h i
  unfold capacity RecoveryFixedUnpair.budget at *
  simp only [Nat.zero_add] at hlocal
  have hcap : max (2 * bits.length + 1) (r.steps + 1) ≤ 8192 * (bits.length + 1) ^ 2 := by
    apply max_le
    · nlinarith
    · have hp : 0 < (bits.length + 1) ^ 2 := by positivity
      omega
  exact hlocal.trans hcap

end NearCubicWires.RepairOrdinary.RecoveryTapeSupport
