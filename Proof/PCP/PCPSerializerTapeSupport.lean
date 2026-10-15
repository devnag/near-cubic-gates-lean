import Proof.PCP.PCPSerializerCountReady

/-! Per-tape support bounds avoid charging the global source prefix or
suffix to local serializer workspace. Only the selected tape's initial
head/length enter its support estimate. -/
namespace NearCubicWires.RepairOrdinary.PCPSerializerReuse
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem head_step {t s : ℕ} (p : Machine t s) (c d : Configuration t s)
    (i : Fin t) (position : ℕ) (hh : c.heads i ≤ position) (hs : step p c=some d) :
    d.heads i ≤ position+1 := by
  unfold step at hs
  obtain ⟨a,_,he⟩ := Option.map_eq_some_iff.mp hs
  subst d
  change (a.move i).apply (c.heads i) ≤ position+1
  cases hm : a.move i <;> simp only [HeadMove.apply] <;> omega

theorem tape_step {t s : ℕ} (p : Machine t s) (c d : Configuration t s)
    (i : Fin t) (cap position : ℕ) (hh : c.heads i ≤ position)
    (ht : (c.tapes i).length ≤ max cap (position+1)) (hs : step p c=some d) :
    (d.tapes i).length ≤ max cap (position+1+1) := by
  unfold step at hs
  obtain ⟨a,_,he⟩ := Option.map_eq_some_iff.mp hs
  subst d
  simp only [applyAction]
  cases ha : a.write i
  · dsimp only; omega
  · simp only [RecoveryTapeSupport.write_length]
    omega

theorem tape_support {t s : ℕ} (p : Machine t s) (fuel : ℕ)
    (c : Configuration t s) (r : ExecutionReceipt t s) (hr : runFrom p fuel c=some r)
    (i : Fin t) (cap position : ℕ) (hh : c.heads i ≤ position)
    (ht : (c.tapes i).length ≤ max cap (position+1)) :
    (r.final.tapes i).length ≤ max cap (position+r.steps+1) := by
  induction fuel generalizing c r position with
  | zero =>
    simp only [runFrom] at hr
    split at hr
    · cases hr; simpa using ht
    · contradiction
  | succ fuel ih =>
    simp only [runFrom] at hr
    split at hr
    · cases hr; simpa using ht
    · cases hs : step p c with
      | none => simp [hs] at hr
      | some d =>
        cases htail : runFrom p fuel d with
        | none => simp [hs,htail] at hr
        | some tail =>
          simp only [hs,htail,Option.some.injEq] at hr
          subst r
          have h := ih d tail htail (position+1) (head_step p c d i position hh hs)
            (tape_step p c d i cap position hh ht hs)
          simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

end NearCubicWires.RepairOrdinary.PCPSerializerReuse
