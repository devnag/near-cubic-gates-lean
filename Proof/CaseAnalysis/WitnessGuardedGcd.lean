import Proof.CaseAnalysis.WitnessGcdGuard

/-! One actual branch checks both original numeric fields before entering
the existing gcd loop. Rejected fields never execute that loop. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.GcdGuard
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev gcdStates := Fintype.card (RecoveryCalls.Control CompetitorGcd.sizes)
abbrev guardStates := Fintype.card (RecoveryCalls.Control sizes)
def callSizes : Fin 2 → ℕ := ![guardStates, gcdStates]
noncomputable def gcdMachine := TapeEmbedding.machine 2 CompetitorGcd.machine
noncomputable def calls : (j : Fin 2) → Machine 9 (callSizes j)
  | ⟨0,_⟩ => guards
  | ⟨1,_⟩ => gcdMachine
  | ⟨n+2,h⟩ => False.elim (by omega)
def callNext (j : Fin 2) (_ : Fin (callSizes j)) (scanned : Fin 9 → Bool) : Option (Fin 2) :=
  if j.val = 0 ∧ scanned 8 = true then some 1 else none
noncomputable def machine := RecoveryCalls.machine callSizes calls 0 callNext
def budget (w cap : ℕ) := 8*w+16+(2*cap+1)*(32*w+40)

theorem gcd_ready (w a b c : ℕ) (ha : a < 2^w) (hb : b < 2^w) :
    ∃ t aa bb, t ≤ (a+b+1)*(32*w+40) ∧
      ReadyRun CompetitorGcd.machine t (CompetitorGcd.data w a b c false)
        (CompetitorGcd.data w aa bb (Nat.gcd a b) true) := by
  obtain ⟨t, aa, bb, ht, path⟩ := CompetitorGcd.loop w a b c false ha hb
  obtain ⟨r, hr, hf, hs⟩ := path.run (by
    change (RecoveryCalls.machine CompetitorGcd.sizes CompetitorGcd.programs 0 CompetitorGcd.next).halted
      (RecoveryCalls.stopped CompetitorGcd.sizes (fun _ => 0)
        (CompetitorGcd.data w aa bb (Nat.gcd a b) true)).control = true
    simp [RecoveryCalls.machine, RecoveryCalls.stopped])
  exact ⟨t, aa, bb, ht, r, hr,
    by simp [hf, CompetitorGcd.stopped, RecoveryCalls.stopped],
    by intro i; simp [hf, CompetitorGcd.stopped, RecoveryCalls.stopped], hs⟩

theorem guarded_ready (w a b c cap : ℕ) (flag : Bool)
    (ha : a < 2^w) (hb : b < 2^w) (hc : cap < 2^w) :
    ∃ t aa bb, t ≤ budget w cap ∧
      ReadyRun machine t (bank w a b c cap false flag)
        (if a ≤ cap ∧ b ≤ cap then bank w aa bb (Nat.gcd a b) cap true true
          else bank w a b c cap false false) := by
  obtain ⟨t, ht, hguard⟩ := guards_ready w a b c cap flag ha hb hc
  by_cases hcap : a ≤ cap ∧ b ≤ cap
  · rw [decide_eq_true hcap] at hguard
    have first := hguard.call callSizes calls 0 callNext 0 1 (by intro q; rfl)
    obtain ⟨g, aa, bb, hg, hrun⟩ := gcd_ready w a b c ha hb
    have he := hrun.embed (![frame (SignedSortKey.binary w cap), [true]] : Fin 2 → List Bool)
    have last := he.stop callSizes calls 0 callNext 1 (by intro q; rfl)
    have h := first.trans last
    obtain ⟨r, hr, hf, hs⟩ := h.run (by simp [RecoveryCalls.machine, RecoveryCalls.stopped])
    refine ⟨_, aa, bb, ?_, r, hr, ?_, ?_, hs⟩
    · have hm := Nat.mul_le_mul_right (32*w+40) (show a+b+1 ≤ 2*cap+1 by omega)
      unfold budget
      omega
    · rw [if_pos hcap]
      rw [hf]
      rfl
    · intro i; rw [hf]; rfl
  · rw [decide_eq_false hcap] at hguard
    have h := hguard.stop callSizes calls 0 callNext 0 (by intro q; rfl)
    obtain ⟨r, hr, hf, hs⟩ := h.run (by simp [RecoveryCalls.machine, RecoveryCalls.stopped])
    refine ⟨_, a, b, ?_, r, hr, ?_, ?_, hs⟩
    · unfold budget; omega
    · simp only [hcap, if_false]
      rw [hf]
      rfl
    · intro i; rw [hf]; rfl

theorem guarded_run (w a b c cap : ℕ)
    (ha : a < 2^w) (hb : b < 2^w) (hc : cap < 2^w) :
    ∃ r, run machine (budget w cap) (bank w a b c cap false false) = some r ∧
      r.steps ≤ budget w cap ∧ (∀ i, r.final.heads i = 0) ∧
      (readTapeBit (r.final.tapes 8) 0 = true ↔ a ≤ cap ∧ b ≤ cap) ∧
      (a ≤ cap ∧ b ≤ cap →
        r.final.tapes 2 = frame (SignedSortKey.binary w (Nat.gcd a b))) := by
  obtain ⟨t, aa, bb, ht, r, hr, rt, rh, rs⟩ := guarded_ready w a b c cap false ha hb hc
  have hm := run_moreFuel machine t (budget w cap-t) _ r hr
  rw [Nat.add_sub_of_le ht] at hm
  refine ⟨r, hm, rs.le.trans ht, rh, ?_, ?_⟩
  · rw [rt]
    by_cases h : a ≤ cap ∧ b ≤ cap
    · rw [if_pos h]
      constructor
      · intro _; exact h
      · intro _; rfl
    · rw [if_neg h]
      constructor
      · intro hf
        change false = true at hf
        cases hf
      · intro hp; exact False.elim (h hp)
  · intro h
    rw [rt, if_pos h]
    rfl

theorem capped_budget (w cap C : ℕ) (h : cap < 2*C) :
    budget w cap ≤ 8*w+16+(4*C+1)*(32*w+40) := by
  unfold budget
  exact Nat.add_le_add_left (Nat.mul_le_mul_right (32*w+40) (by omega)) (8*w+16)

end NearCubicWires.RepairOrdinary.CloseoutWitness.GcdGuard
