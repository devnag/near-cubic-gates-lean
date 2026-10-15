import Proof.Amplification.RecoveryFocusedMachine

/-! Exact time prefixes for scalar algorithms. Space is still the actual tape
storage in the underlying receipts; these lemmas merely hide an unused peak
bound while composing the polynomial-time recovery interpreter. -/
namespace NearCubicWires.RepairOrdinary.RecoveryExecution
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def Timed {t s : Nat} (p : Machine t s) (n : Nat)
    (c d : Configuration t s) : Prop := ∃ space, Prefix p space n c d

theorem Timed.refl {t s : Nat} (p : Machine t s) (c : Configuration t s) : Timed p 0 c c :=
  ⟨c.tapeCells, Prefix.refl c (Nat.le_refl _)⟩

theorem Timed.step {t s n : Nat} {p : Machine t s} {c d e : Configuration t s}
    (hn : p.halted c.control = false) (hs : LocalBitMultitape.step p c = some d)
    (tail : Timed p n d e) : Timed p (n + 1) c e := by
  obtain ⟨space, hp⟩ := tail
  exact ⟨max c.tapeCells space, Prefix.step (Nat.le_max_left _ _) hn hs
    (hp.enlarge (Nat.le_max_right _ _))⟩

theorem Timed.single {t s : Nat} {p : Machine t s} {c d : Configuration t s}
    (hn : p.halted c.control = false) (hs : LocalBitMultitape.step p c = some d) : Timed p 1 c d :=
  Timed.step hn hs (Timed.refl p d)

theorem Timed.trans {t s n m : Nat} {p : Machine t s} {c d e : Configuration t s}
    (h : Timed p n c d) (k : Timed p m d e) : Timed p (n + m) c e := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := k
  exact ⟨max a b, (ha.enlarge (Nat.le_max_left _ _)).trans
    (hb.enlarge (Nat.le_max_right _ _))⟩

theorem Timed.run {t s n : Nat} {p : Machine t s} {c d : Configuration t s}
    (h : Timed p n c d) (hd : p.halted d.control = true) :
    ∃ r : ExecutionReceipt t s, runFrom p n c = some r ∧ r.final = d ∧ r.steps = n := by
  obtain ⟨space, hp⟩ := h
  obtain ⟨r, hr, hf, hs, _⟩ := (hp.enlarge (Nat.le_max_left space d.tapeCells)).run hd
    (Nat.le_max_right space d.tapeCells)
  exact ⟨r, hr, hf, hs⟩

end NearCubicWires.RepairOrdinary.RecoveryExecution
