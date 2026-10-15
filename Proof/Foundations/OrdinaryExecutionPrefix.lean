import Proof.Foundations.OrdinaryMachine

/-! Finite nonhalting prefixes, used to verify the inner record loop of the
ordinary sorting pass. Every edge is an actual local transition; the space
bound covers every configuration, including the endpoint. -/
namespace NearCubicWires.RepairOrdinary
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

inductive Prefix {t s : ℕ} (p : Machine t s) (space : ℕ) :
    ℕ → Configuration t s → Configuration t s → Prop where
  | refl (c : Configuration t s) (hc : c.tapeCells ≤ space) : Prefix p space 0 c c
  | step {n : ℕ} {c d e : Configuration t s}
      (hc : c.tapeCells ≤ space) (hn : p.halted c.control = false)
      (hs : LocalBitMultitape.step p c = some d)
      (tail : Prefix p space n d e) : Prefix p space (n + 1) c e

namespace Prefix

theorem trans {t s space n m : ℕ} {p : Machine t s}
    {c d e : Configuration t s} (h : Prefix p space n c d)
    (k : Prefix p space m d e) : Prefix p space (n + m) c e := by
  induction h with
  | refl => simpa using k
  | step hc hn hs _ ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      Prefix.step hc hn hs (ih k)

theorem followedBy {t s space n fuel : ℕ} {p : Machine t s}
    {c d : Configuration t s} (h : Prefix p space n c d)
    (r : ExecutionReceipt t s) (hr : runFrom p fuel d = some r) :
    ∃ joined : ExecutionReceipt t s,
      runFrom p (n + fuel) c = some joined ∧ joined.final = r.final ∧
      joined.steps = n + r.steps ∧ joined.peakTapeCells ≤ max space r.peakTapeCells := by
  induction h with
  | refl =>
    exact ⟨r, by simpa using hr, rfl, by omega, Nat.le_max_right _ _⟩
  | @step k c d e hc hn hs tail ih =>
    obtain ⟨next, hnext, hf, hsteps, hpeak⟩ := ih hr
    refine ⟨⟨next.final, next.steps + 1, max c.tapeCells next.peakTapeCells⟩,
      ?_, hf, ?_, ?_⟩
    · have hj := runFrom_step p c d next hn hs hnext
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hj
    · dsimp only
      omega
    · exact max_le (hc.trans (Nat.le_max_left _ _)) hpeak

theorem run {t s space n : ℕ} {p : Machine t s}
    {c d : Configuration t s} (h : Prefix p space n c d)
    (hd : p.halted d.control = true) (hspace : d.tapeCells ≤ space) :
    ∃ r : ExecutionReceipt t s, runFrom p n c = some r ∧
      r.final = d ∧ r.steps = n ∧ r.peakTapeCells ≤ space := by
  obtain ⟨r, hr, hf, hs, hp⟩ := h.followedBy
    ⟨d, 0, d.tapeCells⟩ (runFrom_zero_of_halted p d hd)
  exact ⟨r, by simpa using hr, hf, by simpa using hs,
    hp.trans (max_le (Nat.le_refl _) hspace)⟩

end Prefix
end NearCubicWires.RepairOrdinary
