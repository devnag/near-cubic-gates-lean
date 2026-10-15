import Proof.Foundations.RecoveryOracleContracts
import Proof.MachineModel.OrdinaryZeroPadding
import Proof.Amplification.RecoveryTapeSupport

/-! Trace operations used by the paid ordinary-oracle compositor. Padding
retains allocated cells and preserves the literal cost of every oracle ask. -/
namespace NearCubicWires.RepairSource.OrdinaryOracleCompose
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem trans {o : ℕ → Bool} {p : OrdinaryOracleProgram} {a b c : p.Config}
    {n m : ℕ} (h : OrdinaryOracleTrace o p n a b)
    (k : OrdinaryOracleTrace o p m b c) : OrdinaryOracleTrace o p (n + m) a c := by
  induction h with
  | refl => simpa using k
  | cons hs ht ih =>
    simpa only [Nat.add_assoc] using OrdinaryOracleTrace.cons hs (ih k)

theorem single {o : ℕ → Bool} {p : OrdinaryOracleProgram} {a b : p.Config}
    {n : ℕ} (h : OrdinaryOracleStep o p n a b) : OrdinaryOracleTrace o p n a b := by
  simpa using OrdinaryOracleTrace.cons h (OrdinaryOracleTrace.refl b)

theorem step_padding {o : ℕ → Bool} {p : OrdinaryOracleProgram}
    {n : ℕ} {a b : p.Config} (caps : Fin p.base.tapeCount → ℕ)
    (h : OrdinaryOracleStep o p n a b) :
    OrdinaryOracleStep o p n (ZeroPadding.config caps a) (ZeroPadding.config caps b) := by
  cases h with
  | «local» a b hh hq hs =>
    exact .local _ _ hh hq (ZeroPadding.step_config p.base.machine caps a b hs)
  | ask a bits padding rule hh hq hr hw =>
    have hout : (ZeroPadding.config caps a).tapes p.queryTape =
        frame bits ++ (padding ++ List.replicate
          (caps p.queryTape - (a.tapes p.queryTape).length) false) := by
      simp only [ZeroPadding.config, ZeroPadding.pad, hw, List.append_assoc]
    exact .ask _ bits _ rule hh hq hr hout

theorem trace_padding {o : ℕ → Bool} {p : OrdinaryOracleProgram}
    {n : ℕ} {a b : p.Config} (caps : Fin p.base.tapeCount → ℕ)
    (h : OrdinaryOracleTrace o p n a b) :
    OrdinaryOracleTrace o p n (ZeroPadding.config caps a) (ZeroPadding.config caps b) := by
  induction h with
  | refl => exact .refl _
  | cons hs ht ih => exact .cons (step_padding caps hs) ih

theorem local_head_bound {p : OrdinaryOracleProgram} {a b : p.Config}
    (hs : step p.base.machine a = some b) (i : Fin p.base.tapeCount) :
    b.heads i ≤ a.heads i + 1 := by
  unfold step at hs
  obtain ⟨x, _, hx⟩ := Option.map_eq_some_iff.mp hs
  subst b
  change (x.move i).apply (a.heads i) ≤ a.heads i + 1
  cases x.move i <;> simp only [HeadMove.apply] <;> omega

theorem local_tape_bound {p : OrdinaryOracleProgram} {a b : p.Config}
    (hs : step p.base.machine a = some b) (i : Fin p.base.tapeCount) :
    (b.tapes i).length ≤ max (a.tapes i).length (a.heads i + 1) := by
  unfold step at hs
  obtain ⟨x, _, hx⟩ := Option.map_eq_some_iff.mp hs
  subst b
  simp only [applyAction]
  cases hw : x.write i
  · exact Nat.le_max_left _ _
  · simp only [RecoveryTapeSupport.write_length]
    exact Nat.le_refl _

/-- One physical local step grows a blank tape by at most the local-step
count. Oracle answers move no heads and allocate no tape cells. -/
theorem trace_support {o : ℕ → Bool} {p : OrdinaryOracleProgram}
    {cost : ℕ} {a b : p.Config} (h : OrdinaryOracleTrace o p cost a b)
    (position : ℕ) (hh : ∀ i, a.heads i ≤ position)
    (caps : Fin p.base.tapeCount → ℕ)
    (ht : ∀ i, (a.tapes i).length ≤ max (caps i) position) :
    ∀ i, b.heads i ≤ position + cost ∧
      (b.tapes i).length ≤ max (caps i) (position + cost) := by
  induction h generalizing position with
  | refl => intro i; simpa using And.intro (hh i) (ht i)
  | @cons cost rest a middle b hs htail ih =>
    cases hs with
    | «local» a middle hhalt hquery hstep =>
      have hheads : ∀ i, middle.heads i ≤ position + 1 := by
        intro i
        exact (local_head_bound hstep i).trans (Nat.add_le_add_right (hh i) 1)
      have htapes : ∀ i, (middle.tapes i).length ≤ max (caps i) (position + 1) := by
        intro i
        have hb := local_tape_bound hstep i
        have ha := ht i
        have hp := hh i
        omega
      intro i
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (position + 1) hheads htapes i
    | ask a bits padding rule hhalt hquery hr hw =>
      have h := ih position hh ht
      intro i
      have hi := h i
      constructor <;> omega

theorem run_support {o : ℕ → Bool} {p : OrdinaryOracleProgram}
    {input output : List Bool} {budget : ℕ}
    (h : OrdinaryOracleRuns o p input output budget) :
    ∃ cost final, cost ≤ budget ∧
      OrdinaryOracleTrace o p cost
        (initialConfiguration p.base.machine (p.base.inputTapes input)) final ∧
      p.base.machine.halted final.control = true ∧
      final.tapes p.base.outputTape = frame output ∧
      (∀ i, final.heads i ≤ cost) ∧
      (∀ i, i.val ≠ 0 → (final.tapes i).length ≤ cost) := by
  obtain ⟨cost, final, hc, htrace, hh, ht⟩ := h
  have hs := trace_support htrace 0 (by simp [initialConfiguration])
    (fun i => (p.base.inputTapes input i).length) (by simp [initialConfiguration])
  refine ⟨cost, final, hc, htrace, hh, ht, ?_, ?_⟩
  · intro i
    simpa using (hs i).1
  · intro i hi
    simpa [Program.inputTapes, hi] using (hs i).2

end NearCubicWires.RepairSource.OrdinaryOracleCompose
