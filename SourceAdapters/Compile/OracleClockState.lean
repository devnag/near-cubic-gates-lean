import SourceAdapters.Compile.OracleRequestRun

/-!
proof of `thm:short-pcp-ours`, Step 4: the remaining charged clock is a finite state component, not
an unbounded meta-level recursion parameter. Halts absorb further rounds;
stuck, malformed, unrewound or over-budget steps become explicit failure.
-/
namespace NearCubicGates.Adapters.Compile.OracleExecution
open NearCubicWires NearCubicWires.RepairSource NearCubicWires.LocalBitMultitape
set_option autoImplicit false

structure ClockState (p : OrdinaryOracleProgram) (width cap : ℕ) where
  window : Window p.base.tapeCount p.base.stateCount width
  remaining : Fin (cap+1)

noncomputable def clockAdvance (o : ℕ → Bool) (p : OrdinaryOracleProgram) (width cap : ℕ)
    (a : ClockState p width cap) : Option (ClockState p width cap) :=
  if p.base.machine.halted a.window.view.control then some a else
    match windowStep o p width a.window with
    | none => none
    | some (cost,b) =>
      if cost ≤ a.remaining.val then
        some ⟨b,⟨a.remaining.val-cost,by have := a.remaining.isLt; omega⟩⟩
      else none

noncomputable def clockRounds (o : ℕ → Bool) (p : OrdinaryOracleProgram) (width cap : ℕ) :
    ℕ → ClockState p width cap → Option (ClockState p width cap)
  | 0, a => some a
  | rounds+1, a => (clockAdvance o p width cap a).bind (clockRounds o p width cap rounds)

theorem clockRounds_halted (o : ℕ → Bool) (p : OrdinaryOracleProgram) (width cap rounds : ℕ)
    (a : ClockState p width cap) (hh : p.base.machine.halted a.window.view.control=true) :
    clockRounds o p width cap rounds a=some a := by
  induction rounds with
  | zero => rfl
  | succ rounds ih => simpa [clockRounds,clockAdvance,hh] using ih

/-- The finite clock register implements exactly the charged-window runner. -/
theorem clockRounds_window (o : ℕ → Bool) (p : OrdinaryOracleProgram) (width cap rounds : ℕ)
    (a : ClockState p width cap) :
    (clockRounds o p width cap rounds a).bind
      (fun b => if p.base.machine.halted b.window.view.control then some b.window else none)=
      windowRounds o p width rounds a.remaining.val a.window := by
  induction rounds generalizing a with
  | zero => rfl
  | succ rounds ih =>
    by_cases hh : p.base.machine.halted a.window.view.control=true
    · rw [clockRounds_halted o p width cap (rounds+1) a hh]
      simp [windowRounds,hh]
    · simp only [clockRounds,clockAdvance,if_neg hh,windowRounds]
      cases hs : windowStep o p width a.window with
      | none => simp
      | some pair =>
        obtain ⟨cost,b⟩ := pair
        by_cases hc : cost ≤ a.remaining.val
        · simp only [if_pos hc,Option.bind_some]
          exact ih ⟨b,⟨a.remaining.val-cost,by have := a.remaining.isLt; omega⟩⟩
        · simp [hc]

def requestClockState (p : OrdinaryOracleProgram) (r : OracleCompilationRequest)
    (z : BitInput r.ell) : ClockState p (requestWidth r) r.fuel :=
  ⟨requestWindow p r z,⟨r.fuel,Nat.lt_succ_self _⟩⟩

theorem requestClockRun_eq (p : OrdinaryOracleProgram) (r : OracleCompilationRequest)
    (O : BitInput r.ell → Bool) (z : BitInput r.ell) :
    (clockRounds (fixedArityOracle O) p (requestWidth r) r.fuel r.fuel
      (requestClockState p r z)).bind
      (fun b => if p.base.machine.halted b.window.view.control then some b.window else none)=
        requestRun p r O z :=
  clockRounds_window _ _ _ _ _ _

end NearCubicGates.Adapters.Compile.OracleExecution
