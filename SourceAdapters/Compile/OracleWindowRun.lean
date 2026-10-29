import SourceAdapters.Compile.OracleWindow

/-!
proof of `thm:short-pcp-ours`: fixed-round charged execution in a finite window, with exact
allocated lengths. The checked local head-growth bound guarantees no genuine
bounded computation is rejected by the window guard. This is an executable
finite schedule; its oracle-expression lowering and physical serialization
remain separate steps. -/
namespace NearCubicGates.Adapters.Compile.OracleExecution
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
  NearCubicWires.LocalBitMultitape
set_option autoImplicit false

noncomputable def windowRounds (o : ℕ → Bool) (p : OrdinaryOracleProgram) (width : ℕ) :
    ℕ → ℕ → Window p.base.tapeCount p.base.stateCount width →
      Option (Window p.base.tapeCount p.base.stateCount width)
  | 0, _, a => if p.base.machine.halted a.view.control then some a else none
  | rounds+1, budget, a =>
    if p.base.machine.halted a.view.control then some a else
      match windowStep o p width a with
      | none => none
      | some (cost,b) =>
        if cost ≤ budget then windowRounds o p width rounds (budget-cost) b else none

theorem windowRounds_sound (o : ℕ → Bool) (p : OrdinaryOracleProgram)
    (width rounds budget : ℕ) (a b : Window p.base.tapeCount p.base.stateCount width)
    (h : windowRounds o p width rounds budget a=some b) :
    ∃ cost, cost ≤ budget ∧ OrdinaryOracleTrace o p cost a.unpack b.unpack ∧
      p.base.machine.halted b.view.control=true := by
  induction rounds generalizing budget a with
  | zero =>
    simp only [windowRounds] at h
    split at h
    · rename_i hh
      cases h
      exact ⟨0,Nat.zero_le _,.refl _,hh⟩
    · simp at h
  | succ rounds ih =>
    simp only [windowRounds] at h
    split at h
    · rename_i hh
      cases h
      exact ⟨0,Nat.zero_le _,.refl _,hh⟩
    · cases hs : windowStep o p width a with
      | none => simp [hs] at h
      | some pair =>
        obtain ⟨cost,middle⟩ := pair
        simp only [hs] at h
        split at h
        · rename_i hc
          obtain ⟨rest,hr,ht,hh⟩ := ih (budget-cost) middle h
          exact ⟨cost+rest,by omega,.cons (windowStep_sound hs) ht,hh⟩
        · simp at h

theorem windowRounds_complete {o : ℕ → Bool} {p : OrdinaryOracleProgram}
    {cost : ℕ} {a b : p.Config} (h : OrdinaryOracleTrace o p cost a b)
    (hh : p.base.machine.halted b.control=true) (rounds budget width : ℕ)
    (hr : cost ≤ rounds) (hb : cost ≤ budget)
    (start : Window p.base.tapeCount p.base.stateCount width) (he : start.unpack=a)
    (hroom : ∀ tape, a.heads tape+budget < width)
    (htapes : ∀ tape, (a.tapes tape).length ≤ width) :
    ∃ final, windowRounds o p width rounds budget start=some final ∧ final.unpack=b := by
  induction h generalizing rounds budget start with
  | refl a =>
    have hs : p.base.machine.halted start.view.control=true := by
      change p.base.machine.halted start.unpack.control=true
      rw [he,hh]
    exact ⟨start,by cases rounds <;> simp [windowRounds,hs],he⟩
  | @cons cost rest a middle b hs ht ih =>
    have hp := step_cost_positive hs
    have hn : p.base.machine.halted a.control=false := by cases hs <;> assumption
    cases rounds with
    | zero => omega
    | succ rounds =>
      have hc : cost ≤ budget := by omega
      obtain ⟨hfit,hroom'⟩ := step_room hs hc hroom htapes
      have hw : windowStep o p width start=some (cost,Window.pack middle hfit) :=
        windowStep_complete (by rw [he]; exact hs) hfit
      obtain ⟨final,hf,hu⟩ := ih hh rounds (budget-cost)
        (by omega) (by omega) (Window.pack middle hfit) (Window.unpack_pack _ _)
        hroom' hfit.2
      refine ⟨final,?_,hu⟩
      have hstart : p.base.machine.halted start.view.control=false := by
        change p.base.machine.halted start.unpack.control=false
        rw [he,hn]
      simp only [windowRounds,hstart,Bool.false_eq_true,↓reduceIte,hw]
      rw [if_pos hc]
      exact hf

/-- The finite schedule has exactly the actual bounded charged trace semantics. -/
theorem windowRun_iff (o : ℕ → Bool) (p : OrdinaryOracleProgram) (width fuel : ℕ)
    (a : Window p.base.tapeCount p.base.stateCount width) (b : p.Config)
    (hroom : ∀ tape, a.unpack.heads tape+fuel < width) :
    (∃ final, windowRounds o p width fuel fuel a=some final ∧ final.unpack=b) ↔
      ∃ cost, cost ≤ fuel ∧ OrdinaryOracleTrace o p cost a.unpack b ∧
        p.base.machine.halted b.control=true := by
  constructor
  · rintro ⟨final,hr,he⟩
    obtain ⟨cost,hc,ht,hh⟩ := windowRounds_sound o p width fuel fuel a final hr
    refine ⟨cost,hc,?_,?_⟩
    · rwa [he] at ht
    · change p.base.machine.halted final.unpack.control=true at hh
      rwa [he] at hh
  · rintro ⟨cost,hc,ht,hh⟩
    exact windowRounds_complete ht hh fuel fuel width hc hc a rfl hroom a.unpack_fits.2

end NearCubicGates.Adapters.Compile.OracleExecution
