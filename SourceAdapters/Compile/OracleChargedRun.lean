import SourceAdapters.Compile.OracleChargedStep

/-!
proof of `thm:short-pcp-ours`, Step 4: bounded execution with the literal ordinary-oracle charge.
The outer round counter is bounded by fuel because every actual step costs
at least one. The remaining budget separately charges the full framed-query
length; exhaustion or a malformed/unrewound query rejects. This is the
trace semantics used by the separate circuit construction and ordinary code generator.
-/
namespace NearCubicGates.Adapters.Compile.OracleExecution
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
  NearCubicWires.LocalBitMultitape
set_option autoImplicit false

/-- Fixed number of scheduling rounds, with a separate literal cost ledger. -/
def chargedRounds (o : ℕ → Bool) (p : OrdinaryOracleProgram) :
    ℕ → ℕ → p.Config → Option p.Config
  | 0, _, a => if p.base.machine.halted a.control then some a else none
  | rounds+1, budget, a =>
    if p.base.machine.halted a.control then some a else
      match chargedStep o p a with
      | none => none
      | some (cost,b) =>
        if cost ≤ budget then chargedRounds o p rounds (budget-cost) b else none

theorem chargedRounds_sound (o : ℕ → Bool) (p : OrdinaryOracleProgram)
    (rounds budget : ℕ) (a b : p.Config)
    (h : chargedRounds o p rounds budget a=some b) :
    ∃ cost, cost ≤ budget ∧ OrdinaryOracleTrace o p cost a b ∧
      p.base.machine.halted b.control=true := by
  induction rounds generalizing budget a with
  | zero =>
    simp only [chargedRounds] at h
    split at h
    · rename_i hh
      cases h
      exact ⟨0,Nat.zero_le _,.refl _,hh⟩
    · simp at h
  | succ rounds ih =>
    simp only [chargedRounds] at h
    split at h
    · rename_i hh
      cases h
      exact ⟨0,Nat.zero_le _,.refl _,hh⟩
    · cases hs : chargedStep o p a with
      | none => simp [hs] at h
      | some pair =>
        obtain ⟨cost,middle⟩ := pair
        simp only [hs] at h
        split at h
        · rename_i hc
          obtain ⟨rest,hr,ht,hh⟩ := ih (budget-cost) middle h
          exact ⟨cost+rest,by omega,.cons (chargedStep_sound hs) ht,hh⟩
        · simp at h

theorem chargedRounds_complete {o : ℕ → Bool} {p : OrdinaryOracleProgram}
    {cost : ℕ} {a b : p.Config} (h : OrdinaryOracleTrace o p cost a b)
    (hh : p.base.machine.halted b.control=true) (rounds budget : ℕ)
    (hr : cost ≤ rounds) (hb : cost ≤ budget) :
    chargedRounds o p rounds budget a=some b := by
  induction h generalizing rounds budget with
  | refl a => cases rounds <;> simp [chargedRounds,hh]
  | @cons cost rest a middle b hs ht ih =>
    have hp := step_cost_positive hs
    have hn : p.base.machine.halted a.control=false := by cases hs <;> assumption
    cases rounds with
    | zero => omega
    | succ rounds =>
      have hc : cost ≤ budget := by omega
      simp only [chargedRounds,hn,Bool.false_eq_true,↓reduceIte,chargedStep_complete hs]
      rw [if_pos hc]
      exact ih hh rounds (budget-cost) (by omega) (by omega)

def chargedRun (o : ℕ → Bool) (p : OrdinaryOracleProgram) (fuel : ℕ) (a : p.Config) :
    Option p.Config := chargedRounds o p fuel fuel a

theorem chargedRun_iff (o : ℕ → Bool) (p : OrdinaryOracleProgram)
    (fuel : ℕ) (a b : p.Config) :
    chargedRun o p fuel a=some b ↔
      ∃ cost, cost ≤ fuel ∧ OrdinaryOracleTrace o p cost a b ∧
        p.base.machine.halted b.control=true := by
  constructor
  · exact chargedRounds_sound o p fuel fuel a b
  · rintro ⟨cost,hc,ht,hh⟩
    exact chargedRounds_complete ht hh fuel fuel hc hc

/-- Exact full-list output equality, including the outer input frame. -/
theorem runs_iff (o : ℕ → Bool) (p : OrdinaryOracleProgram)
    (input output : List Bool) (fuel : ℕ) :
    OrdinaryOracleRuns o p input output fuel ↔
      ∃ final, chargedRun o p fuel
        (initialConfiguration p.base.machine (p.base.inputTapes input))=some final ∧
        final.tapes p.base.outputTape=RepairOrdinary.frame output := by
  constructor
  · rintro ⟨cost,final,hc,ht,hh,ho⟩
    exact ⟨final,(chargedRun_iff _ _ _ _ _).2 ⟨cost,hc,ht,hh⟩,ho⟩
  · rintro ⟨final,hr,ho⟩
    obtain ⟨cost,hc,ht,hh⟩ := (chargedRun_iff _ _ _ _ _).1 hr
    exact ⟨cost,final,hc,ht,hh,ho⟩

end NearCubicGates.Adapters.Compile.OracleExecution
