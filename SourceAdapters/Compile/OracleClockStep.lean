import SourceAdapters.Compile.OracleQueryAction
import SourceAdapters.Compile.OracleGuardExpressions

/-!
proof of `thm:short-pcp-ours`, Step 4: connect the explicit guarded gate updates to the actual charged
oracle interpreter. All conditions come from OrdinaryOracleStep; a successful
finite clock step supplies an actual source step and its literal charged cost.
-/
namespace NearCubicGates.Adapters.Compile.OracleExecution
open NearCubicWires NearCubicWires.RepairSource NearCubicWires.LocalBitMultitape
set_option autoImplicit false

theorem clockAdvance_receipt {o : ℕ → Bool} {p : OrdinaryOracleProgram} {width cap : ℕ}
    {a b : ClockState p width cap} (hh : p.base.machine.halted a.window.view.control=false)
    (h : clockAdvance o p width cap a=some b) :
    ∃ cost, OrdinaryOracleStep o p cost a.window.unpack b.window.unpack ∧
      cost ≤ a.remaining.val ∧ b.remaining.val=a.remaining.val-cost := by
  simp only [clockAdvance,hh,Bool.false_eq_true,↓reduceIte] at h
  cases hs : windowStep o p width a.window with
  | none => simp [hs] at h
  | some pair =>
    obtain ⟨cost,middle⟩ := pair
    simp only [hs] at h
    split at h
    · rename_i hc
      cases h
      exact ⟨cost,windowStep_sound hs,hc,rfl⟩
    · simp at h

theorem clockAdvance_of_step {o : ℕ → Bool} {p : OrdinaryOracleProgram} {width cap cost : ℕ}
    (a : ClockState p width cap) (after : p.Config)
    (hs : OrdinaryOracleStep o p cost a.window.unpack after) (hf : Fits width after)
    (hc : cost ≤ a.remaining.val) :
    clockAdvance o p width cap a=
      some ⟨Window.pack after hf,⟨a.remaining.val-cost,by have := a.remaining.isLt; omega⟩⟩ := by
  have hh : p.base.machine.halted a.window.view.control=false := by cases hs <;> assumption
  simp only [clockAdvance,hh,Bool.false_eq_true,↓reduceIte,windowStep_complete hs hf,hc]

theorem clockAdvance_local {o : ℕ → Bool} {p : OrdinaryOracleProgram} {width cap : ℕ}
    (a : ClockState p width cap) (action : Action p.base.tapeCount p.base.stateCount)
    (hh : p.base.machine.halted a.window.view.control=false)
    (hq : p.query a.window.view.control=none)
    (hr : p.base.machine.rule a.window.view.control a.window.unpack.scanned=some action)
    (hp : 0<a.remaining.val)
    (hf : ∀ tape, (action.move tape).apply (a.window.observed.heads tape).val < width) :
    clockAdvance o p width cap a=some (localState a action hf) := by
  have hs : OrdinaryOracleStep o p 1 a.window.unpack (applyAction a.window.unpack action) :=
    .local _ _ hh hq (by simp only [step,show a.window.unpack.control=a.window.view.control from rfl,hr,
      Option.map_some])
  exact clockAdvance_of_step a _ hs (actionWindow_fits a action hf) (by omega)

theorem clockAdvance_query {o : ℕ → Bool} {p : OrdinaryOracleProgram} {width cap : ℕ}
    (a : ClockState p width cap) (rule : OracleReturn p.base.stateCount) (bits padding : List Bool)
    (hh : p.base.machine.halted a.window.view.control=false)
    (hq : p.query a.window.view.control=some rule)
    (hr : a.window.unpack.heads p.queryTape=0)
    (hw : a.window.unpack.tapes p.queryTape=RepairOrdinary.frame bits++padding)
    (hc : 2*bits.length+2 ≤ a.remaining.val) :
    clockAdvance o p width cap a=
      some (queryState a rule (o (CanonicalBinary.bitsValue bits)) (2*bits.length+2)) := by
  have hs := OrdinaryOracleStep.ask (oracle := o) a.window.unpack bits padding rule hh hq hr hw
  have hcost : (RepairOrdinary.frame bits).length+1=2*bits.length+2 := by simp [RepairOrdinary.frame_length]
  rw [hcost] at hs
  exact clockAdvance_of_step a _ hs ⟨a.window.unpack_fits.1,a.window.unpack_fits.2⟩ hc


theorem clockAdvance_local_reject {o : ℕ → Bool} {p : OrdinaryOracleProgram} {width cap : ℕ}
    (a : ClockState p width cap) (action : Action p.base.tapeCount p.base.stateCount)
    (hh : p.base.machine.halted a.window.view.control=false)
    (hq : p.query a.window.view.control=none)
    (hr : p.base.machine.rule a.window.view.control a.window.unpack.scanned=some action)
    (hg : (localGuardExpression p width cap action).eval a.encode=false) :
    clockAdvance o p width cap a=none := by
  cases hrun : clockAdvance o p width cap a with
  | none => rfl
  | some b =>
    obtain ⟨cost,hs,hc,_⟩ := clockAdvance_receipt hh hrun
    have known : OrdinaryOracleStep o p 1 a.window.unpack (applyAction a.window.unpack action) :=
      .local _ _ hh hq (by simp only [step,show a.window.unpack.control=a.window.view.control from rfl,hr,
        Option.map_some])
    have he := Option.some.inj ((chargedStep_complete hs).symm.trans (chargedStep_complete known))
    have hcost : cost=1 := congrArg Prod.fst he
    have hafter : b.window.unpack=applyAction a.window.unpack action := congrArg Prod.snd he
    have hfit : ∀ tape, (action.move tape).apply (a.window.observed.heads tape).val < width := by
      intro tape
      have hb := b.window.unpack_fits.1 tape
      rw [hafter] at hb
      exact hb
    have hyes := (localGuardExpression_eval p width cap a action).2 ⟨by omega,hfit⟩
    rw [hg] at hyes
    cases hyes

theorem clockAdvance_missing {o : ℕ → Bool} {p : OrdinaryOracleProgram} {width cap : ℕ}
    (a : ClockState p width cap)
    (hh : p.base.machine.halted a.window.view.control=false)
    (hq : p.query a.window.view.control=none)
    (hr : p.base.machine.rule a.window.view.control a.window.unpack.scanned=none) :
    clockAdvance o p width cap a=none := by
  have hs : chargedStep o p a.window.unpack=none := by
    simp [chargedStep,show a.window.unpack.control=a.window.view.control from rfl,hh,hq,step,hr]
  simp [clockAdvance,hh,windowStep,hs]

theorem query_step_fields {o : ℕ → Bool} {p : OrdinaryOracleProgram} {cost : ℕ}
    {before after : p.Config} (hs : OrdinaryOracleStep o p cost before after)
    (hq : p.query before.control ≠ none) :
    ∃ bits padding, before.heads p.queryTape=0 ∧
      before.tapes p.queryTape=RepairOrdinary.frame bits++padding ∧ cost=2*bits.length+2 := by
  cases hs with
  | «local» before after _ hn _ => exact (hq hn).elim
  | ask before bits padding ret _ _ hr hw =>
    exact ⟨bits,padding,hr,hw,by simp [RepairOrdinary.frame_length]⟩

theorem clockAdvance_query_reject {o : ℕ → Bool} {p : OrdinaryOracleProgram} {width cap : ℕ}
    (a : ClockState p width cap) (rule : OracleReturn p.base.stateCount)
    (hh : p.base.machine.halted a.window.view.control=false)
    (hq : p.query a.window.view.control=some rule)
    (hg : (queryGuardExpression p width cap).eval a.encode=false) :
    clockAdvance o p width cap a=none := by
  cases hrun : clockAdvance o p width cap a with
  | none => rfl
  | some b =>
    obtain ⟨cost,hs,hc,_⟩ := clockAdvance_receipt hh hrun
    have hn : p.query a.window.unpack.control ≠ none := by
      change p.query a.window.view.control ≠ none
      rw [hq]
      simp
    obtain ⟨bits,padding,hr,hw,hcost⟩ := query_step_fields hs hn
    have hyes := (queryGuardExpression_eval p width cap a).2
      ⟨hr,bits,padding,hw,by omega⟩
    rw [hg] at hyes
    cases hyes

end NearCubicGates.Adapters.Compile.OracleExecution
