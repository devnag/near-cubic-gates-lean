import SourceAdapters.Joins.ComputationToCircuit
import Proof.MachineModel.OrdinaryOracleComposeTrace

/-!
proof of `thm:short-pcp-ours`, Step 4: compile the actual short oracle computation, with its counted
query operations. Statement.OrdinaryOracleStep.ask requires the query head
already rewound, charges the literal framed prefix length plus one, and
changes only control. This functional step has exactly those semantics.
The frame parser is defined locally; this module imports no audit implementation.
-/
namespace NearCubicGates.Adapters.Compile.OracleExecution
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
  NearCubicWires.LocalBitMultitape
set_option autoImplicit false

/-- A literal terminated prefix is required; blank or truncated lists fail. -/
def parseFrame : List Bool → Option (List Bool × List Bool)
  | [] => none
  | false :: tail => some ([],tail)
  | [true] => none
  | true :: bit :: tail => (parseFrame tail).map fun p => (bit::p.1,p.2)

theorem parseFrame_append (bits padding : List Bool) :
    parseFrame (RepairOrdinary.frame bits++padding)=some (bits,padding) := by
  induction bits with
  | nil => simp [RepairOrdinary.frame,parseFrame]
  | cons bit bits ih => simp [RepairOrdinary.frame,parseFrame,ih]

theorem parseFrame_sound (word bits padding : List Bool)
    (h : parseFrame word=some (bits,padding)) : word=RepairOrdinary.frame bits++padding := by
  induction word using parseFrame.induct generalizing bits padding with
  | case1 => simp [parseFrame] at h
  | case2 tail =>
    simp only [parseFrame,Option.some.injEq,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩
    rfl
  | case3 => simp [parseFrame] at h
  | case4 bit tail ih =>
    obtain ⟨pair,hp,he⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨a,b⟩ := pair
    cases he
    simp [RepairOrdinary.frame,ih a b hp]

theorem parseFrame_iff (word bits padding : List Bool) :
    parseFrame word=some (bits,padding) ↔ word=RepairOrdinary.frame bits++padding :=
  ⟨parseFrame_sound word bits padding, fun h => h ▸ parseFrame_append bits padding⟩

/-- Query answers affect control only. Both ordinary and oracle costs are explicit. -/
def chargedStep (o : ℕ → Bool) (p : OrdinaryOracleProgram) (a : p.Config) :
    Option (ℕ × p.Config) :=
  if p.base.machine.halted a.control then none else
    match p.query a.control with
    | none => (step p.base.machine a).map fun b => (1,b)
    | some rule =>
      if a.heads p.queryTape=0 then
        (parseFrame (a.tapes p.queryTape)).map fun pair =>
          ((RepairOrdinary.frame pair.1).length+1,
            {a with control:=if o (CanonicalBinary.bitsValue pair.1) then rule.onTrue else rule.onFalse})
      else none

theorem chargedStep_complete {o : ℕ → Bool} {p : OrdinaryOracleProgram}
    {cost : ℕ} {a b : p.Config} (h : OrdinaryOracleStep o p cost a b) :
    chargedStep o p a=some (cost,b) := by
  cases h with
  | «local» a b hh hq hs => simp [chargedStep,hh,hq,hs]
  | ask a bits padding rule hh hq hr hw =>
    simp [chargedStep,hh,hq,hr,hw,parseFrame_append]

theorem chargedStep_sound {o : ℕ → Bool} {p : OrdinaryOracleProgram}
    {cost : ℕ} {a b : p.Config} (h : chargedStep o p a=some (cost,b)) :
    OrdinaryOracleStep o p cost a b := by
  unfold chargedStep at h
  split at h
  · simp at h
  · rename_i hh
    have halted : p.base.machine.halted a.control=false := by simpa using hh
    cases hq : p.query a.control with
    | none =>
      simp only [hq] at h
      obtain ⟨after,hs,he⟩ := Option.map_eq_some_iff.mp h
      cases he
      exact .local _ _ halted hq hs
    | some rule =>
      simp only [hq] at h
      split at h
      · rename_i hr
        obtain ⟨pair,hp,he⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨bits,padding⟩ := pair
        cases he
        exact .ask a bits padding rule halted hq hr (parseFrame_sound _ _ _ hp)
      · simp at h

theorem chargedStep_iff {o : ℕ → Bool} {p : OrdinaryOracleProgram}
    {cost : ℕ} {a b : p.Config} :
    chargedStep o p a=some (cost,b) ↔ OrdinaryOracleStep o p cost a b :=
  ⟨chargedStep_sound,chargedStep_complete⟩

theorem step_cost_positive {o : ℕ → Bool} {p : OrdinaryOracleProgram}
    {cost : ℕ} {a b : p.Config} (h : OrdinaryOracleStep o p cost a b) : 0<cost := by
  cases h <;> omega

end NearCubicGates.Adapters.Compile.OracleExecution
