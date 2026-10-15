import Proof.Gates.Interfaces.Transfer
import Proof.Gates.OuterM.Width
import Proof.Gates.CheckedPCPP.Harness
import Proof.Gates.GateRecovery.Proof.CaseAnalysis.Language

set_option autoImplicit false

namespace NearCubicGates.Close.Recovery

open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicGates.Close.Transfer

noncomputable abbrev donor (s : GateSources) (g : GateParams) : OuterM.WidthDonor s.mw (g.sv s) :=
  OuterM.widthDonor s.mw (g.sv s)

noncomputable abbrev donorProgram (s : GateSources) (g : GateParams) : Program :=
  Rewind.program (donor s g).unary.program

theorem width_step (s : GateSources) (g : GateParams) (ν : ℕ) :
    g.width s (ν + 1) ≤ g.width s ν + (g.k + 2) * (Outer.apad s.mw (g.sv s) + 1) := by
  unfold GateParams.width Outer.width
  exact Outer.widthOf_step g.k _ ν

/-- **The (a′) native width as GR's `WidthSource`.** -/
noncomputable def widthSource (s : GateSources) (g : GateParams) :
    GR.NearCubicWires.RepairSource.WidthSource where
  width := g.width s
  jump := (g.k + 2) * (Outer.apad s.mw (g.sv s) + 1)
  lower := fun ν => g.nu_lt_width s ν
  step := width_step s g
  tapes := (donorProgram s g).tapeCount
  states := (donorProgram s g).stateCount
  machine := (donorProgram s g).machine
  inPort := ⟨0, by have := (donorProgram s g).twoTapes; omega⟩
  outPort := (donorProgram s g).outputTape
  ports_ne := by
    intro h
    exact (donorProgram s g).outputFresh (congrArg Fin.val h).symm
  budget := fun ν => 2 * ((donor s g).K * (2 ^ ν + 1) ^ 1) + 2
  run := by
    intro ν
    obtain ⟨out, hr, ho⟩ := CheckedPCPP.wordFunction_ready (donor s g).unary ⟨2 ^ ν, fun _ => true⟩
    refine ⟨out, ?_, ?_⟩
    · have hin : (Rewind.program (donor s g).unary.program).inputTapes (List.ofFn fun _ : Fin (2 ^ ν) => true) =
          fun i => if i = (⟨0, by have := (donorProgram s g).twoTapes; omega⟩ : Fin (donorProgram s g).tapeCount)
            then RepairOrdinary.frame (List.replicate (2 ^ ν) true) else [] := by
        funext i
        rw [CheckedPCPP.program_inputTapes]
        by_cases h : i.val = 0
        · have hi : i = (⟨0, by have := (donorProgram s g).twoTapes; omega⟩ : Fin (donorProgram s g).tapeCount) :=
            Fin.ext h
          rw [if_pos h, if_pos hi, List.ofFn_const]
        · have hi : i ≠ (⟨0, by have := (donorProgram s g).twoTapes; omega⟩ : Fin (donorProgram s g).tapeCount) :=
            fun he => h (by rw [he])
          rw [if_neg h, if_neg hi]
      rw [← hin]
      exact hr
    · rw [ho]
      show List.replicate (OuterM.qOf s.mw (g.sv s) (2 ^ ν)) true = List.replicate (g.width s ν) true
      rw [OuterM.qOf_two_pow]
      rfl
  coefficient := 2 * (donor s g).K + 2
  degree := 1
  poly := by
    intro ν
    show 2 * ((donor s g).K * (2 ^ ν + 1) ^ 1) + 2 ≤ (2 * (donor s g).K + 2) * (2 ^ ν + 1) ^ 1
    rw [pow_one]
    nlinarith [Nat.zero_le (2 ^ ν), Nat.zero_le (donor s g).K]

/-- The gate sources as GR's narrow bundle at `g`. -/
noncomputable def toEight (s : GateSources) (g : GateParams) : GR.NearCubicWires.RepairSource.GateEightSources :=
  ⟨s.normalization, widthSource s g, ⟨s.hierarchyRefuter, s.xor⟩, s.amplifier⟩

theorem hierarchy_eq (s : GateSources) (g : GateParams) (T : ℕ → ℕ) (clock : OrdinaryClock T) :
    (toEight s g).hierarchy T clock = s.hierarchy T clock := rfl

theorem amplification_eq (s : GateSources) (g : GateParams) : (toEight s g).amplification = s.amplification := rfl

/-- GR's core arity at `(K_amp, log₂P − 1, d_G)` is `m(q(N_ν))`. -/
theorem widthAt_eq (s : GateSources) (g : GateParams) (hpl : 1 ≤ g.positionLog) (ν : ℕ) :
    GR.NearCubicWires.RepairSource.CloseoutLanguage.widthAt (toEight s g) g.k g.clock g.ampFactor
      (g.positionLog - 1) g.clauseDegree ν = g.coreArity s ν := by
  unfold GR.NearCubicWires.RepairSource.CloseoutLanguage.widthAt
    GR.NearCubicWires.RepairSource.CloseoutLanguage.coreWidth GateParams.coreArity GateParams.tableArity
  have h : g.positionLog - 1 + 1 = g.positionLog := by omega
  rw [h]
  rfl

end NearCubicGates.Close.Recovery
