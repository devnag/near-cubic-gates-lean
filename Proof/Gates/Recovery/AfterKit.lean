import Proof.Gates.Recovery.AfterGlue
import Proof.Gates.Recovery.CaseOneRuns
import Proof.Gates.Recovery.HardTableRuns
import Proof.Gates.ENP.TableSpec

set_option autoImplicit false

namespace NearCubicGates.Close.Recovery.After

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicGates.Close.Transfer NearCubicGates.Close.Gadget

/-- The Case 1 machine for the selected amplifier (data of `Recovery.CaseOneRuns`; `sec:gadget-extract` Case 1 (i)/(iii),
`sec:all-lengths` "Run the general amplifier"). -/
structure CaseOneKit (s : GateSources) (g : GateParams) where
  t : ℕ
  st : ℕ
  M : Machine t st
  output : Fin t
  large : 3 ≤ output.val
  C : ℕ
  E : ℕ
  run : ∀ (a q : ℕ) (w : BitInput (2 ^ a)) (rest : List Bool) (n : ℕ) (point : BitInput n),
    1 ≤ q → q ≤ n → ((selectedAmplifier s.amplification g.degree).output q (cycFn a w q)).arity ≤ n →
    ∃ out, ClockJoin.ReadyRun M (C * (2 ^ n + 1) ^ E)
      (oneInput t (RepairOrdinary.frame (List.ofFn w) ++ rest) (RepairOrdinary.frame (List.ofFn point)) q) out ∧
      out output = RepairOrdinary.frame
        (GateParams.amplified (selectedAmplifier s.amplification g.degree) q (cycFn a w q) n point).toNat.bits

/-- The Case 2 producer (data of `Recovery.HardTableRuns`; `sec:all-lengths` "the honest PCPP proof and each AND helper are
computable in polynomial time once the pair is known"). -/
structure HTKit (s : GateSources) (P : ThreeQueryPCPP) (g : GateParams) where
  t : ℕ
  st : ℕ
  M : Machine t st
  output : Fin t
  large : 5 ≤ output.val
  cutoff : ℕ
  C : ℕ
  E : ℕ
  run : ∀ (n : ℕ) (point : BitInput n) (ν : ℕ) (z : BitInput (2 ^ ν)), ν ≤ n → cutoff ≤ 2 ^ ν →
    ∀ h : g.IsCaseTwo s ν z,
    ∃ out, ClockJoin.ReadyRun M (C * (2 ^ n + 1) ^ E)
      (portInput t (CheckedPCPP.mwWord s g (2 ^ ν) (g.selectedPair s ν z h).src)
        (RepairOrdinary.frame (OuterPCPRecovery.canonicalBoundedCircuitDescription (g.bound s ν)
          (g.selectedPair s ν z h).pf))
        (RepairOrdinary.frame (List.ofFn point)) (g.width s ν) (g.bound s ν)) out ∧
      out output = RepairOrdinary.frame (g.gateCore s P (selectedAmplifier s.amplification g.degree) ν z
        (CloseoutLanguage.clauseWidth g.clauseDegree (g.width s ν)) g.positionLog n point).toNat.bits

structure Kit (s : GateSources) (P : ThreeQueryPCPP) (g : GateParams) where
  ts : ENP.TStage
  c1 : CaseOneKit s g
  ht : HTKit s P g

theorem caseOneKit_of (h : CaseOneRuns) (s : GateSources) (g : GateParams) : Nonempty (CaseOneKit s g) := by
  obtain ⟨t, st, M, output, large, C, E, run⟩ := h (selectedAmplifier s.amplification g.degree)
  exact ⟨⟨t, st, M, output, large, C, E, run⟩⟩

theorem htKit_of (h : HardTableRuns) (s : GateSources) (P : ThreeQueryPCPP) (g : GateParams) :
    Nonempty (HTKit s P g) := by
  obtain ⟨t, st, M, output, large, cutoff, C, E, run⟩ := h s P g
  exact ⟨⟨t, st, M, output, large, cutoff, C, E, run⟩⟩

theorem kit_of (hT : ENP.TStageRuns) (h1 : CaseOneRuns) (h2 : HardTableRuns) (s : GateSources)
    (P : ThreeQueryPCPP) (g : GateParams) : Nonempty (Kit s P g) := by
  obtain ⟨ts⟩ := hT
  obtain ⟨c1⟩ := caseOneKit_of h1 s g
  obtain ⟨ht⟩ := htKit_of h2 s P g
  exact ⟨⟨ts, c1, ht⟩⟩

end NearCubicGates.Close.Recovery.After
