import Proof.Gates.Recovery.TableSem

set_option autoImplicit false

namespace NearCubicGates.Close.Recovery.HTCore

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.Bindings.CLW20Lemma311
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close.Recovery.TableSem
open NearCubicWires.RepairOrdinary.RadixSemantics (value)

/-- The Case 2 branch of `gateCore` without a fit: `false` (`sec:gadget-extract`, `sec:all-lengths`: the table is
padded only when it
fits the target arity). -/
theorem gateCore_two_nofit (s : GateSources) (g : GateParams) (P : ThreeQueryPCPP) {c d : ℕ}
    (amplifier : OrdinaryScheduleAmplifier c d) (ν : ℕ) (z : BitInput (2 ^ ν)) (cl pl target : ℕ)
    (h : g.IsCaseTwo s ν z) (hfit : ¬(g.D s ν (g.selectedPair s ν z h)).n + cl + pl ≤ target) :
    g.gateCore s P amplifier ν z cl pl target = fun _ => false := by
  unfold GateParams.gateCore
  rw [dif_pos h.1, dif_pos h.2.1]
  simp only []
  rw [dif_pos h, dif_neg hfit]

theorem gateCore_two_point (s : GateSources) (g : GateParams) (P : ThreeQueryPCPP) {c d : ℕ}
    (amplifier : OrdinaryScheduleAmplifier c d) (ν : ℕ) (z : BitInput (2 ^ ν)) (cl pl n : ℕ) (point : BitInput n)
    (h : g.IsCaseTwo s ν z) :
    g.gateCore s P amplifier ν z cl pl n point =
      if hfit : g.width s ν + cl + pl ≤ n then
        let D := g.D s ν (g.selectedPair s ν z h)
        let xp : BitInput D.n := fun i => point ⟨i.val, by
          have := i.isLt; change i.val < g.width s ν at this; omega⟩
        tableBit (P.output (checkedCircuit P.code D))
          (List.ofFn (Fin.addCases (sysEnc P.code D.n xp)
            (P.honest (acceptedInput P.code D xp (g.selected_taut s ν z h xp))) :
            BitInput ((checkedCircuit P.code D).n + (P.output (checkedCircuit P.code D)).proofBits)))
          (value (List.ofFn fun i : Fin cl => point ⟨g.width s ν + i.val, by omega⟩))
          (value (List.ofFn fun i : Fin pl => point ⟨g.width s ν + cl + i.val, by omega⟩))
      else false := by
  by_cases hfit : g.width s ν + cl + pl ≤ n
  · rw [dif_pos hfit, gateCore_small s g P amplifier ν z cl pl n h hfit, padCore_eq]
    dsimp only
    rw [hardTable_eq, natOfBits_eq_value, natOfBits_eq_value]
    rfl
  · rw [dif_neg hfit, gateCore_two_nofit s g P amplifier ν z cl pl n h hfit]

end NearCubicGates.Close.Recovery.HTCore
