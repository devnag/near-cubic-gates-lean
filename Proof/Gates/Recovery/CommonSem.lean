import Proof.Gates.Recovery.AfterSpec
import Proof.Gates.Transfer.CaseTwo

/-!
# The padded native family, read at the full final length

`sec:all-lengths`: "pad the function in either case to exactly m(q) = K_amp q₀(q) inputs, ignoring a suffix … For a final
length n, choose the largest ν with m(q(N_ν)) ≤ n/2. When none exists, set the slice to zero." The native function at
length `n` is the gate core padded to `m(q(N_ν))`; the padded family reads it on the first `m(q(N_ν))` bits of the
final address. `gateCore_prefix`: padding first to `t ≥ m(q(N_ν))` and then to `m ≥ t` reads the same prefix as padding
straight to `m` (both branches fit in `m(q(N_ν))`: the hard table has `q + ⌈d_G lg(q+2)⌉ + log₂P ≤ m(q)` inputs, the
amplified function at most `m(q)` by `K_amp ≥ a_G`). `padded_eq`: the padded native family at `(n, x)` is the gate core
at the full length `n`, or `false` off the live lengths — exactly the value the after-prefix program prints.
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Recovery

open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairOrdinary NearCubicWires.RecoveryPipeline
open NearCubicWires.RepairSource.CloseoutLanguage NearCubicGates.Close.Transfer NearCubicGates.Close.Gadget
open NearCubicGates.HeadlineAssembly

variable (s : GateSources) (P : ThreeQueryPCPP) (g : GateParams)

/-- Padding first to `t` and then to `m ≥ t` reads the same prefix as padding straight to `m`, once `t ≥ m(q(N_ν))`. -/
theorem gateCore_prefix (hr : AfterReady s g) (ν : ℕ) (z : BitInput (2 ^ ν)) (t m : ℕ) (htm : t ≤ m)
    (hfit : g.coreArity s ν ≤ t) (x : BitInput m) :
    g.gateCore s P (selectedAmplifier s.amplification g.degree) ν z (clauseWidth g.clauseDegree (g.width s ν))
        g.positionLog t (fun i => x ⟨i.val, lt_of_lt_of_le i.isLt htm⟩) =
      g.gateCore s P (selectedAmplifier s.amplification g.degree) ν z (clauseWidth g.clauseDegree (g.width s ν))
        g.positionLog m x := by
  classical
  have htab : g.width s ν + clauseWidth g.clauseDegree (g.width s ν) + g.positionLog ≤ g.coreArity s ν := by
    unfold GateParams.coreArity GateParams.tableArity
    exact Nat.le_mul_of_pos_left _ hr.ampPos
  have hamp : ∀ f : BoolFunction (g.width s ν),
      ((selectedAmplifier s.amplification g.degree).output (g.width s ν) f).arity ≤ g.coreArity s ν := by
    intro f
    have hq : 1 ≤ g.width s ν := by have := g.nu_lt_width s ν; omega
    refine ((selectedAmplifier s.amplification g.degree).arityBound _ f hq).trans ?_
    unfold GateParams.coreArity GateParams.tableArity
    exact Nat.mul_le_mul hr.ampLarge (by omega)
  have hampl : ∀ f : BoolFunction (g.width s ν),
      GateParams.amplified (selectedAmplifier s.amplification g.degree) (g.width s ν) f t
          (fun i => x ⟨i.val, lt_of_lt_of_le i.isLt htm⟩) =
        GateParams.amplified (selectedAmplifier s.amplification g.degree) (g.width s ν) f m x := by
    intro f
    unfold GateParams.amplified
    rw [dif_pos ((hamp f).trans hfit), dif_pos (((hamp f).trans hfit).trans htm), padCore_eq, padCore_eq]
  unfold GateParams.gateCore
  by_cases h1 : g.SrcExists s ν z
  · rw [dif_pos h1, dif_pos h1]
    by_cases h2 : ∃ t, HonestTable (g.outC s ν (g.firstSrc s ν z h1)).circuit t
    · rw [dif_pos h2, dif_pos h2]
      by_cases h : g.IsCaseTwo s ν z
      · simp only []
        rw [dif_pos h, dif_pos h]
        have hD : (g.D s ν (g.selectedPair s ν z h)).n + clauseWidth g.clauseDegree (g.width s ν) + g.positionLog ≤
            g.coreArity s ν := htab
        rw [dif_pos (hD.trans hfit), dif_pos ((hD.trans hfit).trans htm), padCore_eq, padCore_eq]
      · simp only []
        rw [dif_neg h, dif_neg h]
        exact hampl _
    · rw [dif_neg h2, dif_neg h2]
  · rw [dif_neg h1, dif_neg h1]
    exact hampl _

/-- **The padded native family at `(n, x)`**: the gate core at the full length `n` on the live lengths, `false`
otherwise. -/
theorem padded_eq (hr : AfterReady s g) (M : OrdinaryWeakMachine) (n : ℕ) (x : BitInput n) :
    padded (g.nativeLength s) (g.nativeLength_le s) (g.native s P M) n x =
      if 1 ≤ g.selected s n ∧ g.sourceOnset ≤ 2 ^ g.selected s n then
        g.gateCore s P (selectedAmplifier s.amplification g.degree) (g.selected s n)
          ((s.hierarchy (fun n => n ^ (g.k + 2)) g.clock).output M (2 ^ g.selected s n))
          (clauseWidth g.clauseDegree (g.width s (g.selected s n))) g.positionLog n x
      else false := by
  classical
  unfold padded GateParams.native
  by_cases hlive : 1 ≤ g.selected s n ∧ g.sourceOnset ≤ 2 ^ g.selected s n
  · rw [if_pos hlive, if_pos hlive]
    have hν0 : g.selected s n ≠ 0 := by omega
    have hfits : 1 ≤ g.selected s n ∧ g.coreArity s (g.selected s n) ≤ n / 2 :=
      selectedIndex_fits (g.coreArity s) n hν0
    have hlen : g.nativeLength s n = g.coreArity s (g.selected s n) := by
      unfold GateParams.nativeLength
      exact min_eq_left (hfits.2.trans (Nat.div_le_self n 2))
    exact gateCore_prefix s P g hr (g.selected s n) _ (g.nativeLength s n) n (g.nativeLength_le s n)
      (le_of_eq hlen.symm) x
  · rw [if_neg hlive, if_neg hlive]

end NearCubicGates.Close.Recovery
