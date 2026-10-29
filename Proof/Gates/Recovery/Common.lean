import Proof.Gates.Recovery.CommonRuns
import Proof.Gates.Transfer.RecoveryTarget
import Proof.Amplification.RecoveryEncodedNPVerifier
import Proof.CaseAnalysis.CloseoutRecoveryBudget

/-!
# The `E^NP` recovery of the padded native family

`sec:all-lengths`: "For completeness, all canonical choices are recoverable in E^NP. The fixed-machine refuter runs in
poly(T_clk(N_ν)) = 2^{O(q)} time with SAT access. The choices of sec:gadget-transfer are recovered in three stages …
Since q = O(n), the final functions belong to E^NP." `recoveryPart_of`: for every closure, after raising its source onset
to the refuter prefix's (the refuter's ordinary run is only guaranteed past the little-o onset of `M`), the padded native
family has an ordinary `E^NP` certificate — the common program (refuter prefix, then the after-prefix program
`AfterRun`, or `false` off the live lengths) computes it within `C (2^n + 1)^E` steps with SAT access on every final
length (`Closeout.certificate_of_runs`). `recoverySupply_of`: `Transfer.RecoverySupply` from `AfterSupply`.
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Recovery.Common

open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairSource.OrdinaryOracleCompose NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicGates.Close.Transfer NearCubicGates.Close.Gadget NearCubicGates.HeadlineAssembly

variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams}

/-- A ready run of the common program is an ordinary oracle run. -/
theorem runs_of_ready (p : Params s P g) (bits : List Bool) (b : List Bool) (cost budget : ℕ)
    (out : Fin (tapes p) → List Bool)
    (h : Ready RecoveryOracle.correctedSat (program p) cost (input p bits) out)
    (ho : out (ports p).outputTape = RepairOrdinary.frame b) (hc : cost ≤ budget) :
    OrdinaryOracleRuns RecoveryOracle.correctedSat (program p) bits b budget := by
  obtain ⟨final, ht, hh, _, hf⟩ := h
  refine ⟨cost, final, hc, ?_, hh, ?_⟩
  · rw [ordinary_input]
    exact ht
  · change final.tapes (ports p).outputTape = _
    rw [hf]
    exact ho

theorem budget_le (C E Ca Ea n : ℕ) (a b : ℕ) (ha : a ≤ C * (2 ^ n + 1) ^ E) (hb : b ≤ Ca * (2 ^ n + 1) ^ Ea) :
    a + 1 + (b + 1) ≤ (C + Ca + 8) * (2 ^ n + 1) ^ (E + Ea) := by
  have hx : 1 ≤ 2 ^ n + 1 := Nat.le_add_left 1 _
  have h1 : (2 ^ n + 1) ^ E ≤ (2 ^ n + 1) ^ (E + Ea) := Nat.pow_le_pow_right hx (Nat.le_add_right E Ea)
  have h2 : (2 ^ n + 1) ^ Ea ≤ (2 ^ n + 1) ^ (E + Ea) := Nat.pow_le_pow_right hx (Nat.le_add_left Ea E)
  have h3 : 1 ≤ (2 ^ n + 1) ^ (E + Ea) := Nat.one_le_pow _ _ hx
  have ha' := ha.trans (Nat.mul_le_mul_left C h1)
  have hb' := hb.trans (Nat.mul_le_mul_left Ca h2)
  nlinarith

/-- **The `E^NP` recovery for one closure** (`sec:all-lengths`). -/
theorem recoveryPart_of (hA : AfterSupply) {ε : ℝ} (c : GateClosure s P ε) :
    ∃ o, c.g.sourceOnset ≤ o ∧ RecoveryPart (withOnset c o) := by
  classical
  have hr : AfterReady s c.g := afterReady_of c.ready
  let ar : AfterRun s P c.g := Classical.choice (hA s P c.g hr)
  obtain ⟨onset, h1, hcut, r, As, Bs, C, E, hpre⟩ :=
    GR.NearCubicWires.RepairSource.CloseoutCommonPrefix.exists_selected (toEight s c.g) c.g.k c.g.clauseDegree
      c.g.ampFactor (c.g.positionLog - 1) (max c.g.sourceOnset ar.cutoff) 0 0 c.g.clock c.ready.clausePos c.M
      c.littleO
  let p : Params s P c.g := ⟨As, Bs, onset, 0, 0, r, ar⟩
  refine ⟨onset, le_trans (le_max_left _ _) hcut, ?_⟩
  let g' := (withOnset c onset).g
  have hr' : AfterReady s g' := ⟨hr.ampPos, hr.ampLarge, hr.positionPos, hr.clausePos⟩
  refine ⟨RecoveryOracle.correctedSat, ⟨RecoveryColdVerifier.encodedNPVerifier⟩,
    ⟨Closeout.certificate_of_runs _ (program p) (C + ar.C + 8) (E + ar.E) ?_⟩⟩
  intro n point
  have htarget := padded_eq s P g' hr' c.M n point
  have hW : GR.NearCubicWires.RepairSource.CloseoutLanguage.widthAt (toEight s c.g) c.g.k c.g.clock
      c.g.ampFactor (c.g.positionLog - 1) c.g.clauseDegree = c.g.coreArity s :=
    funext (widthAt_eq s c.g hr.positionPos)
  have hb := hpre (List.ofFn point)
  dsimp only at hb
  obtain ⟨cost, hcost, out, hrun, haddr, hflag, _, hword, hlive⟩ := hb
  rw [List.length_ofFn] at hcost
  generalize hN : GR.NearCubicWires.RepairSource.CloseoutSchedule.Framed.selectedLength
      (GR.NearCubicWires.RepairSource.CloseoutLanguage.widthAt (toEight s c.g) c.g.k c.g.clock c.g.ampFactor
        (c.g.positionLog - 1) c.g.clauseDegree) (List.ofFn point).length = N at hflag hword hlive
  rw [List.length_ofFn, hW] at hN
  have hsel : GR.NearCubicWires.RepairSource.CloseoutLanguage.selectedIndex (c.g.coreArity s) n = c.g.selected s n :=
    rfl
  unfold GR.NearCubicWires.RepairSource.CloseoutSchedule.Framed.selectedLength at hN
  rw [hsel] at hN
  have hgsel : g'.selected s n = c.g.selected s n := rfl
  by_cases hν : c.g.selected s n = 0
  · -- no live source index: `false`
    rw [if_pos hν] at hN
    subst hN
    have hf : readTapeBit (out (flagP p)) 0 = false := by
      rw [show out (flagP p) = [decide (onset ≤ 0)] from hflag]
      simp [readTapeBit, show ¬ onset ≤ 0 by omega]
    obtain ⟨final, hready, hout⟩ := inactive_ready p (List.ofFn point) cost out hrun hf
    have hval : padded (g'.nativeLength s) (g'.nativeLength_le s) (g'.native s P c.M) n point = false := by
      rw [htarget, if_neg]
      rw [hgsel, hν]
      omega
    refine runs_of_ready p (List.ofFn point) _ _ _ final hready ?_ ?_
    · rw [hout]
      change RepairOrdinary.frame false.toNat.bits =
        RepairOrdinary.frame (padded (g'.nativeLength s) (g'.nativeLength_le s) (g'.native s P c.M) n point).toNat.bits
      rw [hval]
    · have h2 : 1 ≤ (2 ^ n + 1) ^ (E + ar.E) := Nat.one_le_pow _ _ (Nat.le_add_left 1 _)
      have h3 : (2 ^ n + 1) ^ E ≤ (2 ^ n + 1) ^ (E + ar.E) :=
        Nat.pow_le_pow_right (Nat.le_add_left 1 _) (Nat.le_add_right _ _)
      have h4 := Nat.mul_le_mul_left C h3
      nlinarith
  · rw [if_neg hν] at hN
    subst hN
    set ν := c.g.selected s n with hνdef
    by_cases hon : onset ≤ 2 ^ ν
    · -- a live source index: the after-prefix program
      have hfits : 1 ≤ ν ∧ c.g.coreArity s ν ≤ n / 2 := selectedIndex_fits (c.g.coreArity s) n hν
      rw [if_pos hon] at hword
      obtain ⟨_, qlen, _, hquery⟩ := hlive hon
      have hf : readTapeBit (out (flagP p)) 0 = true := by
        rw [show out (flagP p) = [decide (onset ≤ 2 ^ ν)] from hflag]
        simp [readTapeBit, hon]
      have hcutν : ar.cutoff ≤ 2 ^ ν := le_trans (le_max_right _ _) (hcut.trans hon)
      obtain ⟨acost, hac, outA, hA', houtA⟩ := ar.run n point ν
        ((s.hierarchy (fun n => n ^ (c.g.k + 2)) c.g.clock).output c.M (2 ^ ν))
        (RepairOrdinary.frame ((s.hierarchy (fun n => n ^ (c.g.k + 2)) c.g.clock).hierarchy.time
          (List.ofFn ((s.hierarchy (fun n => n ^ (c.g.k + 2)) c.g.clock).output c.M (2 ^ ν))).length).bits)
        hfits.1 hcutν hfits.2
      have haddr' : out (addressP p) = RepairOrdinary.frame (List.ofFn point) := by
        have he := GR.NearCubicWires.RepairSource.CloseoutCommonPrefix.first_address (work s c.g) r c.g.k
        show out (GR.NearCubicWires.RepairSource.CloseoutCommonPrefix.firstSlots (work s c.g) r c.g.k
          (GR.NearCubicWires.RepairSource.CloseoutCommonPrefix.address (work s c.g) r)) = _
        rw [he]
        exact haddr
      obtain ⟨final, hready, hout⟩ := live_ready p (List.ofFn point) cost out hrun hf _ hword haddr' qlen hquery
        acost outA hA'
      have hval : padded (g'.nativeLength s) (g'.nativeLength_le s) (g'.native s P c.M) n point =
          c.g.gateCore s P (selectedAmplifier s.amplification c.g.degree) ν
            ((s.hierarchy (fun n => n ^ (c.g.k + 2)) c.g.clock).output c.M (2 ^ ν))
            (clauseWidth c.g.clauseDegree (c.g.width s ν)) c.g.positionLog n point := by
        rw [htarget, if_pos]
        · rfl
        · exact ⟨hfits.1, hon⟩
      refine runs_of_ready p (List.ofFn point) _ _ _ final hready ?_ ?_
      · rw [hout, houtA]
        exact congrArg (fun b : Bool => RepairOrdinary.frame b.toNat.bits) hval.symm
      · exact budget_le C E ar.C ar.E n cost acost hcost hac
    · -- below the onset: `false`
      have hf : readTapeBit (out (flagP p)) 0 = false := by
        rw [show out (flagP p) = [decide (onset ≤ 2 ^ ν)] from hflag]
        simp [readTapeBit, hon]
      obtain ⟨final, hready, hout⟩ := inactive_ready p (List.ofFn point) cost out hrun hf
      have hval : padded (g'.nativeLength s) (g'.nativeLength_le s) (g'.native s P c.M) n point = false := by
        rw [htarget, if_neg]
        rintro ⟨_, h⟩
        exact hon h
      refine runs_of_ready p (List.ofFn point) _ _ _ final hready ?_ ?_
      · rw [hout]
        change RepairOrdinary.frame false.toNat.bits =
          RepairOrdinary.frame (padded (g'.nativeLength s) (g'.nativeLength_le s) (g'.native s P c.M) n point).toNat.bits
        rw [hval]
      · have h2 : 1 ≤ (2 ^ n + 1) ^ (E + ar.E) := Nat.one_le_pow _ _ (Nat.le_add_left 1 _)
        have h3 : (2 ^ n + 1) ^ E ≤ (2 ^ n + 1) ^ (E + ar.E) :=
          Nat.pow_le_pow_right (Nat.le_add_left 1 _) (Nat.le_add_right _ _)
        have h4 := Nat.mul_le_mul_left C h3
        nlinarith

/-- **`Transfer.RecoverySupply` from the after-prefix program.** -/
theorem recoverySupply_of (hA : AfterSupply) : RecoverySupply :=
  fun _s _P _ε c => recoveryPart_of hA c

end NearCubicGates.Close.Recovery.Common
