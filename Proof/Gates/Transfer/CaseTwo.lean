import Proof.Gates.Interfaces.TransferParts

set_option autoImplicit false

namespace NearCubicGates.Close.Transfer

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.RecoveryPipeline NearCubicWires.Bindings.CLW20Lemma311
open NearCubicGates.Close.Gadget NearCubicGates.HeadlineAssembly NearCubicGates.Target

theorem refuterYes {T : ℕ → ℕ} (source : JointOrdinarySource T) (M : OrdinaryWeakMachine)
    (littleO : OrdinaryLittleO M T)
    (oneSided : ∀ n x, M.accepts n x → source.hierarchy.timedView.accepts n x = true) :
    ∃ onset, ∀ n, onset ≤ n → ¬M.accepts n (source.refuter.output M n) ∧
      source.hierarchy.timedView.accepts n (source.refuter.output M n) = true := by
  obtain ⟨onset, conflict⟩ := source.refuter.separates M littleO
  refine ⟨onset, fun n hn => ?_⟩
  have hconflict := conflict n hn
  have reject : ¬M.accepts n (source.refuter.output M n) := by
    intro accept
    have htrue := oneSided n _ accept
    have hfalse := hconflict.mp accept
    simp [htrue] at hfalse
  refine ⟨reject, ?_⟩
  cases h : source.hierarchy.timedView.accepts n (source.refuter.output M n)
  · exact False.elim (reject (hconflict.mpr h))
  · rfl

/-- Padding reads a prefix. -/
theorem padCore_eq {core target : ℕ} (f : BoolFunction core) (h : core ≤ target) :
    padCore f h = fun x => f (fun i => x ⟨i.val, lt_of_lt_of_le i.isLt h⟩) := by
  funext x
  simp only [padCore]
  congr 1

/-- The Case 2 branch of `gateCore`. -/
theorem gateCore_small (s : GateSources) (g : GateParams) (P : ThreeQueryPCPP) {c d : ℕ}
    (amplifier : OrdinaryScheduleAmplifier c d) (ν : ℕ) (z : BitInput (2 ^ ν)) (cl pl target : ℕ)
    (h : g.IsCaseTwo s ν z) (hfit : (g.D s ν (g.selectedPair s ν z h)).n + cl + pl ≤ target) :
    g.gateCore s P amplifier ν z cl pl target =
      padCore (hardTable P (g.D s ν (g.selectedPair s ν z h)) (g.selected_taut s ν z h) cl pl) hfit := by
  unfold GateParams.gateCore
  rw [dif_pos h.1, dif_pos h.2.1]
  simp only []
  rw [dif_pos h, dif_pos hfit]

open NearCubicWires.RepairSource.CloseoutLanguage in
/-- **CaseTwoPart.** -/
theorem caseTwoPart {s : GateSources} {P : ThreeQueryPCPP} {ε : ℝ} (c : GateClosure s P ε) :
    CaseTwoPart c := by
  classical
  intro hsel
  let H := s.hierarchy (fun n => n ^ (c.g.k + 2)) c.g.clock
  obtain ⟨refOnset, refReady⟩ := refuterYes H.joint c.M c.littleO c.oneSided
  obtain ⟨cOnset, hcomp⟩ := c.complete
  obtain ⟨o, hfacts⟩ := hsel.2
  obtain ⟨n0, hn0⟩ := hsel.1 (max cOnset refOnset)
  refine ⟨max o n0, fun n hn hsmall C hC => ?_⟩
  have hon : o ≤ n := le_trans (le_max_left _ _) hn
  have hn0' : n0 ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨hν1, hνsrc, hlen⟩ := hfacts n hon
  have hνbig := hn0 n hn0'
  set ν := c.g.selected s n with hνdef
  have hνc : cOnset ≤ ν := le_trans (le_max_left _ _) hνbig
  have hνr : refOnset ≤ 2 ^ ν :=
    le_trans (le_max_right _ _) (le_trans hνbig (Nat.lt_two_pow_self).le)
  have hreject : ¬ c.M.accepts (2 ^ ν) (c.input n) := (refReady (2 ^ ν) hνr).1
  -- the selected pair: sizes, CHECK, tautology
  set B := c.g.selectedPair s ν (c.input n) hsmall with hBdef
  have hD := c.g.selected_taut s ν (c.input n) hsmall
  have hsrc : B.src.size ≤ c.g.bound s ν :=
    (RecoveryChoice.oracleSelector (c.g.checkPCP s ν (c.input n)) c.g.degree (c.input n) hsmall.1).sizeBounded
  have hpf : B.pf.size ≤ c.g.bound s ν :=
    (RecoveryChoice.oracleSelector _ c.g.degree (c.input n) hsmall.2.2.2).sizeBounded
  have hcheck : Outer.Check ν (c.input n) B.src :=
    (ENP.unitOuter_check ν _ _ (c.input n) (c.input n) _ (fun _ => false)).mp
      ((RecoveryChoice.oracleSelector (c.g.checkPCP s ν (c.input n)) c.g.degree (c.input n) hsmall.1).accepts
        (fun _ => false))
  -- the native function is the padded hard table
  set cl := clauseWidth c.g.clauseDegree (c.g.width s ν)
  have hDn : (c.g.D s ν B).n = c.g.width s ν := rfl
  have hfit : (c.g.D s ν B).n + cl + c.g.positionLog ≤ c.g.nativeLength s n := by
    rw [hlen, hDn]
    unfold GateParams.coreArity GateParams.tableArity
    exact Nat.le_mul_of_pos_left _ c.ready.ampPos
  have hnative : c.nativeFn n = padCore (hardTable P (c.g.D s ν B) hD cl c.g.positionLog) hfit := by
    simp only [GateClosure.nativeFn, GateParams.native]
    rw [if_pos ⟨hν1, hνsrc⟩]
    exact gateCore_small s c.g P _ ν (c.input n) cl c.g.positionLog _ hsmall hfit
  -- restrict to the table length
  obtain ⟨small, hw, hag⟩ := exists_prefix_restriction hfit C (hardTable P (c.g.D s ν B) hD cl c.g.positionLog)
  rw [hnative, padCore_eq]
  refine lt_of_le_of_lt hag ?_
  by_contra hge
  have hge := not_lt.mp hge
  exact hreject (hcomp ν hνc (c.input n) B hsrc hpf hcheck hD small (hw ▸ hC) hge)

end NearCubicGates.Close.Transfer
