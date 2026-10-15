import Proof.Gates.Recovery.AfterOne
import Proof.Gates.Recovery.AfterStageBudget
import Proof.Gates.Recovery.CaseOneFinal
import Proof.Gates.Recovery.HTFinal

set_option autoImplicit false

namespace NearCubicGates.Close.Recovery.After

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairSource.OrdinaryOracleCompose NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicGates.Close.Transfer NearCubicGates.Close.Gadget

/-- **The clear capacity covers a polynomial**: `C (2^n + 1)^E ≤ 2^{E n + (E + C)}`. -/
theorem cap_cover (C E n : ℕ) : C * (2 ^ n + 1) ^ E ≤ CloseoutCapacity.capacity E (E + C) n := by
  unfold CloseoutCapacity.capacity
  have h1 : 2 ^ n + 1 ≤ 2 ^ (n + 1) := by rw [pow_succ]; have := Nat.one_le_two_pow (n := n); omega
  have h2 : (2 ^ n + 1) ^ E ≤ 2 ^ ((n + 1) * E) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left h1 E
  have h3 : C ≤ 2 ^ C := Nat.lt_two_pow_self.le
  have h4 : 2 ^ (E * n + (E + C)) = 2 ^ C * 2 ^ ((n + 1) * E) := by
    rw [← pow_add]; congr 1; ring
  rw [h4, Nat.mul_comm (2 ^ C)]
  calc C * (2 ^ n + 1) ^ E ≤ 2 ^ C * 2 ^ ((n + 1) * E) := Nat.mul_le_mul h3 h2
    _ = 2 ^ ((n + 1) * E) * 2 ^ C := Nat.mul_comm _ _

/-- `V^a ≤ V^b` for `a ≤ b`, `V = 2^n + 1`. -/
theorem vpow_mono (n : ℕ) {a b : ℕ} (h : a ≤ b) : (2 ^ n + 1) ^ a ≤ (2 ^ n + 1) ^ b :=
  Nat.pow_le_pow_right (Nat.succ_pos _) h

section

variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams}

/-- The constants of `qfits_bound`. -/
def qD (g : GateParams) : ℕ := 2 ^ oracleDepth g.degree

noncomputable def qC (K : Kit s P g) : ℕ := K.ts.K * (1915 + (aR s g).K) ^ K.ts.e

noncomputable def qE (K : Kit s P g) : ℕ := (2 * qD g + (aR s g).e) * K.ts.e

/-- **Stage 2's cost is a fixed polynomial in `2^n`** (paper §11.6: formulas of size `2^{O(q)}`, `q ≤ n`). -/
theorem qfits_bound (K : Kit s P g) (n ν : ℕ) (hL : Live s g n ν) :
    K.ts.K * (2 ^ g.width s ν + (39 * (g.width s ν + g.bound s ν + 5) ^ 2 + ν +
      (aR s g).K * (ν + 1) ^ (aR s g).e) + 1) ^ K.ts.e ≤ qC K * (2 ^ n + 1) ^ qE K := by
  obtain ⟨hνq, hqm, hmn⟩ := hL.width_le
  set q := g.width s ν with hq
  set V := 2 ^ n + 1 with hV
  set D := qD g with hD
  have hV1 : 1 ≤ V := Nat.le_add_left 1 _
  have hn : n < 2 ^ n := Nat.lt_two_pow_self
  have hqn : q ≤ n := by omega
  have hqV : q + 1 ≤ V := by omega
  have hD1 : 1 ≤ D := Nat.one_le_two_pow
  have hB : g.bound s ν + 1 ≤ (q + 1) ^ D := by
    unfold GateParams.bound oracleSizeBound
    exact PolynomialClock.pairIter_add_one_le_pow _ _
  have hBV : g.bound s ν + 1 ≤ V ^ D := hB.trans (Nat.pow_le_pow_left hqV D)
  set W := V ^ (2 * D + (aR s g).e) with hW
  have hVD : V ≤ V ^ D := by
    calc V = V ^ 1 := (pow_one V).symm
      _ ≤ V ^ D := Nat.pow_le_pow_right hV1 hD1
  have hW1 : V ^ D ≤ W := Nat.pow_le_pow_right hV1 (by omega)
  have hW2 : V ^ (2 * D) ≤ W := Nat.pow_le_pow_right hV1 (by omega)
  have hW3 : V ^ (aR s g).e ≤ W := Nat.pow_le_pow_right hV1 (by omega)
  have h2q : 2 ^ q ≤ V := by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hqn; omega
  have hsum : q + g.bound s ν + 5 ≤ 7 * V ^ D := by omega
  have hsq : (q + g.bound s ν + 5) ^ 2 ≤ 49 * V ^ (2 * D) := by
    calc (q + g.bound s ν + 5) ^ 2 ≤ (7 * V ^ D) ^ 2 := Nat.pow_le_pow_left hsum 2
      _ = 49 * V ^ (2 * D) := by ring
  have hνV : ν + 1 ≤ V := by omega
  have hae : (ν + 1) ^ (aR s g).e ≤ W := (Nat.pow_le_pow_left hνV _).trans hW3
  have hS : 2 ^ q + (39 * (q + g.bound s ν + 5) ^ 2 + ν + (aR s g).K * (ν + 1) ^ (aR s g).e) + 1 ≤
      (1915 + (aR s g).K) * W := by
    have e1 : 39 * (q + g.bound s ν + 5) ^ 2 ≤ 1911 * W := by
      have := Nat.mul_le_mul_left 39 hsq; nlinarith
    have e2 : (aR s g).K * (ν + 1) ^ (aR s g).e ≤ (aR s g).K * W := Nat.mul_le_mul_left _ hae
    have e3 : V ≤ W := hVD.trans hW1
    nlinarith
  calc K.ts.K * (2 ^ q + (39 * (q + g.bound s ν + 5) ^ 2 + ν + (aR s g).K * (ν + 1) ^ (aR s g).e) + 1) ^ K.ts.e
      ≤ K.ts.K * ((1915 + (aR s g).K) * W) ^ K.ts.e := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hS _)
    _ = qC K * V ^ qE K := by
      unfold qC qE
      rw [hW, Nat.mul_pow, ← pow_mul]
      ring

end

/-- The parameter facts of the after-prefix program, granted live indices. -/
theorem live_of {s : GateSources} {g : GateParams} (hR : AfterReady s g) {n ν : ℕ} (cut : ℕ) (hν : 1 ≤ ν)
    (hcut : max cut (2 ^ (g.sv s).onset) ≤ 2 ^ ν) (har : g.coreArity s ν ≤ n / 2) : Live s g n ν := by
  refine ⟨hν, har, ?_, hR.ampPos, hR.ampLarge⟩
  have h := le_trans (le_max_right _ _) hcut
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h

/-- **The assembly** (paper §11.6), from the three run segments. -/
theorem afterSupply_of_segs
    (hHead : ∀ (s : GateSources) (P : ThreeQueryPCPP) (g : GateParams) (K : Kit s P g) (c : Cfg), HeadRuns K c)
    (hMid : ∀ (s : GateSources) (P : ThreeQueryPCPP) (g : GateParams) (K : Kit s P g) (c : Cfg), MidRuns K c)
    (hTail : ∀ (s : GateSources) (P : ThreeQueryPCPP) (g : GateParams) (K : Kit s P g) (c : Cfg), TailRuns K c)
    (hT : ENP.TStageRuns) (hC : ∀ s P, Setup.CompU s P) : AfterSupply := by
  intro s P g hR
  obtain ⟨K⟩ := kit_of hT Recovery.CaseOneMachine.caseOneRuns (Recovery.hardTableRuns_of_compU hC) s P g
  obtain ⟨A, B, C0, E0, hSB⟩ := stageBudget g.degree
  let Cc := C0 + qC K
  let Ec := max E0 (qE K)
  let c : Cfg := ⟨A, B, Ec, Ec + Cc⟩
  have hSB' : StageBudgetAt g.degree c.A c.B C0 E0 := hSB
  have hcap : ∀ n, Cc * (2 ^ n + 1) ^ Ec ≤ CloseoutCapacity.capacity c.Aq c.Bq n := fun n => cap_cover Cc Ec n
  have hclr : ∀ n, C0 * (2 ^ n + 1) ^ E0 ≤ CloseoutCapacity.capacity c.Aq c.Bq n := by
    intro n
    refine le_trans ?_ (hcap n)
    exact Nat.mul_le_mul (by omega) (vpow_mono n (le_max_left _ _))
  have hQF : QFits K c := by
    intro n ν hL
    refine (qfits_bound K n ν hL).trans (le_trans ?_ (hcap n))
    exact Nat.mul_le_mul (by omega) (vpow_mono n (le_max_right _ _))
  obtain ⟨CH, EH, hH⟩ := hHead s P g K c C0 E0 hSB'
  obtain ⟨CM, EM, hM⟩ := hMid s P g K c hQF
  obtain ⟨CT, ET, hTl⟩ := hTail s P g K c C0 E0 hSB'
  obtain ⟨C1, E1, h1⟩ := caseOne_i_runs K c
  refine ⟨{
    prog := prog K c
    zPort := sh K 0
    pointPort := sh K 1
    zPoint := by change sh K 0 ≠ sh K 1; simp
    zQuery := by change sh K 0 ≠ sh K 3; simp
    pointQuery := by change sh K 1 ≠ sh K 3; simp
    zOutput := by change sh K 0 ≠ sh K 2; simp
    pointOutput := by change sh K 1 ≠ sh K 2; simp
    queryOutput := by change sh K 3 ≠ sh K 2; simp
    cutoff := max K.ht.cutoff (2 ^ (g.sv s).onset)
    C := CH + CM + CT + C1 + 5
    E := max (max EH EM) (max ET E1)
    run := ?_ }⟩
  intro n point ν z post hν hcut har
  have hL : Live s g n ν := live_of hR K.ht.cutoff hν hcut har
  have hcutHT : K.ht.cutoff ≤ 2 ^ ν := le_trans (le_max_left _ _) hcut
  have vH : CH * (2 ^ n + 1) ^ EH ≤ CH * (2 ^ n + 1) ^ max (max EH EM) (max ET E1) :=
    Nat.mul_le_mul_left _ (vpow_mono n (by omega))
  have vM : CM * (2 ^ n + 1) ^ EM ≤ CM * (2 ^ n + 1) ^ max (max EH EM) (max ET E1) :=
    Nat.mul_le_mul_left _ (vpow_mono n (by omega))
  have vT : CT * (2 ^ n + 1) ^ ET ≤ CT * (2 ^ n + 1) ^ max (max EH EM) (max ET E1) :=
    Nat.mul_le_mul_left _ (vpow_mono n (by omega))
  have v1 : C1 * (2 ^ n + 1) ^ E1 ≤ C1 * (2 ^ n + 1) ^ max (max EH EM) (max ET E1) :=
    Nat.mul_le_mul_left _ (vpow_mono n (by omega))
  have vE : 1 ≤ (2 ^ n + 1) ^ max (max EH EM) (max ET E1) := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have ve : (CH + CM + CT + C1 + 5) * (2 ^ n + 1) ^ max (max EH EM) (max ET E1) =
      CH * (2 ^ n + 1) ^ max (max EH EM) (max ET E1) + CM * (2 ^ n + 1) ^ max (max EH EM) (max ET E1) +
      CT * (2 ^ n + 1) ^ max (max EH EM) (max ET E1) + C1 * (2 ^ n + 1) ^ max (max EH EM) (max ET E1) +
      5 * (2 ^ n + 1) ^ max (max EH EM) (max ET E1) := by ring
  obtain ⟨c1, hc1, A1, f0, f1, f2, f3, f7, f8, f9, f10, f11, f12, f13, f15, f16, f17, f18, f21, f22, f23, f24, f31,
    fb, hyes, hno⟩ := hH n point ν z post hL
  by_cases hS : g.SrcExists s ν z
  · obtain ⟨tr1, f14⟩ := hyes hS
    obtain ⟨c2, hc2, A2, fr, fd, fq, fb2, hhon, hnohon⟩ := hM n ν z A1 hS hL f14 (f3.trans (hclr n)) f15 f7 f8 f9
      f16 f17 f18 (fun x hx => fb x (le_trans (off_mono K (by norm_num)) hx))
    by_cases hH2 : ∃ t, HonestTable (g.outC s ν (g.firstSrc s ν z hS)).circuit t
    · obtain ⟨tr2, ftbl⟩ := hhon hH2
      obtain ⟨c3, hc3, B3, tr3, hout⟩ := hTl n point ν z A2 hS hH2 hL hcutHT ftbl
        (by rw [fr 1 (by decide)]; exact f1) fq (by rw [fr 9 (by decide)]; exact f9)
        (by rw [fr 10 (by decide)]; exact f10) (by rw [fr 11 (by decide)]; exact f11)
        (by rw [fr 12 (by decide)]; exact f12) (by rw [fr 13 (by decide)]; exact f13)
        (by rw [fr 15 (by decide)]; exact f15) fd
        (by rw [fr 2 (by decide)]; exact f2) (by rw [fr 21 (by decide)]; exact f21)
        (by rw [fr 22 (by decide)]; exact f22) (by rw [fr 23 (by decide)]; exact f23)
        (by rw [fr 24 (by decide)]; exact f24) (by rw [fr 31 (by decide)]; exact f31)
        (fun x hx => fb2 x (le_trans (off_mono K (by norm_num)) hx))
      refine ⟨c1 + c2 + c3, ?_, B3, graph_ready (ports K) (pieces K c) 0 (next K c) (trans (trans tr1 tr2) tr3), hout⟩
      rw [ve]; omega
    · have tr2 := hnohon hH2
      obtain ⟨B3, tr3, hout⟩ := falseRuns K c n point ν z A2 hS hH2 (by rw [fr 2 (by decide)]; exact f2) fb2
      refine ⟨c1 + c2 + 5, ?_, B3, graph_ready (ports K) (pieces K c) 0 (next K c) (trans (trans tr1 tr2) tr3), hout⟩
      rw [ve]; omega
  · have tr1 := hno hS
    obtain ⟨c2, hc2, B2, tr2, hout⟩ := h1 n point ν z post A1 hL hS f0 f1 f7 f2 fb
    refine ⟨c1 + c2, ?_, B2, graph_ready (ports K) (pieces K c) 0 (next K c) (trans tr1 tr2), hout⟩
    rw [ve]; omega

end NearCubicGates.Close.Recovery.After

