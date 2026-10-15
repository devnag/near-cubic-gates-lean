import Proof.Gates.Expand.PolyTabTail1
import Proof.Gates.Expand.PolyTabTail2
import Proof.Gates.Expand.PolyTabVal

set_option autoImplicit false

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.Tabulator NearCubicGates.Close.TabMachine NearCubicGates.Close.Interfaces.Formats
open NearCubicWires.RepairOrdinary.CompetitorCrossScheduler (producer)

/-- **The tail program.** -/
noncomputable def tailP (te : ℕ) (a : WilliamsAlgorithm) : WMX (NSx te (Qa a)) NRk :=
  .seq (cutM sZ rY (sP 0)) (.seq bregs (back a sP sQ sOUT (rB 0) (rB 1) (rB 2) (rB 3) (rB 4) (rB 5) (rB 6) (rB 7)
    (rB 8) (rB 9)))

theorem pq_eq {te qa : ℕ} (i : Fin 130) (j : Fin qa) (h : sP (te := te) (qa := qa) i = sQ j) : i = 128 ∧ j.val = 0 := by
  have := congrArg Fin.val h
  simp only [sP_val, sQ_val, qv] at this
  split_ifs at this with hj
  · exact ⟨Fin.ext (by simp; omega), hj⟩
  · omega

/-- `2x ≤ 2^x` for `x ≥ 1`. -/
theorem two_mul_le_pow (x : ℕ) (hx : 1 ≤ x) : 2 * x ≤ 2 ^ x := by
  induction x with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have := ih hn; rw [pow_succ]; omega

/-- `4x ≤ 2^x` for `x ≥ 4`. -/
theorem four_mul_le_pow (x : ℕ) (hx : 4 ≤ x) : 4 * x ≤ 2 ^ x := by
  induction x with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 4 with h | h
    · interval_cases n <;> simp_all
    · have := ih h; rw [pow_succ]; omega

/-- The register program's cap (from `TailPre.capBig`). -/
theorem cap_bregs (E : ExpandMachine) (r : TabReq) (cap : ℕ) (hbig : 2 ^ (2 * (r.s + Wdk E r + 10)) ≤ cap) :
    2 ^ (2 * ((r.s + 1) / 2)) + 2 * ((r.s + 1) / 2) + 2 * Wdk E r + 10 ≤ cap ∧
      ∀ n q : ℕ, n ≤ 2 ^ (r.s + 1) → q = (r.s + 1) / 2 + 2 * Wdk E r + 5 → n * (2 * q + 3) + 2 * q + 4 ≤ cap := by
  have hX : 2 ^ (2 * (r.s + Wdk E r + 10)) = 2 ^ (r.s + 1) * 2 ^ (r.s + 2 * Wdk E r + 19) := by
    rw [← pow_add]; congr 1; omega
  have hX2 := two_mul_le_pow (r.s + 2 * Wdk E r + 19) (by omega)
  have h2 : 2 ≤ 2 ^ (r.s + 1) := by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show 1 ≤ r.s + 1 by omega); simpa using this
  have h3 : 2 ≤ 2 ^ (r.s + 2 * Wdk E r + 19) := by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show 1 ≤ r.s + 2 * Wdk E r + 19 by omega); simpa using this
  have hab := Nat.add_le_mul h2 h3
  have hp2d : 2 ^ (2 * ((r.s + 1) / 2)) ≤ 2 ^ (r.s + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine ⟨by omega, fun n q hn hq => ?_⟩
  have hX4 := four_mul_le_pow (r.s + 2 * Wdk E r + 19) (by omega)
  have a1 : n * (2 * q + 3) + 2 * q + 4 ≤ (2 ^ (r.s + 1) + 1) * (2 * q + 4) := by
    have := Nat.mul_le_mul_right (2 * q + 4) (show n + 1 ≤ 2 ^ (r.s + 1) + 1 by omega)
    have e : (n + 1) * (2 * q + 4) = n * (2 * q + 3) + n + 2 * q + 4 := by ring
    omega
  have a2 : (2 ^ (r.s + 1) + 1) * (2 * q + 4) ≤ 2 ^ (r.s + 1) * (4 * q + 8) := by
    have e1 : (2 ^ (r.s + 1) + 1) * (2 * q + 4) = 2 ^ (r.s + 1) * (2 * q + 4) + (2 * q + 4) := by ring
    have e2 : 2 ^ (r.s + 1) * (4 * q + 8) = 2 ^ (r.s + 1) * (2 * q + 4) + 2 ^ (r.s + 1) * (2 * q + 4) := by ring
    have : 2 * q + 4 ≤ 2 ^ (r.s + 1) * (2 * q + 4) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have a3 : 2 ^ (r.s + 1) * (4 * q + 8) ≤ 2 ^ (r.s + 1) * 2 ^ (r.s + 2 * Wdk E r + 19) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

section Streams
variable (E : ExpandMachine) (a : WilliamsAlgorithm) (r : TabReq) (cap : ℕ)
  (σ τ : WState (NSx E.wf.program.tapeCount (Qa a)) NRk)

theorem notCut (x : Fin (NSx E.wf.program.tapeCount (Qa a) + 1)) (hz : ∀ i, x ≠ sZ i) (h0 : x ≠ sP 0) :
    x ∉ (sP 0 :: cutIdx.map sZ) := by
  intro hm
  simp only [List.mem_cons, List.mem_map] at hm
  rcases hm with e | ⟨i, -, e⟩
  · exact h0 e
  · exact hz i e.symm

theorem p_ne_z (i : Fin 130) (k : Fin 64) : sP (te := E.wf.program.tapeCount) (qa := Qa a) i ≠ sZ k := by
  have := i.isLt; have := k.isLt; polyTabNe

theorem q_ne_z (j : Fin (Qa a)) (k : Fin 64) : sQ (te := E.wf.program.tapeCount) j ≠ sZ k := by
  have := j.isLt; have := k.isLt; polyTabNe

theorem out_ne_z (k : Fin 64) : sOUT (te := E.wf.program.tapeCount) (qa := Qa a) ≠ sZ k := by
  have := k.isLt; polyTabNe

theorem q_ne_p0 (j : Fin (Qa a)) : sQ (te := E.wf.program.tapeCount) j ≠ sP 0 := by
  have := j.isLt; polyTabNe

theorem out_ne_p0 : sOUT (te := E.wf.program.tapeCount) (qa := Qa a) ≠ sP 0 := by polyTabNe

theorem tail_streams (h : TailPre E a r cap σ) (c2 : τ.sh (sP 0) = 0)
    (s1 : ∀ x, x ∉ (sP 0 :: cutIdx.map sZ) → τ.st x = σ.st x ∧ τ.sh x = σ.sh x) :
    (∀ i, i ≠ 0 → τ.st (sP i) = []) ∧ (∀ i, τ.sh (sP i) = 0) ∧ (∀ j : Fin (Qa a), j.val ≠ 0 → τ.st (sQ j) = []) ∧
      (∀ j, τ.sh (sQ j) = 0) ∧ τ.st sOUT = [] ∧ τ.sh sOUT = 0 := by
  have hP : ∀ i, i ≠ 0 → τ.st (sP i) = σ.st (sP i) ∧ τ.sh (sP i) = σ.sh (sP i) := fun i hi =>
    s1 _ (notCut E a _ (p_ne_z E a i) (fun e => hi (sP.injective e)))
  have hQ : ∀ j, τ.st (sQ j) = σ.st (sQ j) ∧ τ.sh (sQ j) = σ.sh (sQ j) := fun j =>
    s1 _ (notCut E a _ (q_ne_z E a j) (q_ne_p0 E a j))
  have hO := s1 _ (notCut E a _ (out_ne_z E a) (out_ne_p0 E a))
  refine ⟨fun i hi => (hP i hi).1.trans (h.pBlank i).1, fun i => ?_, fun j _ => (hQ j).1.trans (h.qBlank j).1,
    fun j => (hQ j).2.trans (h.qBlank j).2, hO.1.trans h.outBlank.1, hO.2.trans h.outBlank.2⟩
  by_cases hi : i = 0
  · subst hi; exact c2
  · exact (hP i hi).2.trans (h.pBlank i).2

end Streams

theorem out_ne_p {te : ℕ} (a : WilliamsAlgorithm) (i : Fin 130) : sOUT (te := te) (qa := Qa a) ≠ sP i := by
  have := i.isLt; have : 124 ≤ Qa a := by unfold Qa; omega
  polyTabNe

theorem out_ne_q {te qa : ℕ} (j : Fin qa) : sOUT (te := te) (qa := qa) ≠ sQ j := by have := j.isLt; polyTabNe

/-- The value: the back end's printed list is the table in `printerOrder`. -/
theorem tail_value (E : ExpandMachine) (r : TabReq) :
    recStream ((pvals (inp E r).odd (wdOf (inp E r))).map fun z => binary (qOf (inp E r) + 1) (SInt.encS z)) =
      tableWord (CounterMachine.printerOrder r.s) (width E r) r := by
  unfold inp
  rw [pvals_input (tabT E r) (Wdk E r) (fits_Wd E r) (s67 r) (capT E r)]
  unfold tableWord
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, tabT_target]
  rfl

/-- **PolyTab tail.** -/
theorem tail_spec (E : ExpandMachine) (a : WilliamsAlgorithm) (r : TabReq) (cap : ℕ)
    (σ : WState (NSx E.wf.program.tapeCount (Qa a)) NRk) (h : TailPre E a r cap σ) :
    Runs cap (tailP E.wf.program.tapeCount a) σ (tailCost E a r)
      (fun τ => τ.st sOUT = tableWord (CounterMachine.printerOrder r.s) (width E r) r) := by
  obtain ⟨hcapB, hcapC⟩ := cap_bregs E r cap h.capBig
  have hd1 : 1 ≤ (r.s + 1) / 2 := by have := s67 r; omega
  refine Runs.seq (cut_run E a r cap σ h) fun τ1 hc => ?_
  obtain ⟨c1, c2, c3⟩ := hc
  have v1 : ∀ x, x ∉ [rY 74] → τ1.val x = σ.val x := c3.2.1
  have vY : ∀ i : Fin 112, i ≠ 74 → τ1.val (rY i) = σ.val (rY i) := fun i hi =>
    v1 _ (by simp only [List.mem_singleton]; exact fun e => hi (rY.injective e))
  have vB : ∀ j : Fin 10, τ1.val (rB j) = 0 := fun j => by
    rw [v1 _ (by simp only [List.mem_singleton]; exact fun e => rB_ne_rY j 74 e)]; exact h.bRegs j
  have hb := bregs_spec (te := E.wf.program.tapeCount) (qa := Qa a) cap ((r.s + 1) / 2) (Wdk E r)
    (decide (r.s % 2 = 1)) τ1
    (by rw [vY 100 (by decide)]; exact h.y100) (by rw [vY 101 (by decide)]; exact h.y101)
    (by rw [vY 103 (by decide)]; exact h.y103) (by rw [vY 105 (by decide)]; exact h.y105)
    (by rw [vY 106 (by decide)]; exact h.y106) (by rw [vY 107 (by decide)]; exact h.y107) vB hcapB
  refine Runs.seq hb fun τ2 hτ2 => ?_
  obtain ⟨tp, tph, tq, tqh, tO, tOh⟩ := tail_streams E a r cap σ τ1 h c2 c3.1
  have hN : τ2.val (rB 0) = nOf (inp E r) := by
    rw [hτ2.b0]; unfold nOf; rw [inp_d, inp_odd, nOf_pow _ _ hd1]
  have hQ : τ2.val (rB 2) = qOf (inp E r) := by rw [hτ2.b2]; unfold qOf; rw [inp_d, inp_p]
  have hQ1 : τ2.val (rB 3) = qOf (inp E r) - 1 := by rw [hτ2.b3]; unfold qOf; rw [inp_d, inp_p]
  have hODD : τ2.val (rB 9) = (inp E r).odd.toNat := by rw [hτ2.b9, inp_odd]
  have hnOf : nOf (inp E r) ≤ 2 ^ (r.s + 1) := by
    rw [← hN, hτ2.b0]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hqOf : qOf (inp E r) = (r.s + 1) / 2 + 2 * Wdk E r + 5 := by unfold qOf; rw [inp_d, inp_p]
  have hback := back_spec cap a (pmap := sP (te := E.wf.program.tapeCount) (qa := Qa a)) (qmap := sQ) (OUT := sOUT)
    (NR := rB 0) (N2 := rB 1) (QR := rB 2) (Q1R := rB 3) (K2 := rB 4) (CO := rB 5) (CP := rB 6) (TOP := rB 7)
    (SEEN := rB 8) (ODDR := rB 9) sP.injective sQ.injective (sQ_zero _ rfl)
    (fun i j e => by obtain ⟨h1, h2⟩ := pq_eq i j e; exact ⟨h1, Fin.ext h2⟩)
    (fun i => (out_ne_p a i).symm) (fun j => (out_ne_q j).symm) (by polyTabNe) (inp E r) τ2
    (by rw [hτ2.st]; exact c1) (fun i hi => by rw [hτ2.st]; exact tp i hi)
    (fun j hj => by rw [hτ2.st]; exact tq j (fun e => hj (Fin.ext e)))
    (fun i => by rw [hτ2.sh]; exact tph i) (fun j => by rw [hτ2.sh]; exact tqh j) (by rw [hτ2.st]; exact tO)
    (by rw [hτ2.sh]; exact tOh) hN hQ hQ1 hODD hτ2.b1 hτ2.b4 hτ2.b5 hτ2.b6 hτ2.b7 hτ2.b8 (inp_hg E r)
    (hcapC _ _ hnOf hqOf)
  exact hback.post fun τ hτ => hτ.1.trans (tail_value E r)

end NearCubicGates.Close.Expand.PolyTab
