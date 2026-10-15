import Proof.Gates.Cells.CellLoop

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicGates.Close.CounterMachine

variable {C : Ctx}

def cellBody (gP sysPr : St VV MM) : St VV MM :=
  .seq blkP (.ite (.eq cPass v1) (passP gP sysPr) (.op (.inc vUnc)))

def blkCost (R W : ℕ) : ℕ := 1 + (1 + (R + 1 + (R * (12 * W + 12 + 1 + (1 + 1 + 20) + 4) + 4) + 1) + 1) + 1

section B
variable {B1 B2 cT : ℕ} (c : Call) (p : Params) (wt : Wit c.n) (hadm : c.Admitted B1 B2)
  (hs : Spec cT (header c) p) (w : List Bool) (hw : decodeWitness c p w = some wt)

include hs hw in
theorem cb_eq : cellBits wt.I = c.n - p.k := by
  have h1 := card_cells wt.I
  have h2 := cells_card c p wt (decodeWitness_card c p w wt hw)
  rw [h1] at h2
  exact Nat.pow_right_injective (le_refl 2) h2

include hs in
theorem reqIds_lt_pow (Big Wd : ℕ) (hWd : wdNeed c p wt Big ≤ Wd) : (reqIds c p).length < 2 ^ Wd := by
  rw [reqIds_len]
  have h1 := requestCount_le c p hs
  have h2 := P_le_n c p hs
  have hwd : 256 * (p.J + 4) * (Big + c.n + 16) + 4 * recWidth c p wt ≤ Wd := hWd
  have h3 : p.P ^ (2 * p.J + 4) ≤ (2 ^ c.n) ^ (2 * p.J + 4) :=
    Nat.pow_le_pow_left (h2.trans Nat.lt_two_pow_self.le) _
  have h4 : (2 ^ c.n) ^ (2 * p.J + 4) = 2 ^ (c.n * (2 * p.J + 4)) := by rw [← pow_mul]
  have h5 : c.n * (2 * p.J + 4) < Wd := by nlinarith
  have h6 : 2 ^ (c.n * (2 * p.J + 4)) < 2 ^ Wd := Nat.pow_lt_pow_right (by norm_num) h5
  omega

open Classical in
include hadm hs hw in
/-- **One cell.** -/
theorem cellBody_spec (S : SolveMachine) (gP sysPr : St VV MM) (tg : Ctx → Call → Params → ℕ → ℕ)
    (ts : SolveMachine → Ctx → Call → Params → ℕ → ℕ) (hG : GatherGoal gP tg) (hS : SysGoal sysPr ts)
    (hK : C.K = Callee.ofSolve S) (Big : ℕ) (hBig : ∀ x ∈ cellN c p wt, natBitLength x ≤ Big)
    (hWd : wdNeed c p wt Big ≤ C.Wd)
    (hLB : ∀ (y : Cells wt.I) part κ, κ ∈ digitVectors c p wt y →
      (sysWord (sysOf c p wt y κ part)).length ≤ C.Lk ∧ S.budget (sysOf c p wt y κ part) ≤ C.Bk)
    (pre : List Bool) (hinp : C.inp = pre ++ cellWord c p wt)
    (i : ℕ) (hi : i < 2 ^ cellBits wt.I) (a : DS VV MM) (hI : Iface c p wt a) (hSt : Sto c p wt a)
    (hip : a.ip = pre.length + i * ((reqIds c p).length * (2 * recWidth c p wt + 1)))
    (hcI : a.env cI = i) (hcnt : a.env vCnt ≤ i * 2 ^ p.k) (hunc : a.env vUnc ≤ i) :
    Hs C (cellBody gP sysPr) a (blkCost (reqIds c p).length (recWidth c p wt) + 3 +
      passCost c.n (cellN c p wt).length (ctrL c p wt (cellOf wt.I i)).length
      (kxL c p wt (cellOf wt.I i)).length (gWork c p wt (cellOf wt.I i)) (formsCost (cellN c p wt).length c.n)
      (tg C c p Big) (ts S C c p Big)) (fun b =>
      Iface c p wt b ∧ Sto c p wt b ∧
      b.ip = pre.length + (i + 1) * ((reqIds c p).length * (2 * recWidth c p wt + 1)) ∧
      (b.env vCnt : ℚ) = a.env vCnt +
        (if CellTests c p wt (cellOf wt.I i) then cellCount c p wt (cellOf wt.I i) else 0) ∧
      b.env vCnt ≤ (i + 1) * 2 ^ p.k ∧
      b.env vUnc = a.env vUnc + (if CellTests c p wt (cellOf wt.I i) then 0 else 1) ∧ b.env cI = a.env cI) := by
  have hwd : 256 * (p.J + 4) * (Big + c.n + 16) + 4 * recWidth c p wt ≤ C.Wd := hWd
  have hcb := cb_eq c p wt hs w hw
  have hk : p.k < c.n := hs.k_lt
  have hpos : 0 < 256 * (p.J + 4) * (Big + c.n + 16) := by positivity
  have hn2 : 2 ^ cellBits wt.I * 2 ^ p.k = 2 ^ c.n := by rw [← pow_add, hcb]; congr 1; omega
  have hRec : recWidth c p wt = cellBits wt.I + keyW c p + valueWidth c p := rfl
  have hRW := reqIds_lt_pow c p wt hs Big C.Wd hWd
  have hpw : ∀ m, m ≤ recWidth c p wt → 2 * 2 ^ m ≤ 2 ^ C.Wd := by
    intro m hm; rw [← pow_succ']; exact pw_mono (by omega)
  have htv : TestVals a C := ⟨by rw [hI.VW]; positivity, by rw [hI.KW]; positivity, by rw [hI.KF]; positivity,
    by rw [hI.VW]; exact hpw _ (by omega), by rw [hI.KW]; exact hpw _ (by omega),
    by rw [hI.KF]; exact hpw _ (by omega)⟩
  have hcw : C.inp.drop a.ip = (blk c p wt i).flatMap (fun x => RepairOrdinary.frame (binary (recWidth c p wt) x)) ++
      (cellWord c p wt).drop ((i + 1) * ((reqIds c p).length * (2 * recWidth c p wt + 1))) := by
    rw [hinp, hip, ← List.drop_drop, List.drop_append_length, cellWord_drop c p wt hs w hw i hi]; rfl
  have hB : ∀ x ∈ blk c p wt i, x < 2 ^ recWidth c p wt := by
    intro x hx
    obtain ⟨id, hid, rfl⟩ := mem_blk c p wt hx
    have h1 := (cellRec_bounds c p wt hs w hw i id hid).2
    have h2 : (i + 1) * 2 ^ (keyW c p + valueWidth c p) ≤ 2 ^ cellBits wt.I * 2 ^ (keyW c p + valueWidth c p) :=
      Nat.mul_le_mul_right _ hi
    rw [← pow_add] at h2
    rw [hRec, Nat.add_assoc]; omega
  have hold : (a.ram sCT).length ≤ (blk c p wt i).length ∧ a.rc sCT ≤ (a.ram sCT).length :=
    ⟨by rw [blk_length]; exact hSt.lCT, hSt.rcur sCT⟩
  have hb := blkP_spec (C := C) a hI.cst htv (recWidth c p wt) (blk c p wt i) _ hcw hB (by omega)
    (by rw [hI.R, blk_length]) (by rw [blk_length]; exact hRW) hold
  refine Hs.bseq (Hs.mono hb (show 1 + (1 + (a.rc sCT + 1 + ((blk c p wt i).length * (12 * recWidth c p wt + 12 + 1 +
      (1 + 1 + 20) + 4) + 4) + 1) + 1) + 1 ≤ blkCost (reqIds c p).length (recWidth c p wt) by
      unfold blkCost; rw [blk_length]; have := hSt.lCT; have := hSt.rcur sCT; omega) (fun _ h => h))
    (by omega) (fun e1 ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ => ?_)
  have hkk := decodeWitness_card c p w wt hw
  have htest : (blk c p wt i).all (fun x => decide (recOKm (a.env p2VW) (a.env p2K) (a.env p2KF) (a.env pTH)
      (a.env pTL) x)) = true ↔ CellTests c p wt (cellOf wt.I i) := by
    rw [List.all_eq_true, ← tests_iff c p wt hs w hw i, hI.VW, hI.KW, hI.KF, hI.TH, hI.TL]
    simp only [decide_eq_true_eq]
    apply forall₂_congr
    intro x _
    unfold recOKm recOK
    have hm : x % 2 ^ valueWidth c p < 2 ^ valueWidth c p := Nat.mod_lt _ (by positivity)
    simp only [lt_min_iff, hm, and_true]
  have I1 : Iface c p wt e1 := hI.of_fr b9 (by decide)
  have S1 : Sto c p wt e1 := by
    refine ⟨by rw [b2, Function.update_of_ne (by decide), hSt.sN], by rw [b2, Function.update_of_ne (by decide), hSt.sP],
      by rw [b2, Function.update_of_ne (by decide), hSt.sR], by rw [b2, Function.update_self, blk_length],
      by rw [b2, Function.update_of_ne (by decide)]; exact hSt.lZb, fun y => ?_, fun y => ?_, fun y => ?_, fun y => ?_,
      fun y => ?_, fun m => ?_, by rw [b5, hSt.out], by rw [b6, hSt.kin], by rw [b7, b8]; exact hSt.kc⟩
    · rw [b2, Function.update_of_ne (by decide)]; exact hSt.lE y
    · rw [b2, Function.update_of_ne (by decide)]; exact hSt.lX y
    · rw [b2, Function.update_of_ne (by decide)]; exact hSt.lG y
    · rw [b2, Function.update_of_ne (by decide)]; exact hSt.lB y
    · rw [b2, Function.update_of_ne (by decide)]; exact hSt.lA y
    · by_cases hm : m = sCT
      · subst hm; rw [b2, b3, Function.update_self, Function.update_self]
      · rw [b2, b3, Function.update_of_ne hm, Function.update_of_ne hm]; exact hSt.rcur m
  have e1ip : e1.ip = pre.length + (i + 1) * ((reqIds c p).length * (2 * recWidth c p wt + 1)) := by
    rw [b4, hip, blk_length]; ring
  have e1cI : e1.env cI = i := by rw [b9 cI (by decide)]; exact hcI
  have e1cnt : e1.env vCnt = a.env vCnt := b9 vCnt (by decide)
  have e1unc : e1.env vUnc = a.env vUnc := b9 vUnc (by decide)
  refine Hs.mono (Hs.ite (t := passCost c.n (cellN c p wt).length (ctrL c p wt (cellOf wt.I i)).length
      (kxL c p wt (cellOf wt.I i)).length (gWork c p wt (cellOf wt.I i)) (formsCost (cellN c p wt).length c.n)
      (tg C c p Big) (ts S C c p Big) + 1) (c := .eq cPass v1) (show cPass ≠ v1 by decide)
    (fun ht => ?_) (fun ht => ?_)) (by omega) (fun _ h => h)
  · simp only [Cnd.eval, decide_eq_true_eq, I1.cst.one] at ht
    have hT : CellTests c p wt (cellOf wt.I i) := by
      rw [b1] at ht; split_ifs at ht with h0
      · exact htest.1 h0
    have hcert := certain_of_tests c p wt (cellOf wt.I i) hs hkk hT
    obtain ⟨-, -, hden, hnn, hle⟩ := hcert
    have hcnt' : e1.env vCnt ≤ 2 ^ c.n := by
      rw [e1cnt]
      have : i * 2 ^ p.k ≤ 2 ^ cellBits wt.I * 2 ^ p.k := Nat.mul_le_mul_right _ hi.le
      omega
    have hp := passP_spec c p wt hadm hs w hw S gP sysPr tg ts hG hS hK Big hBig hWd hLB i hi hT e1 I1 S1
      (by rw [b2, Function.update_self]) e1cI hcnt'
    refine Hs.mono hp (by omega) ?_
    rintro b ⟨q1, q2, q3, q4, q5, q6, q7⟩
    refine ⟨q1, q2, by rw [q4, e1ip], by rw [q5, e1cnt, if_pos hT], ?_, by rw [q6, e1unc, if_pos hT]; rfl, by
      rw [q7, e1cI, hcI]⟩
    have h1 : ((b.env vCnt : ℕ) : ℚ) ≤ ((i * 2 ^ p.k : ℕ) : ℚ) + 2 ^ p.k := by
      rw [q5, e1cnt]; push_cast; have := (Nat.cast_le (α := ℚ)).2 hcnt; push_cast at this; linarith
    have h2 : ((b.env vCnt : ℕ) : ℚ) ≤ (((i + 1) * 2 ^ p.k : ℕ) : ℚ) := by push_cast at h1 ⊢; linarith
    exact_mod_cast h2
  · simp only [Cnd.eval, decide_eq_false_iff_not, I1.cst.one] at ht
    have hT : ¬ CellTests c p wt (cellOf wt.I i) := by
      intro h; apply ht; rw [b1, if_pos (htest.2 h)]
    have hu : e1.env vUnc + 1 < 2 ^ C.Wd := by
      rw [e1unc]
      have h1 : 2 ^ cellBits wt.I ≤ 2 ^ c.n := pw_mono (by omega)
      have h2 : 2 ^ c.n < 2 ^ C.Wd := Nat.pow_lt_pow_right (by norm_num) (by nlinarith)
      omega
    refine Hs.mono (hs_inc C vUnc e1 hu) (by omega) ?_
    rintro b rfl
    refine ⟨I1.of_eq (fun x hx => DS.set_env_ne _ _ (fun h => by subst h; revert hx; decide)),
      ⟨S1.sN, S1.sP, S1.sR, S1.lCT, S1.lZb, S1.lE, S1.lX, S1.lG, S1.lB, S1.lA, S1.rcur, S1.out, S1.kin, S1.kc⟩,
      e1ip, ?_, ?_, ?_, ?_⟩
    · rw [DS.set_env_ne _ _ (by decide), e1cnt, if_neg hT]; simp
    · rw [DS.set_env_ne _ _ (by decide), e1cnt]
      have : i * 2 ^ p.k ≤ (i + 1) * 2 ^ p.k := Nat.mul_le_mul_right _ (by omega)
      omega
    · rw [DS.set_env_self, e1unc, if_neg hT]
    · rw [DS.set_env_ne _ _ (by decide), e1cI, hcI]

end B

end NearCubicGates.Close.Cells
