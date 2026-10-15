import Proof.Wire_3_5.PrimAsmFiltNum
import Proof.Wire_3_5.PrimAsmSymQ

/-! # PA library (b): the SYM sample count `Q` in unary registers

The register program behind `SymQ.symQval` at the gate (`D = 1`): from the call's numbers (the SYM cap `B_sym(n)`, `n`,
`errExp = fe·L`, `L`, `kh`, the number of carriers, `a` and the bottom counts `m_j` padded by `0` to four slots) it
computes, in unary registers, the filter's seed bits (`GapParams.seedBits`, from `FiltNum`), the list's walk side
bits, the exponent `E`, the masses `Π(m_j+1)²` and `2^a·Π(3m_j+1) = Π_{j<a}(6m_j+2)`, `I = 2^E·Π(m+1)²·(2𝔐)² + 1` and
`Q = 2^{(5kh+3)/4}·(2^{13}·I·n²)`.

Paper quantity of the main type: `SeedFix.symCount` (through `SymQ.symCount_eq` and `SymIn.Q_eq`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SymQM
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat NearCubicWires.WireExponent3_5.PrimAsm.UnaryArith
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.WireExponent3_5.PrimAsm.SparseNum
open NearCubicWires.WireExponent3_5.PrimAsm.FiltNum NearCubicWires.WireExponent3_5.PrimAsm.CapNum
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists

/-! ## The values -/

/-- The call's numbers for the SYM count. -/
structure SymIn where
  capS : ℕ
  n : ℕ
  errExp : ℕ
  L : ℕ
  kh : ℕ
  numCar : ℕ
  a : ℕ
  m : Fin 4 → ℕ

namespace SymIn
variable (x : SymIn)

def FP : GapParams := ⟨2 * (x.n + 1) ^ 26, x.capS, x.errExp⟩
def Bv : ℕ := x.numCar * (4096 * x.capS)
def Mv : ℕ := x.m 0 + x.m 1 + x.m 2 + x.m 3
def rank : ℕ := BaseListParams.rank ⟨x.Mv, x.Bv⟩
def sb : ℕ := SupplierWalkBridge.toeplitzWalkSideBits x.rank
def wlL : ℕ := SymQ.listWalk 1 x.L
def E : ℕ := SymQ.symE x.FP 1 x.Mv x.Bv x.L
def pSq : ℕ := ∏ j, (x.m j + 1) ^ 2
def pMod : ℕ := 2 ^ x.a * ∏ j, (3 * x.m j + 1)
def mass : ℕ := 2 * x.pSq * x.pMod
def Pv : ℕ := x.pSq * x.mass ^ 2
def Iv : ℕ := 2 ^ x.E * x.Pv + 1
def X : ℕ := (5 * x.kh + 3) / 4
def Q : ℕ := 2 ^ x.X * (2 ^ 13 * x.Iv * x.n ^ 2)

/-- The padded circuit list: `a ≤ 4` bottom counts, `0` beyond. -/
def Padded (ms : List ℕ) : Prop := x.a = ms.length ∧ x.a ≤ 4 ∧ ∀ j : Fin 4, x.m j = ms.getD j.val 0

theorem prodSq_eq (ms : List ℕ) (h : x.Padded ms) : SymQ.prodSq ms = x.pSq := by
  obtain ⟨ha, h4, hm⟩ := h
  unfold SymQ.prodSq pSq
  rw [Fin.prod_univ_four, hm 0, hm 1, hm 2, hm 3]
  match ms, ha, h4 with
  | [], _, _ => simp
  | [a0], _, _ => simp
  | [a0, a1], _, _ => simp
  | [a0, a1, a2], _, _ => simp; ring
  | [a0, a1, a2, a3], _, _ => simp; ring
  | _ :: _ :: _ :: _ :: _ :: _, ha', h4' => simp at ha'; omega

theorem prodMod_eq (ms : List ℕ) (h : x.Padded ms) : SymQ.prodMod ms = x.pMod := by
  obtain ⟨ha, h4, hm⟩ := h
  have hl : ms.length ≤ 4 := ha ▸ h4
  unfold SymQ.prodMod pMod
  rw [Fin.prod_univ_four, hm 0, hm 1, hm 2, hm 3, ha]
  match ms, hl with
  | [], _ => simp
  | [a0], _ => simp; ring
  | [a0, a1], _ => simp; ring
  | [a0, a1, a2], _ => simp; ring
  | [a0, a1, a2, a3], _ => simp; ring
  | _ :: _ :: _ :: _ :: _ :: _, hl' => simp at hl'; omega

theorem Mv_eq (ms : List ℕ) (h : x.Padded ms) : x.Mv = ms.sum := by
  obtain ⟨ha, h4, hm⟩ := h
  have hl : ms.length ≤ 4 := ha ▸ h4
  unfold Mv
  rw [hm 0, hm 1, hm 2, hm 3]
  match ms, hl with
  | [], _ => simp
  | [a0], _ => simp
  | [a0, a1], _ => simp
  | [a0, a1, a2], _ => simp; ring
  | [a0, a1, a2, a3], _ => simp; ring
  | _ :: _ :: _ :: _ :: _ :: _, hl' => simp at hl'; omega

/-- **The register value is the formula**: `Q = symQval 1 kh n FP M B L ms` for the padded list. -/
theorem Q_eq (ms : List ℕ) (h : x.Padded ms) :
    x.Q = SymQ.symQval 1 x.kh x.n x.FP x.Mv x.Bv x.L ms := by
  unfold Q SymQ.symQval Sampler.sampleCount
  rw [prodSq_eq x ms h, prodMod_eq x ms h]
  unfold Iv Pv mass E X
  ring

/-! ### The register values and their sizes -/

theorem lb_ge (hc : 1 ≤ x.capS) : 1 ≤ x.FP.labelBits := by
  have h1 : 0 < x.FP.prefixBits := Nat.clog_pos (by norm_num) (by simp [FP]; omega)
  have h2 : x.FP.prefixBits ≤ x.FP.labelBits := le_max_left _ _
  omega

theorem sG_eq (hc : 1 ≤ x.capS) : x.FP.seedBits =
    (x.FP.labelBits + x.FP.labelBits + x.FP.labelBits - 1 + x.FP.fieldBits + x.FP.fieldBits) * 256 +
      (x.FP.walkLen - 1) * 160 := by
  have := lb_ge x hc
  unfold GapParams.seedBits
  omega

theorem rank_ge : 9 ≤ x.rank := by
  unfold rank BaseListParams.rank BaseListParams.J; omega

theorem sb_eq : x.sb = (x.rank + x.rank + x.rank) / 2 := by
  have := rank_ge x
  unfold sb SupplierWalkBridge.toeplitzWalkSideBits SupplierWalkBridge.toeplitzSeedBits
  congr 1; omega

theorem wlL_eq : x.wlL = 2 * ((x.L + 5) / 2 / 2) + 1 := by
  unfold wlL SymQ.listWalk; omega

theorem E_eq : x.E = x.FP.seedBits + x.sb + x.sb + (x.wlL - 1) * 160 := by
  unfold E SymQ.symE sb wlL rank; ring

theorem rank_eq : x.rank = max (Nat.clog 2 x.Bv + 9) (Nat.clog 2 x.Mv) := rfl

theorem pow_E_ge {v : ℕ} (hv : v ≤ x.E) : 2 ^ v ≤ 2 ^ x.E := Nat.pow_le_pow_right (by norm_num) hv

theorem cap_le_E (hc : 1 ≤ x.capS) : x.capS * 32 ≤ 2 ^ x.E := by
  have h1 : 32 * x.capS ≤ 2 ^ x.FP.prefixBits := Nat.le_pow_clog (by norm_num) _
  have h2 : x.FP.prefixBits ≤ x.FP.labelBits := le_max_left _ _
  have h3 : x.FP.labelBits ≤ x.E := by rw [E_eq, sG_eq x hc]; omega
  have := pow_E_ge x (le_trans h2 h3)
  omega

theorem len_le_E (hc : 1 ≤ x.capS) : (x.n + 1) ^ 26 * 2 * 16 ≤ 2 ^ x.E := by
  have h1 : x.FP.len ≤ 2 ^ Nat.clog 2 x.FP.len := Nat.le_pow_clog (by norm_num) _
  have h3 : x.FP.fieldBits ≤ x.E := by rw [E_eq, sG_eq x hc]; omega
  have h4 := pow_E_ge x h3
  have h5 : 2 ^ x.FP.fieldBits = 2 ^ Nat.clog 2 x.FP.len * 16 := by
    unfold GapParams.fieldBits; rw [pow_add]; norm_num
  have h6 : x.FP.len = 2 * (x.n + 1) ^ 26 := rfl
  omega

theorem n_le_E (hc : 1 ≤ x.capS) : x.n + 1 ≤ 2 ^ x.E := by
  have h1 := len_le_E x hc
  have h2 : x.n + 1 ≤ (x.n + 1) ^ 26 := Nat.le_self_pow (by norm_num) _
  omega

theorem errExp_le_E (hc : 1 ≤ x.capS) : x.errExp + 8 ≤ x.E := by
  have h1 : x.FP.walkLen = 2 * (x.errExp / 4) + 1 := rfl
  have := lb_ge x hc
  rw [E_eq, sG_eq x hc]
  omega

theorem B_le_E : x.Bv ≤ 2 ^ x.E := by
  have h1 : x.Bv ≤ 2 ^ Nat.clog 2 x.Bv := Nat.le_pow_clog (by norm_num) _
  have h2 : Nat.clog 2 x.Bv ≤ x.rank := by rw [rank_eq]; omega
  have h3 : x.rank ≤ x.E := by have := rank_ge x; rw [E_eq, sb_eq]; omega
  exact le_trans h1 (pow_E_ge x (le_trans h2 h3))

theorem M_le_E : x.Mv ≤ 2 ^ x.E := by
  have h1 : x.Mv ≤ 2 ^ Nat.clog 2 x.Mv := Nat.le_pow_clog (by norm_num) _
  have h2 : Nat.clog 2 x.Mv ≤ x.rank := by rw [rank_eq]; omega
  have h3 : x.rank ≤ x.E := by have := rank_ge x; rw [E_eq, sb_eq]; omega
  exact le_trans h1 (pow_E_ge x (le_trans h2 h3))

theorem L_le_E : x.L + 8 ≤ x.E := by
  rw [E_eq, wlL_eq]; omega

theorem rank3_le_E : x.rank + x.rank + x.rank + 1 ≤ x.E + 2 := by
  have := rank_ge x; rw [E_eq, sb_eq]; omega

theorem pS_pos : 1 ≤ x.pSq := Finset.one_le_prod' fun j _ => Nat.one_le_pow _ _ (by omega)

theorem prod3_pos : 1 ≤ ∏ j, (3 * x.m j + 1) := Finset.one_le_prod' fun j _ => by omega

theorem pM_pos : 1 ≤ x.pMod := Nat.mul_le_mul Nat.one_le_two_pow (prod3_pos x)

theorem mass_ge : 2 * x.pMod ≤ x.mass := by
  unfold mass
  have := pS_pos x
  nlinarith

theorem Pv_ge_mass : x.mass ≤ x.Pv := by
  unfold Pv
  have := pS_pos x
  have hm : 1 ≤ x.mass := le_trans (by have := pM_pos x; omega) (mass_ge x)
  nlinarith

theorem pS_le_Pv : x.pSq ≤ x.Pv := by
  unfold Pv
  have hm : 1 ≤ x.mass := le_trans (by have := pM_pos x; omega) (mass_ge x)
  have : 1 ≤ x.mass ^ 2 := Nat.one_le_pow _ _ hm
  nlinarith

theorem Pv_lt_I : x.Pv < x.Iv := by
  unfold Iv
  have := Nat.one_le_two_pow (n := x.E)
  nlinarith

theorem twoE_le_I : 2 ^ x.E < x.Iv := by
  unfold Iv
  have := le_trans (pS_pos x) (pS_le_Pv x)
  have : 2 ^ x.E ≤ 2 ^ x.E * x.Pv := Nat.le_mul_of_pos_right _ (by omega)
  omega

theorem I_le_Q : x.Iv * 8192 * x.n * x.n ≤ x.Q := by
  unfold Q
  have h1 : 1 ≤ 2 ^ x.X := Nat.one_le_two_pow
  have e : 2 ^ 13 * x.Iv * x.n ^ 2 = x.Iv * 8192 * x.n * x.n := by ring
  rw [e]
  exact Nat.le_mul_of_pos_left _ h1

theorem I_small_le_Q (hn : 2 ≤ x.n) : x.Iv * 8192 + 8192 ≤ x.Q := by
  have h := I_le_Q x
  have h1 : x.Iv * 8192 * 2 ≤ x.Iv * 8192 * x.n := Nat.mul_le_mul_left _ hn
  have h2 : x.Iv * 8192 * x.n ≤ x.Iv * 8192 * x.n * x.n := Nat.le_mul_of_pos_right _ (by omega)
  have h3 : 1 ≤ x.Iv := by unfold Iv; omega
  omega

theorem X_le_Q (hn : 1 ≤ x.n) : 2 ^ (x.X + 1) ≤ x.Q := by
  unfold Q
  have h3 : 1 ≤ x.Iv := by unfold Iv; omega
  have : 2 ≤ 2 ^ 13 * x.Iv * x.n ^ 2 := by
    have : 1 ≤ x.n ^ 2 := Nat.one_le_pow _ _ hn
    nlinarith
  rw [pow_succ]
  exact Nat.mul_le_mul_left _ this

theorem kh_le_Q (hn : 1 ≤ x.n) : x.kh * 5 + 8 ≤ x.Q := by
  have h1 : x.kh < 2 ^ x.kh := Nat.lt_two_pow_self
  have h2 : 2 ^ x.kh ≤ 2 ^ x.X := Nat.pow_le_pow_right (by norm_num) (by unfold X; omega)
  have h3 : 1 ≤ x.Iv := by unfold Iv; omega
  have h4 : 2 ^ x.X * 8192 ≤ x.Q := by
    unfold Q
    have : 1 ≤ x.n ^ 2 := Nat.one_le_pow _ _ hn
    have : 8192 ≤ 2 ^ 13 * x.Iv * x.n ^ 2 := by nlinarith
    nlinarith
  omega

end SymIn

/-! ## The register parts

Each part works in its own block `S` of registers: inputs first, then its outputs and scratch at `0`; at the end only the
outputs have changed. -/

section Parts
variable {ns nr : ℕ} (cap : ℕ)

theorem nbl_zero : natBitLength 0 = 1 := by simp [natBitLength]

/-- `⌈log₂ x⌉` from the bit length of `x − 1`, with the two small cases. -/
theorem clog_val (x : ℕ) : Nat.clog 2 x = if 1 < x then natBitLength (x - 1) else natBitLength (x - 1) - 1 := by
  rcases Nat.lt_or_ge 1 x with h | h
  · rw [if_pos h]; exact clog_eq_nbl x h
  · rw [if_neg (by omega), show x - 1 = 0 by omega, nbl_zero]
    interval_cases x <;> simp

/-- `2^s` with the value named, within one unit. `R = (s, out, t, w)`. -/
theorem pow2v (R : Fin 4 ↪ Fin nr) (s : ℕ) (σ : WState ns nr) (hs : σ.val (R 0) = s) (h1 : σ.val (R 1) = 0)
    (h2 : σ.val (R 2) = 0) (h3 : σ.val (R 3) = 0) (hcap : 2 ^ (s + 1) ≤ cap) :
    WExec cap (pow2W R) σ (σ.setv (R 1) (2 ^ s)) (UnaryPow.sq cap) := by
  have h := pow2W_spec cap R σ h1 h2 h3 (by rw [hs]; exact hcap)
  rw [hs] at h
  refine WExec.mono h ?_
  have hlt : s < 2 ^ s := Nat.lt_two_pow_self
  have hp : 2 ^ (s + 1) = 2 * 2 ^ s := by rw [pow_succ]; ring
  have hc2 : 2 * 2 ^ s ≤ cap := by omega
  have hm : s * (18 * 2 ^ s + 7) ≤ cap * (18 * cap + 7) := Nat.mul_le_mul (by omega) (by omega)
  unfold UnaryPow.sq
  nlinarith

def e3 : Fin 5 ↪ Fin 10 := ⟨![3, 4, 5, 6, 7], by decide⟩
def e4 : Fin 5 ↪ Fin 10 := ⟨![4, 5, 6, 7, 8], by decide⟩
@[simp] theorem e3_apply (i : Fin 5) : e3 i = ![3, 4, 5, 6, 7] i := rfl
@[simp] theorem e4_apply (i : Fin 5) : e4 i = ![4, 5, 6, 7, 8] i := rfl

/-! ### The filter's seed bits -/

/-- `S3 := (lb+lb+lb−1+fb+fb)·256`; `S = (lb, fb, wl, out, scratch)`. -/
def sgA (S : Fin 10 ↪ Fin nr) : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (S 0) (S 3) (S 4)) (.seq (addTo (S 0) (S 3) (S 4)) (.seq (addTo (S 0) (S 3) (S 4))
  (.seq (.dec (S 3)) (.seq (addTo (S 1) (S 3) (S 4)) (.seq (addTo (S 1) (S 3) (S 4))
  (.seq (StarNums.incN (S 4) 256) (.seq (mulByW (e3.trans S)) (WM.clear (S 4)))))))))

theorem sgA_spec (S : Fin 10 ↪ Fin nr) (σ : WState ns nr) (lb fb : ℕ) (h0 : σ.val (S 0) = lb)
    (h1 : σ.val (S 1) = fb) (hz : ∀ i : Fin 10, 3 ≤ i.val → σ.val (S i) = 0) (hlb : 1 ≤ lb)
    (hc : (lb + lb + lb - 1 + fb + fb) * 256 + 256 ≤ cap) :
    WExec cap (sgA S) σ (σ.setv (S 3) ((lb + lb + lb - 1 + fb + fb) * 256)) (20 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  unfold sgA
  refine seqD cap _ 1 (copy1 cap (S 0) (S 3) (S 4) (by simp) (by simp) (by simp) lb σ h0 (by simp [hz])
    (by simp [hz]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (add1 cap (S 0) (S 3) (S 4) (by simp) (by simp) (by simp) lb lb _ (by simp [h0]) (by simp)
    (by simp [hz]) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (add1 cap (S 0) (S 3) (S 4) (by simp) (by simp) (by simp) lb (lb + lb) _ (by simp [h0])
    (by simp) (by simp [hz]) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (dec1 cap (S 3) (lb + lb + lb) _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (add1 cap (S 1) (S 3) (S 4) (by simp) (by simp) (by simp) fb (lb + lb + lb - 1) _
    (by simp [h1]) (by simp) (by simp [hz]) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (add1 cap (S 1) (S 3) (S 4) (by simp) (by simp) (by simp) fb (lb + lb + lb - 1 + fb) _
    (by simp [h1]) (by simp) (by simp [hz]) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (incN0 cap (S 4) 256 _ (by simp [hz]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 3 (mulBy1 cap (e3.trans S) (lb + lb + lb - 1 + fb + fb) 256 _ (by simp) (by simp)
    (by simp [hz]) (by simp [hz]) (by simp [hz]) (by omega) (by omega) (by omega)) (by omega) (by omega) ?_
  refine endD cap _ 1 (clear1 cap (S 4) 256 _ (by simp) (by omega)) ?_ (by omega) (by omega)
  simp only [Function.Embedding.trans_apply, e3_apply, Matrix.cons_val]
  clear h0 h1 hlb hc hsq
  have hb0 := setv_base S σ
  simp only [hb0, setv_blk]
  congr 1
  funext i
  fin_cases i <;> simp [Function.update_apply, hz]

/-- `S3 += (S2 − 1)·160`; `S2` kept, `S4 … S9` scratch. -/
def sgB (S : Fin 10 ↪ Fin nr) : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (S 2) (S 4) (S 5)) (.seq (.dec (S 4)) (.seq (StarNums.incN (S 5) 160)
  (.seq (mulByW (e4.trans S)) (.seq (WM.clear (S 5)) (.seq (addTo (S 4) (S 3) (S 5)) (WM.clear (S 4)))))))

theorem sgB_spec (S : Fin 10 ↪ Fin nr) (σ : WState ns nr) (y wl : ℕ) (h2 : σ.val (S 2) = wl)
    (h3 : σ.val (S 3) = y) (hz : ∀ i : Fin 10, 4 ≤ i.val → σ.val (S i) = 0)
    (hc : y + (wl - 1) * 160 + wl + 160 ≤ cap) :
    WExec cap (sgB S) σ (σ.setv (S 3) (y + (wl - 1) * 160)) (16 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  unfold sgB
  refine seqD cap _ 1 (copy1 cap (S 2) (S 4) (S 5) (by simp) (by simp) (by simp) wl σ h2 (by simp [hz])
    (by simp [hz]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (dec1 cap (S 4) wl _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (incN0 cap (S 5) 160 _ (by simp [hz]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 3 (mulBy1 cap (e4.trans S) (wl - 1) 160 _ (by simp) (by simp) (by simp [hz]) (by simp [hz])
    (by simp [hz]) (by omega) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (clear1 cap (S 5) 160 _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (add1 cap (S 4) (S 3) (S 5) (by simp) (by simp) (by simp) ((wl - 1) * 160) y _ (by simp)
    (by simp [h3]) (by simp) (by omega) (by omega)) (by omega) (by omega) ?_
  refine endD cap _ 1 (clear1 cap (S 4) ((wl - 1) * 160) _ (by simp) (by omega)) ?_ (by omega) (by omega)
  simp only [Function.Embedding.trans_apply, e4_apply, Matrix.cons_val]
  clear h2 hc hsq
  have hb0 := setv_base S σ
  simp only [hb0, setv_blk]
  congr 1
  funext i
  fin_cases i <;> simp [Function.update_apply, hz, h3]

/-! ### The list's rank -/

def cB : Fin 8 ↪ Fin 10 := ⟨![2, 3, 4, 5, 1, 6, 7, 8], by decide⟩
def cG : Fin 6 ↪ Fin 10 := ⟨![0, 2, 3, 4, 5, 6], by decide⟩
@[simp] theorem cB_apply (i : Fin 8) : cB i = ![2, 3, 4, 5, 1, 6, 7, 8] i := rfl
@[simp] theorem cG_apply (i : Fin 6) : cG i = ![0, 2, 3, 4, 5, 6] i := rfl

/-- `S1 := ⌈log₂ S0⌉`; `S = (x, out, scratch)`. -/
def clogW (S : Fin 10 ↪ Fin nr) : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (S 0) (S 2) (S 3)) (.seq (.dec (S 2)) (.seq (bitLenM (cB.trans S))
  (.seq (WM.clear (S 2)) (.seq (StarNums.incN (S 2) 1) (.seq (gtFlagW (cG.trans S)) (.seq (WM.clear (S 2))
  (.seq (.ifr (S 3) .skip (.dec (S 1))) (WM.clear (S 3)))))))))

theorem clogW_spec (S : Fin 10 ↪ Fin nr) (σ : WState ns nr) (x : ℕ) (h0 : σ.val (S 0) = x)
    (hz : ∀ i : Fin 10, 1 ≤ i.val → σ.val (S i) = 0) (hc : x + 2 ≤ cap) :
    WExec cap (clogW S) σ (σ.setv (S 1) (Nat.clog 2 x)) (20 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  have hnb : natBitLength (x - 1) ≤ x + 1 := by
    have := CopyNat.natBitLength_le_self_succ (x - 1); omega
  unfold clogW
  refine seqD cap _ 1 (copy1 cap (S 0) (S 2) (S 3) (by simp) (by simp) (by simp) x σ h0 (by simp [hz])
    (by simp [hz]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (dec1 cap (S 2) x _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (bitLen1 cap (cB.trans S) (x - 1) _ (by simp) (by simp [hz]) (by simp [hz]) (by simp [hz])
    (by simp [hz]) (by simp [hz]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (clear1 cap (S 2) (x - 1) _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (incN0 cap (S 2) 1 _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (gt1 cap (cG.trans S) x 1 _ (by simp [h0]) (by simp) (by simp [hz]) (by simp [hz])
    (by simp [hz]) (by simp [hz]) (by omega) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (clear1 cap (S 2) 1 _ (by simp) (by omega)) (by omega) (by omega) ?_
  simp only [Function.Embedding.trans_apply, cB_apply, cG_apply, Matrix.cons_val]
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = ((((((σ.setv (S 2) x).setv (S 2) (x - 1)).setv (S 1) (natBitLength (x - 1))).setv (S 2)
      0).setv (S 2) 1).setv (S 3) (if 1 < x then 1 else 0)).setv (S 2) 0 := ⟨_, rfl⟩
  rw [← hτ]
  have hv1 : τ.val (S 1) = natBitLength (x - 1) := by rw [hτ]; simp
  have hv3 : τ.val (S 3) = if 1 < x then 1 else 0 := by rw [hτ]; simp
  have hif : WExec cap (.ifr (S 3) .skip (.dec (S 1))) τ (τ.setv (S 1) (Nat.clog 2 x)) (UnaryPow.sq cap) := by
    by_cases h1x : 1 < x
    · have hs : τ.setv (S 1) (Nat.clog 2 x) = τ := by
        rw [clog_val, if_pos h1x, ← hv1]; exact wsetv_same _ _
      rw [hs]
      exact WExec.mono (WExec.ifrT (by rw [hv3, if_pos h1x]; omega) (WExec.skip _)) (by omega)
    · have hs : τ.setv (S 1) (Nat.clog 2 x) = τ.setv (S 1) (τ.val (S 1) - 1) := by
        rw [clog_val, if_neg h1x, hv1]
      rw [hs]
      exact WExec.mono (WExec.ifrF (by rw [hv3, if_neg h1x]) (WExec.dec (cap := cap) (S 1) τ (by rw [hv1]; omega)))
        (by omega)
  refine seqD cap _ 1 hif (by omega) (by omega) ?_
  refine endD cap _ 1 (clear1 cap (S 3) (if 1 < x then 1 else 0) _ (by simp [hv3]) (by split_ifs <;> omega)) ?_
    (by omega) (by omega)
  rw [hτ]
  clear h0 hc hsq hnb hif hv1 hv3 hτ
  have hb0 := setv_base S σ
  simp only [hb0, setv_blk]
  congr 1
  funext i
  fin_cases i <;> simp [Function.update_apply, hz]

/-! ### The list's numbers `B = numCar·4096·cap`, `M = Σ m_j` -/

def e68 : Fin 5 ↪ Fin 14 := ⟨![6, 8, 9, 10, 11], by decide⟩
def e60 : Fin 5 ↪ Fin 14 := ⟨![6, 0, 9, 10, 11], by decide⟩
@[simp] theorem e68_apply (i : Fin 5) : e68 i = ![6, 8, 9, 10, 11] i := rfl
@[simp] theorem e60_apply (i : Fin 5) : e60 i = ![6, 0, 9, 10, 11] i := rfl

/-- `S6 := cap·4096·numCar`, `S7 := m₀+m₁+m₂+m₃`; `S = (numCar, cap, m₀, m₁, m₂, m₃, B, M, scratch)`. -/
def bmW (S : Fin 14 ↪ Fin nr) : WM ns nr :=
  .seq (StarNums.incN (S 8) 4096) (.seq (FinalPass.Hash4.wcopyR (S 1) (S 6) (S 9)) (.seq (mulByW (e68.trans S))
  (.seq (WM.clear (S 8)) (.seq (mulByW (e60.trans S)) (.seq (FinalPass.Hash4.wcopyR (S 2) (S 7) (S 8))
  (.seq (addTo (S 3) (S 7) (S 8)) (.seq (addTo (S 4) (S 7) (S 8)) (addTo (S 5) (S 7) (S 8)))))))))

theorem bmW_spec (S : Fin 14 ↪ Fin nr) (σ : WState ns nr) (nc cS m0 m1 m2 m3 : ℕ) (h0 : σ.val (S 0) = nc)
    (h1 : σ.val (S 1) = cS) (h2 : σ.val (S 2) = m0) (h3 : σ.val (S 3) = m1) (h4 : σ.val (S 4) = m2)
    (h5 : σ.val (S 5) = m3) (hz : ∀ i : Fin 14, 6 ≤ i.val → σ.val (S i) = 0)
    (hc : cS * 4096 * nc + cS * 4096 + nc + cS + 4096 + m0 + m1 + m2 + m3 ≤ cap) :
    WExec cap (bmW S) σ ((σ.setv (S 6) (cS * 4096 * nc)).setv (S 7) (m0 + m1 + m2 + m3)) (22 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  unfold bmW
  refine seqD cap _ 1 (incN0 cap (S 8) 4096 σ (by simp [hz]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (copy1 cap (S 1) (S 6) (S 9) (by simp) (by simp) (by simp) cS _ (by simp [h1]) (by simp [hz])
    (by simp [hz]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 3 (mulBy1 cap (e68.trans S) cS 4096 _ (by simp) (by simp) (by simp [hz]) (by simp [hz])
    (by simp [hz]) (by nlinarith) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (clear1 cap (S 8) 4096 _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 3 (mulBy1 cap (e60.trans S) (cS * 4096) nc _ (by simp) (by simp [h0]) (by simp [hz])
    (by simp [hz]) (by simp [hz]) (by omega) (by nlinarith) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (copy1 cap (S 2) (S 7) (S 8) (by simp) (by simp) (by simp) m0 _ (by simp [h2]) (by simp [hz])
    (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (add1 cap (S 3) (S 7) (S 8) (by simp) (by simp) (by simp) m1 m0 _ (by simp [h3]) (by simp)
    (by simp) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (add1 cap (S 4) (S 7) (S 8) (by simp) (by simp) (by simp) m2 (m0 + m1) _ (by simp [h4]) (by simp)
    (by simp) (by omega) (by omega)) (by omega) (by omega) ?_
  refine endD cap _ 1 (add1 cap (S 5) (S 7) (S 8) (by simp) (by simp) (by simp) m3 (m0 + m1 + m2) _ (by simp [h5])
    (by simp) (by simp) (by omega) (by omega)) ?_ (by omega) (by omega)
  simp only [Function.Embedding.trans_apply, e68_apply, e60_apply, Matrix.cons_val]
  clear h0 h1 h2 h3 h4 h5 hc hsq
  have hb0 := setv_base S σ
  simp only [hb0, setv_blk]
  congr 1
  funext i
  fin_cases i <;> simp [Function.update_apply, hz]

/-! ### The larger of two registers -/

def gG : Fin 6 ↪ Fin 10 := ⟨![0, 1, 3, 4, 5, 6], by decide⟩
@[simp] theorem gG_apply (i : Fin 6) : gG i = ![0, 1, 3, 4, 5, 6] i := rfl

/-- `S2 := max S0 S1`; `S = (x, y, out, flag, scratch)`. -/
def maxW (S : Fin 10 ↪ Fin nr) : WM ns nr :=
  .seq (gtFlagW (gG.trans S)) (.seq (.ifr (S 3) (FinalPass.Hash4.wcopyR (S 0) (S 2) (S 4))
    (FinalPass.Hash4.wcopyR (S 1) (S 2) (S 4))) (WM.clear (S 3)))

theorem maxW_spec (S : Fin 10 ↪ Fin nr) (σ : WState ns nr) (x y : ℕ) (h0 : σ.val (S 0) = x) (h1 : σ.val (S 1) = y)
    (hz : ∀ i : Fin 10, 2 ≤ i.val → σ.val (S i) = 0) (hx : x ≤ cap) (hy : y ≤ cap) (hc1 : 1 ≤ cap) :
    WExec cap (maxW S) σ (σ.setv (S 2) (max x y)) (6 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  unfold maxW
  refine seqD cap _ 1 (gt1 cap (gG.trans S) x y σ (by simp [h0]) (by simp [h1]) (by simp [hz]) (by simp [hz])
    (by simp [hz]) (by simp [hz]) hx hy hc1) (by omega) (by omega) ?_
  simp only [Function.Embedding.trans_apply, gG_apply, Matrix.cons_val]
  have hbr : WExec cap (.ifr (S 3) (FinalPass.Hash4.wcopyR (S 0) (S 2) (S 4)) (FinalPass.Hash4.wcopyR (S 1) (S 2) (S 4)))
      (σ.setv (S 3) (if y < x then 1 else 0)) ((σ.setv (S 3) (if y < x then 1 else 0)).setv (S 2) (max x y))
      (2 * UnaryPow.sq cap) := by
    by_cases h : y < x
    · rw [show max x y = x by omega]
      exact WExec.mono (WExec.ifrT (by simp [h]) (copy1 cap (S 0) (S 2) (S 4) (by simp) (by simp) (by simp) x _
        (by simp [h0]) (by simp [hz]) (by simp [hz]) hx)) (by omega)
    · rw [show max x y = y by omega]
      exact WExec.mono (WExec.ifrF (by simp [h]) (copy1 cap (S 1) (S 2) (S 4) (by simp) (by simp) (by simp) y _
        (by simp [h1]) (by simp [hz]) (by simp [hz]) hy)) (by omega)
  refine seqD cap _ 2 hbr (by omega) (by omega) ?_
  refine endD cap _ 1 (clear1 cap (S 3) (if y < x then 1 else 0) _ (by simp) (by split_ifs <;> omega)) ?_
    (by omega) (by omega)
  clear h0 h1 hx hy hc1 hsq hbr
  have hb0 := setv_base S σ
  simp only [hb0, setv_blk]
  congr 1
  funext i
  fin_cases i <;> simp [Function.update_apply, hz]

/-! ### The walk side bits and the list's walk length -/

/-- `S1 := (S0+S0+S0)/2` (the walk side bits `(2r + (r−1) + 1)/2` for `r ≥ 1`); `S = (rank, out, scratch)`. -/
def sbW (S : Fin 10 ↪ Fin nr) : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (S 0) (S 1) (S 2)) (.seq (addTo (S 0) (S 1) (S 2)) (.seq (addTo (S 0) (S 1) (S 2))
  (.seq (halveM (S 1) (S 2) (S 3)) (WM.clear (S 3)))))

theorem sbW_spec (S : Fin 10 ↪ Fin nr) (σ : WState ns nr) (r : ℕ) (h0 : σ.val (S 0) = r)
    (hz : ∀ i : Fin 10, 1 ≤ i.val → σ.val (S i) = 0) (hc : r + r + r + 1 ≤ cap) :
    WExec cap (sbW S) σ (σ.setv (S 1) ((r + r + r) / 2)) (10 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  unfold sbW
  refine seqD cap _ 1 (copy1 cap (S 0) (S 1) (S 2) (by simp) (by simp) (by simp) r σ h0 (by simp [hz])
    (by simp [hz]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (add1 cap (S 0) (S 1) (S 2) (by simp) (by simp) (by simp) r r _ (by simp [h0]) (by simp)
    (by simp [hz]) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (add1 cap (S 0) (S 1) (S 2) (by simp) (by simp) (by simp) r (r + r) _ (by simp [h0]) (by simp)
    (by simp [hz]) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (halve1 cap (S 1) (S 2) (S 3) (by simp) (by simp) (by simp) (r + r + r) _ (by simp)
    (by simp [hz]) (by simp [hz]) (by omega) (by omega)) (by omega) (by omega) ?_
  refine endD cap _ 1 (clear1 cap (S 3) ((r + r + r) % 2) _ (by simp) (by omega)) ?_ (by omega) (by omega)
  clear h0 hc hsq
  have hb0 := setv_base S σ
  simp only [hb0, setv_blk]
  congr 1
  funext i
  fin_cases i <;> simp [Function.update_apply, hz]

/-- `S1 := 2⌊(S0+5)/4⌋ + 1`; `S = (L, out, scratch)`. -/
def wlW (S : Fin 10 ↪ Fin nr) : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (S 0) (S 1) (S 2)) (.seq (StarNums.incN (S 1) 5) (.seq (halveM (S 1) (S 2) (S 3))
  (.seq (WM.clear (S 3)) (.seq (halveM (S 1) (S 2) (S 3)) (.seq (WM.clear (S 3)) (.seq (dbl (S 1) (S 2))
  (.inc (S 1))))))))

theorem wlW_spec (S : Fin 10 ↪ Fin nr) (σ : WState ns nr) (L : ℕ) (h0 : σ.val (S 0) = L)
    (hz : ∀ i : Fin 10, 1 ≤ i.val → σ.val (S i) = 0) (hc : L + 8 ≤ cap) :
    WExec cap (wlW S) σ (σ.setv (S 1) (2 * ((L + 5) / 2 / 2) + 1)) (16 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  unfold wlW
  refine seqD cap _ 1 (copy1 cap (S 0) (S 1) (S 2) (by simp) (by simp) (by simp) L σ h0 (by simp [hz])
    (by simp [hz]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (incN1 cap (S 1) L 5 _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (halve1 cap (S 1) (S 2) (S 3) (by simp) (by simp) (by simp) (L + 5) _ (by simp)
    (by simp [hz]) (by simp [hz]) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (clear1 cap (S 3) ((L + 5) % 2) _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (halve1 cap (S 1) (S 2) (S 3) (by simp) (by simp) (by simp) ((L + 5) / 2) _ (by simp)
    (by simp [hz]) (by simp) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (clear1 cap (S 3) ((L + 5) / 2 % 2) _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (dbl1 cap (S 1) (S 2) (by simp) ((L + 5) / 2 / 2) _ (by simp) (by simp [hz]) (by omega))
    (by omega) (by omega) ?_
  refine endD cap _ 1 (inc1 cap (S 1) (2 * ((L + 5) / 2 / 2)) _ (by simp) (by omega)) ?_ (by omega) (by omega)
  clear h0 hc hsq
  have hb0 := setv_base S σ
  simp only [hb0, setv_blk]
  congr 1
  funext i
  fin_cases i <;> simp [Function.update_apply, hz]

/-- `S3 := S0 + S1 + S1`; `S = (sG, sb, wl, out, scratch)`. -/
def eW (S : Fin 10 ↪ Fin nr) : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (S 0) (S 3) (S 4)) (.seq (addTo (S 1) (S 3) (S 4)) (addTo (S 1) (S 3) (S 4)))

theorem eW_spec (S : Fin 10 ↪ Fin nr) (σ : WState ns nr) (g b : ℕ) (h0 : σ.val (S 0) = g) (h1 : σ.val (S 1) = b)
    (hz : ∀ i : Fin 10, 3 ≤ i.val → σ.val (S i) = 0) (hc : g + b + b ≤ cap) :
    WExec cap (eW S) σ (σ.setv (S 3) (g + b + b)) (6 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  unfold eW
  refine seqD cap _ 1 (copy1 cap (S 0) (S 3) (S 4) (by simp) (by simp) (by simp) g σ h0 (by simp [hz])
    (by simp [hz]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (add1 cap (S 1) (S 3) (S 4) (by simp) (by simp) (by simp) b g _ (by simp [h1]) (by simp)
    (by simp [hz]) (by omega) (by omega)) (by omega) (by omega) ?_
  refine endD cap _ 1 (add1 cap (S 1) (S 3) (S 4) (by simp) (by simp) (by simp) b (g + b) _ (by simp [h1]) (by simp)
    (by simp [hz]) (by omega) (by omega)) ?_ (by omega) (by omega)
  clear h0 h1 hc hsq
  have hb0 := setv_base S σ
  simp only [hb0, setv_blk]
  congr 1
  funext i
  fin_cases i <;> simp [Function.update_apply, hz]

/-! ### The masses -/

def f12 : Fin 5 ↪ Fin 10 := ⟨![1, 2, 3, 4, 5], by decide⟩
def g23 : Fin 5 ↪ Fin 10 := ⟨![2, 3, 4, 5, 6], by decide⟩
@[simp] theorem f12_apply (i : Fin 5) : f12 i = ![1, 2, 3, 4, 5] i := rfl
@[simp] theorem g23_apply (i : Fin 5) : g23 i = ![2, 3, 4, 5, 6] i := rfl

/-- `S1 := S1·(S0+1)·(S0+1)`; `S = (m, acc, scratch)`. -/
def sqStepW (S : Fin 10 ↪ Fin nr) : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (S 0) (S 2) (S 3)) (.seq (.inc (S 2)) (.seq (mulByW (f12.trans S))
  (.seq (mulByW (f12.trans S)) (WM.clear (S 2)))))

theorem sqStepW_spec (S : Fin 10 ↪ Fin nr) (σ : WState ns nr) (m acc : ℕ) (h0 : σ.val (S 0) = m)
    (h1 : σ.val (S 1) = acc) (hz : ∀ i : Fin 10, 2 ≤ i.val → σ.val (S i) = 0)
    (hc : acc * (m + 1) * (m + 1) + m + 1 ≤ cap) :
    WExec cap (sqStepW S) σ (σ.setv (S 1) (acc * (m + 1) * (m + 1))) (13 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  have hm1 : acc * (m + 1) ≤ acc * (m + 1) * (m + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hm0 : acc ≤ acc * (m + 1) := Nat.le_mul_of_pos_right _ (by omega)
  unfold sqStepW
  refine seqD cap _ 1 (copy1 cap (S 0) (S 2) (S 3) (by simp) (by simp) (by simp) m σ h0 (by simp [hz])
    (by simp [hz]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (inc1 cap (S 2) m _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 3 (mulBy1 cap (f12.trans S) acc (m + 1) _ (by simp [h1]) (by simp) (by simp [hz]) (by simp [hz])
    (by simp [hz]) (by omega) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 3 (mulBy1 cap (f12.trans S) (acc * (m + 1)) (m + 1) _ (by simp) (by simp) (by simp [hz])
    (by simp [hz]) (by simp [hz]) (by omega) (by omega) (by omega)) (by omega) (by omega) ?_
  refine endD cap _ 1 (clear1 cap (S 2) (m + 1) _ (by simp) (by omega)) ?_ (by omega) (by omega)
  simp only [Function.Embedding.trans_apply, f12_apply, Matrix.cons_val]
  clear h0 h1 hc hsq hm1 hm0
  have hb0 := setv_base S σ
  simp only [hb0, setv_blk]
  congr 1
  funext i
  fin_cases i <;> simp [Function.update_apply, hz]

/-- `S1 := S1·(3·S0+1)`; `S = (m, acc, scratch)`. -/
def modStepW (S : Fin 10 ↪ Fin nr) : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (S 0) (S 2) (S 3)) (.seq (StarNums.incN (S 3) 3) (.seq (mulByW (g23.trans S))
  (.seq (WM.clear (S 3)) (.seq (.inc (S 2)) (.seq (mulByW (f12.trans S)) (WM.clear (S 2)))))))

theorem modStepW_spec (S : Fin 10 ↪ Fin nr) (σ : WState ns nr) (m acc : ℕ) (h0 : σ.val (S 0) = m)
    (h1 : σ.val (S 1) = acc) (hz : ∀ i : Fin 10, 2 ≤ i.val → σ.val (S i) = 0)
    (hc : acc * (m * 3 + 1) + m * 3 + 4 ≤ cap) (hacc : 1 ≤ acc) :
    WExec cap (modStepW S) σ (σ.setv (S 1) (acc * (m * 3 + 1))) (17 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  have hm0 : acc ≤ acc * (m * 3 + 1) := Nat.le_mul_of_pos_right _ (by omega)
  unfold modStepW
  refine seqD cap _ 1 (copy1 cap (S 0) (S 2) (S 3) (by simp) (by simp) (by simp) m σ h0 (by simp [hz])
    (by simp [hz]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (incN0 cap (S 3) 3 _ (by simp [hz]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 3 (mulBy1 cap (g23.trans S) m 3 _ (by simp) (by simp) (by simp [hz]) (by simp [hz])
    (by simp [hz]) (by omega) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (clear1 cap (S 3) 3 _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (inc1 cap (S 2) (m * 3) _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 3 (mulBy1 cap (f12.trans S) acc (m * 3 + 1) _ (by simp [h1]) (by simp) (by simp [hz])
    (by simp [hz]) (by simp [hz]) (by omega) (by omega) (by omega)) (by omega) (by omega) ?_
  refine endD cap _ 1 (clear1 cap (S 2) (m * 3 + 1) _ (by simp) (by omega)) ?_ (by omega) (by omega)
  simp only [Function.Embedding.trans_apply, f12_apply, g23_apply, Matrix.cons_val]
  clear h0 h1 hc hacc hsq hm0
  have hb0 := setv_base S σ
  simp only [hb0, setv_blk]
  congr 1
  funext i
  fin_cases i <;> simp [Function.update_apply, hz]

/-! ### `I = 2^E·pS·mass² + 1` -/

def h41 : Fin 5 ↪ Fin 12 := ⟨![4, 1, 5, 6, 7], by decide⟩
def h54 : Fin 5 ↪ Fin 12 := ⟨![5, 4, 6, 7, 8], by decide⟩
def h35 : Fin 5 ↪ Fin 12 := ⟨![3, 5, 6, 7, 8], by decide⟩
def p23 : Fin 4 ↪ Fin 12 := ⟨![2, 3, 6, 7], by decide⟩
@[simp] theorem h41_apply (i : Fin 5) : h41 i = ![4, 1, 5, 6, 7] i := rfl
@[simp] theorem h54_apply (i : Fin 5) : h54 i = ![5, 4, 6, 7, 8] i := rfl
@[simp] theorem h35_apply (i : Fin 5) : h35 i = ![3, 5, 6, 7, 8] i := rfl
@[simp] theorem p23_apply (i : Fin 4) : p23 i = ![2, 3, 6, 7] i := rfl

/-- `S4 := 2·pS·pM`, `S5 := pS·S4·S4`; `S = (pS, pM, E, out, scratch)`. -/
def massAW (S : Fin 12 ↪ Fin nr) : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (S 0) (S 4) (S 5)) (.seq (mulByW (h41.trans S)) (.seq (dbl (S 4) (S 5))
  (.seq (FinalPass.Hash4.wcopyR (S 0) (S 5) (S 6)) (.seq (mulByW (h54.trans S)) (mulByW (h54.trans S))))))

theorem massAW_spec (S : Fin 12 ↪ Fin nr) (σ : WState ns nr) (pS pM : ℕ) (h0 : σ.val (S 0) = pS)
    (h1 : σ.val (S 1) = pM) (hz : ∀ i : Fin 12, 3 ≤ i.val → σ.val (S i) = 0) (hS : pS ≤ cap) (hM : pM ≤ cap)
    (hm : 2 * (pS * pM) ≤ cap) (hq1 : pS * (2 * (pS * pM)) ≤ cap)
    (hq2 : pS * (2 * (pS * pM)) * (2 * (pS * pM)) ≤ cap) :
    WExec cap (massAW S) σ ((σ.setv (S 4) (2 * (pS * pM))).setv (S 5) (pS * (2 * (pS * pM)) * (2 * (pS * pM))))
      (18 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  unfold massAW
  refine seqD cap _ 1 (copy1 cap (S 0) (S 4) (S 5) (by simp) (by simp) (by simp) pS σ h0 (by simp [hz])
    (by simp [hz]) hS) (by omega) (by omega) ?_
  refine seqD cap _ 3 (mulBy1 cap (h41.trans S) pS pM _ (by simp) (by simp [h1]) (by simp [hz]) (by simp [hz])
    (by simp [hz]) (by omega) hS hM) (by omega) (by omega) ?_
  refine seqD cap _ 1 (dbl1 cap (S 4) (S 5) (by simp) (pS * pM) _ (by simp) (by simp [hz]) hm) (by omega)
    (by omega) ?_
  refine seqD cap _ 1 (copy1 cap (S 0) (S 5) (S 6) (by simp) (by simp) (by simp) pS _ (by simp [h0]) (by simp [hz])
    (by simp [hz]) hS) (by omega) (by omega) ?_
  refine seqD cap _ 3 (mulBy1 cap (h54.trans S) pS (2 * (pS * pM)) _ (by simp) (by simp) (by simp [hz])
    (by simp [hz]) (by simp [hz]) hq1 hS hm) (by omega) (by omega) ?_
  refine endD cap _ 3 (mulBy1 cap (h54.trans S) (pS * (2 * (pS * pM))) (2 * (pS * pM)) _ (by simp) (by simp)
    (by simp [hz]) (by simp [hz]) (by simp [hz]) hq2 hq1 hm) ?_ (by omega) (by omega)
  simp only [Function.Embedding.trans_apply, h41_apply, h54_apply, Matrix.cons_val]
  clear h0 h1 hS hM hm hq1 hq2 hsq
  have hb0 := setv_base S σ
  simp only [hb0, setv_blk]
  congr 1
  funext i
  fin_cases i <;> simp [Function.update_apply, hz]

/-- `S3 := 2^{S2}·S5 + 1`, then `S4`, `S5` cleared. -/
def massBW (S : Fin 12 ↪ Fin nr) : WM ns nr :=
  .seq (pow2W (p23.trans S)) (.seq (mulByW (h35.trans S)) (.seq (.inc (S 3)) (.seq (WM.clear (S 4))
    (WM.clear (S 5)))))

theorem massBW_spec (S : Fin 12 ↪ Fin nr) (τ : WState ns nr) (E ms P : ℕ) (h2 : τ.val (S 2) = E)
    (h3 : τ.val (S 3) = 0) (h4 : τ.val (S 4) = ms) (h5 : τ.val (S 5) = P)
    (hz : ∀ i : Fin 12, 6 ≤ i.val → τ.val (S i) = 0) (hP : P ≤ cap) (hms : ms ≤ cap)
    (hE : 2 ^ (E + 1) ≤ cap) (hI : 2 ^ E * P + 1 < cap) :
    WExec cap (massBW S) τ (((τ.setv (S 3) (2 ^ E * P + 1)).setv (S 4) 0).setv (S 5) 0) (11 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  have hp2 : 2 ^ E ≤ cap := le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hE
  unfold massBW
  refine seqD cap _ 1 (pow2v cap (p23.trans S) E τ (by simp [h2]) (by simp [h3]) (by simp [hz]) (by simp [hz]) hE)
    (by omega) (by omega) ?_
  refine seqD cap _ 3 (mulBy1 cap (h35.trans S) (2 ^ E) P _ (by simp) (by simp [h5]) (by simp [hz]) (by simp [hz])
    (by simp [hz]) (by omega) hp2 hP) (by omega) (by omega) ?_
  refine seqD cap _ 1 (inc1 cap (S 3) (2 ^ E * P) _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (clear1 cap (S 4) ms _ (by simp [h4]) hms) (by omega) (by omega) ?_
  refine endD cap _ 1 (clear1 cap (S 5) P _ (by simp [h5]) hP) ?_ (by omega) (by omega)
  simp only [Function.Embedding.trans_apply, p23_apply, h35_apply, Matrix.cons_val]
  clear h2 h4 h5 hP hms hE hI hsq hp2
  have hb0 := setv_base S τ
  simp only [hb0, setv_blk]
  congr 1
  funext i
  fin_cases i <;> simp [Function.update_apply, hz, h3]

/-- **`I`** from `pS`, `pM`, `E`: `S3 := 2^E·pS·(2pSpM)² + 1`. -/
theorem massW_spec (S : Fin 12 ↪ Fin nr) (σ : WState ns nr) (pS pM E : ℕ) (h0 : σ.val (S 0) = pS)
    (h1 : σ.val (S 1) = pM) (h2 : σ.val (S 2) = E) (hz : ∀ i : Fin 12, 3 ≤ i.val → σ.val (S i) = 0)
    (hS : pS ≤ cap) (hM : pM ≤ cap) (hm : 2 * (pS * pM) ≤ cap) (hq1 : pS * (2 * (pS * pM)) ≤ cap)
    (hq2 : pS * (2 * (pS * pM)) * (2 * (pS * pM)) ≤ cap) (hE : 2 ^ (E + 1) ≤ cap)
    (hI : 2 ^ E * (pS * (2 * (pS * pM)) * (2 * (pS * pM))) + 1 < cap) :
    WExec cap (.seq (massAW S) (massBW S)) σ (σ.setv (S 3) (2 ^ E * (pS * (2 * (pS * pM)) * (2 * (pS * pM))) + 1))
      (30 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  have hA := massAW_spec cap S σ pS pM h0 h1 hz hS hM hm hq1 hq2
  have hB := massBW_spec cap S ((σ.setv (S 4) (2 * (pS * pM))).setv (S 5) (pS * (2 * (pS * pM)) * (2 * (pS * pM))))
    E (2 * (pS * pM)) (pS * (2 * (pS * pM)) * (2 * (pS * pM))) (by simp [h2]) (by simp [hz]) (by simp) (by simp)
    (fun i hi => by
      have h4 : i ≠ 4 := by intro h; subst h; simp at hi
      have h5 : i ≠ 5 := by intro h; subst h; simp at hi
      simp [Function.update_apply, h4, h5, hz i (by omega)]) hq2 hm hE hI
  refine WExec.cast cap (WExec.seq hA hB) ?_ (by omega)
  clear hA hB h0 h1 h2 hS hM hm hq1 hq2 hE hI hsq
  have hb0 := setv_base S σ
  simp only [hb0, setv_blk]
  congr 1
  funext i
  fin_cases i <;> simp [Function.update_apply, hz]

/-! ### `Q = 2^{(5kh+3)/4}·(2^{13}·I·n²)` -/

def q45 : Fin 5 ↪ Fin 12 := ⟨![4, 5, 6, 7, 8], by decide⟩
def q56 : Fin 5 ↪ Fin 12 := ⟨![5, 6, 7, 8, 9], by decide⟩
def q52 : Fin 5 ↪ Fin 12 := ⟨![5, 2, 6, 7, 8], by decide⟩
def r43 : Fin 4 ↪ Fin 12 := ⟨![4, 3, 5, 6], by decide⟩
@[simp] theorem q45_apply (i : Fin 5) : q45 i = ![4, 5, 6, 7, 8] i := rfl
@[simp] theorem q56_apply (i : Fin 5) : q56 i = ![5, 6, 7, 8, 9] i := rfl
@[simp] theorem q52_apply (i : Fin 5) : q52 i = ![5, 2, 6, 7, 8] i := rfl
@[simp] theorem r43_apply (i : Fin 4) : r43 i = ![4, 3, 5, 6] i := rfl

/-- `S4 := (5kh+3)/4`; `S = (I, kh, n, out, scratch)`. -/
def qAW (S : Fin 12 ↪ Fin nr) : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (S 1) (S 4) (S 5)) (.seq (StarNums.incN (S 5) 5) (.seq (mulByW (q45.trans S))
  (.seq (WM.clear (S 5)) (.seq (StarNums.incN (S 4) 3) (.seq (halveM (S 4) (S 5) (S 6)) (.seq (WM.clear (S 6))
  (.seq (halveM (S 4) (S 5) (S 6)) (WM.clear (S 6)))))))))

theorem qAW_spec (S : Fin 12 ↪ Fin nr) (σ : WState ns nr) (kh : ℕ) (h1 : σ.val (S 1) = kh)
    (hz : ∀ i : Fin 12, 3 ≤ i.val → σ.val (S i) = 0) (hc : kh * 5 + 8 ≤ cap) :
    WExec cap (qAW S) σ (σ.setv (S 4) ((kh * 5 + 3) / 2 / 2)) (20 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  unfold qAW
  refine seqD cap _ 1 (copy1 cap (S 1) (S 4) (S 5) (by simp) (by simp) (by simp) kh σ h1 (by simp [hz])
    (by simp [hz]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (incN0 cap (S 5) 5 _ (by simp [hz]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 3 (mulBy1 cap (q45.trans S) kh 5 _ (by simp) (by simp) (by simp [hz]) (by simp [hz])
    (by simp [hz]) (by omega) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (clear1 cap (S 5) 5 _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (incN1 cap (S 4) (kh * 5) 3 _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (halve1 cap (S 4) (S 5) (S 6) (by simp) (by simp) (by simp) (kh * 5 + 3) _ (by simp)
    (by simp) (by simp [hz]) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (clear1 cap (S 6) ((kh * 5 + 3) % 2) _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (halve1 cap (S 4) (S 5) (S 6) (by simp) (by simp) (by simp) ((kh * 5 + 3) / 2) _ (by simp)
    (by simp) (by simp) (by omega) (by omega)) (by omega) (by omega) ?_
  refine endD cap _ 1 (clear1 cap (S 6) ((kh * 5 + 3) / 2 % 2) _ (by simp) (by omega)) ?_ (by omega) (by omega)
  simp only [Function.Embedding.trans_apply, q45_apply, Matrix.cons_val]
  clear h1 hc hsq
  have hb0 := setv_base S σ
  simp only [hb0, setv_blk]
  congr 1
  funext i
  fin_cases i <;> simp [Function.update_apply, hz]

/-- `S3 := 2^{S4}`, `S5 := S0·8192`. -/
def qB1W (S : Fin 12 ↪ Fin nr) : WM ns nr :=
  .seq (pow2W (r43.trans S)) (.seq (FinalPass.Hash4.wcopyR (S 0) (S 5) (S 6)) (.seq (StarNums.incN (S 6) 8192)
  (.seq (mulByW (q56.trans S)) (WM.clear (S 6)))))

theorem qB1W_spec (S : Fin 12 ↪ Fin nr) (τ : WState ns nr) (I X : ℕ) (h0 : τ.val (S 0) = I) (h3 : τ.val (S 3) = 0)
    (h4 : τ.val (S 4) = X) (hz : ∀ i : Fin 12, 5 ≤ i.val → τ.val (S i) = 0) (hX : 2 ^ (X + 1) ≤ cap)
    (hI : I * 8192 + 8192 ≤ cap) :
    WExec cap (qB1W S) τ ((τ.setv (S 3) (2 ^ X)).setv (S 5) (I * 8192)) (12 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  unfold qB1W
  refine seqD cap _ 1 (pow2v cap (r43.trans S) X τ (by simp [h4]) (by simp [h3]) (by simp [hz]) (by simp [hz]) hX)
    (by omega) (by omega) ?_
  refine seqD cap _ 1 (copy1 cap (S 0) (S 5) (S 6) (by simp) (by simp) (by simp) I _ (by simp [h0]) (by simp [hz])
    (by simp [hz]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (incN0 cap (S 6) 8192 _ (by simp [hz]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 3 (mulBy1 cap (q56.trans S) I 8192 _ (by simp) (by simp) (by simp [hz]) (by simp [hz])
    (by simp [hz]) (by omega) (by omega) (by omega)) (by omega) (by omega) ?_
  refine endD cap _ 1 (clear1 cap (S 6) 8192 _ (by simp) (by omega)) ?_ (by omega) (by omega)
  simp only [Function.Embedding.trans_apply, r43_apply, q56_apply, Matrix.cons_val]
  clear h0 h4 hX hI hsq
  have hb0 := setv_base S τ
  simp only [hb0, setv_blk]
  congr 1
  funext i
  fin_cases i <;> simp [Function.update_apply, hz, h3]

/-- `S5 ·= n·n`, `S3 ·= S5`, then `S5`, `S4` cleared. -/
def qB2W (S : Fin 12 ↪ Fin nr) : WM ns nr :=
  .seq (mulByW (q52.trans S)) (.seq (mulByW (q52.trans S)) (.seq (mulByW (h35.trans S)) (.seq (WM.clear (S 5))
    (WM.clear (S 4)))))

theorem qB2W_spec (S : Fin 12 ↪ Fin nr) (τ : WState ns nr) (n X T : ℕ) (h2 : τ.val (S 2) = n)
    (h3 : τ.val (S 3) = 2 ^ X) (h4 : τ.val (S 4) = X) (h5 : τ.val (S 5) = T)
    (hz : ∀ i : Fin 12, 6 ≤ i.val → τ.val (S i) = 0) (hn : n ≤ cap) (hX : X ≤ cap) (hp : 2 ^ X ≤ cap)
    (hT1 : T * n ≤ cap) (hT2 : T * n * n ≤ cap) (hQ : 2 ^ X * (T * n * n) ≤ cap) (hT : T ≤ cap) :
    WExec cap (qB2W S) τ (((τ.setv (S 3) (2 ^ X * (T * n * n))).setv (S 5) 0).setv (S 4) 0) (16 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  unfold qB2W
  refine seqD cap _ 3 (mulBy1 cap (q52.trans S) T n τ (by simp [h5]) (by simp [h2]) (by simp [hz]) (by simp [hz])
    (by simp [hz]) hT1 hT hn) (by omega) (by omega) ?_
  refine seqD cap _ 3 (mulBy1 cap (q52.trans S) (T * n) n _ (by simp) (by simp [h2]) (by simp [hz]) (by simp [hz])
    (by simp [hz]) hT2 hT1 hn) (by omega) (by omega) ?_
  refine seqD cap _ 3 (mulBy1 cap (h35.trans S) (2 ^ X) (T * n * n) _ (by simp [h3]) (by simp) (by simp [hz])
    (by simp [hz]) (by simp [hz]) hQ hp hT2) (by omega) (by omega) ?_
  refine seqD cap _ 1 (clear1 cap (S 5) (T * n * n) _ (by simp) hT2) (by omega) (by omega) ?_
  refine endD cap _ 1 (clear1 cap (S 4) X _ (by simp [h4]) hX) ?_ (by omega) (by omega)
  simp only [Function.Embedding.trans_apply, q52_apply, h35_apply, Matrix.cons_val]
  clear h2 h4 h5 hn hX hp hT1 hT2 hQ hT hsq
  have hb0 := setv_base S τ
  simp only [hb0, setv_blk]
  congr 1
  funext i
  fin_cases i <;> simp [Function.update_apply, hz]

/-- **`Q`**: `S3 := 2^{(5kh+3)/4}·(I·8192·n·n)`; `S = (I, kh, n, out, scratch)`. -/
theorem qW_spec (S : Fin 12 ↪ Fin nr) (σ : WState ns nr) (I kh n : ℕ) (h0 : σ.val (S 0) = I)
    (h1 : σ.val (S 1) = kh) (h2 : σ.val (S 2) = n) (hz : ∀ i : Fin 12, 3 ≤ i.val → σ.val (S i) = 0)
    (hc : kh * 5 + 8 ≤ cap) (hn : n ≤ cap) (hX : 2 ^ ((kh * 5 + 3) / 2 / 2 + 1) ≤ cap) (hI : I * 8192 + 8192 ≤ cap)
    (hT1 : I * 8192 * n ≤ cap) (hT2 : I * 8192 * n * n ≤ cap)
    (hQ : 2 ^ ((kh * 5 + 3) / 2 / 2) * (I * 8192 * n * n) ≤ cap) :
    WExec cap (.seq (qAW S) (.seq (qB1W S) (qB2W S))) σ
      (σ.setv (S 3) (2 ^ ((kh * 5 + 3) / 2 / 2) * (I * 8192 * n * n))) (51 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  set X := (kh * 5 + 3) / 2 / 2 with hXd
  have hXl : X < 2 ^ X := Nat.lt_two_pow_self
  have hp : 2 ^ X ≤ cap := le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hX
  have hA := qAW_spec cap S σ kh h1 hz hc
  have hB1 := qB1W_spec cap S (σ.setv (S 4) X) I X (by simp [h0]) (by simp [hz]) (by simp)
    (fun i hi => by
      have h4 : i ≠ 4 := by intro h; subst h; simp at hi
      simp [Function.update_apply, h4, hz i (by omega)]) hX hI
  have hB2 := qB2W_spec cap S (((σ.setv (S 4) X).setv (S 3) (2 ^ X)).setv (S 5) (I * 8192)) n X (I * 8192)
    (by simp [h2]) (by simp) (by simp) (by simp)
    (fun i hi => by
      have h4 : i ≠ 4 := by intro h; subst h; simp at hi
      have h3 : i ≠ 3 := by intro h; subst h; simp at hi
      have h5 : i ≠ 5 := by intro h; subst h; simp at hi
      simp [Function.update_apply, h4, h3, h5, hz i (by omega)]) hn (by omega) hp hT1 hT2 hQ (by omega)
  refine WExec.cast cap (WExec.seq hA (WExec.seq hB1 hB2)) ?_ (by omega)
  clear hA hB1 hB2 h0 h1 h2 hc hn hX hI hT1 hT2 hQ hXl hp hsq
  have hb0 := setv_base S σ
  simp only [hb0, setv_blk]
  congr 1
  funext i
  fin_cases i <;> simp [Function.update_apply, hz]

end Parts

/-! ## The whole count

The block `K : Fin 64 ↪ Fin nr`: inputs `0` cap, `1` n, `2` errExp, `3` L, `4` kh, `5` numCar, `6` a, `7 … 10` the bottom
counts; the filter's `11` prefixBits, `12` labelBits, `13` fieldBits, `14` walkLen; outputs `40` seed bits, `41` B,
`42` M, `43` J, `44` ⌈log₂M⌉, `45` rank, `46` side bits, `47` the list's walk, `48` E, `49` Π(m+1)², `50` 2^a·Π(3m+1),
`51` I, `52` Q; scratch `15 … 39` and `53 … 63`. -/

section Top
variable {ns nr : ℕ} (cap : ℕ)

def gB : Fin 32 ↪ Fin 64 := ⟨![0, 1, 2, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
  32, 33, 34, 35, 36, 37, 38, 39], by decide⟩
def sS : Fin 10 ↪ Fin 64 := ⟨![12, 13, 14, 40, 15, 16, 17, 18, 19, 20], by decide⟩
def bS : Fin 14 ↪ Fin 64 := ⟨![5, 0, 7, 8, 9, 10, 41, 42, 15, 16, 17, 18, 19, 20], by decide⟩
def cBS : Fin 10 ↪ Fin 64 := ⟨![41, 43, 15, 16, 17, 18, 19, 20, 21, 22], by decide⟩
def cMS : Fin 10 ↪ Fin 64 := ⟨![42, 44, 15, 16, 17, 18, 19, 20, 21, 22], by decide⟩
def mxS : Fin 10 ↪ Fin 64 := ⟨![43, 44, 45, 15, 16, 17, 18, 19, 20, 21], by decide⟩
@[simp] theorem gB_apply (i : Fin 32) : gB i = ![0, 1, 2, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26,
  27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39] i := rfl
@[simp] theorem sS_apply (i : Fin 10) : sS i = ![12, 13, 14, 40, 15, 16, 17, 18, 19, 20] i := rfl
@[simp] theorem bS_apply (i : Fin 14) : bS i = ![5, 0, 7, 8, 9, 10, 41, 42, 15, 16, 17, 18, 19, 20] i := rfl
@[simp] theorem cBS_apply (i : Fin 10) : cBS i = ![41, 43, 15, 16, 17, 18, 19, 20, 21, 22] i := rfl
@[simp] theorem cMS_apply (i : Fin 10) : cMS i = ![42, 44, 15, 16, 17, 18, 19, 20, 21, 22] i := rfl
@[simp] theorem mxS_apply (i : Fin 10) : mxS i = ![43, 44, 45, 15, 16, 17, 18, 19, 20, 21] i := rfl

/-- Registers of `K` at the listed indices are unchanged. -/
def Same (K : Fin 64 ↪ Fin nr) (τ τ' : WState ns nr) (js : List (Fin 64)) : Prop := ∀ j ∈ js, τ'.val (K j) = τ.val (K j)

/-- Everything outside the block is unchanged. -/
def Frm (K : Fin 64 ↪ Fin nr) (τ τ' : WState ns nr) : Prop :=
  τ'.st = τ.st ∧ τ'.sh = τ.sh ∧ τ'.cell = τ.cell ∧ ∀ r, (∀ i, K i ≠ r) → τ'.val r = τ.val r

theorem Frm.trans {K : Fin 64 ↪ Fin nr} {τ τ' τ'' : WState ns nr} (h1 : Frm K τ τ') (h2 : Frm K τ' τ'') :
    Frm K τ τ'' :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, fun r hr => (h2.2.2.2 r hr).trans (h1.2.2.2 r hr)⟩

/-- Stage A: the filter's numbers and the seed bits (`K 40`). -/
def stAW (K : Fin 64 ↪ Fin nr) : WM ns nr :=
  .seq (filtM (gB.trans K)) (.seq (sgA (sS.trans K)) (sgB (sS.trans K)))

theorem stA_spec (K : Fin 64 ↪ Fin nr) (σ : WState ns nr) (x : SymIn) (c0 : σ.val (K 0) = x.capS)
    (c1 : σ.val (K 1) = x.n) (c2 : σ.val (K 2) = x.errExp) (hz : ∀ i : Fin 64, 11 ≤ i.val → σ.val (K i) = 0)
    (hcS : 1 ≤ x.capS) (hn : 2 ≤ x.n) (hcap : 2 * x.Q ≤ cap) :
    ∃ τ, WExec cap (stAW K) σ τ (240 * UnaryPow.sq cap) ∧ τ.val (K 40) = x.FP.seedBits ∧
      Same K σ τ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 15, 16, 17, 18, 19, 20, 21, 22, 41, 42, 43, 44, 45, 46, 47, 48, 49,
        50, 51, 52] ∧ Frm K σ τ := by
  have hsq := UnaryPow.sq_ge cap
  have hQ1 := x.I_small_le_Q hn
  have hEI := x.twoE_le_I
  have hEle : x.E < 2 ^ x.E := Nat.lt_two_pow_self
  have hc1 := x.cap_le_E hcS
  have hc2 := x.len_le_E hcS
  have hc3 := x.errExp_le_E hcS
  have hn1 := x.n_le_E hcS
  have hlb := x.lb_ge hcS
  have hsG := x.sG_eq hcS
  have hsGE : x.FP.seedBits ≤ x.E := by rw [x.E_eq]; omega
  have hFP0 : x.FP.cap = x.capS := rfl
  have hFP2 : x.FP.errExp = x.errExp := rfl
  have h := WExec.seq (filtM_spec cap (gB.trans K) σ x.FP x.n rfl (by simp [c0]; rfl) (by simp [c1])
    (by simp [c2]; rfl)
    (fun i hi => by simp only [Function.Embedding.trans_apply]; exact hz _ (by fin_cases i <;> simp at hi ⊢))
    hcS (by omega) (by rw [hFP0]; omega) (by omega) (by omega) (by rw [hFP2]; omega))
    (WExec.seq (sgA_spec cap (sS.trans K) _ x.FP.labelBits x.FP.fieldBits (by simp) (by simp)
      (fun i hi => by fin_cases i <;> simp [hz] at hi ⊢) hlb (by omega))
    (sgB_spec cap (sS.trans K) _ ((x.FP.labelBits + x.FP.labelBits + x.FP.labelBits - 1 +
      x.FP.fieldBits + x.FP.fieldBits) * 256) x.FP.walkLen (by simp) (by simp)
      (fun i hi => by fin_cases i <;> simp [hz] at hi ⊢) (by omega)))
  simp only [Function.Embedding.trans_apply, gB_apply, sS_apply, Matrix.cons_val] at h
  refine ⟨_, WExec.mono h (by omega), by simp [hsG], by simp [Same], ?_⟩
  refine ⟨by simp, by simp, by simp, fun r hr => ?_⟩
  have hr' : ∀ i, r ≠ K i := fun i h => hr i h.symm
  simp [Function.update_apply, hr']

def sbS : Fin 10 ↪ Fin 64 := ⟨![45, 46, 15, 16, 17, 18, 19, 20, 21, 22], by decide⟩
@[simp] theorem sbS_apply (i : Fin 10) : sbS i = ![45, 46, 15, 16, 17, 18, 19, 20, 21, 22] i := rfl
def wlS : Fin 10 ↪ Fin 64 := ⟨![3, 47, 15, 16, 17, 18, 19, 20, 21, 22], by decide⟩
@[simp] theorem wlS_apply (i : Fin 10) : wlS i = ![3, 47, 15, 16, 17, 18, 19, 20, 21, 22] i := rfl
def pS0 : Fin 10 ↪ Fin 64 := ⟨![7, 49, 15, 16, 17, 18, 19, 20, 21, 22], by decide⟩
@[simp] theorem pS0_apply (i : Fin 10) : pS0 i = ![7, 49, 15, 16, 17, 18, 19, 20, 21, 22] i := rfl
def pS1 : Fin 10 ↪ Fin 64 := ⟨![8, 49, 15, 16, 17, 18, 19, 20, 21, 22], by decide⟩
@[simp] theorem pS1_apply (i : Fin 10) : pS1 i = ![8, 49, 15, 16, 17, 18, 19, 20, 21, 22] i := rfl
def pS2 : Fin 10 ↪ Fin 64 := ⟨![9, 49, 15, 16, 17, 18, 19, 20, 21, 22], by decide⟩
@[simp] theorem pS2_apply (i : Fin 10) : pS2 i = ![9, 49, 15, 16, 17, 18, 19, 20, 21, 22] i := rfl
def pS3 : Fin 10 ↪ Fin 64 := ⟨![10, 49, 15, 16, 17, 18, 19, 20, 21, 22], by decide⟩
@[simp] theorem pS3_apply (i : Fin 10) : pS3 i = ![10, 49, 15, 16, 17, 18, 19, 20, 21, 22] i := rfl
def pM0 : Fin 10 ↪ Fin 64 := ⟨![7, 50, 15, 16, 17, 18, 19, 20, 21, 22], by decide⟩
@[simp] theorem pM0_apply (i : Fin 10) : pM0 i = ![7, 50, 15, 16, 17, 18, 19, 20, 21, 22] i := rfl
def pM1 : Fin 10 ↪ Fin 64 := ⟨![8, 50, 15, 16, 17, 18, 19, 20, 21, 22], by decide⟩
@[simp] theorem pM1_apply (i : Fin 10) : pM1 i = ![8, 50, 15, 16, 17, 18, 19, 20, 21, 22] i := rfl
def pM2 : Fin 10 ↪ Fin 64 := ⟨![9, 50, 15, 16, 17, 18, 19, 20, 21, 22], by decide⟩
@[simp] theorem pM2_apply (i : Fin 10) : pM2 i = ![9, 50, 15, 16, 17, 18, 19, 20, 21, 22] i := rfl
def pM3 : Fin 10 ↪ Fin 64 := ⟨![10, 50, 15, 16, 17, 18, 19, 20, 21, 22], by decide⟩
@[simp] theorem pM3_apply (i : Fin 10) : pM3 i = ![10, 50, 15, 16, 17, 18, 19, 20, 21, 22] i := rfl
def eS : Fin 10 ↪ Fin 64 := ⟨![40, 46, 47, 48, 15, 16, 17, 18, 19, 20], by decide⟩
@[simp] theorem eS_apply (i : Fin 10) : eS i = ![40, 46, 47, 48, 15, 16, 17, 18, 19, 20] i := rfl
def p2S : Fin 4 ↪ Fin 64 := ⟨![6, 50, 15, 16], by decide⟩
@[simp] theorem p2S_apply (i : Fin 4) : p2S i = ![6, 50, 15, 16] i := rfl
def maS : Fin 12 ↪ Fin 64 := ⟨![49, 50, 48, 51, 15, 16, 17, 18, 19, 20, 21, 22], by decide⟩
@[simp] theorem maS_apply (i : Fin 12) : maS i = ![49, 50, 48, 51, 15, 16, 17, 18, 19, 20, 21, 22] i := rfl
def qS : Fin 12 ↪ Fin 64 := ⟨![51, 4, 1, 52, 15, 16, 17, 18, 19, 20, 21, 22], by decide⟩
@[simp] theorem qS_apply (i : Fin 12) : qS i = ![51, 4, 1, 52, 15, 16, 17, 18, 19, 20, 21, 22] i := rfl

/-- Stage B: `B`, `M`, `J`, `⌈log₂M⌉`, the rank (`K 41 … 45`). -/
def stBW (K : Fin 64 ↪ Fin nr) : WM ns nr :=
  .seq (bmW (bS.trans K)) (.seq (clogW (cBS.trans K)) (.seq (StarNums.incN (K 43) 9) (.seq (clogW (cMS.trans K))
    (maxW (mxS.trans K)))))

theorem stB_spec (K : Fin 64 ↪ Fin nr) (τ : WState ns nr) (x : SymIn) (c0 : τ.val (K 0) = x.capS)
    (c5 : τ.val (K 5) = x.numCar) (c7 : τ.val (K 7) = x.m 0) (c8 : τ.val (K 8) = x.m 1) (c9 : τ.val (K 9) = x.m 2)
    (c10 : τ.val (K 10) = x.m 3) (hz : ∀ i : Fin 64, i ∈ [15, 16, 17, 18, 19, 20, 21, 22, 41, 42, 43, 44, 45] →
      τ.val (K i) = 0) (hcS : 1 ≤ x.capS) (hn : 2 ≤ x.n) (hcap : 2 * x.Q ≤ cap) :
    ∃ τ', WExec cap (stBW K) τ τ' (75 * UnaryPow.sq cap) ∧ τ'.val (K 41) = x.Bv ∧ τ'.val (K 42) = x.Mv ∧
      τ'.val (K 45) = x.rank ∧ Same K τ τ' [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 15, 16, 17, 18, 19, 20, 21, 22, 40, 46,
        47, 48, 49, 50, 51, 52] ∧ Frm K τ τ' := by
  have hsq := UnaryPow.sq_ge cap
  have hQ1 := x.I_small_le_Q hn
  have hEI := x.twoE_le_I
  have hc1 := x.cap_le_E hcS
  have hc4 := x.B_le_E
  have hc5 := x.M_le_E
  have hrk := x.rank_eq
  have hr3 := x.rank3_le_E
  have hEle : x.E < 2 ^ x.E := Nat.lt_two_pow_self
  have hBv : x.Bv = x.capS * 4096 * x.numCar := by unfold SymIn.Bv; ring
  have hMv : x.Mv = x.m 0 + x.m 1 + x.m 2 + x.m 3 := rfl
  have hncB : x.numCar ≤ x.Bv := by rw [hBv]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hcB : Nat.clog 2 x.Bv + 9 ≤ x.rank := by rw [hrk]; omega
  have hcM : Nat.clog 2 x.Mv ≤ x.rank := by rw [hrk]; omega
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
  have h := WExec.seq (bmW_spec cap (bS.trans K) τ x.numCar x.capS (x.m 0) (x.m 1) (x.m 2) (x.m 3) (by simp [c5])
      (by simp [c0]) (by simp [c7]) (by simp [c8]) (by simp [c9]) (by simp [c10])
      (fun i hi => by fin_cases i <;> simp at hi ⊢ <;> exact hz _ (by decide)) (by rw [← hBv]; omega))
    (WExec.seq (clogW_spec cap (cBS.trans K) _ x.Bv (by simp [hBv])
      (fun i hi => by fin_cases i <;> simp at hi ⊢ <;> exact hz _ (by decide)) (by omega))
    (WExec.seq (incN1 cap (K 43) (Nat.clog 2 x.Bv) 9 _ (by simp) (by omega))
    (WExec.seq (clogW_spec cap (cMS.trans K) _ x.Mv (by simp [hMv])
      (fun i hi => by fin_cases i <;> simp at hi ⊢ <;> exact hz _ (by decide)) (by omega))
    (maxW_spec cap (mxS.trans K) _ (Nat.clog 2 x.Bv + 9) (Nat.clog 2 x.Mv) (by simp) (by simp)
      (fun i hi => by fin_cases i <;> simp at hi ⊢ <;> exact hz _ (by decide)) (by omega) (by omega) (by omega)))))
  simp only [Function.Embedding.trans_apply, bS_apply, cBS_apply, cMS_apply, mxS_apply, Matrix.cons_val] at h
  refine ⟨_, WExec.mono h (by omega), by simp [hBv], by simp [hMv], by simp [hrk], by simp [Same], ?_⟩
  refine ⟨by simp, by simp, by simp, fun r hr => ?_⟩
  have hr' : ∀ i, r ≠ K i := fun i h => hr i h.symm
  simp [Function.update_apply, hr']

/-- Stage C: the walk side bits, the list's walk, `E` (`K 46, 47, 48`). -/
def stCW (K : Fin 64 ↪ Fin nr) : WM ns nr :=
  .seq (sbW (sbS.trans K)) (.seq (wlW (wlS.trans K)) (.seq (eW (eS.trans K)) (sgB (eS.trans K))))

theorem stC_spec (K : Fin 64 ↪ Fin nr) (τ : WState ns nr) (x : SymIn) (c3 : τ.val (K 3) = x.L)
    (c40 : τ.val (K 40) = x.FP.seedBits) (c45 : τ.val (K 45) = x.rank)
    (hz : ∀ i : Fin 64, i ∈ [15, 16, 17, 18, 19, 20, 21, 22, 46, 47, 48] → τ.val (K i) = 0)
    (hn : 2 ≤ x.n) (hcap : 2 * x.Q ≤ cap) :
    ∃ τ', WExec cap (stCW K) τ τ' (52 * UnaryPow.sq cap) ∧ τ'.val (K 48) = x.E ∧
      Same K τ τ' [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 15, 16, 17, 18, 19, 20, 21, 22, 40, 41, 42, 45, 49, 50, 51, 52] ∧
      Frm K τ τ' := by
  have hsq := UnaryPow.sq_ge cap
  have hQ1 := x.I_small_le_Q hn
  have hEI := x.twoE_le_I
  have hEle : x.E < 2 ^ x.E := Nat.lt_two_pow_self
  have hr3 := x.rank3_le_E
  have hL := x.L_le_E
  have hEe := x.E_eq
  have hsb := x.sb_eq
  have hwl := x.wlL_eq
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
  have h := WExec.seq (sbW_spec cap (sbS.trans K) τ x.rank (by simp [c45])
      (fun i hi => by fin_cases i <;> simp at hi ⊢ <;> exact hz _ (by decide)) (by omega))
    (WExec.seq (wlW_spec cap (wlS.trans K) _ x.L (by simp [c3])
      (fun i hi => by fin_cases i <;> simp at hi ⊢ <;> exact hz _ (by decide)) (by omega))
    (WExec.seq (eW_spec cap (eS.trans K) _ x.FP.seedBits ((x.rank + x.rank + x.rank) / 2) (by simp [c40]) (by simp)
      (fun i hi => by fin_cases i <;> simp at hi ⊢ <;> exact hz _ (by decide)) (by rw [← hsb]; omega))
    (sgB_spec cap (eS.trans K) _ (x.FP.seedBits + (x.rank + x.rank + x.rank) / 2 + (x.rank + x.rank + x.rank) / 2)
      (2 * ((x.L + 5) / 2 / 2) + 1) (by simp) (by simp)
      (fun i hi => by fin_cases i <;> simp at hi ⊢ <;> exact hz _ (by decide)) (by rw [← hsb, ← hwl]; omega))))
  simp only [Function.Embedding.trans_apply, sbS_apply, wlS_apply, eS_apply, Matrix.cons_val] at h
  refine ⟨_, WExec.mono h (by omega), by simp [hEe, hsb, hwl], by simp [Same], ?_⟩
  refine ⟨by simp, by simp, by simp, fun r hr => ?_⟩
  have hr' : ∀ i, r ≠ K i := fun i h => hr i h.symm
  simp [Function.update_apply, hr']

/-- Stage D: `Π(m_j+1)²` and `2^a·Π(3m_j+1)` (`K 49, 50`). -/
def stDW (K : Fin 64 ↪ Fin nr) : WM ns nr :=
  .seq (.inc (K 49)) (.seq (sqStepW (pS0.trans K)) (.seq (sqStepW (pS1.trans K)) (.seq (sqStepW (pS2.trans K))
  (.seq (sqStepW (pS3.trans K)) (.seq (pow2W (p2S.trans K)) (.seq (modStepW (pM0.trans K))
  (.seq (modStepW (pM1.trans K)) (.seq (modStepW (pM2.trans K)) (modStepW (pM3.trans K))))))))))

theorem stD_spec (K : Fin 64 ↪ Fin nr) (τ : WState ns nr) (x : SymIn) (c6 : τ.val (K 6) = x.a)
    (c7 : τ.val (K 7) = x.m 0) (c8 : τ.val (K 8) = x.m 1) (c9 : τ.val (K 9) = x.m 2) (c10 : τ.val (K 10) = x.m 3)
    (hz : ∀ i : Fin 64, i ∈ [15, 16, 17, 18, 19, 20, 21, 22, 49, 50] → τ.val (K i) = 0)
    (hn : 2 ≤ x.n) (hcap : 2 * x.Q ≤ cap) :
    ∃ τ', WExec cap (stDW K) τ τ' (140 * UnaryPow.sq cap) ∧ τ'.val (K 49) = x.pSq ∧ τ'.val (K 50) = x.pMod ∧
      Same K τ τ' [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 15, 16, 17, 18, 19, 20, 21, 22, 40, 41, 42, 45, 48, 51, 52] ∧
      Frm K τ τ' := by
  have hsq := UnaryPow.sq_ge cap
  have hQ1 := x.I_small_le_Q hn
  have hEI := x.twoE_le_I
  have hPI := x.Pv_lt_I
  have hSP := x.pS_le_Pv
  have hMm := x.mass_ge
  have hmP := x.Pv_ge_mass
  have hM := x.M_le_E
  have hMv : x.Mv = x.m 0 + x.m 1 + x.m 2 + x.m 3 := rfl
  set a1 := 1 * (x.m 0 + 1) * (x.m 0 + 1) with ha1
  set a2 := a1 * (x.m 1 + 1) * (x.m 1 + 1) with ha2
  set a3 := a2 * (x.m 2 + 1) * (x.m 2 + 1) with ha3
  have ha4 : a3 * (x.m 3 + 1) * (x.m 3 + 1) = x.pSq := by
    unfold SymIn.pSq; rw [Fin.prod_univ_four]; simp only [ha1, ha2, ha3]; ring
  have hle : ∀ u v : ℕ, u ≤ u * (v + 1) * (v + 1) := fun u v => by
    have := Nat.le_mul_of_pos_right u (show 0 < (v + 1) * (v + 1) by positivity); rw [← Nat.mul_assoc] at this; exact this
  have h12 := hle a1 (x.m 1)
  have h23 := hle a2 (x.m 2)
  have h34 := hle a3 (x.m 3)
  set b0 := 2 ^ x.a with hb0
  set b1 := b0 * (x.m 0 * 3 + 1) with hb1
  set b2 := b1 * (x.m 1 * 3 + 1) with hb2
  set b3 := b2 * (x.m 2 * 3 + 1) with hb3
  have hb4 : b3 * (x.m 3 * 3 + 1) = x.pMod := by
    unfold SymIn.pMod; rw [Fin.prod_univ_four]; simp only [hb1, hb2, hb3, hb0]; ring
  have hle' : ∀ u v : ℕ, u ≤ u * (v * 3 + 1) := fun u v => Nat.le_mul_of_pos_right u (by omega)
  have hq01 := hle' b0 (x.m 0)
  have hq12 := hle' b1 (x.m 1)
  have hq23 := hle' b2 (x.m 2)
  have hq34 := hle' b3 (x.m 3)
  have hb0p : 1 ≤ b0 := Nat.one_le_two_pow
  have hpa : 2 ^ (x.a + 1) ≤ x.Pv := by rw [pow_succ]; omega
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
  have h := WExec.seq (inc1 cap (K 49) 0 τ (by simp [hz]) (by omega))
    (WExec.seq (sqStepW_spec cap (pS0.trans K) _ (x.m 0) 1 (by simp [c7]) (by simp [ha1, ha2, ha3, hb0, hb1, hb2, hb3])
      (fun i hi => by fin_cases i <;> simp at hi ⊢ <;> exact hz _ (by decide)) (by omega))
    (WExec.seq (sqStepW_spec cap (pS1.trans K) _ (x.m 1) a1 (by simp [c8]) (by simp [ha1, ha2, ha3, hb0, hb1, hb2, hb3])
      (fun i hi => by fin_cases i <;> simp at hi ⊢ <;> exact hz _ (by decide)) (by omega))
    (WExec.seq (sqStepW_spec cap (pS2.trans K) _ (x.m 2) a2 (by simp [c9]) (by simp [ha1, ha2, ha3, hb0, hb1, hb2, hb3])
      (fun i hi => by fin_cases i <;> simp at hi ⊢ <;> exact hz _ (by decide)) (by omega))
    (WExec.seq (sqStepW_spec cap (pS3.trans K) _ (x.m 3) a3 (by simp [c10]) (by simp [ha1, ha2, ha3, hb0, hb1, hb2, hb3])
      (fun i hi => by fin_cases i <;> simp at hi ⊢ <;> exact hz _ (by decide)) (by omega))
    (WExec.seq (pow2v cap (p2S.trans K) x.a _ (by simp [c6]) (by simp [hz]) (by simp [hz]) (by simp [hz]) (by omega))
    (WExec.seq (modStepW_spec cap (pM0.trans K) _ (x.m 0) b0 (by simp [c7]) (by simp [ha1, ha2, ha3, hb0, hb1, hb2, hb3])
      (fun i hi => by fin_cases i <;> simp at hi ⊢ <;> exact hz _ (by decide)) (by omega) hb0p)
    (WExec.seq (modStepW_spec cap (pM1.trans K) _ (x.m 1) b1 (by simp [c8]) (by simp [ha1, ha2, ha3, hb0, hb1, hb2, hb3])
      (fun i hi => by fin_cases i <;> simp at hi ⊢ <;> exact hz _ (by decide)) (by omega) (by omega))
    (WExec.seq (modStepW_spec cap (pM2.trans K) _ (x.m 2) b2 (by simp [c9]) (by simp [ha1, ha2, ha3, hb0, hb1, hb2, hb3])
      (fun i hi => by fin_cases i <;> simp at hi ⊢ <;> exact hz _ (by decide)) (by omega) (by omega))
    (modStepW_spec cap (pM3.trans K) _ (x.m 3) b3 (by simp [c10]) (by simp [ha1, ha2, ha3, hb0, hb1, hb2, hb3])
      (fun i hi => by fin_cases i <;> simp at hi ⊢ <;> exact hz _ (by decide)) (by omega) (by omega))))))))))
  simp only [Function.Embedding.trans_apply, pS0_apply, pS1_apply, pS2_apply, pS3_apply, p2S_apply, pM0_apply,
    pM1_apply, pM2_apply, pM3_apply, Matrix.cons_val] at h
  refine ⟨_, WExec.mono h (by omega), by simp [← ha4], by simp [← hb4], by simp [Same], ?_⟩
  refine ⟨by simp, by simp, by simp, fun r hr => ?_⟩
  have hr' : ∀ i, r ≠ K i := fun i h => hr i h.symm
  simp [Function.update_apply, hr']

/-- Stage E: `I` (`K 51`). -/
def stEW (K : Fin 64 ↪ Fin nr) : WM ns nr := .seq (massAW (maS.trans K)) (massBW (maS.trans K))

theorem stE_spec (K : Fin 64 ↪ Fin nr) (τ : WState ns nr) (x : SymIn) (c48 : τ.val (K 48) = x.E)
    (c49 : τ.val (K 49) = x.pSq) (c50 : τ.val (K 50) = x.pMod)
    (hz : ∀ i : Fin 64, i ∈ [15, 16, 17, 18, 19, 20, 21, 22, 51] → τ.val (K i) = 0)
    (hn : 2 ≤ x.n) (hcap : 2 * x.Q ≤ cap) :
    ∃ τ', WExec cap (stEW K) τ τ' (30 * UnaryPow.sq cap) ∧ τ'.val (K 51) = x.Iv ∧
      Same K τ τ' [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 15, 16, 17, 18, 19, 20, 21, 22, 52] ∧ Frm K τ τ' := by
  have hQ1 := x.I_small_le_Q hn
  have hEI := x.twoE_le_I
  have hPI := x.Pv_lt_I
  have hSP := x.pS_le_Pv
  have hMm := x.mass_ge
  have hmP := x.Pv_ge_mass
  have hSpos := x.pS_pos
  have hMpos := x.pM_pos
  have hmass : x.mass = 2 * (x.pSq * x.pMod) := by unfold SymIn.mass; ring
  have hPv : x.Pv = x.pSq * (2 * (x.pSq * x.pMod)) * (2 * (x.pSq * x.pMod)) := by
    unfold SymIn.Pv; rw [hmass]; ring
  have hq1 : x.pSq * (2 * (x.pSq * x.pMod)) ≤ x.Pv := by
    rw [hPv]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hE2 : 2 ^ (x.E + 1) ≤ cap := by rw [pow_succ]; omega
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
  have h := massW_spec cap (maS.trans K) τ x.pSq x.pMod x.E (by simp [c49]) (by simp [c50]) (by simp [c48])
    (fun i hi => by fin_cases i <;> simp at hi ⊢ <;> exact hz _ (by decide)) (by omega) (by omega)
    (by rw [← hmass]; omega) (by omega) (by rw [← hPv]; omega) hE2 (by rw [← hPv]; unfold SymIn.Iv at hQ1; omega)
  simp only [Function.Embedding.trans_apply, maS_apply, Matrix.cons_val] at h
  refine ⟨_, h, by simp [SymIn.Iv, hPv], by simp [Same], ?_⟩
  refine ⟨by simp, by simp, by simp, fun r hr => ?_⟩
  have hr' : ∀ i, r ≠ K i := fun i h => hr i h.symm
  simp [Function.update_apply, hr']

/-- Stage F: `Q` (`K 52`). -/
def stFW (K : Fin 64 ↪ Fin nr) : WM ns nr := .seq (qAW (qS.trans K)) (.seq (qB1W (qS.trans K)) (qB2W (qS.trans K)))

theorem stF_spec (K : Fin 64 ↪ Fin nr) (τ : WState ns nr) (x : SymIn) (c1 : τ.val (K 1) = x.n)
    (c4 : τ.val (K 4) = x.kh) (c51 : τ.val (K 51) = x.Iv)
    (hz : ∀ i : Fin 64, i ∈ [15, 16, 17, 18, 19, 20, 21, 22, 52] → τ.val (K i) = 0)
    (hn : 2 ≤ x.n) (hcap : 2 * x.Q ≤ cap) :
    ∃ τ', WExec cap (stFW K) τ τ' (51 * UnaryPow.sq cap) ∧ τ'.val (K 52) = x.Q ∧
      Same K τ τ' [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] ∧ Frm K τ τ' := by
  have hQ1 := x.I_small_le_Q hn
  have hIQ := x.I_le_Q
  have hXQ := x.X_le_Q (by omega)
  have hkQ := x.kh_le_Q (by omega)
  have hX : x.X = (x.kh * 5 + 3) / 2 / 2 := by unfold SymIn.X; omega
  have hQe : x.Q = 2 ^ x.X * (x.Iv * 8192 * x.n * x.n) := by unfold SymIn.Q; ring
  have hT1 : x.Iv * 8192 * x.n ≤ x.Iv * 8192 * x.n * x.n := Nat.le_mul_of_pos_right _ (by omega)
  have hnT : x.n ≤ x.Iv * 8192 * x.n := by
    have h3 : 1 ≤ x.Iv := by unfold SymIn.Iv; omega
    exact Nat.le_mul_of_pos_left _ (by positivity)
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
  have h := qW_spec cap (qS.trans K) τ x.Iv x.kh x.n (by simp [c51]) (by simp [c4]) (by simp [c1])
    (fun i hi => by fin_cases i <;> simp at hi ⊢ <;> exact hz _ (by decide)) (by omega) (by omega)
    (by rw [← hX]; omega) (by omega) (by omega) (by omega) (by rw [← hX, ← hQe]; omega)
  simp only [Function.Embedding.trans_apply, qS_apply, Matrix.cons_val] at h
  refine ⟨_, h, by simp [hQe, hX], by simp [Same], ?_⟩
  refine ⟨by simp, by simp, by simp, fun r hr => ?_⟩
  have hr' : ∀ i, r ≠ K i := fun i h => hr i h.symm
  simp [Function.update_apply, hr']

/-- The inputs of `x` in the block, the rest of the block `0`. -/
structure InBlk (K : Fin 64 ↪ Fin nr) (σ : WState ns nr) (x : SymIn) : Prop where
  c0 : σ.val (K 0) = x.capS
  c1 : σ.val (K 1) = x.n
  c2 : σ.val (K 2) = x.errExp
  c3 : σ.val (K 3) = x.L
  c4 : σ.val (K 4) = x.kh
  c5 : σ.val (K 5) = x.numCar
  c6 : σ.val (K 6) = x.a
  c7 : σ.val (K 7) = x.m 0
  c8 : σ.val (K 8) = x.m 1
  c9 : σ.val (K 9) = x.m 2
  c10 : σ.val (K 10) = x.m 3
  z : ∀ i : Fin 64, 11 ≤ i.val → σ.val (K i) = 0

/-- **The SYM count program.** -/
def symQW (K : Fin 64 ↪ Fin nr) : WM ns nr :=
  .seq (stAW K) (.seq (stBW K) (.seq (stCW K) (.seq (stDW K) (.seq (stEW K) (stFW K)))))

/-! ### The index lists of the stages -/

def LA : List (Fin 64) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 15, 16, 17, 18, 19, 20, 21, 22, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52]
def LB : List (Fin 64) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 15, 16, 17, 18, 19, 20, 21, 22, 40, 46, 47, 48, 49, 50, 51, 52]
def LC : List (Fin 64) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 15, 16, 17, 18, 19, 20, 21, 22, 40, 41, 42, 45, 49, 50, 51, 52]
def LD : List (Fin 64) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 15, 16, 17, 18, 19, 20, 21, 22, 40, 41, 42, 45, 48, 51, 52]
def LE : List (Fin 64) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 15, 16, 17, 18, 19, 20, 21, 22, 52]
def LF : List (Fin 64) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
def zB : List (Fin 64) := [15, 16, 17, 18, 19, 20, 21, 22, 41, 42, 43, 44, 45]
def zC : List (Fin 64) := [15, 16, 17, 18, 19, 20, 21, 22, 46, 47, 48]
def zD : List (Fin 64) := [15, 16, 17, 18, 19, 20, 21, 22, 49, 50]
def zE : List (Fin 64) := [15, 16, 17, 18, 19, 20, 21, 22, 51]
def zF : List (Fin 64) := [15, 16, 17, 18, 19, 20, 21, 22, 52]

theorem zB_LA : zB ⊆ LA := by decide
theorem zC_LB : zC ⊆ LB := by decide
theorem zC_LA : zC ⊆ LA := by decide
theorem zD_LC : zD ⊆ LC := by decide
theorem zD_LB : zD ⊆ LB := by decide
theorem zD_LA : zD ⊆ LA := by decide
theorem zE_LD : zE ⊆ LD := by decide
theorem zE_LC : zE ⊆ LC := by decide
theorem zE_LB : zE ⊆ LB := by decide
theorem zE_LA : zE ⊆ LA := by decide
theorem zF_LE : zF ⊆ LE := by decide
theorem zF_LD : zF ⊆ LD := by decide
theorem zF_LC : zF ⊆ LC := by decide
theorem zF_LB : zF ⊆ LB := by decide
theorem zF_LA : zF ⊆ LA := by decide
theorem LF_LE : LF ⊆ LE := by decide
theorem LF_LD : LF ⊆ LD := by decide
theorem LF_LC : LF ⊆ LC := by decide
theorem LF_LB : LF ⊆ LB := by decide
theorem LF_LA : LF ⊆ LA := by decide
theorem zB_ge : ∀ i ∈ zB, 11 ≤ i.val := by decide
theorem zC_ge : ∀ i ∈ zC, 11 ≤ i.val := by decide
theorem zD_ge : ∀ i ∈ zD, 11 ≤ i.val := by decide
theorem zE_ge : ∀ i ∈ zE, 11 ≤ i.val := by decide
theorem zF_ge : ∀ i ∈ zF, 11 ≤ i.val := by decide

theorem symQ_spec (K : Fin 64 ↪ Fin nr) (σ : WState ns nr) (x : SymIn) (hI : InBlk K σ x) (hcS : 1 ≤ x.capS)
    (hn : 2 ≤ x.n) (hcap : 2 * x.Q ≤ cap) :
    ∃ τ, WExec cap (symQW K) σ τ (600 * UnaryPow.sq cap) ∧ τ.val (K 52) = x.Q ∧ Same K σ τ LF ∧ Frm K σ τ := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, hz⟩ := hI
  have hsq := UnaryPow.sq_ge cap
  obtain ⟨τ1, h1, v40, S1, F1⟩ := stA_spec cap K σ x c0 c1 c2 hz hcS hn hcap
  have e1 : ∀ j ∈ LA, τ1.val (K j) = σ.val (K j) := S1
  have f0 : ∀ j ∈ LF, τ1.val (K j) = σ.val (K j) := fun j hj => e1 j (LF_LA hj)
  obtain ⟨τ2, h2, v41, v42, v45, S2, F2⟩ := stB_spec cap K τ1 x (by rw [f0 0 (by decide), c0])
    (by rw [f0 5 (by decide), c5]) (by rw [f0 7 (by decide), c7]) (by rw [f0 8 (by decide), c8])
    (by rw [f0 9 (by decide), c9]) (by rw [f0 10 (by decide), c10])
    (fun i hi => by rw [e1 i (zB_LA hi)]; exact hz i (zB_ge i hi)) hcS hn hcap
  have e2 : ∀ j ∈ LB, τ2.val (K j) = τ1.val (K j) := S2
  obtain ⟨τ3, h3, v48, S3, F3⟩ := stC_spec cap K τ2 x (by rw [e2 3 (LF_LB (by decide)), f0 3 (by decide), c3])
    (by rw [e2 40 (by decide), v40]) v45
    (fun i hi => by rw [e2 i (zC_LB hi), e1 i (zC_LA hi)]; exact hz i (zC_ge i hi)) hn hcap
  have e3 : ∀ j ∈ LC, τ3.val (K j) = τ2.val (K j) := S3
  have g3 : ∀ j ∈ LF, τ3.val (K j) = σ.val (K j) := fun j hj => by
    rw [e3 j (LF_LC hj), e2 j (LF_LB hj), f0 j hj]
  obtain ⟨τ4, h4, v49, v50, S4, F4⟩ := stD_spec cap K τ3 x (by rw [g3 6 (by decide), c6]) (by rw [g3 7 (by decide), c7])
    (by rw [g3 8 (by decide), c8]) (by rw [g3 9 (by decide), c9]) (by rw [g3 10 (by decide), c10])
    (fun i hi => by rw [e3 i (zD_LC hi), e2 i (zD_LB hi), e1 i (zD_LA hi)]; exact hz i (zD_ge i hi)) hn hcap
  have e4 : ∀ j ∈ LD, τ4.val (K j) = τ3.val (K j) := S4
  obtain ⟨τ5, h5, v51, S5, F5⟩ := stE_spec cap K τ4 x (by rw [e4 48 (by decide), v48]) v49 v50
    (fun i hi => by
      rw [e4 i (zE_LD hi), e3 i (zE_LC hi), e2 i (zE_LB hi), e1 i (zE_LA hi)]; exact hz i (zE_ge i hi)) hn hcap
  have e5 : ∀ j ∈ LE, τ5.val (K j) = τ4.val (K j) := S5
  have g5 : ∀ j ∈ LF, τ5.val (K j) = σ.val (K j) := fun j hj => by
    rw [e5 j (LF_LE hj), e4 j (LF_LD hj), g3 j hj]
  obtain ⟨τ6, h6, v52, S6, F6⟩ := stF_spec cap K τ5 x (by rw [g5 1 (by decide), c1]) (by rw [g5 4 (by decide), c4]) v51
    (fun i hi => by
      rw [e5 i (zF_LE hi), e4 i (zF_LD hi), e3 i (zF_LC hi), e2 i (zF_LB hi), e1 i (zF_LA hi)]
      exact hz i (zF_ge i hi)) hn hcap
  refine ⟨τ6, WExec.mono (WExec.seq h1 (WExec.seq h2 (WExec.seq h3 (WExec.seq h4 (WExec.seq h5 h6))))) (by omega), v52,
    fun j hj => ?_, F1.trans (F2.trans (F3.trans (F4.trans (F5.trans F6))))⟩
  rw [S6 j hj, g5 j hj]

/-- **The register's `Q` is the call's sample count** (`SeedFix.symCount`) at the gate's `D = 1`, `carrierDeg = 26`,
for the call's numbers and its padded bottom counts. -/
theorem Q_call {kclk : ℕ} {E : Cost.Envelope} {B : Cost.TimeBudget kclk E} (I : PrimitiveInputs B) (hD : I.D = 1)
    (hcd : I.carrierDeg = 26) {n : ℕ} (hs : I.StarAt n) {a : ℕ}
    (Cs : Fin a → SupplierPipeline.NormalizedSymmetricThresholdCircuit n) (carriers : List (Stars.Carrier n))
    (x : SymIn) (h1 : x.capS = B.capOf .sym n) (h2 : x.n = n)
    (h3 : x.errExp = I.filterErrDeg * Nat.clog 2 (n + 2)) (h4 : x.L = Nat.clog 2 (n + 2))
    (h5 : x.kh = SeedFix.callKh (I.starParams n hs)) (h6 : x.numCar = carriers.length)
    (hp : x.Padded (List.ofFn fun i => (Cs i).bottomCount)) :
    x.Q = SeedFix.symCount I hs Cs carriers := by
  rw [SymQ.symCount_eq, x.Q_eq _ hp, hD]
  have hFP : x.FP = I.filterParams .sym n := by
    unfold SymIn.FP PrimitiveInputs.filterParams; rw [hcd, h1, h2, h3]
  have hM : x.Mv = ∑ i, (Cs i).bottomCount := by rw [x.Mv_eq _ hp, List.sum_ofFn]
  have hB : x.Bv = carriers.length * (4096 * B.capOf .sym n) := by unfold SymIn.Bv; rw [h6, h1]
  rw [hFP, hM, hB, h4, h5, h2]

end Top

end NearCubicWires.WireExponent3_5.PrimAsm.SymQM
