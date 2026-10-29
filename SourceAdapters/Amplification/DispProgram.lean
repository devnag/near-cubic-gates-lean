import SourceAdapters.Amplification.DispCap
import SourceAdapters.Amplification.CappedDock

/-!
# The dispatcher cell program (A05, `app:sources`, "Full-range amplification interface")

`dispP` runs on `middle2 r = 1^(n+4) ++ false :: amplifierInput r` (`DispUnary.lean`): it reads `n`, computes the cap
`Cs·(2^(n+3) + n^c + D1)` (`capP`), writes the request `(cap, 1^n)` for the capped time constructor (X8's
`cappedWordFunction`, the callee), calls it, reads the doubly framed answer (`parseKP`), and branches as the paper does:

* timeout, or `S(n) = 0`, or `S(n) ≥ U(n) = 2^(n+3)`: the constant output;
* `n < n0`: parity on `S(n)+1` bits;
* `S(n) ≤ n^c`: parity on `n+1` bits;
* otherwise: `k = dyadicExp c S(n)` (`dyadP`) and the X9 encoder body `restP` on the input table.

`dispP_run`: the output is exactly `truthTableWord (ampG …) r` (`DispRef.lean` reads each regime), within an
explicit cost. A timeout at this cap forces `S(n) > 2^(n+3) + n^c + D1 - 1`, hence `n ≥ n0` and the constant regime
(`D1 = Σ_{i<n0} S(i) + 1`).
-/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Adapters.Amplification.Enc

open NearCubicGates.Close.Cells NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.ExecutableInterfaces
open NearCubicWires.LocalBitMultitape NearCubicWires.WireExponent3_5
open NearCubicWires.RepairSource (amplifierInput)
open NearCubicWires.Bindings.CLW20Lemma39 NearCubicGates.Adapters.Joins Finset

/-- The callee: the capped run of the time-constructor program `p` (X8, `Machine/CappedWordProof.lean`). -/
noncomputable def capCallee (p : Program) : Callee :=
  ⟨CappedRequest, cappedRequestWord, fun r => frame (cappedResultWord p r), fun r => 55 * (r.1 + r.2.length + 1),
    Machine.Capped.cappedWordFunction p⟩

/-- The constant `D1 = Σ_{i<n0} S(i) + 1`. -/
def smallSum (S : ℕ → ℕ) (n0 : ℕ) : ℕ := (∑ i ∈ range n0, S i) + 1

theorem lt_smallSum (S : ℕ → ℕ) (n0 i : ℕ) (hi : i < n0) : S i < smallSum S n0 := by
  unfold smallSum
  have := Finset.single_le_sum (f := S) (fun _ _ => Nat.zero_le _) (mem_range.mpr hi)
  omega

/-- The cap. -/
def dispCap (Cs D1 c n : ℕ) : ℕ := Cs * (2 ^ (n + 3) + n ^ c + D1)

/-! ## The branches -/

def parFrom (src : Var) : Sc := .seq (.op (.copy vT src)) (.seq (.op (.inc vT)) parP)

theorem parFrom_spec (C : Ctx) (src : Var) (hsrc : vT ≠ src) (b : Ds) (hc : Consts b) (x : ℕ) (hx : b.env src = x)
    (hW : x + 3 ≤ C.Wd) :
    Runs C (parFrom src) b (parCost (x + 1) + 4) (vT :: parS) (parityWord (x + 1)) (fun _ => True) := by
  have hxW : x + 1 < 2 ^ C.Wd := lt_of_lt_of_le (by omega) (Nat.lt_two_pow_self (n := C.Wd)).le
  refine Runs.op1 (run_copy C (vT :: parS) b vT src (by decide) hsrc) ?_ (by omega)
  refine Runs.op1 (run_inc C (vT :: parS) _ vT (by decide) (by rw [env_set, if_pos rfl, hx]; exact hxW)) ?_
    (by omega)
  have hc2 : Consts ((b.set vT (b.env src)).set vT ((b.set vT (b.env src)).env vT + 1)) :=
    (hc.of_fr (Fr.set [vT] b vT _ (by decide)) (by decide)).of_fr (Fr.set [vT] _ vT _ (by decide)) (by decide)
  refine (parP_spec C _ hc2 (x + 1) (by rw [env_set, if_pos rfl, env_set, if_pos rfl, hx]) (by omega)).mono
    (by omega) (List.subset_cons_self _ _) (fun _ _ h => h)

def midP (R : ℕ) : Sc := .seq dyadP (.seq (.op (.zero vP)) (restP R))

def midS : List Var := dyadS ++ [vP] ++ allS

theorem dyadicExp_le (c S n : ℕ) (hc : 1 ≤ c) (hS : S < 2 ^ (n + 3)) :
    c * dyadicExp c S hc < n + 3 + c ∧ dyadicExp c S hc ≤ n + 3 := by
  rcases Nat.eq_zero_or_pos (dyadicExp c S hc) with h0 | hpos
  · rw [h0]; omega
  · have h1 := two_pow_lt_of_lt_dyadicExp c S hc (dyadicExp c S hc - 1) (by omega)
    have h2 : c * (dyadicExp c S hc - 1) < n + 3 :=
      (Nat.pow_lt_pow_iff_right (by norm_num)).mp (lt_trans h1 hS)
    have : c * dyadicExp c S hc = c * (dyadicExp c S hc - 1) + c := by
      rw [Nat.mul_sub, Nat.mul_one, Nat.sub_add_cancel (Nat.le_mul_of_pos_right c hpos)]
    have h3 : dyadicExp c S hc - 1 ≤ c * (dyadicExp c S hc - 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega

theorem midP_spec (C : Ctx) (R : ℕ) (b : Ds) (hc : Consts b) (c : ℕ) (hc1 : 1 ≤ c) (n S : ℕ) (hS : S < 2 ^ (n + 3))
    (hn : b.env vN = n) (hcc : b.env vCc = c) (hSV : b.env vSV = S) (hW : (44 + R.size) * (2 * n + 5) + 2 * c + n + 10 ≤ C.Wd)
    (T : ℕ → Bool) (base : ℕ) (hT : TableAt C base n T) (hip : b.ip = base) :
    Runs C (midP R) b (c * 5 + dyadicExp c S hc1 * 7 + 20 + restCost R n (dyadicExp c S hc1) + 3) midS
      (frame (arityParam R n (dyadicExp c S hc1)).bits ++
        tableBits ((prm0 R n (dyadicExp c S hc1)).withP (GF.firstPrimitive (tParam R n (dyadicExp c S hc1)))) T)
      (fun _ => True) := by
  obtain ⟨hck, hkn⟩ := dyadicExp_le c S n hc1 hS
  refine Runs.callS (dyadP_spec C b hc c S hc1 hcc hSV (by omega)) (by decide) ?_ (by omega)
  intro b1 hb1 hK
  have hc2 : Consts b1 := hc.of_fr hb1 (by decide)
  have hc3 : Consts (b1.set vP 0) := hc2.of_fr (Fr.set midS b1 vP 0 (by decide)) (by decide)
  have hl := arity_le R n (dyadicExp c S hc1)
  have hmul : (44 + R.size) * (n + dyadicExp c S hc1 + 1) ≤ (44 + R.size) * (2 * n + 5) :=
    Nat.mul_le_mul_left _ (by omega)
  have hR := restP_spec C R (b1.set vP 0) hc3 n (dyadicExp c S hc1)
    (by rw [env_set, if_neg (by decide), hb1.env vN (by decide), hn])
    (by rw [env_set, if_neg (by decide), hK]) (by rw [env_set, if_pos rfl]) (by omega) T base hT
    (by rw [DS.set_ip, hb1.ip, hip])
  have hsub : allS ⊆ midS := by unfold midS; exact List.subset_append_right _ _
  refine Runs.op1 (run_zero C midS b1 vP (by decide))
    ((hR.mono le_rfl hsub (fun _ _ h => h)).costLe (by omega)) (by omega)

def branchP (R : ℕ) : Sc :=
  .ite (.eq vSU vZ) constOutP <| .ite (.eq vSV vZ) constOutP <| .ite (.lt vN vN0) (parFrom vSV) <|
  .ite (.lt vNC vSV) (.ite (.lt vSV vP3) (midP R) constOutP) (parFrom vN)

/-- The cost of the branches (only the branch that can be taken at `n` is counted). -/
noncomputable def branchCost (R n0 c : ℕ) (hc : 1 ≤ c) (S : ℕ → ℕ) (n : ℕ) : ℕ :=
  20 + (if n < n0 then parCost (S n + 1) else 0) + parCost (n + 1) +
    (if S n < 2 ^ (n + 3) then c * 5 + dyadicExp c (S n) hc * 7 + restCost R n (dyadicExp c (S n) hc) + 30 else 0)

theorem ex_of_runs {C : Ctx} {P : Sc} {b : Ds} {m : ℕ} {S : List Var} {w : List Bool} {Q : Ds → Prop}
    (h : Runs C P b m S w Q) (hout : b.out = []) : ∃ b', Ex C P b b' m ∧ b'.out = w := by
  obtain ⟨b', e, hf, -⟩ := h
  exact ⟨b', e, by rw [hf.out, hout, List.nil_append]⟩

theorem branchP_run (C : Ctx) (R A a c : ℕ) (hc : 1 ≤ c) (S : ℕ → ℕ) (Cs : ℕ)
    (n : ℕ) (f : BoolFunction n) (b : Ds) (hcb : Consts b) (hn : b.env vN = n) (hn0 : b.env vN0 = ampOnset A a)
    (hcc : b.env vCc = c) (hP3 : b.env vP3 = 2 ^ (n + 3)) (hNC : b.env vNC = n ^ c) (hout : b.out = [])
    (base : ℕ) (hip : b.ip = base) (hT : TableAt C base n (msgT f))
    (b0 : Bool) (x : ℕ) (hSU : b.env vSU = b0.toNat) (hSV : b.env vSV = x)
    (hcase : (b0 = true ∧ x = S n) ∨
      (b0 = false ∧ x = 0 ∧ dispCap Cs (smallSum S (ampOnset A a)) c n < Cs * (S n + 1)))
    (hW : smallSum S (ampOnset A a) + (44 + R.size) * (2 * n + 5) + 2 * c + n + 10 ≤ C.Wd) :
    ∃ b' m, Ex C (branchP R) b b' m ∧ b'.out = truthTableWord (ampG R A a c hc S) ⟨n, f⟩ ∧
      m ≤ branchCost R (ampOnset A a) c hc S n := by
  have hz : b.env vZ = 0 := hcb.1
  have wfE : ∀ x y : Var, x ≠ y → (Cnd.eq x y).wf := fun x y h => h
  have wfL : ∀ x y : Var, x ≠ y → (Cnd.lt x y).wf := fun x y h => h
  set n0 := ampOnset A a with hn0d
  have hD1 : ∀ i < n0, S i < smallSum S n0 := lt_smallSum S n0
  have hss : 1 ≤ smallSum S n0 := by unfold smallSum; omega
  have hp3 : 1 ≤ 2 ^ (n + 3) := Nat.one_le_two_pow
  rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl, htime⟩
  · have e1 : (Cnd.eq vSU vZ).eval b = false := by simp [Cnd.eval, hSU, hz]
    by_cases h0 : S n = 0
    · obtain ⟨b', e, ho⟩ := ex_of_runs (constOutP_spec C [] b) hout
      refine ⟨b', _, Ex.iteF (wfE _ _ (by decide)) e1 (Ex.iteT (wfE _ _ (by decide))
        (by simp [Cnd.eval, hSV, hz, h0]) e), ?_, ?_⟩
      · rw [ho, amp_zero R A a c hc S n f h0]
      · unfold branchCost; omega
    have e2 : (Cnd.eq vSV vZ).eval b = false := by simp [Cnd.eval, hSV, hz, h0]
    by_cases h1 : n < n0
    · have hsm := hD1 n h1
      obtain ⟨b', e, ho⟩ := ex_of_runs (parFrom_spec C vSV (by decide) b hcb (S n) hSV (by omega)) hout
      refine ⟨b', _, Ex.iteF (wfE _ _ (by decide)) e1 (Ex.iteF (wfE _ _ (by decide)) e2
        (Ex.iteT (wfL _ _ (by decide)) (by simp [Cnd.eval, hn, hn0, h1]) e)), ?_, ?_⟩
      · rw [ho, amp_small R A a c hc S n f h0 h1]
      · unfold branchCost; rw [if_pos h1]; omega
    have e3 : (Cnd.lt vN vN0).eval b = false := by simp [Cnd.eval, hn, hn0, h1]
    by_cases h2 : n ^ c < S n
    · have e4 : (Cnd.lt vNC vSV).eval b = true := by simp [Cnd.eval, hNC, hSV, h2]
      by_cases h3 : S n < 2 ^ (n + 3)
      · obtain ⟨b', e, ho⟩ := ex_of_runs (midP_spec C R b hcb c hc n (S n) h3 hn hcc hSV (by omega) (msgT f) base
          hT hip) hout
        refine ⟨b', _, Ex.iteF (wfE _ _ (by decide)) e1 (Ex.iteF (wfE _ _ (by decide)) e2
          (Ex.iteF (wfL _ _ (by decide)) e3 (Ex.iteT (wfL _ _ (by decide)) e4
          (Ex.iteT (wfL _ _ (by decide)) (by simp [Cnd.eval, hP3, hSV, h3]) e)))), ?_, ?_⟩
        · rw [ho, amp_mid R A a c hc S n f h0 h1 (by omega) (by omega), encoderOutput_eq]
          rfl
        · unfold branchCost; rw [if_pos h3]; omega
      · obtain ⟨b', e, ho⟩ := ex_of_runs (constOutP_spec C [] b) hout
        refine ⟨b', _, Ex.iteF (wfE _ _ (by decide)) e1 (Ex.iteF (wfE _ _ (by decide)) e2
          (Ex.iteF (wfL _ _ (by decide)) e3 (Ex.iteT (wfL _ _ (by decide)) e4
          (Ex.iteF (wfL _ _ (by decide)) (by simp [Cnd.eval, hP3, hSV, h3]) e)))), ?_, ?_⟩
        · rw [ho, amp_big R A a c hc S n f h0 h1 (by omega) (by omega)]
        · unfold branchCost; omega
    · have e4 : (Cnd.lt vNC vSV).eval b = false := by simp [Cnd.eval, hNC, hSV, h2]
      obtain ⟨b', e, ho⟩ := ex_of_runs (parFrom_spec C vN (by decide) b hcb n hn (by omega)) hout
      refine ⟨b', _, Ex.iteF (wfE _ _ (by decide)) e1 (Ex.iteF (wfE _ _ (by decide)) e2
        (Ex.iteF (wfL _ _ (by decide)) e3 (Ex.iteF (wfL _ _ (by decide)) e4 e))), ?_, ?_⟩
      · rw [ho, amp_poly R A a c hc S n f h0 h1 (by omega)]
      · unfold branchCost; omega
  · -- timeout: `S(n) > 2^(n+3) + n^c + D1 - 1`
    have hgt : 2 ^ (n + 3) + n ^ c + smallSum S n0 < S n + 1 := Nat.lt_of_mul_lt_mul_left htime
    have h0 : S n ≠ 0 := by have := Nat.one_le_two_pow (n := n + 3); omega
    have h1 : ¬ n < n0 := fun h => by have := hD1 n h; omega
    obtain ⟨b', e, ho⟩ := ex_of_runs (constOutP_spec C [] b) hout
    refine ⟨b', _, Ex.iteT (wfE _ _ (by decide)) (by simp [Cnd.eval, hSU, hz]) e, ?_, ?_⟩
    · rw [ho, amp_big R A a c hc S n f h0 h1 (by omega) (by omega)]
    · unfold branchCost; omega

/-! ## The whole dispatcher -/

def dispP (R n0 c Cs D1 : ℕ) : Sc :=
  .seq constP <| .seq skipP <| .seq parseP <| .seq (.op (.copy vN vPV)) <| .seq (capP n0 c Cs D1) <|
  .seq reqP <| .seq (.op .kcall) <| .seq parseKP <| .seq (.op (.copy vSV vPV)) (branchP R)

/-- The cost before the branches. -/
def preCost (n0 c Cs D1 Wd Lk Bk n : ℕ) : ℕ :=
  5 + ((n + 4) * 3 + 4) + (n.size * 10 + 10) + 1 + capCost n0 c Cs D1 n + ((dispCap Cs D1 c n + n) * 7 + 20) +
    (1 + Lk + Bk) + (Wd * 14 + 20) + 1 + 9

theorem dispP_run (Wd Lk Bk : ℕ) (inp : List Bool) (p : Program) (R A a c : ℕ) (hc : 1 ≤ c) (S : ℕ → ℕ)
    (Cs : ℕ) (hCs : 0 < Cs)
    (hS : ∀ n, ∃ receipt, run p.machine (Cs * (S n + 1)) (p.inputTapes (List.replicate n true)) = some receipt ∧
      receipt.final.tapes p.outputTape = (S n).bits)
    (r : AmplifierRequest) (hin : inp = middle2 r)
    (hW : 2 * dispCap Cs (smallSum S (ampOnset A a)) c r.inputArity + ampOnset A a + Cs +
      (44 + R.size) * (2 * r.inputArity + 5) + 2 * c + r.inputArity + 10 ≤ Wd)
    (hLk : 2 * dispCap Cs (smallSum S (ampOnset A a)) c r.inputArity + 2 * r.inputArity + 2 ≤ Lk)
    (hBk : 55 * (dispCap Cs (smallSum S (ampOnset A a)) c r.inputArity + r.inputArity + 1) ≤ Bk) (hBW : Bk ≤ Wd) :
    ∃ b m, Ex (⟨Wd, inp, capCallee p, Lk, Bk⟩ : Ctx) (dispP R (ampOnset A a) c Cs (smallSum S (ampOnset A a)))
      (a0 : Ds) b m ∧ b.out = truthTableWord (ampG R A a c hc S) r ∧
      m ≤ preCost (ampOnset A a) c Cs (smallSum S (ampOnset A a)) Wd Lk Bk r.inputArity +
        branchCost R (ampOnset A a) c hc S r.inputArity := by
  obtain ⟨n, f⟩ := r
  simp only at hin hW hLk hBk ⊢
  set C : Ctx := ⟨Wd, inp, capCallee p, Lk, Bk⟩ with hC
  set n0 := ampOnset A a with hn0d
  set D1 := smallSum S n0 with hD1d
  set cap := dispCap Cs D1 c n with hcapd
  have hcapge : 2 ^ (n + 3) + n ^ c + D1 ≤ cap := by
    rw [hcapd, dispCap]; exact Nat.le_mul_of_pos_left _ hCs
  have hWlt : Wd < 2 ^ Wd := Nat.lt_two_pow_self
  have hcapEq : dispCap Cs D1 c n = Cs * (2 ^ (n + 3) + n ^ c + D1) := rfl
  have hzD : smallSum S (ampOnset A a) = D1 := rfl
  have hCW : C.Wd = Wd := rfl
  have h2CW : 2 ^ C.Wd = 2 ^ Wd := rfl
  have hCL : C.Lk = Lk := rfl
  have hCB : C.Bk = Bk := rfl
  have hsz := size_le_self n
  have hinC : C.inp = middle2 ⟨n, f⟩ := hin
  -- constants
  set a1 : Ds := ((((a0 : Ds).set vONE ((a0 : Ds).env vONE + 1)).set vTWO
    (((a0 : Ds).set vONE ((a0 : Ds).env vONE + 1)).env vTWO + 1))).set vTWO
    ((((a0 : Ds).set vONE ((a0 : Ds).env vONE + 1)).set vTWO
    (((a0 : Ds).set vONE ((a0 : Ds).env vONE + 1)).env vTWO + 1)).env vTWO + 1)
  have h2W : 2 < 2 ^ C.Wd := by
    have : 2 ^ 2 ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) (show 2 ≤ Wd by omega)
    simp at this; omega
  have e0 : Ex C constP (a0 : Ds) a1 5 :=
    Ex.seq (Ex.op (OpEx.inc vONE _ (by simp [a0]; omega))) (Ex.seq (Ex.op (OpEx.inc vTWO _
      (by simp (config := { decide := true }) [a0, env_set]; omega)))
      (Ex.op (OpEx.inc vTWO _ (by simp (config := { decide := true }) [a0, env_set]; omega))))
  have hc1 : Consts a1 := ⟨by simp (config := { decide := true }) [a1, a0, env_set],
    by simp (config := { decide := true }) [a1, a0, env_set], by simp (config := { decide := true }) [a1, a0, env_set]⟩
  -- skip the prefix, read `n`
  obtain ⟨b1, e1, hf1, hip1⟩ := skipP_spec C (n + 4) (amplifierInput ⟨n, f⟩) hinC a1 hc1 (by simp [a1, a0, DS.set])
  have hc_b1 : Consts b1 := ⟨(hf1.env _ (by decide)).trans hc1.1, (hf1.env _ (by decide)).trans hc1.2.1,
    (hf1.env _ (by decide)).trans hc1.2.2⟩
  have hin2 : C.inp = (List.replicate (n + 4) true ++ [false]) ++ frame n.bits ++ boolFunctionTable f := by
    rw [hinC]; simp [middle2, amplifierInput, List.append_assoc]
  obtain ⟨b2, e2, hf2, hip2, hn2⟩ := parseP_spec C n (n + 4 + 1) _ _ hin2 (by simp) (by omega) b1 hc_b1 hip1
  have hc_b2 : Consts b2 := ⟨(hf2.env _ (by decide)).trans hc_b1.1, (hf2.env _ (by decide)).trans hc_b1.2.1,
    (hf2.env _ (by decide)).trans hc_b1.2.2⟩
  set b3 := b2.set vN (b2.env vPV) with hb3
  have e3 : Ex C (.op (.copy vN vPV)) b2 b3 1 := Ex.op (OpEx.copy vN vPV b2 (by decide))
  have hc_b3 : Consts b3 := hc_b2.of_fr (Fr.set [vN] b2 vN _ (by decide)) (by decide)
  have hn3 : b3.env vN = n := by rw [hb3, DS.set_env_self, hn2]
  set base := n + 4 + 1 + 2 * n.size + 1 with hbase
  have hT : TableAt C base n (msgT f) := by
    have hlen : (List.replicate (n + 4) true ++ [false] ++ frame n.bits).length = base := by
      simp [frame_length, Nat.size_eq_bits_len]; omega
    constructor
    · rw [hin2, List.length_append, hlen]; simp [boolFunctionTable]
    · intro i hi
      rw [hin2, ← hlen, List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]
      exact table_getD f i hi
  have hip3 : b3.ip = base := by rw [hb3, DS.set_ip, hip2]
  have hkin3 : b3.kin = [] := by
    rw [hb3, DS.set_kin, hf2.kin, hf1.kin]; simp [a1, a0, DS.set]
  have hout3 : b3.out = [] := by
    rw [hb3, DS.set_out, hf2.out, hf1.out]; simp [a1, a0, DS.set]
  -- the cap
  obtain ⟨b4, e4, hf4, hN04, hCc4, hP34, hNC4, hCap4⟩ := capP_spec C b3 hc_b3 n0 c Cs D1 n hn3 hc (by omega)
    (by omega)
  have hc_b4 : Consts b4 := hc_b3.of_fr hf4 (by decide)
  have hn4 : b4.env vN = n := (hf4.env vN (by decide)).trans hn3
  -- the request
  obtain ⟨b5, e5, hf5, hk5⟩ := reqP_spec C b4 hc_b4 cap n hCap4 hn4 (by rw [hf4.kin, hkin3]) hLk
  -- the call
  have hbud : C.K.bud ((cap, List.replicate n true) : CappedRequest) ≤ C.Bk := by
    show 55 * (cap + (List.replicate n true).length + 1) ≤ Bk
    simp only [List.length_replicate]; exact hBk
  have e6 : Ex C (.op .kcall) b5 (b5.called (frame (cappedResultWord p (cap, List.replicate n true))))
      (1 + Lk + Bk) := Ex.op (OpEx.kcall (C := C) ((cap, List.replicate n true) : CappedRequest) b5 hk5 hbud)
  set b6 := b5.called (frame (cappedResultWord p (cap, List.replicate n true))) with hb6
  have hlen6 : (frame (cappedResultWord p (cap, List.replicate n true))).length ≤ Bk + 3 :=
    callee_hB C _ hbud
  have hf6 : FrQ ([vU] ++ capS) [] b3 b6 := ((hf4.toQ.mono (by decide)).trans0 (hf5.mono (by decide))).called_right _
  have hc_b6 : Consts b6 := hc_b3.of_frq hf6 (by decide)
  -- the answer
  obtain ⟨b0, x, hres, hcase⟩ : ∃ (b0 : Bool) (x : ℕ),
      cappedResultWord p (cap, List.replicate n true) = b0 :: frame x.bits ∧
      ((b0 = true ∧ x = S n) ∨ (b0 = false ∧ x = 0 ∧ cap < Cs * (S n + 1))) := by
    rcases cappedResult_cases p (List.replicate n true) (S n).bits (Cs * (S n + 1)) (hS n) cap with h | ⟨h, hlt⟩
    · exact ⟨true, S n, h, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨false, 0, by rw [h, Nat.zero_bits], Or.inr ⟨rfl, rfl, hlt⟩⟩
  have hxW : x.size + 2 ≤ C.Wd := by
    rw [hres] at hlen6
    have h1 := (kout_get b0 x.bits).1
    rw [Nat.size_eq_bits_len] at h1
    omega
  obtain ⟨b7, e7, hf7, hSU7, hPV7⟩ := parseKP_spec C b6 hc_b6 b0 x (by rw [hb6]; simp [DS.called, hres])
    (by rw [hb6]; simp [DS.called]) hxW
  set b8 := b7.set vSV (b7.env vPV) with hb8
  have e8 : Ex C (.op (.copy vSV vPV)) b7 b8 1 := Ex.op (OpEx.copy vSV vPV b7 (by decide))
  have hf8 : FrQ ([vU] ++ capS ++ parseKS ++ [vSV]) [] b3 b8 :=
    (((hf6.mono (by decide)).trans0 (hf7.mono (by decide))).set_right vSV _ (by decide))
  have hc_b8 : Consts b8 := hc_b3.of_frq hf8 (by decide)
  have hf48 : FrQ ([vU] ++ parseKS ++ [vSV]) [] b4 b8 :=
    ((((hf5.called_right _).mono (by decide)).trans0 (hf7.mono (by decide))).set_right vSV _ (by decide))
  obtain ⟨b9, m9, e9, ho9, hm9⟩ := branchP_run C R A a c hc S Cs n f b8 hc_b8
    (by rw [hf8.env vN (by decide), hn3]) (by rw [hf48.env vN0 (by decide), hN04])
    (by rw [hf48.env vCc (by decide), hCc4]) (by rw [hf48.env vP3 (by decide), hP34])
    (by rw [hf48.env vNC (by decide), hNC4]) (by rw [hf8.out, hout3, List.nil_append]) base
    (by rw [hf8.ip, hip3]) hT b0 x
    (by rw [hb8, env_set, if_neg (by decide), hSU7]) (by rw [hb8, env_set, if_pos rfl, hPV7]) hcase (by omega)
  refine ⟨b9, _, Ex.seq e0 (Ex.seq e1 (Ex.seq e2 (Ex.seq e3 (Ex.seq e4 (Ex.seq e5 (Ex.seq e6 (Ex.seq e7
    (Ex.seq e8 e9)))))))), ho9, ?_⟩
  have hxs : x.size ≤ Wd := by omega
  have hbc : branchCost R (ampOnset A a) c hc S n = branchCost R n0 c hc S n := rfl
  unfold preCost
  omega

end NearCubicGates.Adapters.Amplification.Enc
