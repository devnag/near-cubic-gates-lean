import SourceAdapters.Amplification.DispKit

/-!
# The cap and the dyadic exponent in the dispatcher (A05, `app:sources`, "Full-range amplification interface")

* `capP`: `vCap := Cs·(2^(n+3) + n^c + D1)`, with `vP3 = 2^(n+3) = U(n)`, `vNC = n^c`, `vN0 = n0`, `vCc = c`. The cap
  of `app:sources`, "Full-range amplification interface" is `C(U(n)+1)`; the dispatcher adds `n^c` (so that a timeout also excludes `S(n) ≤ n^c`, which leaves implicit) and the constant `D1 = Σ_{i<n0} S(i) + 1` (so that no length below the onset times out:
   hardcodes those finitely many values; the cap realizes the hardcoding).
* `dyadP`: `vK := dyadicExp c S`, the least `k` with `S ≤ 2^(ck)` ("Compute the least integer `k`
  such that `2^{ck} ≥ S`"), by multiplying by `2^c` while the power is below `S`.
-/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Adapters.Amplification.Enc

open NearCubicGates.Close.Cells NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.ExecutableInterfaces

abbrev vCs : Var := 16
abbrev vNC : Var := 18
abbrev vP3 : Var := 19
abbrev vSV : Var := 32
abbrev vCc : Var := 41
abbrev vN0 : Var := 45
abbrev vTm : Var := 77
abbrev vJ : Var := 79

/-! ## Two constants -/

def constsP (n0 c : ℕ) : Sc := .seq (.op (.zero vN0)) <| .seq (incN vN0 n0) <| .seq (.op (.zero vCc)) (incN vCc c)

def constsS : List Var := [vN0, vCc, vT2]

theorem constsP_spec (C : Ctx) (a : Ds) (n0 c : ℕ) (hW : n0 + c < 2 ^ C.Wd) :
    Runs C (constsP n0 c) a (2 * (n0 + c) + 8) constsS [] (fun b => b.env vN0 = n0 ∧ b.env vCc = c) := by
  refine Runs.op1 (run_zero C constsS a vN0 (by decide)) ?_ (by omega)
  refine Runs.callS (incN_spec C vN0 (by decide) [vN0, vT2] (by decide) (by decide) n0 _ (by norm_env; omega))
    (by decide) ?_ (by omega)
  intro b1 hb1 hN0
  refine Runs.op1 (run_zero C constsS b1 vCc (by decide)) ?_ (by omega)
  refine (incN_spec C vCc (by decide) [vCc, vT2] (by decide) (by decide) c _ (by norm_env; omega)).mono
    (by omega) (by decide) ?_
  intro b2 hb2 hCc
  refine ⟨?_, ?_⟩
  · rw [hb2.env vN0 (by decide)]; norm_env; rw [hN0]; norm_env; omega
  · rw [hCc]; norm_env; omega

/-! ## `2^(n+3)` -/

def pow3P : Sc := .seq (.op (.copy vEE vN)) <| .seq (incN vEE 3) <| .seq pow2P (.op (.copy vP3 vPD))

def pow3S : List Var := [vEE, vT2, vPD, vEJ, vP3]

theorem pow3P_spec (C : Ctx) (a : Ds) (hc : Consts a) (n : ℕ) (hn : a.env vN = n) (hW : n + 5 ≤ C.Wd) :
    Runs C pow3P a (n * 5 + 40) pow3S [] (fun b => b.env vP3 = 2 ^ (n + 3)) := by
  have hlt : n + 3 < 2 ^ C.Wd := lt_of_lt_of_le (by omega) (Nat.lt_two_pow_self (n := C.Wd)).le
  refine Runs.op1 (run_copy C pow3S a vEE vN (by decide) (by decide)) ?_ (by omega)
  refine Runs.callS (incN_spec C vEE (by decide) [vEE, vT2] (by decide) (by decide) 3 _ (by rw [env_set, if_pos rfl, hn]; omega))
    (by decide) ?_ (by omega)
  intro b1 hb1 hE
  have hc1 : Consts b1 := (hc.of_fr (Fr.set pow3S a vEE _ (by decide)) (by decide)).of_fr hb1 (by decide)
  refine Runs.callS (pow2P_spec C b1 hc1 (n + 3) (by rw [hE]; norm_env; rw [hn]) (by omega)) (by decide) ?_
    (by omega)
  intro b2 _ hD
  refine Runs.last (run_copy C pow3S b2 vP3 vPD (by decide) (by decide)) ?_ (by omega)
  intro _
  norm_env
  exact hD

/-! ## `n^c` -/

def powCBody : Sc := .seq (.op (.mul vNC vN vTm)) (.seq (.op (.copy vNC vTm)) (.op (.inc vJ)))

def powCP : Sc := .seq (.op (.copy vNC vONE)) <| .seq (.op (.zero vJ)) <| .loop (.lt vJ vCc) powCBody

def powCS : List Var := [vNC, vJ, vTm]

theorem pow_le_pow_c (n j c : ℕ) (hj : j ≤ c) (hj1 : 1 ≤ j) : n ^ j ≤ n ^ c := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [zero_pow (by omega)]; exact Nat.zero_le _
  · exact Nat.pow_le_pow_right hn hj

theorem powCP_spec (C : Ctx) (a : Ds) (hc : Consts a) (n c : ℕ) (hn : a.env vN = n) (hcc : a.env vCc = c)
    (hc1 : 1 ≤ c) (hW : n ^ c + c < 2 ^ C.Wd) :
    Runs C powCP a (c * 7 + 6) powCS [] (fun b => b.env vNC = n ^ c) := by
  refine Runs.op1 (run_copy C powCS a vNC vONE (by decide) (by decide)) ?_ (by omega)
  refine Runs.op1 (run_zero C powCS _ vJ (by decide)) ?_ (by omega)
  refine (Runs.loopN0 (C := C) (c := .lt vJ vCc) (body := powCBody) (S := powCS) (by unfold Cnd.wf; decide) c 5
    (fun j b => Fr powCS [] a b ∧ b.env vNC = n ^ j ∧ b.env vJ = j) ?step ?stop _ ?init).mono (by omega)
    (List.Subset.refl _) (fun _ _ h => h.2.1)
  case init =>
    refine ⟨((Fr.refl _ _).set_right _ _ (by decide)).set_right _ _ (by decide), ?_, ?_⟩ <;> norm_env
    · simp [hc.2.1]
  case stop =>
    rintro b ⟨hf, -, hJ⟩
    simp [Cnd.eval, hJ, (hf.env vCc (by decide)).trans hcc]
  case step =>
    rintro j hj b ⟨hf, hP, hJ⟩
    have hnb : b.env vN = n := (hf.env vN (by decide)).trans hn
    refine ⟨by simp [Cnd.eval, hJ, (hf.env vCc (by decide)).trans hcc, hj], ?_⟩
    have hle : n ^ (j + 1) ≤ n ^ c := pow_le_pow_c n (j + 1) c (by omega) (by omega)
    refine Runs.op1 (run_mul C powCS b vNC vN vTm (by decide) (by decide) (by decide) (by decide)
      (by rw [hP, hnb, ← pow_succ]; omega)) ?_ (by omega)
    refine Runs.op1 (run_copy C powCS _ vNC vTm (by decide) (by decide)) ?_ (by omega)
    refine Runs.last (run_inc C powCS _ vJ (by decide) (by norm_env; rw [hJ]; omega)) ?_ (by omega)
    intro _
    refine ⟨((hf.set_right _ _ (by decide)).set_right _ _ (by decide)).set_right _ _ (by decide), ?_, ?_⟩ <;> norm_env
    · rw [hP, hnb, pow_succ]
    · rw [hJ]

/-! ## The cap -/

def capMulP (D1 Cs : ℕ) : Sc :=
  .seq (.op (.copy vTm vP3)) <| .seq (.op (.add vTm vNC)) <| .seq (incN vTm D1) <| .seq (.op (.zero vCs)) <|
  .seq (incN vCs Cs) (.op (.mul vCs vTm vCap))

def capMulS : List Var := [vTm, vT2, vCs, vCap]

theorem capMulP_spec (C : Ctx) (a : Ds) (D1 Cs P N : ℕ) (hP : a.env vP3 = P) (hN : a.env vNC = N)
    (hW : Cs * (P + N + D1) + P + N + D1 + Cs < 2 ^ C.Wd) :
    Runs C (capMulP D1 Cs) a (2 * (D1 + Cs) + 15) capMulS [] (fun b => b.env vCap = Cs * (P + N + D1)) := by
  refine Runs.op1 (run_copy C capMulS a vTm vP3 (by decide) (by decide)) ?_ (by omega)
  refine Runs.op1 (run_add C capMulS _ vTm vNC (by decide) (by decide) (by norm_env; rw [hP, hN]; omega)) ?_
    (by omega)
  refine Runs.callS (incN_spec C vTm (by decide) [vTm, vT2] (by decide) (by decide) D1 _
    (by norm_env; rw [hP, hN]; omega)) (by decide) ?_ (by omega)
  intro b1 hb1 hT
  have hT' : b1.env vTm = P + N + D1 := by rw [hT]; norm_env; rw [hP, hN]
  refine Runs.op1 (run_zero C capMulS b1 vCs (by decide)) ?_ (by omega)
  refine Runs.callS (incN_spec C vCs (by decide) [vCs, vT2] (by decide) (by decide) Cs _ (by norm_env; omega))
    (by decide) ?_ (by omega)
  intro b2 hb2 hC
  have hC' : b2.env vCs = Cs := by rw [hC]; norm_env; omega
  have hT2 : b2.env vTm = P + N + D1 := by rw [hb2.env vTm (by decide)]; norm_env; exact hT'
  refine Runs.last (run_mul C capMulS b2 vCs vTm vCap (by decide) (by decide) (by decide) (by decide)
    (by rw [hC', hT2]; omega)) ?_ (by omega)
  intro _
  norm_env
  rw [hC', hT2]

def capP (n0 c Cs D1 : ℕ) : Sc := .seq (constsP n0 c) <| .seq pow3P <| .seq powCP (capMulP D1 Cs)

def capS : List Var := constsS ++ pow3S ++ powCS ++ capMulS

def capCost (n0 c Cs D1 n : ℕ) : ℕ := 2 * (n0 + c + D1 + Cs) + n * 5 + c * 7 + 90

theorem capP_spec (C : Ctx) (a : Ds) (hc : Consts a) (n0 c Cs D1 n : ℕ) (hn : a.env vN = n) (hc1 : 1 ≤ c)
    (hW1 : n + 5 ≤ C.Wd)
    (hW2 : Cs * (2 ^ (n + 3) + n ^ c + D1) + n0 + c + Cs + 2 ^ (n + 3) + n ^ c + D1 < 2 ^ C.Wd) :
    Runs C (capP n0 c Cs D1) a (capCost n0 c Cs D1 n) capS []
      (fun b => b.env vN0 = n0 ∧ b.env vCc = c ∧ b.env vP3 = 2 ^ (n + 3) ∧ b.env vNC = n ^ c ∧
        b.env vCap = Cs * (2 ^ (n + 3) + n ^ c + D1)) := by
  have hP0 := Nat.zero_le (2 ^ (n + 3))
  have hQ0 := Nat.zero_le (Cs * (2 ^ (n + 3) + n ^ c + D1))
  refine Runs.callS (constsP_spec C a n0 c (by omega)) (by decide) ?_ (by unfold capCost; omega)
  intro b1 hb1 ⟨hN0, hCc⟩
  have hc1' : Consts b1 := hc.of_fr hb1 (by decide)
  have hn1 : b1.env vN = n := (hb1.env vN (by decide)).trans hn
  refine Runs.callS (pow3P_spec C b1 hc1' n hn1 hW1) (by decide) ?_ (by unfold capCost; omega)
  intro b2 hb2 hP3
  have hc2 : Consts b2 := hc1'.of_fr hb2 (by decide)
  have hn2 : b2.env vN = n := (hb2.env vN (by decide)).trans hn1
  have hCc2 : b2.env vCc = c := (hb2.env vCc (by decide)).trans hCc
  refine Runs.callS (powCP_spec C b2 hc2 n c hn2 hCc2 hc1 (by omega)) (by decide) ?_ (by unfold capCost; omega)
  intro b3 hb3 hNC
  have hP33 : b3.env vP3 = 2 ^ (n + 3) := (hb3.env vP3 (by decide)).trans hP3
  refine (capMulP_spec C b3 D1 Cs _ _ hP33 hNC (by omega)).mono (by unfold capCost; omega) (by decide) ?_
  intro b4 hb4 hCap
  refine ⟨?_, ?_, ?_, ?_, hCap⟩
  · rw [hb4.env vN0 (by decide), hb3.env vN0 (by decide), hb2.env vN0 (by decide), hN0]
  · rw [hb4.env vCc (by decide), hb3.env vCc (by decide), hCc2]
  · rw [hb4.env vP3 (by decide), hP33]
  · rw [hb4.env vNC (by decide), hNC]

/-! ## The dyadic exponent -/

def dyadBody : Sc := .seq (.op (.mul vT1 vPD vTm)) (.seq (.op (.copy vT1 vTm)) (.op (.inc vK)))

def dyadP : Sc :=
  .seq (.op (.copy vEE vCc)) <| .seq pow2P <| .seq (.op (.zero vK)) <| .seq (.op (.copy vT1 vONE)) <|
  .loop (.lt vT1 vSV) dyadBody

def dyadS : List Var := [vEE, vPD, vEJ, vK, vT1, vTm]

theorem dyadP_spec (C : Ctx) (a : Ds) (hc : Consts a) (c S : ℕ) (hc1 : 1 ≤ c) (hcc : a.env vCc = c)
    (hS : a.env vSV = S) (hW : c * dyadicExp c S hc1 + c + 2 ≤ C.Wd) :
    Runs C dyadP a (c * 5 + dyadicExp c S hc1 * 7 + 20) dyadS [] (fun b => b.env vK = dyadicExp c S hc1) := by
  set k := dyadicExp c S hc1 with hk
  have hpw : ∀ i, i ≤ c * k → 2 ^ i < 2 ^ C.Wd := fun i hi => Nat.pow_lt_pow_right (by norm_num) (by omega)
  refine Runs.op1 (run_copy C dyadS a vEE vCc (by decide) (by decide)) ?_ (by omega)
  have hc1' : Consts (a.set vEE (a.env vCc)) := hc.of_fr (Fr.set dyadS a vEE _ (by decide)) (by decide)
  refine Runs.callS (pow2P_spec C _ hc1' c (by norm_env; exact hcc) (by omega)) (by decide) ?_ (by omega)
  intro b1 hb1 hD
  have hc2 : Consts b1 := hc1'.of_fr hb1 (by decide)
  refine Runs.op1 (run_zero C dyadS b1 vK (by decide)) ?_ (by omega)
  refine Runs.op1 (run_copy C dyadS _ vT1 vONE (by decide) (by decide)) ?_ (by omega)
  have hSb : ∀ b : Ds, Fr dyadS [] a b → b.env vSV = S := fun b hb => (hb.env vSV (by decide)).trans hS
  refine (Runs.loopN0 (C := C) (c := .lt vT1 vSV) (body := dyadBody) (S := dyadS) (by unfold Cnd.wf; decide) k 5
    (fun j b => Fr dyadS [] a b ∧ b.env vT1 = 2 ^ (c * j) ∧ b.env vK = j ∧ b.env vPD = 2 ^ c) ?step ?stop _
    ?init).mono (by omega) (List.Subset.refl _) (fun _ _ h => h.2.2.1)
  case init =>
    refine ⟨(((Fr.set dyadS a vEE _ (by decide)).trans0 (hb1.mono (by decide))).set_right _ _ (by decide)).set_right _ _ (by decide),
      ?_, ?_, ?_⟩ <;> norm_env
    · simp [hc2.2.1]
    · exact hD
  case stop =>
    rintro b ⟨hf, hT, -, -⟩
    have := le_two_pow_dyadicExp c S hc1
    simp [Cnd.eval, hT, hSb b hf]
    rw [← hk] at this; omega
  case step =>
    rintro j hj b ⟨hf, hT, hK, hD'⟩
    have hlt := two_pow_lt_of_lt_dyadicExp c S hc1 j hj
    refine ⟨by simp [Cnd.eval, hT, hSb b hf, hlt], ?_⟩
    have hmul : 2 ^ (c * j) * 2 ^ c = 2 ^ (c * (j + 1)) := by rw [← pow_add]; ring_nf
    have hjk : c * (j + 1) ≤ c * k := Nat.mul_le_mul_left c hj
    refine Runs.op1 (run_mul C dyadS b vT1 vPD vTm (by decide) (by decide) (by decide) (by decide)
      (by rw [hT, hD', hmul]; exact hpw _ hjk)) ?_ (by omega)
    refine Runs.op1 (run_copy C dyadS _ vT1 vTm (by decide) (by decide)) ?_ (by omega)
    have hkW : j + 1 < 2 ^ C.Wd := by
      have := hpw (c * k) le_rfl
      have := Nat.lt_two_pow_self (n := c * k)
      have : j + 1 ≤ c * k := le_trans (Nat.le_mul_of_pos_left (j + 1) (by omega)) hjk
      omega
    refine Runs.last (run_inc C dyadS _ vK (by decide) (by norm_env; rw [hK]; exact hkW)) ?_ (by omega)
    intro _
    refine ⟨((hf.set_right _ _ (by decide)).set_right _ _ (by decide)).set_right _ _ (by decide), ?_, ?_, ?_⟩ <;>
      norm_env
    · rw [hT, hD', hmul]
    · rw [hK]
    · exact hD'

end NearCubicGates.Adapters.Amplification.Enc
