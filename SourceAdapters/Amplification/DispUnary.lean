import SourceAdapters.Amplification.DispPrep

/-!
# Widening the prefix to `n + 4` ones (A05, `app:sources`, "Full-range amplification interface")

The dispatcher calls the capped time constructor with a cap of order `2^(n+3)`, so its cell program needs call
bounds `2^Ω(n)`, i.e. `Ω(n)` leading ones. `unaryP` (cell language, width from `size n` leading ones) reads `n`
and writes `frame (1^(n+4) ++ false :: amplifierInput r)`.
-/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Adapters.Amplification.Enc

open NearCubicGates.Close.Cells NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.ExecutableInterfaces
open NearCubicWires.RepairSource (amplifierInput)

abbrev vU : Var := 17
abbrev vRB : Var := 18
abbrev vCN : Var := 19

theorem flatMap_range_const (l : List Bool) : ∀ m, (List.range m).flatMap (fun _ => l) = (List.replicate m l).flatten
  | 0 => rfl
  | m + 1 => by
    rw [List.range_succ, List.flatMap_append, flatMap_range_const l m, List.replicate_succ', List.flatten_append]
    simp

/-- `n + 4` framed ones. -/
def onesP : Sc := .seq (.op (.copy vU vPV)) <| .seq (incN vU 4) <|
  .loop (.lt vZ vU) (.seq (.op (.emit true)) (.seq (.op (.emit true)) (.op (.sub vU vONE))))

theorem onesP_spec (C : Ctx) (a : Ds) (hc : Consts a) (n : ℕ) (hn : a.env vPV = n) (hW : n + 4 < 2 ^ C.Wd) :
    Runs C onesP a (n * 8 + 60) [vU, vT2] (List.replicate (n + 4) [true, true]).flatten (fun _ => True) := by
  refine Runs.op1 (run_copy C [vU, vT2] a vU vPV (by decide) (by decide)) ?_ (by omega)
  refine Runs.call (incN_spec C vU (by decide) [vU, vT2] (by decide) (by decide) 4 _ (by norm_env; omega)) ?_
    (by omega)
  intro b hb hbU
  simp (config := { decide := true }) only [env_set, ite_true] at hbU
  have hcb : Consts b := hc.of_fr (((Fr.refl _ a).set_right vU _ (by decide)).trans0 hb) (by decide)
  have e := Runs.loopN (C := C) (c := .lt vZ vU) (body := .seq (.op (.emit true)) (.seq (.op (.emit true))
    (.op (.sub vU vONE)))) (S := [vU, vT2]) (by unfold Cnd.wf; decide) (n + 4) 6 (fun _ => [true, true])
    (fun j d => Consts d ∧ d.env vU = n + 4 - j) ?step ?stop b ⟨hcb, by rw [hbU, hn]; simp⟩
  case stop => rintro d ⟨hcd, hU⟩; simp [Cnd.eval, hU, hcd.1]
  case step =>
    rintro j hj d ⟨hcd, hU⟩
    refine ⟨by simp [Cnd.eval, hU, hcd.1]; omega, ?_⟩
    refine Runs.emit1 (run_emit C _ d true) ?_ (by omega)
    refine Runs.emit1 (run_emit C _ _ true) ?_ (by omega)
    refine Runs.last (run_sub C _ _ vU vONE (by decide) (by decide) (by simp [hU, hcd.2.1]; omega)) ?_ (by omega)
    intro _
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩ <;> simp (config := { decide := true }) [env_set, hcd.1, hcd.2.1, hcd.2.2, hU]
    omega
  have e2 := e.mono (n' := n * 8 + 60 - 2 - (2 * 4 + 1) - 1) (by omega) (List.Subset.refl _) (fun _ _ _ => trivial)
  rw [← flatMap_range_const]; exact e2

/-! ## Moving back and copying the input -/

def backBody : Sc := .seq (.op .bkI) (.op (.sub vRB vONE))

theorem backLoop_spec (C : Ctx) (a : Ds) (hc : Consts a) (d : ℕ) (hd : a.env vRB = d) (hip : d ≤ a.ip) :
    ∃ b, Ex C (.loop (.lt vZ vRB) backBody) a b (d * (3 + 2) + 2) ∧ FrI [vRB] [] a b ∧ b.ip = a.ip - d := by
  have hstep : ∀ j < d, ∀ b : Ds, (FrI [vRB] [] a b ∧ b.ip = a.ip - j ∧ b.env vRB = d - j) →
      (Cnd.lt vZ vRB).eval b = true ∧ ∃ b', Ex C backBody b b' 3 ∧
        (FrI [vRB] [] a b' ∧ b'.ip = a.ip - (j + 1) ∧ b'.env vRB = d - (j + 1)) := by
    rintro j hj b ⟨hf, hbip, hR⟩
    have hz : b.env vZ = 0 := (hf.env vZ (by decide)).trans hc.1
    have h1 : b.env vONE = 1 := (hf.env vONE (by decide)).trans hc.2.1
    refine ⟨by simp [Cnd.eval, hz, hR]; omega, _, Ex.seq (Ex.op (OpEx.bkI b (by omega)))
      (Ex.op (OpEx.sub vRB vONE _ (by decide) (by simp [h1, hR]; omega))), ?_, ?_, ?_⟩
    · exact (hf.ip_right _).set_right _ _ (by decide)
    · simp [DS.set, hbip]; omega
    · simp [env_set, hR, h1]; omega
  obtain ⟨b, e, hb⟩ := ex_loopN (C := C) (c := .lt vZ vRB) (body := backBody) (by unfold Cnd.wf; decide) d 3
    (fun j b => FrI [vRB] [] a b ∧ b.ip = a.ip - j ∧ b.env vRB = d - j) hstep
    (by rintro b ⟨hf, -, hR⟩; have hz : b.env vZ = 0 := (hf.env vZ (by decide)).trans hc.1; simp [Cnd.eval, hz, hR])
    a ⟨⟨fun _ _ => rfl, by simp, rfl, rfl, rfl, rfl, rfl⟩, by simp, by simp [hd]⟩
  exact ⟨b, e, hb.1, hb.2.1⟩

def copyInBody : Sc :=
  .seq (.op (.rdI vR0)) <| .seq (.op (.emit true)) <|
  .seq (.ite (.eq vR0 vONE) (.op (.emit true)) (.op (.emit false))) (.op (.sub vCN vONE))

theorem copyInLoop_spec (C : Ctx) (a : Ds) (hc : Consts a) (u : List Bool) (hCN : a.env vCN = u.length)
    (hlen : a.ip + u.length ≤ C.inp.length) (hu : ∀ i < u.length, C.inp.getD (a.ip + i) false = u.getD i false) :
    ∃ b, Ex C (.loop (.lt vZ vCN) copyInBody) a b (u.length * (8 + 2) + 2) ∧
      FrI [vR0, vCN] (u.flatMap fun x => [true, x]) a b := by
  have hstep : ∀ j < u.length, ∀ b : Ds, (FrI [vR0, vCN] ((u.take j).flatMap fun x => [true, x]) a b ∧
      b.ip = a.ip + j ∧ b.env vCN = u.length - j) → (Cnd.lt vZ vCN).eval b = true ∧ ∃ b', Ex C copyInBody b b' 8 ∧
        (FrI [vR0, vCN] ((u.take (j + 1)).flatMap fun x => [true, x]) a b' ∧ b'.ip = a.ip + (j + 1) ∧
          b'.env vCN = u.length - (j + 1)) := by
    rintro j hj b ⟨hf, hbip, hN⟩
    have hz : b.env vZ = 0 := (hf.env vZ (by decide)).trans hc.1
    have h1 : b.env vONE = 1 := (hf.env vONE (by decide)).trans hc.2.1
    refine ⟨by simp [Cnd.eval, hz, hN]; omega, ?_⟩
    have hrd : b.ip < C.inp.length := by omega
    set b1 : Ds := { b.set vR0 (bitOf C.inp b.ip) with ip := b.ip + 1 }
    have hbit : bitOf C.inp b.ip = (u.getD j false).toNat := by rw [bitOf, hbip, hu j hj]
    set b2 : Ds := { b1 with out := b1.out ++ [true] }
    set x := u.getD j false with hx
    obtain ⟨b3, e3, hb3⟩ : ∃ b3, Ex C (.ite (.eq vR0 vONE) (.op (.emit true)) (.op (.emit false))) b2 b3 2 ∧
        b3 = { b2 with out := b2.out ++ [x] } := by
      cases hxv : x
      · exact ⟨_, Ex.iteF (by unfold Cnd.wf; decide)
          (by simp (config := { decide := true }) [Cnd.eval, b2, b1, env_set, hbit, ← hx, hxv, h1])
          (Ex.op (OpEx.emit false b2)), rfl⟩
      · exact ⟨_, Ex.iteT (by unfold Cnd.wf; decide)
          (by simp (config := { decide := true }) [Cnd.eval, b2, b1, env_set, hbit, ← hx, hxv, h1])
          (Ex.op (OpEx.emit true b2)), rfl⟩
    have e4 : Ex C (.op (.sub vCN vONE)) b3 (b3.set vCN (b3.env vCN - b3.env vONE)) 1 :=
      Ex.op (OpEx.sub vCN vONE b3 (by decide) (by
        rw [hb3]; simp (config := { decide := true }) [b2, b1, env_set, h1, hN]; omega))
    refine ⟨_, (Ex.seq (Ex.op (OpEx.rdI vR0 b hrd)) (Ex.seq (Ex.op (OpEx.emit true b1)) (Ex.seq e3 e4))).mono
      (by omega), ?_, ?_, ?_⟩
    · refine ⟨fun y hy => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
        rw [env_set, if_neg hy.2, hb3]
        simp only [b2, b1, env_set, if_neg hy.1]
        exact hf.env y (by simp [hy.1, hy.2])
      · simp only [DS.set, hb3, b2, b1, hf.out]
        simp [List.flatMap_append, List.append_assoc, hx, List.getD_eq_getElem _ _ hj]
        rw [List.take_add_one, List.flatMap_append, List.getElem?_eq_getElem hj]
        simp
      all_goals simp [DS.set, hb3, b2, b1, hf.ram, hf.rc, hf.kin, hf.kout, hf.kc]
    · simp [DS.set, hb3, b2, b1, hbip]; omega
    · simp (config := { decide := true }) [env_set, hb3, b2, b1, hN, h1]; omega
  obtain ⟨b, e, hb⟩ := ex_loopN (C := C) (c := .lt vZ vCN) (body := copyInBody) (by unfold Cnd.wf; decide)
    u.length 8 (fun j b => FrI [vR0, vCN] ((u.take j).flatMap fun x => [true, x]) a b ∧ b.ip = a.ip + j ∧
      b.env vCN = u.length - j) hstep
    (by rintro b ⟨hf, -, hN⟩; have hz : b.env vZ = 0 := (hf.env vZ (by decide)).trans hc.1; simp [Cnd.eval, hz, hN])
    a ⟨⟨fun _ _ => rfl, by simp, rfl, rfl, rfl, rfl, rfl⟩, by simp, by simp [hCN]⟩
  refine ⟨b, e, ?_⟩
  have := hb.1
  rwa [List.take_length] at this

/-! ## The widening program -/

def midA : Sc := .seq (.op (.copy vSX vPV)) <| .seq sizeP <| .seq (.op (.copy vRB vSS)) <|
  .seq (.op (.add vRB vSS)) (.op (.inc vRB))

def midB : Sc := .seq (.op (.copy vEE vPV)) <| .seq pow2P <| .seq (.op (.copy vCN vPD)) <|
  .seq (.op (.add vCN vSS)) <| .seq (.op (.add vCN vSS)) (.op (.inc vCN))

def unaryS : List Var := [vSX, vSS, vRB, vEE, vPD, vEJ, vCN]

theorem midA_spec (C : Ctx) (a : Ds) (hc : Consts a) (n : ℕ) (hn : a.env vPV = n) (hW : 4 * n + 8 ≤ C.Wd) :
    Runs C midA a (n * 5 + 20) unaryS [] (fun b => b.env vRB = 2 * n.size + 1 ∧ b.env vSS = n.size) := by
  have hsz := size_le_self n
  have hlt : 4 * n + 8 < 2 ^ C.Wd := lt_of_le_of_lt hW Nat.lt_two_pow_self
  refine Runs.op1 (run_copy C unaryS a vSX vPV (by decide) (by decide)) ?_ (by omega)
  refine Runs.callS (sizeP_spec C _ ⟨by norm_env; exact hc.1, by norm_env; exact hc.2.1, by norm_env; exact hc.2.2⟩
    n (by norm_env; exact hn) (by omega)) (by decide) ?_ (by omega)
  intro b hb hbS
  have h1 : b.env vONE = 1 := by rw [hb.env _ (by decide)]; norm_env; exact hc.2.1
  refine Runs.op1 (run_copy C unaryS b vRB vSS (by decide) (by decide)) ?_ (by omega)
  refine Runs.op1 (run_add C unaryS _ vRB vSS (by decide) (by decide) (by norm_env; rw [hbS]; omega)) ?_ (by omega)
  refine Runs.last (run_inc C unaryS _ vRB (by decide) (by norm_env; rw [hbS]; omega)) ?_ (by omega)
  intro _
  norm_env
  rw [hbS]; exact ⟨by ring, rfl⟩

theorem midB_spec (C : Ctx) (a : Ds) (hc : Consts a) (n : ℕ) (hn : a.env vPV = n) (hS : a.env vSS = n.size)
    (hW : 4 * n + 8 ≤ C.Wd) :
    Runs C midB a (n * 5 + 30) unaryS [] (fun b => b.env vCN = 2 ^ n + 2 * n.size + 1) := by
  have hsz := size_le_self n
  have hp : 2 ^ n + 2 * n.size + 1 < 2 ^ C.Wd := by
    have h1 : 2 ^ (n + 2) ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 := Nat.lt_two_pow_self (n := n)
    rw [pow_add] at h1; omega
  refine Runs.op1 (run_copy C unaryS a vEE vPV (by decide) (by decide)) ?_ (by omega)
  refine Runs.callS (pow2P_spec C _ ⟨by norm_env; exact hc.1, by norm_env; exact hc.2.1, by norm_env; exact hc.2.2⟩
    n (by norm_env; exact hn) (by omega)) (by decide) ?_ (by omega)
  intro b hb hbD
  have hbS : b.env vSS = n.size := by rw [hb.env _ (by decide)]; norm_env; exact hS
  refine Runs.op1 (run_copy C unaryS b vCN vPD (by decide) (by decide)) ?_ (by omega)
  refine Runs.op1 (run_add C unaryS _ vCN vSS (by decide) (by decide) (by norm_env; rw [hbS, hbD]; omega)) ?_
    (by omega)
  refine Runs.op1 (run_add C unaryS _ vCN vSS (by decide) (by decide) (by norm_env; rw [hbS, hbD]; omega)) ?_
    (by omega)
  refine Runs.last (run_inc C unaryS _ vCN (by decide) (by norm_env; rw [hbS, hbD]; omega)) ?_ (by omega)
  intro _
  norm_env
  rw [hbS, hbD]; ring

/-- The word the dispatcher reads: `n + 4` ones, a zero, the request. -/
def middle2 (r : AmplifierRequest) : List Bool := List.replicate (r.inputArity + 4) true ++ false :: amplifierInput r

def unaryP : Sc :=
  .seq constP <| .seq skipP <| .seq parseP <| .seq onesP <| .seq (.op (.emit true)) <| .seq (.op (.emit false)) <|
  .seq midA <| .seq (.loop (.lt vZ vRB) backBody) <| .seq midB <| .seq (.loop (.lt vZ vCN) copyInBody) <|
  .op (.emit false)

def unaryCost (n L0 : ℕ) : ℕ := 5 + (L0 * 3 + 4) + (n.size * 10 + 10) + (n * 8 + 60) + (n * 5 + 20) +
  ((2 * n.size + 1) * (3 + 2) + 2) + (n * 5 + 30) + ((2 ^ n + 2 * n.size + 1) * (8 + 2) + 2) + 30

theorem unaryP_run (C : Ctx) (r : AmplifierRequest)
    (hin : C.inp = List.replicate r.inputArity.size true ++ false :: amplifierInput r)
    (hW : 4 * r.inputArity + 8 ≤ C.Wd) :
    ∃ b, Ex C unaryP (a0 : Ds) b (unaryCost r.inputArity r.inputArity.size) ∧ b.out = frame (middle2 r) := by
  obtain ⟨n, f⟩ := r
  simp only at hin hW ⊢
  have hsz := size_le_self n
  have hlt : 4 * n + 8 < 2 ^ C.Wd := lt_of_le_of_lt hW Nat.lt_two_pow_self
  -- constants
  set a1 : Ds := ((((a0 : Ds).set vONE ((a0 : Ds).env vONE + 1)).set vTWO
    (((a0 : Ds).set vONE ((a0 : Ds).env vONE + 1)).env vTWO + 1))).set vTWO
    ((((a0 : Ds).set vONE ((a0 : Ds).env vONE + 1)).set vTWO
    (((a0 : Ds).set vONE ((a0 : Ds).env vONE + 1)).env vTWO + 1)).env vTWO + 1)
  have e0 : Ex C constP (a0 : Ds) a1 5 :=
    Ex.seq (Ex.op (OpEx.inc vONE _ (by simp [a0]; omega))) (Ex.seq (Ex.op (OpEx.inc vTWO _
      (by simp (config := { decide := true }) [a0, env_set]; omega)))
      (Ex.op (OpEx.inc vTWO _ (by simp (config := { decide := true }) [a0, env_set]; omega))))
  have hc1 : Consts a1 := ⟨by simp (config := { decide := true }) [a1, a0, env_set],
    by simp (config := { decide := true }) [a1, a0, env_set], by simp (config := { decide := true }) [a1, a0, env_set]⟩
  obtain ⟨b1, e1, hf1, hip1⟩ := skipP_spec C n.size (amplifierInput ⟨n, f⟩) hin a1 hc1 (by simp [a1, a0, DS.set])
  have hc_b1 : Consts b1 := ⟨(hf1.env _ (by decide)).trans hc1.1, (hf1.env _ (by decide)).trans hc1.2.1,
    (hf1.env _ (by decide)).trans hc1.2.2⟩
  have hin2 : C.inp = (List.replicate n.size true ++ [false]) ++ frame n.bits ++ boolFunctionTable f := by
    rw [hin]; simp [amplifierInput, List.append_assoc]
  obtain ⟨b2, e2, hf2, hip2, hn2⟩ := parseP_spec C n (n.size + 1) _ _ hin2 (by simp) (by omega) b1 hc_b1 hip1
  have hc_b2 : Consts b2 := ⟨(hf2.env _ (by decide)).trans hc_b1.1, (hf2.env _ (by decide)).trans hc_b1.2.1,
    (hf2.env _ (by decide)).trans hc_b1.2.2⟩
  obtain ⟨b3, e3, hf3, -⟩ := onesP_spec C b2 hc_b2 n hn2 (by omega)
  have hc_b3 : Consts b3 := hc_b2.of_fr hf3 (by decide)
  set b4 : Ds := { { b3 with out := b3.out ++ [true] } with out := { b3 with out := b3.out ++ [true] }.out ++ [false] }
  have e4 : Ex C (.seq (.op (.emit true)) (.op (.emit false))) b3 b4 3 :=
    Ex.seq (Ex.op (OpEx.emit true b3)) (Ex.op (OpEx.emit false _))
  have hc_b4 : Consts b4 := hc_b3
  have hn4 : b4.env vPV = n := by rw [show b4.env = b3.env from rfl, hf3.env vPV (by decide), hn2]
  obtain ⟨b5, e5, hf5, hRB5, hS5⟩ := midA_spec C b4 hc_b4 n hn4 hW
  have hc_b5 : Consts b5 := hc_b4.of_fr hf5 (by decide)
  have hip5 : b5.ip = n.size + 1 + 2 * n.size + 1 := by rw [hf5.ip]; simp [b4, hf3.ip, hip2]
  obtain ⟨b6, e6, hf6, hip6⟩ := backLoop_spec C b5 hc_b5 (2 * n.size + 1) hRB5 (by omega)
  have hc_b6 : Consts b6 := ⟨(hf6.env _ (by decide)).trans hc_b5.1, (hf6.env _ (by decide)).trans hc_b5.2.1,
    (hf6.env _ (by decide)).trans hc_b5.2.2⟩
  have hn6 : b6.env vPV = n := by rw [hf6.env vPV (by decide), hf5.env vPV (by decide), hn4]
  have hS6 : b6.env vSS = n.size := by rw [hf6.env vSS (by decide), hS5]
  obtain ⟨b7, e7, hf7, hCN7⟩ := midB_spec C b6 hc_b6 n hn6 hS6 hW
  have hc_b7 : Consts b7 := hc_b6.of_fr hf7 (by decide)
  have hulen : (amplifierInput ⟨n, f⟩).length = 2 ^ n + 2 * n.size + 1 := by
    rw [amplifierInput_length']; simp only; omega
  have hip7 : b7.ip = n.size + 1 := by rw [hf7.ip, hip6, hip5]; omega
  obtain ⟨b8, e8, hf8⟩ := copyInLoop_spec C b7 hc_b7 (amplifierInput ⟨n, f⟩) (by rw [hCN7, hulen])
    (by rw [hip7, hin]; simp only [List.length_append, List.length_replicate, List.length_cons]; omega)
    (by
      intro i hi
      rw [hip7, hin, show List.replicate n.size true ++ false :: amplifierInput ⟨n, f⟩ =
        (List.replicate n.size true ++ [false]) ++ amplifierInput ⟨n, f⟩ by simp,
        List.getD_append_right _ _ _ _ (by simp)]
      simp)
  have e9 : Ex C (.op (.emit false)) b8 { b8 with out := b8.out ++ [false] } 1 := Ex.op (OpEx.emit false b8)
  have et : Ex C (.op (.emit true)) b3 { b3 with out := b3.out ++ [true] } 1 := Ex.op (OpEx.emit true b3)
  have ef : Ex C (.op (.emit false)) { b3 with out := b3.out ++ [true] } b4 1 := Ex.op (OpEx.emit false _)
  refine ⟨_, (Ex.seq e0 (Ex.seq e1 (Ex.seq e2 (Ex.seq e3 (Ex.seq et (Ex.seq ef (Ex.seq e5 (Ex.seq e6
    (Ex.seq e7 (Ex.seq e8 e9)))))))))).mono ?_, ?_⟩
  · unfold unaryCost; omega
  · have ho : b8.out = [] ++ (List.replicate (n + 4) [true, true]).flatten ++ [true, false] ++
        (amplifierInput ⟨n, f⟩).flatMap (fun x => [true, x]) := by
      rw [hf8.out, hf7.out, hf6.out, hf5.out]
      simp only [b4, hf3.out, hf2.out, hf1.out]
      simp [a1, a0, DS.set, List.append_assoc]
    have hrep : ∀ m, (List.replicate m [true, true]).flatten = (List.replicate m true).flatMap (fun x => [true, x]) := by
      intro m; induction m with
      | zero => rfl
      | succ m ih => simp [List.replicate_succ, ih]
    simp only [ho, middle2, frame_replicate, frame_eq_flatMap]
    simp [frame, List.append_assoc, hrep]

/-- Width `8·2^(size n)` from the `size n` leading ones; no calls. -/
def unarySz : Sz := ⟨8, 1, 0, 0, 0, 0⟩

theorem unary_width (r : AmplifierRequest) : 4 * r.inputArity + 8 ≤ unarySz.W (leadOnes (middle1 r)) := by
  rw [middle1, NearCubicGates.Close.CounterMachine.CellTablesProg.leadOnes_rep]
  have := two_pow_size_ge r.inputArity
  simp only [unarySz, Sz.W, one_mul]; omega

/-- The widening machine. -/
noncomputable def unaryWF :
    WordFunction AmplifierRequest middle1 (fun r => frame (middle2 r))
      (fun r => langBudget Code.Parsing.copyCallee unarySz NV 0 (middle1 r)
        (unaryCost r.inputArity r.inputArity.size)) :=
  wordFunction_of_lang middle1 (fun r => frame (middle2 r)) Code.Parsing.copyCallee unarySz unaryP
    (fun r => unaryCost r.inputArity r.inputArity.size)
    (fun r => by
      obtain ⟨b, e, hout⟩ := unaryP_run (ctxOf Code.Parsing.copyCallee unarySz (middle1 r)) r rfl (unary_width r)
      exact ⟨b, _, e, hout, le_rfl⟩)
    (fun r => by have := unary_width r; omega)

end NearCubicGates.Adapters.Amplification.Enc
