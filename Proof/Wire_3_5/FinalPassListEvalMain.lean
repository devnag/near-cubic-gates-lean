import Proof.Wire_3_5.FinalPassListEvalBody

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.ListEval
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.FinalPass.Tm

/-- Compare the report `S` with the state on stream 2: `X := [S ≠ s]`. -/
def compare : LProg :=
  .seq (.whs 2 (.seq (RM.fwdC 2 rSP) (.ifr rS (.dec rS) (RM.setF rX)))) (.ifr rS (RM.setF rX) .skip)

/-- Write the result cell. -/
def output : LProg := .ifr rX (.setc false) (.setc true)

/-- Clear the registers and rewind the streams. -/
def cleanup : LProg :=
  .seq (RM.clear rS) (.seq (RM.clear rX) (.seq (RM.clear rF) (.seq (RM.clear rP) (.seq (RM.clear rMR)
    (.seq (RM.rewind 2 rSP) (RM.rewind 1 rTP))))))

/-- The repair and the comparison. -/
def finalPart : LProg := .seq leqFlag (.seq (.ifr rF (RM.clear rS) .skip) (.seq compare (.seq output cleanup)))

/-- **The stage-5 program.** -/
def main : LProg := .seq (RM.readU 1 rTP rMR) (.seq (.whs 1 body) finalPart)

/-- The blank state with result cell `b`. -/
def blank (b : Bool) : LState := ⟨fun _ => 0, fun _ => 0, b⟩

/-! ## The loop -/

theorem loop_spec (M J : ℕ) (W : ℕ → ℕ) (row : ℕ → List Bool) (Z : List Bool) (s : ℕ) :
    ∀ (js : List ℕ) (acc : Option ℕ × ℕ) (σ : LState), (∀ j ∈ js, (row j).length = Z.length) →
      Inv M J W row Z js acc σ →
      ∃ τ, RExec (streams M J W row Z s) (capOf M J W row Z.length) (.whs 1 body) σ τ
          (js.length * (bodyCost (capOf M J W row Z.length) + 2) + 1) ∧
        Inv M J W row Z [] (levelFold M J W row Z acc js) τ
  | [], acc, σ, _, hinv => by
    refine ⟨σ, RExec.mono (RExec.whsF ?_) (by simp), hinv⟩
    unfold sbit
    exact read_of_cons (by rw [streams_one]; simpa using hinv.1)
  | j :: js, acc, σ, hrows, hinv => by
    obtain ⟨τ1, h1, hinv1⟩ := body_spec M J W row Z s js j acc σ (hrows j (by simp)) hinv
    obtain ⟨τ, h2, hinv2⟩ := loop_spec M J W row Z s js _ τ1 (fun k hk => hrows k (by simp [hk])) hinv1
    refine ⟨τ, RExec.mono (RExec.whsT ?_ h1 h2) (by simp; ring_nf; omega), ?_⟩
    · unfold sbit
      have hd : (streams M J W row Z s 1).drop (σ.sh 1) = true :: (unary (pow (topW J W j)) ++
          (unary (topW J W j) ++ (row j ++ (js.flatMap (record J W row) ++ [false])))) := by
        rw [streams_one, hinv.1]; simp [record]
      exact read_of_cons hd
    · simpa [levelFold] using hinv2

/-! ## The repair and the comparison -/

def repOf (M : ℕ) (o : Option ℕ) : ℕ := match o with
  | some v => if v ≤ M then v else 0
  | none => 0

theorem reportRef_eq_rep (M J : ℕ) (W : ℕ → ℕ) (row : ℕ → List Bool) (Z : List Bool) :
    reportRef M J W row Z = repOf M (levelFold M J W row Z (some 0, 0) (levels J)).1 := by
  unfold reportRef repOf
  rfl

variable (inp : Fin 3 → List Bool) (cap : ℕ)

theorem cmpLoop_spec (rest : List Bool) (hcap : 1 ≤ cap) :
    ∀ (n : ℕ) (σ : LState), (inp 2).drop (σ.sh 2) = List.replicate n true ++ false :: rest →
      σ.val rSP + n ≤ cap → σ.val rS ≤ cap → σ.val rX ≤ 1 →
      RExec inp cap (.whs 2 (.seq (RM.fwdC 2 rSP) (.ifr rS (.dec rS) (RM.setF rX)))) σ
        ((((σ.seth 2 (σ.sh 2 + n)).setv rSP (σ.val rSP + n)).setv rS (σ.val rS - n)).setv rX
          (if σ.val rS < n then 1 else σ.val rX)) (15 * n + 1)
  | 0, σ, hd, _, _, _ => by
    have e : (((σ.seth 2 (σ.sh 2 + 0)).setv rSP (σ.val rSP + 0)).setv rS (σ.val rS - 0)).setv rX
        (if σ.val rS < 0 then 1 else σ.val rX) = σ := by
      rs_eq
    rw [e]
    exact RExec.whsF (by unfold sbit; exact read_of_cons (by simpa using hd))
  | n + 1, σ, hd, hSP, hS, hX => by
    have s1 := fwdC_spec inp cap 2 rSP σ (by omega)
    have hd' : (inp 2).drop (((σ.seth 2 (σ.sh 2 + 1)).setv rSP (σ.val rSP + 1)).sh 2) =
        List.replicate n true ++ false :: rest := by
      simp only [RState.setv_sh, RState.seth_sh, Function.update_self]
      exact drop_succ_of_cons (by simpa [List.replicate_succ] using hd)
    by_cases hS0 : σ.val rS = 0
    · have s2 := setF_spec inp cap rX ((σ.seth 2 (σ.sh 2 + 1)).setv rSP (σ.val rSP + 1)) (by simpa using hX) hcap
      have s2' := RExec.ifrF (r := rS) (P := .dec rS) (by simpa using hS0) s2
      have ih := cmpLoop_spec rest hcap n (((σ.seth 2 (σ.sh 2 + 1)).setv rSP (σ.val rSP + 1)).setv rX 1) (by simpa using hd')
        (by simp; omega) (by simp; omega) (by simp)
      refine RExec.cast inp cap (RExec.whsT (by unfold sbit; exact read_of_cons (by simpa [List.replicate_succ] using hd))
        (RExec.seq s1 s2') ih) ?_ (by omega)
      rs_eq [hS0]
    · have s2 := RExec.dec (inp := inp) (cap := cap) rS ((σ.seth 2 (σ.sh 2 + 1)).setv rSP (σ.val rSP + 1))
        (by simp; omega)
      have s2' := RExec.ifrT (r := rS) (Q := RM.setF rX) (by simpa using hS0) s2
      have ih := cmpLoop_spec rest hcap n (((σ.seth 2 (σ.sh 2 + 1)).setv rSP (σ.val rSP + 1)).setv rS
        (((σ.seth 2 (σ.sh 2 + 1)).setv rSP (σ.val rSP + 1)).val rS - 1)) (by simpa using hd')
        (by simp; omega) (by simp; omega) (by simp; omega)
      refine RExec.cast inp cap (RExec.whsT (by unfold sbit; exact read_of_cons (by simpa [List.replicate_succ] using hd))
        (RExec.seq s1 s2') ih) ?_ (by omega)
      rs_eq
      all_goals split_ifs <;> omega

/-- The step count of the repair, the comparison and the cleanup. -/
def finalCost (cap : ℕ) : ℕ := 200 * cap + 100

theorem finalPart_spec (M J : ℕ) (W : ℕ → ℕ) (row : ℕ → List Bool) (Z : List Bool) (s : ℕ) (acc : Option ℕ × ℕ)
    (σ : LState) (hinv : Inv M J W row Z [] acc σ) (hs : s ≤ M) :
    RExec (streams M J W row Z s) (capOf M J W row Z.length) finalPart σ (blank (decide (repOf M acc.1 = s)))
      (finalCost (capOf M J W row Z.length)) := by
  rcases acc with ⟨o, cp⟩
  obtain ⟨hd, hTP, hs0, hs2, hMR, hP, hPL, hF1, hSB, hsome, hnone, hC, hW, hV, hU, hT, hR, hSP, hX, hT1, hT2⟩ := hinv
  simp only at hP hPL hsome hnone ⊢
  generalize hinp : streams M J W row Z s = inp
  generalize hcapv : capOf M J W row Z.length = cap
  have hin1 : inp 1 = levelWord M J W row := by rw [← hinp]; rfl
  have hin2 : inp 2 = unary s := by rw [← hinp]; rfl
  have hcapB : cap = 4 * (wordLen M J W row + Z.length + 1) := by rw [← hcapv]; rfl
  have hM1 := word_M_le M J W row
  have hlen := drop_len_le hd (by simp)
  have hsh1 : σ.sh 1 ≤ wordLen M J W row := by unfold wordLen; simp at hlen; omega
  -- 1. the flag for `s_0 > M`
  have f1 := leqFlag_spec inp cap σ ⟨hT, hT1, hT2⟩ (by omega) (by omega) hF1 (by omega)
  obtain ⟨σa, hσa⟩ : ∃ τ : LState, τ = σ.setv rF (if σ.val rMR < σ.val rS then 1 else σ.val rF) := ⟨_, rfl⟩
  rw [← hσa] at f1
  -- 2. the repaired report into `S`
  have f2 : RExec inp cap (.ifr rF (RM.clear rS) .skip) σa (σa.setv rS (repOf M o)) (3 * cap + 2) := by
    cases o with
    | none =>
      have hF := hnone rfl
      have hFa : σa.val rF = 1 := by rw [hσa]; simp [hF]
      have c1 := clear_spec inp cap rS (σa.val rS) σa rfl (by rw [hσa]; simp; omega)
      exact RExec.mono (RExec.ifrT (by omega) c1) (by rw [hσa]; simp; omega)
    | some v =>
      obtain ⟨hF0, hS0⟩ := hsome v rfl
      by_cases hMv : M < v
      · have hFa : σa.val rF = 1 := by rw [hσa]; simp [hMR, hS0, hMv]
        have c1 := clear_spec inp cap rS (σa.val rS) σa rfl (by rw [hσa]; simp; omega)
        have hr : repOf M (some v) = 0 := by simp [repOf]; omega
        rw [hr]
        exact RExec.mono (RExec.ifrT (by omega) c1) (by rw [hσa]; simp; omega)
      · have hFa : σa.val rF = 0 := by rw [hσa]; simp [hMR, hS0, hMv, hF0]
        have hr : repOf M (some v) = v := by simp [repOf]; omega
        have e : σa.setv rS (repOf M (some v)) = σa := by
          rw [hr]; rw [hσa]; rs_eq [hS0]
        rw [e]
        exact RExec.mono (RExec.ifrF hFa (RExec.skip σa)) (by omega)
  obtain ⟨σb, hσb⟩ : ∃ τ : LState, τ = σa.setv rS (repOf M o) := ⟨_, rfl⟩
  rw [← hσb] at f2
  have hrepM : repOf M o ≤ M := by unfold repOf; split <;> [split <;> omega; omega]
  -- 3. the comparison with `s`
  have hd2 : (inp 2).drop (σb.sh 2) = List.replicate s true ++ false :: [] := by
    rw [hσb, hσa]; simp [hs2, hin2, unary]
  have f3a := cmpLoop_spec inp cap [] (by omega) s σb hd2 (by rw [hσb, hσa]; simp [hSP]; omega)
    (by rw [hσb]; simp; omega) (by rw [hσb, hσa]; simp [hX])
  obtain ⟨σc, hσc⟩ : ∃ τ : LState, τ = (((σb.seth 2 (σb.sh 2 + s)).setv rSP (σb.val rSP + s)).setv rS
      (σb.val rS - s)).setv rX (if σb.val rS < s then 1 else σb.val rX) := ⟨_, rfl⟩
  rw [← hσc] at f3a
  have hcS : σc.val rS = repOf M o - s := by rw [hσc, hσb]; simp
  have hcX : σc.val rX = if repOf M o < s then 1 else 0 := by rw [hσc, hσb, hσa]; simp [hX]
  have f3b : RExec inp cap (.ifr rS (RM.setF rX) .skip) σc (σc.setv rX (if repOf M o = s then 0 else 1)) 5 := by
    by_cases hz : σc.val rS = 0
    · have e : σc.setv rX (if repOf M o = s then 0 else 1) = σc := by
        have : σc.val rX = if repOf M o = s then 0 else 1 := by
          rw [hcX]; rw [hcS] at hz; split_ifs <;> omega
        rw [← this]; exact setv_same σc rX
      rw [e]
      exact RExec.mono (RExec.ifrF hz (RExec.skip σc)) (by omega)
    · have e : (if repOf M o = s then 0 else 1) = 1 := by rw [hcS] at hz; split_ifs <;> omega
      rw [e]
      exact RExec.mono (RExec.ifrT hz (setF_spec inp cap rX σc (by rw [hcX]; split_ifs <;> omega) (by omega)))
        (by omega)
  -- 4. the result cell
  have f4 : RExec inp cap output (σc.setv rX (if repOf M o = s then 0 else 1))
      ((σc.setv rX (if repOf M o = s then 0 else 1)).setc (decide (repOf M o = s))) 2 := by
    unfold output
    by_cases he : repOf M o = s
    · have := RExec.ifrF (r := rX) (P := RM.setc false) (Q := RM.setc true) (by simp [he])
        (RExec.setc (inp := inp) (cap := cap) true (σc.setv rX (if repOf M o = s then 0 else 1)))
      simpa [he] using this
    · have := RExec.ifrT (r := rX) (P := RM.setc false) (Q := RM.setc true) (by simp [he])
        (RExec.setc (inp := inp) (cap := cap) false (σc.setv rX (if repOf M o = s then 0 else 1)))
      simpa [he] using this
  obtain ⟨σd, hσd⟩ : ∃ τ : LState, τ = (σc.setv rX (if repOf M o = s then 0 else 1)).setc (decide (repOf M o = s)) :=
    ⟨_, rfl⟩
  rw [← hσd] at f4
  -- 5. cleanup
  have hdS : σd.val rS = repOf M o - s := by rw [hσd]; simp [hcS]
  have hdX : σd.val rX ≤ 1 := by rw [hσd]; simp; split_ifs <;> omega
  have hdF : σd.val rF ≤ 1 := by rw [hσd, hσc, hσb, hσa]; simp; split_ifs <;> omega
  have hdP : σd.val rP = cp := by rw [hσd, hσc, hσb, hσa]; simp [hP]
  have hdM : σd.val rMR = M := by rw [hσd, hσc, hσb, hσa]; simp [hMR]
  have hdSP : σd.val rSP = s := by rw [hσd, hσc, hσb, hσa]; simp [hSP]
  have hdTP : σd.val rTP = σ.sh 1 := by rw [hσd, hσc, hσb, hσa]; simp [hTP]
  have g1 := clear_spec inp cap rS (σd.val rS) σd rfl (by rw [hdS]; omega)
  have g2 := clear_spec inp cap rX (σd.val rX) (σd.setv rS 0) (by simp) (by simp; omega)
  have g3 := clear_spec inp cap rF (σd.val rF) ((σd.setv rS 0).setv rX 0) (by simp) (by simp; omega)
  have g4 := clear_spec inp cap rP cp (((σd.setv rS 0).setv rX 0).setv rF 0) (by simp [hdP]) (by simp [hdP]; omega)
  have g5 := clear_spec inp cap rMR M ((((σd.setv rS 0).setv rX 0).setv rF 0).setv rP 0) (by simp [hdM])
    (by simp [hdM]; omega)
  have g6 := rewind_spec inp cap 2 rSP s (((((σd.setv rS 0).setv rX 0).setv rF 0).setv rP 0).setv rMR 0)
    (by simp [hdSP]) (by simp [hdSP]; omega)
  have g7 := rewind_spec inp cap 1 rTP (σ.sh 1) ((((((σd.setv rS 0).setv rX 0).setv rF 0).setv rP 0).setv rMR 0).setv
    rSP 0 |>.seth 2 ((((((σd.setv rS 0).setv rX 0).setv rF 0).setv rP 0).setv rMR 0).sh 2 - s)) (by simp [hdTP])
    (by simp [hdTP]; omega)
  refine RExec.cast inp cap (RExec.seq f1 (RExec.seq f2 (RExec.seq (RExec.seq f3a f3b) (RExec.seq f4
    (RExec.seq g1 (RExec.seq g2 (RExec.seq g3 (RExec.seq g4 (RExec.seq g5 (RExec.seq g6 g7)))))))))) ?_ ?_
  · rw [hσd, hσc, hσb, hσa]
    rs_eq [blank, hs0, hs2, hTP, hC, hW, hV, hU, hT, hR, hSP, hX, hT1, hT2]
  · unfold finalCost
    rw [hdS]
    omega

/-! ## The whole program -/

/-- The step count of the stage-5 program. -/
def mainCost (cap : ℕ) : ℕ := 50 * (cap + 1) * (cap + 1) * (cap + 1)

theorem levels_length (J : ℕ) : (levels J).length = J + 1 := by simp [levels]

theorem word_levels_le (M J : ℕ) (W : ℕ → ℕ) (row : ℕ → List Bool) : J + 1 ≤ wordLen M J W row := by
  have h : (levels J).length ≤ ((levels J).flatMap (record J W row)).length := by
    rw [List.length_flatMap]
    calc (levels J).length = ((levels J).map fun _ => 1).sum := by simp
      _ ≤ ((levels J).map fun j => (record J W row j).length).sum :=
        List.sum_le_sum (fun j _ => by simp [record])
  rw [levels_length] at h
  unfold wordLen levelWord
  simp only [List.length_append]
  omega

theorem main_spec (M J : ℕ) (W : ℕ → ℕ) (row : ℕ → List Bool) (Z : List Bool) (s : ℕ) (b : Bool)
    (hrows : ∀ j ≤ J, (row j).length = Z.length) (hs : s ≤ M) :
    RExec (streams M J W row Z s) (capOf M J W row Z.length) main (blank b)
      (blank (decide (reportRef M J W row Z = s))) (mainCost (capOf M J W row Z.length)) := by
  generalize hcapv : capOf M J W row Z.length = cap
  have hcapB : cap = 4 * (wordLen M J W row + Z.length + 1) := by rw [← hcapv]; rfl
  have hM1 := word_M_le M J W row
  have hJ1 := word_levels_le M J W row
  have hword : levelWord M J W row = List.replicate M true ++ false :: ((levels J).flatMap (record J W row) ++ [false]) :=
    by simp [levelWord, unary]
  have hd0 : (streams M J W row Z s 1).drop ((blank b).sh 1) =
      List.replicate M true ++ false :: ((levels J).flatMap (record J W row) ++ [false]) := by
    rw [streams_one, hword]; rfl
  obtain ⟨ho, he⟩ := ones_of_drop hd0
  have r1 := readU_spec (streams M J W row Z s) cap 1 rTP rMR (by decide) M (blank b) ho he (by simp [blank]; omega)
    (by simp [blank]; omega)
  obtain ⟨σ1, hσ1⟩ : ∃ τ : LState, τ = (((blank b).seth 1 ((blank b).sh 1 + M + 1)).setv rTP
      ((blank b).val rTP + M + 1)).setv rMR ((blank b).val rMR + M) := ⟨_, rfl⟩
  rw [← hσ1] at r1
  have hinv1 : Inv M J W row Z (levels J) (some 0, 0) σ1 := by
    rw [hσ1]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have key : (levelWord M J W row).drop (0 + (List.replicate M true ++ [false]).length) =
          (levels J).flatMap (record J W row) ++ [false] :=
        drop_add_of_append (by rw [List.drop_zero, hword]; simp)
      simp only [List.length_append, List.length_replicate, List.length_singleton, Nat.zero_add] at key
      simpa [blank] using key
    all_goals simp [blank]
  have r2 := loop_spec M J W row Z s (levels J) (some 0, 0) σ1
    (fun j hj => hrows j (by simp [levels] at hj; omega)) hinv1
  rw [hcapv] at r2
  obtain ⟨σ2, r2, hinv2⟩ := r2
  have r3 := finalPart_spec M J W row Z s _ σ2 hinv2 hs
  rw [hcapv] at r3
  rw [reportRef_eq_rep]
  refine RExec.mono (RExec.seq r1 (RExec.seq r2 r3)) ?_
  unfold finalCost mainCost bodyCost
  rw [levels_length]
  have hcc : (J + 1) * (40 * (cap + 1) * (cap + 1) + 2) ≤ cap * (40 * (cap + 1) * (cap + 1) + 2) :=
    Nat.mul_le_mul_right _ (by omega)
  have hc8 : 8 ≤ cap := by omega
  have hMc : M ≤ cap := by omega
  have hsq : 8 * cap ≤ cap * cap := Nat.mul_le_mul_right _ hc8
  have hcube : 0 ≤ cap * cap * cap := Nat.zero_le _
  linarith [hcc, hc8, hMc, hsq, hcube]

end NearCubicWires.WireExponent3_5.FinalPass.ListEval
