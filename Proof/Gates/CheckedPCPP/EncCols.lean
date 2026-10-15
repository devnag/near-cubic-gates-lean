import Proof.Gates.CheckedPCPP.ColRead
import Proof.Gates.CheckedPCPP.Clear

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CheckedPCPP

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.WordPrograms NearCubicGates.PublishedSources.PCPP

variable {ns nr : ℕ} {cap : ℕ}

/-- Clear the first `B` cells of every stream in the list (driver stream `TT = 1^B`, counter `CR`). -/
def clearAll (TT : Fin (ns + 1)) (CR : Fin nr) : List (Fin (ns + 1)) → WMX ns nr
  | [] => WMX.skip
  | X :: Xs => .seq (clearOne X TT CR) (clearAll TT CR Xs)

theorem clearAll_runs (TT : Fin (ns + 1)) (CR : Fin nr) (B : ℕ) (hB : B ≤ cap) :
    ∀ (Xs : List (Fin (ns + 1))) (σ : WState ns nr), Xs.Nodup → TT ∉ Xs → σ.st TT = List.replicate B true →
      σ.sh TT = 0 → σ.val CR = 0 → (∀ X ∈ Xs, σ.sh X = 0) →
      Runs cap (clearAll TT CR Xs) σ (Xs.length * (18 * B + 4))
        (fun τ => (∀ X ∈ Xs, τ.st X = clearPrefix B (σ.st X)) ∧ (∀ Y, Y ∉ Xs → τ.st Y = σ.st Y) ∧
          τ.sh = σ.sh ∧ τ.val = σ.val ∧ τ.cell = σ.cell)
  | [], σ, _, _, _, _, _, _ => ⟨σ, by simpa [clearAll] using WXExec.skip cap σ, by simp, fun _ _ => rfl, rfl, rfl, rfl⟩
  | X :: Xs, σ, hnd, hT, hTst, hTsh, hCR, h0 => by
    have hXT : X ≠ TT := fun e => hT (by simp [e])
    have e1 := clearOne_exec X TT CR hXT B hB σ hTst hTsh (h0 X (by simp)) hCR
    set σ1 := σ.sets X (clearPrefix B (σ.st X)) with hσ1
    obtain ⟨τ, e2, p1, p2, p3, p4, p5⟩ := clearAll_runs TT CR B hB Xs σ1 (List.nodup_cons.1 hnd).2
      (fun h => hT (List.mem_cons_of_mem _ h)) (by simp [hσ1, Function.update_apply, Ne.symm hXT, hTst])
      (by simp [hσ1, hTsh]) (by simp [hσ1, hCR]) (fun Y hY => by simp [hσ1]; exact h0 Y (List.mem_cons_of_mem _ hY))
    have hXn : X ∉ Xs := (List.nodup_cons.1 hnd).1
    refine ⟨τ, WXExec.mono (WXExec.seq e1 e2) (by simp; ring_nf; omega), ?_, ?_, by rw [p3]; simp [hσ1],
      by rw [p4]; simp [hσ1], by rw [p5]; simp [hσ1]⟩
    · intro Y hY
      rcases List.mem_cons.1 hY with rfl | hY'
      · rw [p2 Y hXn]; simp [hσ1]
      · rw [p1 Y hY']
        have hYX : Y ≠ X := fun e => hXn (e ▸ hY')
        simp [hσ1, Function.update_of_ne hYX]
    · intro Y hY
      have hYX : Y ≠ X := fun e => hY (by simp [e])
      rw [p2 Y (fun h => hY (List.mem_cons_of_mem _ h))]
      simp [hσ1, Function.update_of_ne hYX]

/-! ## One column -/

section Cols

variable (E : LinearCodeFamily) {bud : MessageRequest → ℕ}
  (wf : WordFunction MessageRequest messageWord (fun m => FramedSim.pairs (List.ofFn (E.enc m.1 m.2.val))) bud)

/-- The encoder's input tape. -/
def encIn : Fin wf.program.tapeCount := ⟨0, by have := wf.program.twoTapes; omega⟩

/-- One column. Registers: `R 0 = q`, `R 1 = i`, `R 9 = L`, `R 11 = B`; the others are scratch. -/
noncomputable def colBody (tmap : Fin wf.program.tapeCount → Fin (ns + 1)) (MAT TT LG : Fin (ns + 1)) (R : Fin 14 ↪ Fin nr) :
    WMX ns nr :=
  .seq (msgW (tmap (encIn E wf)) (R 0) (R 1) (R 2) (R 3) (R 4) (R 5) (R 6) (R 7))
  (.seq (rewindBy (tmap (encIn E wf)) (R 11) (R 10) (R 7))
  (.seq (WMX.machZ wf.program.machine tmap LG)
  (.seq (.wm (WM.clear (R 9)))
  (.seq (rdCol (tmap wf.program.outputTape) MAT (R 0) (R 1) (R 8) (R 9) (R 10) (R 7) (R 11))
  (.seq (clearAll TT (R 12) (List.ofFn tmap))
    (WMX.inc (R 1)))))))

/-- The state between columns: columns `< i` written. -/
structure ColAt (tmap : Fin wf.program.tapeCount → Fin (ns + 1)) (MAT TT LG : Fin (ns + 1)) (R : Fin 14 ↪ Fin nr)
    (σ0 : WState ns nr) (n B i : ℕ) (σ : WState ns nr) : Prop where
  enc : ∀ j, RdEq (σ.st (tmap j)) [] ∧ σ.sh (tmap j) = 0
  mat : ∀ p, readTapeBit (σ.st MAT) p = matPart E n i 0 p
  math : σ.sh MAT = 0
  q : σ.val (R 0) = n
  col : σ.val (R 1) = i
  len : σ.val (R 9) = if i = 0 then 0 else E.length n
  bnd : σ.val (R 11) = B
  zero : ∀ k : Fin 14, k ≠ 0 → k ≠ 1 → k ≠ 9 → k ≠ 11 → k ≠ 13 → σ.val (R k) = 0
  frame : SameExcept σ0 σ (List.ofFn tmap ++ [MAT]) (List.ofFn R)

/-- The cost bound of one column. -/
def colCost (n L B t : ℕ) : ℕ := msgCost n + rdCost n L B + (t + 2) * (18 * B + 4) + 3 * L + 20

theorem nodup_R (R : Fin 14 ↪ Fin nr) (l : List (Fin 14)) (hl : l.Nodup) : (l.map R).Nodup :=
  hl.map R.injective

theorem colBody_runs (tmap : Fin wf.program.tapeCount → Fin (ns + 1)) (hinj : Function.Injective tmap)
    {MAT TT LG : Fin (ns + 1)} (hM : ∀ j, tmap j ≠ MAT) (hT : ∀ j, tmap j ≠ TT) (hL : ∀ j, tmap j ≠ LG)
    (hMT : MAT ≠ TT) (hML : MAT ≠ LG) (R : Fin 14 ↪ Fin nr) (σ0 : WState ns nr) (B : ℕ)
    (hTT : σ0.st TT = List.replicate B true) (hTTh : σ0.sh TT = 0)
    (hLG : σ0.st LG = List.replicate B false) (hLGh : σ0.sh LG = 0)
    (n i : ℕ) (hn : 2 ≤ n) (hi : i < n)
    (hB : (frame (messageWord (unitReq n i hn))).length + bud (unitReq n i hn) + 1 ≤ B) (hBL : 2 * E.length n ≤ B)
    (hcap : (E.length n + 1) * n + B + 2 * n ≤ cap) (σ : WState ns nr) (hσ : ColAt E wf tmap MAT TT LG R σ0 n B i σ) :
    Runs cap (colBody E wf tmap MAT TT LG R) σ (colCost n (E.length n) B wf.program.tapeCount)
      (fun τ => ColAt E wf tmap MAT TT LG R σ0 n B (i + 1) τ ∧ τ.val (R 13) = σ.val (R 13)) := by
  have hRe : ∀ a b : Fin 14, R a = R b ↔ a = b := fun a b => R.injective.eq_iff
  set IN := tmap (encIn E wf) with hIN
  set OE := tmap wf.program.outputTape with hOE
  have hOM : OE ≠ MAT := hM _
  have hz : ∀ k : Fin 14, k ≠ 0 → k ≠ 1 → k ≠ 9 → k ≠ 11 → k ≠ 13 → σ.val (R k) = 0 := hσ.zero
  -- 1. the encoder's input
  obtain ⟨τ1, e1, p1o, p1N1, p1H, p1RB, p1A, p1BC, p1s⟩ := msgW_runs (cap := cap) IN
    (Q := R 0) (I := R 1) (N1 := R 2) (H := R 3) (RB := R 4) (A := R 5) (BC := R 6) (T := R 7)
    (by simp [hRe]) n i hn hi (by omega) σ [] hσ.q hσ.col (hz 2 (by decide) (by decide) (by decide) (by decide) (by decide))
    (hz 3 (by decide) (by decide) (by decide) (by decide) (by decide)) (hz 4 (by decide) (by decide) (by decide) (by decide) (by decide))
    (hz 5 (by decide) (by decide) (by decide) (by decide) (by decide)) (hz 6 (by decide) (by decide) (by decide) (by decide) (by decide))
    (hz 7 (by decide) (by decide) (by decide) (by decide) (by decide)) ⟨(hσ.enc _).1, (hσ.enc _).2⟩
  simp only [List.nil_append] at p1o
  have v1 : ∀ k : Fin 14, k ≠ 2 → k ≠ 3 → k ≠ 4 → k ≠ 5 → k ≠ 6 → τ1.val (R k) = σ.val (R k) := by
    intro k h2 h3 h4 h5 h6; exact p1s.val (by simp [hRe, h2, h3, h4, h5, h6])
  -- 2. rewind the input
  obtain ⟨τ2, e2, p2h, p2C, p2st, p2s⟩ := rewindBy_runs (cap := cap) IN (R := R 11) (C := R 10) (T := R 7)
    (by simp [hRe]) (by simp [hRe]) (by simp [hRe]) τ1
    (by rw [v1 10 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hz 10 (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [v1 7 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hz 7 (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [v1 11 (by decide) (by decide) (by decide) (by decide) (by decide), hσ.bnd]; omega)
    (by rw [v1 11 (by decide) (by decide) (by decide) (by decide) (by decide), hσ.bnd, p1o.2]; omega)
  rw [v1 11 (by decide) (by decide) (by decide) (by decide) (by decide), hσ.bnd] at e2
  -- streams other than IN are untouched so far
  have st2 : ∀ Y, Y ≠ IN → τ2.st Y = σ.st Y ∧ τ2.sh Y = σ.sh Y := fun Y hY =>
    ⟨by rw [p2s.st (by simp [hY]), p1s.st (by simp [hY])], by rw [p2s.sh (by simp [hY]), p1s.sh (by simp [hY])]⟩
  -- 3. the call
  have hin : ∀ j, RdEq (τ2.st (tmap j)) (wf.program.inputTapes (messageWord (unitReq n i hn)) j) := by
    intro j
    rw [program_inputTapes]
    by_cases hj : j = encIn E wf
    · subst hj; rw [p2st]; simpa [encIn] using p1o.1
    · have hj0 : j.val ≠ 0 := fun h => hj (Fin.ext (by simpa [encIn] using h))
      rw [if_neg hj0, (st2 _ (fun e => hj (hinj e))).1]; exact (hσ.enc j).1
  have h0 : ∀ j, τ2.sh (tmap j) = 0 := by
    intro j
    by_cases hj : j = encIn E wf
    · subst hj; exact p2h
    · rw [(st2 _ (fun e => hj (hinj e))).2]; exact (hσ.enc j).2
  have hLG2 : τ2.st LG = List.replicate B false := by
    rw [(st2 LG (fun e => hL _ e.symm)).1, hσ.frame.st (by simp [hML.symm]; exact fun j => (hL j).symm |> fun h e => h e.symm), hLG]
  set req := unitReq n i hn with hreq
  obtain ⟨τ3, tout, e3, d3, p3o, p3far⟩ := wordFunction_machZ_far (cap := cap) wf req tmap hinj LG hL τ2 h0 hin B
    hLG2 (by rw [(st2 LG (fun e => hL _ e.symm)).2, hσ.frame.sh (by simp [hML.symm]; exact fun j => (hL j).symm |> fun h e => h e.symm), hLGh]) (by omega)
  -- 4. clear LL
  have v3 : ∀ k : Fin 14, k ≠ 2 → k ≠ 3 → k ≠ 4 → k ≠ 5 → k ≠ 6 → k ≠ 10 → τ3.val (R k) = σ.val (R k) := by
    intro k h2 h3 h4 h5 h6 h10
    rw [d3.val, p2s.val (by simp [hRe, h10]), v1 k h2 h3 h4 h5 h6]
  have hLL3 : τ3.val (R 9) ≤ E.length n := by
    rw [v3 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hσ.len]; split_ifs <;> omega
  have e4 := wclear_spec cap (R 9) (τ3.val (R 9)) τ3 rfl (by omega)
  set τ4 := τ3.setv (R 9) 0 with hτ4
  -- 5. store the column
  have v4 : ∀ k : Fin 14, k ≠ 2 → k ≠ 3 → k ≠ 4 → k ≠ 5 → k ≠ 6 → k ≠ 9 → k ≠ 10 → τ4.val (R k) = σ.val (R k) := by
    intro k h2 h3 h4 h5 h6 h9 h10
    rw [hτ4, WState.setv_val, Function.update_of_ne (fun e => h9 (R.injective e)), v3 k h2 h3 h4 h5 h6 h10]
  have hMAT3 : τ3.st MAT = σ.st MAT ∧ τ3.sh MAT = σ.sh MAT := by
    rw [(d3.other MAT hM).1, (d3.other MAT hM).2]; exact st2 MAT (hM _).symm
  have hzσ : ∀ k : Fin 14, k ≠ 0 → k ≠ 1 → k ≠ 9 → k ≠ 11 → k ≠ 13 → σ.val (R k) = 0 := hσ.zero
  obtain ⟨τ5, e5, p5M, p5Mh, p5Oh, p5Ost, p5P, p5LL, p5C, p5T, p5s⟩ := rdCol_runs (cap := cap) E hOM
    (Q := R 0) (I := R 1) (P := R 8) (LL := R 9) (C := R 10) (T := R 7) (BR := R 11) (by simp [hRe]) n i B hi τ4
    (by simp only [hτ4, WState.setv_st]; exact p3o) (by simp [hτ4]; exact d3.sh _)
    (by intro p; simp only [hτ4, WState.setv_st]; rw [hMAT3.1]; exact hσ.mat p)
    (by simp only [hτ4, WState.setv_sh]; rw [hMAT3.2]; exact hσ.math)
    (by rw [v4 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hσ.q)
    (by rw [v4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hσ.col)
    (by rw [v4 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hzσ 8 (by decide) (by decide) (by decide) (by decide) (by decide))
    (by simp [hτ4])
    (by rw [hτ4, WState.setv_val, Function.update_of_ne (fun e => absurd (R.injective e) (by decide)), d3.val, p2C])
    (by rw [v4 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hzσ 7 (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [v4 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hσ.bnd)
    hBL (by omega)
  -- 6. clear the encoder's streams
  have hTTσ : σ.st TT = List.replicate B true ∧ σ.sh TT = 0 := by
    have hx : TT ∉ List.ofFn tmap ++ [MAT] := by
      simp [List.mem_ofFn, Ne.symm hMT]; exact fun j => hT j
    rw [hσ.frame.st hx, hσ.frame.sh hx]; exact ⟨hTT, hTTh⟩
  have hTT5 : τ5.st TT = σ.st TT ∧ τ5.sh TT = σ.sh TT := by
    have h1 : TT ∉ [OE, MAT] := by simp [Ne.symm hMT]; exact (hT _).symm
    rw [p5s.st h1, p5s.sh h1]
    simp only [hτ4, WState.setv_st, WState.setv_sh]
    rw [(d3.other TT hT).1, (d3.other TT hT).2]; exact st2 TT (hT _).symm
  have hsh5 : ∀ j, τ5.sh (tmap j) = 0 := by
    intro j
    by_cases hj : tmap j = OE
    · rw [hj]; exact p5Oh
    · rw [p5s.sh (by simp [hj]; exact hM j)]; simp only [hτ4, WState.setv_sh]; exact d3.sh j
  obtain ⟨τ6, e6, p6c, p6o, p6sh, p6val, p6cell⟩ := clearAll_runs (cap := cap) TT (R 12) B (by omega)
    (List.ofFn tmap) τ5 (List.nodup_ofFn.2 hinj) (by simp [List.mem_ofFn]; exact hT)
    (by rw [hTT5.1, hTTσ.1]) (by rw [hTT5.2, hTTσ.2])
    (by rw [p5s.val (by simp [hRe])]
        rw [v4 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hzσ 12 (by decide) (by decide) (by decide) (by decide) (by decide))
    (by intro X hX; obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hX; exact hsh5 j)
  -- 7. next column
  have hR1 : τ6.val (R 1) = i := by
    rw [p6val, p5s.val (by simp [hRe])]
    rw [v4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hσ.col
  have e7 := WXExec.inc (cap := cap) (R 1) τ6 (by rw [hR1]; omega)
  rw [hR1] at e7
  -- the new column state
  have st5 : ∀ j, τ5.st (tmap j) = τ3.st (tmap j) := by
    intro j
    by_cases hj : tmap j = OE
    · rw [hj, p5Ost]; simp [hτ4]
    · rw [p5s.st (by simp [hj]; exact hM j)]; simp [hτ4]
  have v5 : ∀ k : Fin 14, k ≠ 7 → k ≠ 8 → k ≠ 9 → k ≠ 10 → τ5.val (R k) = τ4.val (R k) := by
    intro k h7 h8 h9 h10; exact p5s.val (by simp [hRe, h7, h8, h9, h10])
  have hz1 : ∀ k : Fin 14, k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 → τ1.val (R k) = 0 := by
    rintro k (rfl | rfl | rfl | rfl | rfl)
    exacts [p1N1, p1H, p1RB, p1A, p1BC]
  refine ⟨_, WXExec.mono (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq (WXExec.wm e4)
    (WXExec.seq e5 (WXExec.seq e6 e7)))))) ?_, ?_, ?_⟩
  · simp only [colCost, List.length_ofFn]
    have hbud : bud req ≤ B := by omega
    nlinarith
  refine ⟨fun j => ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [WState.setv_st]
    rw [p6c _ (List.mem_ofFn.2 ⟨j, rfl⟩), st5 j]
    apply clearPrefix_blank
    intro q hq
    apply p3far j q
    have hlen : (wf.program.inputTapes (messageWord req) j).length ≤ (frame (messageWord req)).length := by
      rw [program_inputTapes]; split_ifs <;> simp
    omega
  · simp only [WState.setv_sh]; rw [p6sh]; exact hsh5 j
  · intro p
    simp only [WState.setv_st]
    rw [p6o MAT (by simp [List.mem_ofFn]; exact hM)]; exact p5M p
  · simp only [WState.setv_sh]; rw [p6sh]; exact p5Mh
  · simp only [WState.setv_val]
    rw [Function.update_of_ne (fun e => absurd (R.injective e) (by decide)), p6val,
      v5 0 (by decide) (by decide) (by decide) (by decide),
      v4 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hσ.q
  · simp
  · simp only [WState.setv_val]
    rw [Function.update_of_ne (fun e => absurd (R.injective e) (by decide)), p6val, p5LL]; simp
  · simp only [WState.setv_val]
    rw [Function.update_of_ne (fun e => absurd (R.injective e) (by decide)), p6val,
      v5 11 (by decide) (by decide) (by decide) (by decide),
      v4 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hσ.bnd
  · intro k h0 h1 h9 h11 h13
    simp only [WState.setv_val]
    rw [Function.update_of_ne (fun e => h1 (R.injective e)), p6val]
    fin_cases k
    all_goals first
      | exact absurd rfl h0 | exact absurd rfl h1 | exact absurd rfl h9 | exact absurd rfl h11 | exact absurd rfl h13
      | exact p5P | exact p5C | exact p5T
      | (rw [v5 _ (by decide) (by decide) (by decide) (by decide), hτ4, WState.setv_val,
            Function.update_of_ne (fun e => absurd (R.injective e) (by decide)), d3.val,
            p2s.val (by simp [hRe])]
         exact hz1 _ (by decide))
      | (rw [v5 _ (by decide) (by decide) (by decide) (by decide),
            v4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
         exact hzσ _ (by decide) (by decide) (by decide) (by decide) (by decide))
  · have hIN : IN ∈ List.ofFn tmap ++ [MAT] := List.mem_append_left _ (List.mem_ofFn.2 ⟨_, rfl⟩)
    have hOE' : OE ∈ List.ofFn tmap ++ [MAT] := List.mem_append_left _ (List.mem_ofFn.2 ⟨_, rfl⟩)
    have hMm : MAT ∈ List.ofFn tmap ++ [MAT] := List.mem_append_right _ (List.mem_singleton_self _)
    have sRm : ∀ (l : List (Fin 14)) r, r ∈ l.map R → r ∈ List.ofFn R := by
      intro l r hr; obtain ⟨k, -, rfl⟩ := List.mem_map.1 hr; exact List.mem_ofFn.2 ⟨k, rfl⟩
    have hsIN : ∀ x ∈ [IN], x ∈ List.ofFn tmap ++ [MAT] := fun x hx => by rw [List.mem_singleton.1 hx]; exact hIN
    have hsOM : ∀ x ∈ [OE, MAT], x ∈ List.ofFn tmap ++ [MAT] := fun x hx => by
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hOE'
      · rw [List.mem_singleton.1 hx]; exact hMm
    have hsT : ∀ x ∈ List.ofFn tmap, x ∈ List.ofFn tmap ++ [MAT] := fun x hx => List.mem_append_left _ hx
    have hnil : ∀ r ∈ ([] : List (Fin nr)), r ∈ List.ofFn R := fun r hr => absurd hr List.not_mem_nil
    have s3 : SameExcept τ2 τ3 (List.ofFn tmap) [] :=
      ⟨fun x hx => d3.other x (fun j e => hx (List.mem_ofFn.2 ⟨j, e⟩)), fun r _ => by rw [d3.val], d3.cell⟩
    have s6 : SameExcept τ5 τ6 (List.ofFn tmap) [] :=
      ⟨fun x hx => ⟨p6o x hx, by rw [p6sh]⟩, fun r _ => by rw [p6val], p6cell⟩
    exact (((((((hσ.frame.trans (p1s.weaken hsIN (sRm [2, 3, 4, 5, 6]))).trans
      (p2s.weaken hsIN (sRm [10]))).trans (s3.weaken hsT hnil)).trans
      (sameExcept_setv _ (sRm [9] _ (List.mem_singleton_self _)) _)).trans
      (p5s.weaken hsOM (sRm [8, 9, 10, 7]))).trans (s6.weaken hsT hnil)).trans
      (sameExcept_setv _ (sRm [1] _ (List.mem_singleton_self _)) _))
  · simp only [WState.setv_val]
    rw [Function.update_of_ne (fun e => absurd (R.injective e) (by decide)), p6val,
      v5 13 (by decide) (by decide) (by decide) (by decide),
      v4 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]

/-- Setting the loop counter `R 13` keeps a column state. -/
theorem ColAt.setv13 {tmap : Fin wf.program.tapeCount → Fin (ns + 1)} {MAT TT LG : Fin (ns + 1)} {R : Fin 14 ↪ Fin nr}
    {σ0 σ : WState ns nr} {n B i : ℕ} (h : ColAt E wf tmap MAT TT LG R σ0 n B i σ) (v : ℕ) :
    ColAt E wf tmap MAT TT LG R σ0 n B i (σ.setv (R 13) v) := by
  have hne : ∀ k : Fin 14, k ≠ 13 → R k ≠ R 13 := fun k hk e => hk (R.injective e)
  refine ⟨h.enc, h.mat, h.math, ?_, ?_, ?_, ?_, ?_, h.frame.trans (sameExcept_setv _ (List.mem_ofFn.2 ⟨13, rfl⟩) _)⟩
  · simp only [WState.setv_val]; rw [Function.update_of_ne (hne 0 (by decide))]; exact h.q
  · simp only [WState.setv_val]; rw [Function.update_of_ne (hne 1 (by decide))]; exact h.col
  · simp only [WState.setv_val]; rw [Function.update_of_ne (hne 9 (by decide))]; exact h.len
  · simp only [WState.setv_val]; rw [Function.update_of_ne (hne 11 (by decide))]; exact h.bnd
  · intro k h0 h1 h9 h11 h13
    simp only [WState.setv_val]; rw [Function.update_of_ne (hne k h13)]; exact h.zero k h0 h1 h9 h11 h13

/-- All columns: `R 13` counts the calls. -/
noncomputable def encCols (tmap : Fin wf.program.tapeCount → Fin (ns + 1)) (MAT TT LG : Fin (ns + 1))
    (R : Fin 14 ↪ Fin nr) : WMX ns nr :=
  .seq (addR (R 0) (R 13) (R 7)) (.whr (R 13) (.seq (WMX.dec (R 13)) (colBody E wf tmap MAT TT LG R)))

/-- The cost bound of `encCols`. -/
def encColsCost (n L B t : ℕ) : ℕ := n * (colCost n L B t + 4) + 18 * n + 5

theorem encCols_runs (tmap : Fin wf.program.tapeCount → Fin (ns + 1)) (hinj : Function.Injective tmap)
    {MAT TT LG : Fin (ns + 1)} (hM : ∀ j, tmap j ≠ MAT) (hT : ∀ j, tmap j ≠ TT) (hL : ∀ j, tmap j ≠ LG)
    (hMT : MAT ≠ TT) (hML : MAT ≠ LG) (R : Fin 14 ↪ Fin nr) (B n : ℕ) (hn : 2 ≤ n)
    (hB : ∀ i, i < n → (frame (messageWord (unitReq n i hn))).length + bud (unitReq n i hn) + 1 ≤ B)
    (hBL : 2 * E.length n ≤ B) (hcap : (E.length n + 1) * n + B + 2 * n ≤ cap) (σ : WState ns nr)
    (hTT : σ.st TT = List.replicate B true) (hTTh : σ.sh TT = 0)
    (hLG : σ.st LG = List.replicate B false) (hLGh : σ.sh LG = 0)
    (henc : ∀ j, RdEq (σ.st (tmap j)) [] ∧ σ.sh (tmap j) = 0)
    (hmat : ∀ p, readTapeBit (σ.st MAT) p = false) (hmath : σ.sh MAT = 0)
    (hq : σ.val (R 0) = n) (hbnd : σ.val (R 11) = B) (hzero : ∀ k : Fin 14, k ≠ 0 → k ≠ 11 → σ.val (R k) = 0) :
    Runs cap (encCols E wf tmap MAT TT LG R) σ (encColsCost n (E.length n) B wf.program.tapeCount)
      (fun τ => (∀ p, readTapeBit (τ.st MAT) p = matBit E n p) ∧ τ.sh MAT = 0 ∧ τ.val (R 9) = E.length n ∧
        τ.val (R 0) = n ∧ τ.val (R 11) = B ∧ (∀ j, RdEq (τ.st (tmap j)) [] ∧ τ.sh (tmap j) = 0) ∧
        SameExcept σ τ (List.ofFn tmap ++ [MAT]) (List.ofFn R)) := by
  have hne : ∀ a b : Fin 14, a ≠ b → R a ≠ R b := fun a b h e => h (R.injective e)
  have e1 := addR_spec cap (hne 0 13 (by decide)) (hne 0 7 (by decide)) (hne 13 7 (by decide)) σ
    (hzero 7 (by decide) (by decide)) (by rw [hzero 13 (by decide) (by decide), hq]; omega)
  rw [hzero 13 (by decide) (by decide), hq, Nat.zero_add] at e1
  have c0 : ColAt E wf tmap MAT TT LG R σ n B 0 (σ.setv (R 13) n) := by
    refine ColAt.setv13 E wf ⟨henc, fun p => by rw [hmat, matPart_zero], hmath, hq,
      hzero 1 (by decide) (by decide), by rw [hzero 9 (by decide) (by decide)]; simp, hbnd,
      fun k h0 _ _ h11 _ => hzero k h0 h11, SameExcept.refl _ _ _⟩ n
  have hloop := Runs.count (cap := cap) (K := R 13) (body := colBody E wf tmap MAT TT LG R)
    (colCost n (E.length n) B wf.program.tapeCount) n (fun k τ => ColAt E wf tmap MAT TT LG R σ n B k τ) (by omega)
    (fun k hk τ hτ _ => (colBody_runs E wf tmap hinj hM hT hL hMT hML R σ B hTT hTTh hLG hLGh n k hn hk (hB k hk)
      hBL hcap _ (hτ.setv13 E wf _)).post (fun ρ hρ => ⟨hρ.1, by rw [hρ.2]; simp⟩))
    (σ.setv (R 13) n) c0 (by simp)
  obtain ⟨τ, e2, hτ, hK⟩ := hloop
  refine ⟨τ, WXExec.mono (WXExec.seq e1 e2) (by simp only [encColsCost]; omega), fun p => ?_, hτ.math, ?_, hτ.q,
    hτ.bnd, hτ.enc, ?_⟩
  · rw [hτ.mat p, matPart_full E n p (by omega)]
  · rw [hτ.len]; simp; omega
  · exact hτ.frame

end Cols

end NearCubicGates.Close.CheckedPCPP
