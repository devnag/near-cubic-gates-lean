import Proof.Gates.Succinct.Points

/-!
# 𝒱_G, part 6: the table loop

Paper: lem:succinct-verifier (app:multitape), stage (3): "For `i = 0, 1, …, N−1` … it evaluates `B` at
`bin_ν(i)0^{a−ν}` … and writes the value into cell `i` of a work tape, which then holds `tt_N(B)`." `pointsW`: for
`i < N` (`N` in `NN`), evaluate the description `d` at the point `pList i` (the evaluator `evalW`), append the value
to the table stream `TT` (framed), advance the point. **`pointsW_spec`**: `TT = frame (ttWord d lb lp N)`, head `0`,
on every description stream.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Succinct

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat NearCubicWires.RepairOrdinary.Streaming
open NearCubicGates.Close.WordPrograms

variable {ns nr : ℕ}

/-- The table computed by the loop (paper lem:succinct-verifier, stage (3)). -/
def ttWord (d : List Bool) (lb lp N : ℕ) : List Bool :=
  List.ofFn fun i : Fin N => evalModel d lb lp (fun j => (i : ℕ).testBit j)

theorem frame_eq_marks' (x : List Bool) : RepairOrdinary.frame x = marks x ++ [false] := by
  induction x with
  | nil => rfl
  | cons b x ih => simp [RepairOrdinary.frame, marks, ih]

theorem ttWord_succ (d : List Bool) (lb lp k : ℕ) :
    ttWord d lb lp (k + 1) = ttWord d lb lp k ++ [evalModel d lb lp (fun j => k.testBit j)] := by
  unfold ttWord; rw [List.ofFn_succ_last]; simp

/-- The evaluator's registers inside the verifier's. -/
def eE (E : VReg → Fin nr) : EReg → Fin nr := fun r => E (.e r)

theorem eE_inj (E : VReg → Fin nr) (hE : Function.Injective E) : Function.Injective (eE E) := by
  intro u₁ u₂ h; have := hE h; injection this

/-- One point: evaluate, append `[true, value]` to `TT`, clear the value, next point. -/
def pointBody (D P VV TT : Fin (ns + 1)) (E : VReg → Fin nr) : WM ns nr :=
  .seq (evalW D P VV (eE E)) (.seq (emitC TT (E .top) true) (.seq (.ifr (E (.e .rv)) (emitC TT (E .top) true)
    (emitC TT (E .top) false)) (.seq (WM.clear (E (.e .rv))) (incP P (E .c)))))

/-- **The table loop** (paper lem:succinct-verifier, stage (3)). -/
def pointsW (D P VV TT : Fin (ns + 1)) (E : VReg → Fin nr) : WM ns nr :=
  .seq (addTo (E .nN) (E .i) (E .t)) (.seq (.whr (E .i) (.seq (.dec (E .i)) (pointBody D P VV TT E)))
    (.seq (emitC TT (E .top) false) (WM.rewind TT (E .top))))

/-- The evaluator's entry conditions, read on the verifier's register file. -/
structure EvalReady (D P VV : Fin (ns + 1)) (E : VReg → Fin nr) (d : List Bool) (lb lp : ℕ) (σ : WState ns nr) :
    Prop where
  st : σ.st D = d
  sh : σ.sh D = 0
  vv : ∃ m, σ.st VV = List.replicate m false
  vvh : σ.sh VV = 0
  ph : σ.sh P = 0
  lb : σ.val (E (.e .lb)) = lb
  lp : σ.val (E (.e .lp)) = lp
  z : ∀ r ∈ scratchE, σ.val (E (.e r)) = 0
  s : σ.val (E (.e .s)) = 0
  j : σ.val (E (.e .j)) = 0
  cd : σ.val (E (.e (.f .cd))) = 0

/-- The per-point cost class. -/
def pointCost (dl lb lp N : ℕ) : ℕ := evalCost dl lb lp + 14 * N + 40

theorem ttWord_length (d : List Bool) (lb lp N : ℕ) : (ttWord d lb lp N).length = N := by simp [ttWord]

set_option hygiene false in
/-- Stream and register disequalities of the table loop. -/
local macro "sfs" : tactic => `(tactic| simp [Function.update_apply, hE.eq_iff, eE, hDP, hDV, hDT, hPV, hPT, hVT,
  Ne.symm hDP, Ne.symm hDV, Ne.symm hDT, Ne.symm hPV, Ne.symm hPT, Ne.symm hVT])

theorem pointsW_spec (cap : ℕ) (D P VV TT : Fin (ns + 1)) (hR : [D, P, VV, TT].Nodup) (E : VReg → Fin nr)
    (hE : Function.Injective E) (σ : WState ns nr) (d : List Bool) (lb lp N : ℕ) (hrd : EvalReady D P VV E d lb lp σ)
    (hP : σ.st P = []) (hTT : σ.st TT = []) (hTTh : σ.sh TT = 0) (hN : σ.val (E .nN) = N)
    (hz : ∀ r ∈ [VReg.i, .t, .top, .c], σ.val (E r) = 0)
    (hcap : 10 * d.length + 8 * (lb + lp) + 16 * 2 ^ (lb + lp + 1) + 4 * N + 200 ≤ cap) :
    ∃ τ, WExec cap (pointsW D P VV TT E) σ τ ((N + 1) * (pointCost d.length lb lp N + 10) + 30 * N + 20) ∧
      τ.st TT = RepairOrdinary.frame (ttWord d lb lp N) ∧ τ.sh TT = 0 ∧ SameExcept σ τ [P, VV, TT] [] ∧
      τ.sh P = 0 ∧ τ.sh VV = 0 := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    not_false_eq_true] at hR
  obtain ⟨⟨hDP, hDV, hDT⟩, ⟨hPV, hPT⟩, hVT⟩ := hR
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  have zi := hz .i (by simp); have zt := hz .t (by simp); have ztop := hz .top (by simp); have zc := hz .c (by simp)
  have zrv : σ.val (E (.e .rv)) = 0 := hrd.z .rv (by simp [scratchE])
  -- `I := N`
  have e1 := addTo_spec cap (E .nN) (E .i) (E .t) (hE.ne (by decide)) (hE.ne (by decide)) (hE.ne (by decide)) σ zt
    (by omega) (by omega)
  rw [zi, hN, Nat.zero_add] at e1
  set σ1 := σ.setv (E .i) N with hσ1
  -- the loop
  let Inv : ℕ → WState ns nr → Prop := fun k τ =>
    τ.st TT = marks (ttWord d lb lp k) ∧ τ.sh TT = 2 * k ∧ τ.val (E .top) = 2 * k ∧ τ.st P = pList k ∧
      EvalReady D P VV E d lb lp τ ∧ τ.val (E (.e .rv)) = 0 ∧ τ.val (E .c) = 0 ∧
      SameExcept σ1 τ [P, VV, TT] [E .top, E .i]
  have hInv0 : Inv 0 σ1 := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hrd
    refine ⟨by simp [σ1, hTT, ttWord, marks], by simp [σ1, hTTh], by simp [σ1, Function.update_apply, hE.eq_iff, ztop],
      by simp [σ1, hP, pList], ⟨by simpa [σ1] using h1, by simpa [σ1] using h2, by simpa [σ1] using h3,
        by simpa [σ1] using h4, by simpa [σ1] using h5, by simp [σ1, Function.update_apply, hE.eq_iff, h6],
        by simp [σ1, Function.update_apply, hE.eq_iff, h7],
        fun r hr => by simp [σ1, Function.update_apply, hE.eq_iff]; exact h8 r hr,
        by simp [σ1, Function.update_apply, hE.eq_iff, h9], by simp [σ1, Function.update_apply, hE.eq_iff, h10],
        by simp [σ1, Function.update_apply, hE.eq_iff, h11]⟩,
      by simp [σ1, Function.update_apply, hE.eq_iff, zrv], by simp [σ1, Function.update_apply, hE.eq_iff, zc],
      SameExcept.refl _ _ _⟩
  have hstep : ∀ k < N, ∀ τ, Inv k τ → τ.val (E .i) = N - k →
      ∃ τ', WExec cap (pointBody D P VV TT E) (τ.setv (E .i) (N - k - 1)) τ' (pointCost d.length lb lp N) ∧
        Inv (k + 1) τ' ∧ τ'.val (E .i) = N - k - 1 := by
    intro k hk τ hI _
    obtain ⟨hT, hTh, htop, hPk, hrd', hrv, hc, hse⟩ := hI
    set τ0 := τ.setv (E .i) (N - k - 1) with hτ0
    -- evaluate
    obtain ⟨m, hm⟩ := hrd'.vv
    obtain ⟨τ1, e1, h1rv, ⟨m', h1V⟩, h1Vh, hse1⟩ := evalW_spec cap D P VV hDP hDV hPV (eE E) (eE_inj E hE) τ0 m d
      lb lp (by simpa [τ0] using hrd'.st) (by simpa [τ0] using hrd'.sh) (by simpa [τ0] using hm)
      (by simpa [τ0] using hrd'.vvh) (by simpa [τ0] using hrd'.ph)
      (by simp [τ0, eE, Function.update_apply, hE.eq_iff, hrd'.lb]) (by simp [τ0, eE, Function.update_apply, hE.eq_iff, hrd'.lp])
      (fun r hr => by simp [τ0, eE, Function.update_apply, hE.eq_iff]; exact hrd'.z r hr)
      (by simp [τ0, eE, Function.update_apply, hE.eq_iff, hrd'.s]) (by simp [τ0, eE, Function.update_apply, hE.eq_iff, hrd'.j])
      (by simp [τ0, eE, Function.update_apply, hE.eq_iff, hrd'.cd]) (by omega)
    have hpt : readTapeBit (τ0.st P) = fun j => k.testBit j := by
      funext j; simp [τ0, hPk, read_pList]
    rw [hpt] at h1rv
    set b := evalModel d lb lp (fun j => k.testBit j) with hb
    have h1rv' : τ1.val (E (.e .rv)) = b.toNat := h1rv
    have n1 : ∀ r : VReg, r ≠ .e .rv → τ1.val (E r) = τ.val (E r) ∨ r = .i := by
      intro r hr
      rw [hse1.val (r := E r) (by simp [eE, hE.eq_iff, hr])]
      by_cases hri : r = .i
      · right; exact hri
      · left; simp [τ0, Function.update_apply, hE.eq_iff, hri]
    have n1' : ∀ r : VReg, r ≠ .e .rv → r ≠ .i → τ1.val (E r) = τ.val (E r) := fun r h1 h2 =>
      (n1 r h1).resolve_right h2
    have s1 : ∀ x, x ≠ VV → τ1.st x = τ.st x ∧ τ1.sh x = τ.sh x := fun x hx =>
      ⟨by rw [hse1.st (by simp [hx])]; simp [τ0], by rw [hse1.sh (by simp [hx])]; simp [τ0]⟩
    -- emit `[true, b]`
    have hlenT : τ1.sh TT = (τ1.st TT).length := by
      rw [(s1 TT (Ne.symm hVT)).1, (s1 TT (Ne.symm hVT)).2, hT, hTh]; simp [ttWord_length]
    have htop1 : τ1.val (E .top) = 2 * k := by rw [n1' _ (by decide) (by decide), htop]
    have e2 := emitC_spec cap TT (E .top) true τ1 hlenT (by rw [htop1]; omega)
    set τ2 := ((τ1.sets TT (τ1.st TT ++ [true])).seth TT (τ1.sh TT + 1)).setv (E .top) (τ1.val (E .top) + 1) with hτ2
    have h2rv : τ2.val (E (.e .rv)) = b.toNat := by simp [τ2, Function.update_apply, hE.eq_iff, h1rv']
    have hlenT2 : τ2.sh TT = (τ2.st TT).length := by simp [τ2, hlenT]
    have htop2 : τ2.val (E .top) = 2 * k + 1 := by simp [τ2, htop1]
    have e3 : WExec cap (.ifr (E (.e .rv)) (emitC TT (E .top) true) (emitC TT (E .top) false)) τ2
        (((τ2.sets TT (τ2.st TT ++ [b])).seth TT (τ2.sh TT + 1)).setv (E .top) (τ2.val (E .top) + 1)) 8 := by
      have hc2 : τ2.val (E .top) < cap := by rw [htop2]; omega
      cases hbv : b
      · exact WExec.mono (WExec.ifrF (by rw [h2rv, hbv]; rfl) (emitC_spec cap TT (E .top) false τ2 hlenT2 hc2))
          (by omega)
      · exact WExec.mono (WExec.ifrT (by rw [h2rv, hbv]; simp) (emitC_spec cap TT (E .top) true τ2 hlenT2 hc2))
          (by omega)
    set τ3 := ((τ2.sets TT (τ2.st TT ++ [b])).seth TT (τ2.sh TT + 1)).setv (E .top) (τ2.val (E .top) + 1) with hτ3
    have e4 := wclear_spec cap (E (.e .rv)) b.toNat τ3 (by simp [τ3, Function.update_apply, hE.eq_iff, h2rv])
      (by simp [τ3, Function.update_apply, hE.eq_iff, h2rv]; have := Bool.toNat_le b; omega)
    set τ4 := τ3.setv (E (.e .rv)) 0 with hτ4
    -- facts about `τ4`
    have s4 : ∀ x, x ≠ TT → τ4.st x = τ1.st x ∧ τ4.sh x = τ1.sh x := by
      intro x hx; simp [τ4, τ3, τ2, Function.update_apply, hx]
    have v4 : ∀ r : VReg, r ≠ .e .rv → r ≠ .top → τ4.val (E r) = τ1.val (E r) := by
      intro r h1 h2; simp [τ4, τ3, τ2, Function.update_apply, hE.eq_iff, h1, h2]
    have h4P : τ4.st P = pList k := by rw [(s4 P hPT).1, (s1 P hPV).1, hPk]
    have h4Ph : τ4.sh P = 0 := by rw [(s4 P hPT).2, (s1 P hPV).2, hrd'.ph]
    have h4c : τ4.val (E .c) = 0 := by rw [v4 _ (by decide) (by decide), n1' _ (by decide) (by decide), hc]
    have hlenP := pList_length_le k
    have e5 := incP_spec cap P (E .c) τ4 (pList k) h4P h4Ph h4c (by omega)
    have h4T : τ4.st TT = marks (ttWord d lb lp (k + 1)) := by
      simp [τ4, τ3, τ2, Function.update_apply]
      rw [(s1 TT (Ne.symm hVT)).1, hT, ttWord_succ, marks_append]; simp [marks, hb]
    have h4Th : τ4.sh TT = 2 * (k + 1) := by
      simp [τ4, τ3, τ2, Function.update_apply]; rw [(s1 TT (Ne.symm hVT)).2, hTh]; ring
    have h4top : τ4.val (E .top) = 2 * (k + 1) := by simp [τ4, τ3, htop2, Function.update_apply, hE.eq_iff]; ring
    refine ⟨τ4.sets P (incList (pList k)), WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5))))
      ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · unfold pointCost; have := Bool.toNat_le b; omega
    · simp [Function.update_apply, Ne.symm hPT, h4T]
    · simp [h4Th]
    · simp [h4top]
    · simp [pList]
    · refine ⟨?_, ?_, ⟨m', ?_⟩, ?_, by simp [h4Ph], ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [Function.update_apply, hDP]; rw [(s4 D hDT).1, (s1 D hDV).1]; exact hrd'.st
      · simp; rw [(s4 D hDT).2, (s1 D hDV).2]; exact hrd'.sh
      · simp [Function.update_apply, Ne.symm hPV]; rw [(s4 VV hVT).1]; exact h1V
      · simp; rw [(s4 VV hVT).2]; exact h1Vh
      · simp; rw [v4 _ (by decide) (by decide), n1' _ (by decide) (by decide), hrd'.lb]
      · simp; rw [v4 _ (by decide) (by decide), n1' _ (by decide) (by decide), hrd'.lp]
      · intro r hr
        by_cases hr2 : r = .rv
        · subst hr2; simp [τ4]
        · simp; rw [v4 _ (by simp [hr2]) (by intro h; cases h), n1' _ (by simp [hr2]) (by intro h; cases h)]
          exact hrd'.z r hr
      · simp; rw [v4 _ (by decide) (by decide), n1' _ (by decide) (by decide), hrd'.s]
      · simp; rw [v4 _ (by decide) (by decide), n1' _ (by decide) (by decide), hrd'.j]
      · simp; rw [v4 _ (by decide) (by decide), n1' _ (by decide) (by decide), hrd'.cd]
    · simp [τ4]
    · simp; exact h4c
    · refine ⟨fun x hx => ?_, fun r hr => ?_, ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
        simp [Function.update_apply, hx.1]
        rw [(s4 x hx.2.2).1, (s4 x hx.2.2).2, (s1 x hx.2.1).1, (s1 x hx.2.1).2]
        exact ⟨hse.st (by simp [hx.1, hx.2.1, hx.2.2]), hse.sh (by simp [hx.1, hx.2.1, hx.2.2])⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp only [WState.sets_val]
        by_cases hrv' : r = E (.e .rv)
        · subst hrv'; simp [τ4, σ1, Function.update_apply, hE.eq_iff, zrv]
        · simp only [τ4, WState.setv_val, Function.update_apply, if_neg hrv']
          simp only [τ3, τ2, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply, if_neg hr.1]
          rw [hse1.val (r := r) (by simp [eE, hrv'])]
          simp only [τ0, WState.setv_val, Function.update_apply, if_neg hr.2]
          exact hse.val (r := r) (by simp [hr.1, hr.2])
      · simp [τ4, τ3, τ2, hse1.cell, τ0, hse.cell]
    · simp; rw [v4 _ (by decide) (by decide)]; rw [hse1.val (r := E .i) (by simp [eE, hE.eq_iff])]; simp [τ0]
  obtain ⟨τ5, e5, hI5, h5i⟩ := UnionMachine.Round.wloopE cap (E .i) (pointBody D P VV TT E)
    (pointCost d.length lb lp N) N Inv (by omega) hstep σ1 hInv0 (by simp [σ1])
  obtain ⟨hT5, hTh5, htop5, hP5, hrd5, hrv5, hc5, hse5⟩ := hI5
  -- close the frame and rewind
  have e6 := emitC_spec cap TT (E .top) false τ5 (by rw [hT5, hTh5]; simp [ttWord_length]) (by rw [htop5]; omega)
  set τ6 := ((τ5.sets TT (τ5.st TT ++ [false])).seth TT (τ5.sh TT + 1)).setv (E .top) (τ5.val (E .top) + 1) with hτ6
  have e7 := wrewind_spec cap TT (E .top) (2 * N + 1) τ6 (by simp [τ6, htop5]) (by simp [τ6, htop5]; omega)
  refine ⟨_, WExec.mono (WExec.seq e1 (WExec.seq e5 (WExec.seq e6 e7))) ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : N * (pointCost d.length lb lp N + 4) + 1 ≤ (N + 1) * (pointCost d.length lb lp N + 10) := by
      have : N * (pointCost d.length lb lp N + 4) ≤ N * (pointCost d.length lb lp N + 10) :=
        Nat.mul_le_mul_left _ (by omega)
      have : (N + 1) * (pointCost d.length lb lp N + 10) =
          N * (pointCost d.length lb lp N + 10) + (pointCost d.length lb lp N + 10) := by ring
      omega
    omega
  · simp [τ6, hT5, RepairOrdinary.frame, frame_eq_marks']
  · simp [τ6, hTh5]
  · refine ⟨fun x hx => ?_, fun r hr => ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      simp [τ6, Function.update_apply, hx.2.2]
      refine ⟨?_, ?_⟩
      · rw [hse5.st (by simp [hx.1, hx.2.1, hx.2.2])]; simp [σ1]
      · rw [hse5.sh (by simp [hx.1, hx.2.1, hx.2.2])]; simp [σ1]
    · by_cases hrt : r = E .top
      · subst hrt; simp [τ6, ztop]
      · by_cases hri : r = E .i
        · subst hri; simp [τ6, Function.update_apply, hE.eq_iff, h5i, zi]
        · simp [τ6, Function.update_apply, hrt]
          rw [hse5.val (r := r) (by simp [hrt, hri])]; simp [σ1, Function.update_apply, hri]
    · simp [τ6, hse5.cell, σ1]
  · simp [τ6, Function.update_apply, hPT]; exact hrd5.ph
  · simp [τ6, Function.update_apply, hVT]; exact hrd5.vvh

end NearCubicGates.Close.Succinct
