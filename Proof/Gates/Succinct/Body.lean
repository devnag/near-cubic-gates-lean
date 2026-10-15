import Proof.Gates.Succinct.HTime

/-!
# 𝒱_G, part 8: the body of the succinct verifier

Paper: lem:succinct-verifier (app:multitape), stages (1)–(4), up to running `𝒟`. On `frame u` (stream 0) and
`frame y` (stream 1), the body:
(1) counts `n = |u|` and copies `u` to the description stream, computes `ν = rootOf G n`;
(2)–(3) sets the guards `lb = hc n`, `lp = hc ν`, computes `N = 2^ν` and the table `tt = ttWord u lb lp N` onto
stream 5 (framed) — on a description `⟨B⟩_ν` this is `tt_N(B)` (`Succinct.evalModel_descriptor`);
(4) computes `H.time N` and the witness prefix `frame (prefixBits y (H.time N))` onto stream 6.
Streams `5 … tH + 4` are the hierarchy verifier's tapes (table, witness, and its blank work tapes).
**`body_spec`** holds for EVERY `u` and `y`.
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

/-- The number of registers. -/
def nrV : ℕ := Fintype.card VReg

/-- The register file. -/
noncomputable def regE : VReg → Fin nrV := Fintype.equivFin VReg

theorem regE_inj : Function.Injective regE := (Fintype.equivFin VReg).injective

section Layout
variable (tH : ℕ)

/-- Stream `i` of the body (`tH + 5` streams). -/
def bs (i : ℕ) (h : i < tH + 5) : Fin (tH + 4 + 1) := ⟨i, h⟩

end Layout

/-- **The body** (paper lem:succinct-verifier, stages (1)–(4)). -/
noncomputable def body (G c k tH : ℕ) (htH : 2 ≤ tH) : WMX (tH + 4) nrV :=
  .seq (.wm (countW (bs tH 0 (by omega)) (bs tH 2 (by omega)) regE))
  (.seq (rootW G regE)
  (.seq (.wm (addTo (regE .nn) (regE .hcx) (regE .t)))
  (.seq (.wm (hcW (regE .hcx) (regE (.e .lb)) (regE .h)))
  (.seq (.wm (addTo (regE .nu) (regE .hcx) (regE .t)))
  (.seq (.wm (hcW (regE .hcx) (regE (.e .lp)) (regE .h)))
  (.seq (pow2W (regE .nN) (regE .nu) (regE .nu2) (regE .t))
  (.seq (.wm (pointsW (bs tH 2 (by omega)) (bs tH 3 (by omega)) (bs tH 4 (by omega)) (bs tH 5 (by omega)) regE))
  (.seq (htW c k regE)
  (.wm (wpW (bs tH 1 (by omega)) (bs tH 6 (by omega)) regE))))))))))

/-- The body's start: `frame u` on stream 0, `frame y` on stream 1, everything else empty or zero. -/
def bodyStart (tH : ℕ) (u y : List Bool) : WState (tH + 4) nrV :=
  ⟨fun _ => 0, fun i => if i.val = 0 then RepairOrdinary.frame u else if i.val = 1 then RepairOrdinary.frame y else [],
    fun _ => 0, false⟩

/-- The table the body computes (paper lem:succinct-verifier, stage (3)). -/
noncomputable def bodyTable (G : ℕ) (u : List Bool) : List Bool :=
  ttWord u (hc u.length) (hc (rootOf G u.length)) (2 ^ rootOf G u.length)

/-- The register capacity of one run. -/
noncomputable def bodyCap (G c k n : ℕ) : ℕ :=
  3 * (n + 2) ^ (G + 3) + 3 * (c + 1) * (2 ^ rootOf G n + 2) ^ (k + 3) +
    16 * 2 ^ (hc n + hc (rootOf G n) + 1) + 8 * (hc n + hc (rootOf G n)) + 20 * n + 4 * 2 ^ rootOf G n +
    2 * htVal c k (2 ^ rootOf G n) + 300

/-- The cost of one run. -/
noncomputable def bodyCost (G c k n : ℕ) : ℕ :=
  (45 * n + 5) + (n + 2) * (stepCost G n + 10) + 2 * (18 * n + 3 + 30 * n + 20 * n + 1) +
    (rootOf G n * (18 * 2 ^ rootOf G n + 11) + 7 * rootOf G n + 7) +
    ((2 ^ rootOf G n + 1) * (pointCost n (hc n) (hc (rootOf G n)) (2 ^ rootOf G n) + 10) + 30 * 2 ^ rootOf G n + 20) +
    (100 * (c + 1) * (k + 3) * (2 ^ rootOf G n + 2) ^ (k + 2) + 10) + (60 * htVal c k (2 ^ rootOf G n) + 30) + 20

theorem hc_le_two_pow (x : ℕ) : 2 ^ hc x ≤ 2 * x + 1 := two_pow_hc_le x

/-- **The body** (paper lem:succinct-verifier, stages (1)–(4)), on every input `u` and witness `y`. -/
theorem body_spec (G c k tH : ℕ) (htH : 2 ≤ tH) (u y : List Bool) :
    ∃ τ, WXExec (bodyCap G c k u.length) (body G c k tH htH) (bodyStart tH u y) τ (bodyCost G c k u.length) ∧
      τ.st (bs tH 5 (by omega)) = RepairOrdinary.frame (bodyTable G u) ∧ τ.sh (bs tH 5 (by omega)) = 0 ∧
      τ.st (bs tH 6 (by omega)) =
        RepairOrdinary.frame (prefixBits y (htVal c k (2 ^ rootOf G u.length))) ∧
      τ.sh (bs tH 6 (by omega)) = 0 ∧ ∀ x : Fin (tH + 4 + 1), 7 ≤ x.val → τ.st x = [] ∧ τ.sh x = 0 := by
  set n := u.length with hn
  have hνn : rootOf G n ≤ n := rootOf_le G n
  obtain ⟨ν, hν⟩ : ∃ ν, rootOf G n = ν := ⟨_, rfl⟩
  rw [hν] at hνn
  obtain ⟨N, hN⟩ : ∃ N, 2 ^ ν = N := ⟨_, rfl⟩
  have hcapE : bodyCap G c k n = 3 * (n + 2) ^ (G + 3) + 3 * (c + 1) * (N + 2) ^ (k + 3) +
      16 * 2 ^ (hc n + hc ν + 1) + 8 * (hc n + hc ν) + 20 * n + 4 * N + 2 * htVal c k N + 300 := by
    simp only [bodyCap, hν, hN]
  set cap := bodyCap G c k n with hcapd
  have hE := regE_inj
  have hcn : hc n ≤ n := hc_le n
  have hcν : hc ν ≤ ν := hc_le ν
  have hN1 : 1 ≤ N := hN ▸ Nat.one_le_two_pow
  have hNν : ν < N := hN ▸ Nat.lt_two_pow_self
  set S0 := bs tH 0 (by omega) with hS0
  set S1 := bs tH 1 (by omega) with hS1
  set S2 := bs tH 2 (by omega) with hS2
  set S3 := bs tH 3 (by omega) with hS3
  set S4 := bs tH 4 (by omega) with hS4
  set S5 := bs tH 5 (by omega) with hS5
  set S6 := bs tH 6 (by omega) with hS6
  have dS : ∀ (i j : ℕ) (hi : i < tH + 5) (hj : j < tH + 5), i ≠ j → bs tH i hi ≠ bs tH j hj := by
    intro i j hi hj h e; exact h (congrArg Fin.val e)
  set σ0 := bodyStart tH u y with hσ0
  have v0 : ∀ r, σ0.val r = 0 := fun _ => rfl
  have h0 : ∀ x, σ0.sh x = 0 := fun _ => rfl
  have st0 : ∀ x : Fin (tH + 4 + 1), 2 ≤ x.val → σ0.st x = [] := by
    intro x hx
    show (if x.val = 0 then _ else if x.val = 1 then _ else []) = []
    rw [if_neg (by omega), if_neg (by omega)]
  -- the cap
  have hpowN : (N + 2) ^ (k + 3) ≥ 1 := Nat.one_le_pow _ _ (by omega)
  have hcap1 : 2 * n + 1 ≤ cap := by rw [hcapE]; omega
  -- 1. count and copy
  have e1 := countW_spec cap S0 S2 (dS 0 2 _ _ (by omega)) regE hE σ0 u (by simp [σ0, bodyStart, S0, bs]) (h0 _)
    (st0 S2 (by simp [S2, bs])) (h0 _) (v0 _) (v0 _) (v0 _) hcap1
  set σ1 := (σ0.sets S2 u).setv (regE .nn) n with hσ1

  have hcapR : 3 * (n + 2) ^ (G + 3) + 2 * n + 10 ≤ cap := by rw [hcapE]; omega
  have e2 := rootW_spec cap G regE hE σ1 n (by simp [σ1]) (by simp [σ1, Function.update_apply, hE.eq_iff, v0])
    (fun q _ => by
      have : q ≠ .nn := by intro h; subst h; simp [stepScratch] at *
      simp [σ1, Function.update_apply, hE.eq_iff, this, v0]) hcapR
  rw [hν] at e2
  set σ2 := σ1.setv (regE .nu) ν with hσ2
  -- 3. `lb := hc n`, `lp := hc ν`
  have e3 := addTo_spec cap (regE .nn) (regE .hcx) (regE .t) (hE.ne (by decide)) (hE.ne (by decide))
    (hE.ne (by decide)) σ2 (by simp [σ2, σ1, Function.update_apply, hE.eq_iff, v0])
    (by simp [σ2, σ1, Function.update_apply, hE.eq_iff]; omega)
    (by simp [σ2, σ1, Function.update_apply, hE.eq_iff, v0]; omega)
  rw [show σ2.val (regE .hcx) + σ2.val (regE .nn) = n by simp [σ2, σ1, Function.update_apply, hE.eq_iff, v0]] at e3
  set σ3 := σ2.setv (regE .hcx) n with hσ3
  have hcapH : hc n + 0 < cap := by
    have : hc n < 2 ^ hc n := Nat.lt_two_pow_self
    have : 2 ^ hc n ≤ 2 ^ (hc n + hc ν + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    rw [hcapE]; omega
  have e4 := hcW_spec cap (regE .hcx) (regE (.e .lb)) (regE .h) (hE.ne (by decide)) (hE.ne (by decide))
    (hE.ne (by decide)) n σ3 (by simp [σ3]) (by simp [σ3, σ2, σ1, Function.update_apply, hE.eq_iff, v0])
    (by simp [σ3, σ2, σ1, Function.update_apply, hE.eq_iff, v0]; omega) (by omega)
  rw [show σ3.val (regE (.e .lb)) + hc n = hc n by simp [σ3, σ2, σ1, Function.update_apply, hE.eq_iff, v0]] at e4
  set σ4 := (σ3.setv (regE .hcx) 0).setv (regE (.e .lb)) (hc n) with hσ4
  have e5 := addTo_spec cap (regE .nu) (regE .hcx) (regE .t) (hE.ne (by decide)) (hE.ne (by decide))
    (hE.ne (by decide)) σ4 (by simp [σ4, σ3, σ2, σ1, Function.update_apply, hE.eq_iff, v0])
    (by simp [σ4, σ3, σ2, σ1, Function.update_apply, hE.eq_iff]; omega)
    (by simp [σ4, σ3, σ2, σ1, Function.update_apply, hE.eq_iff, v0]; omega)
  rw [show σ4.val (regE .hcx) + σ4.val (regE .nu) = ν by simp [σ4, σ3, σ2, σ1, Function.update_apply, hE.eq_iff, v0]]
    at e5
  set σ5 := σ4.setv (regE .hcx) ν with hσ5
  have hcapH' : hc ν + 0 < cap := by
    have : hc ν < 2 ^ hc ν := Nat.lt_two_pow_self
    have : 2 ^ hc ν ≤ 2 ^ (hc n + hc ν + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    rw [hcapE]; omega
  have e6 := hcW_spec cap (regE .hcx) (regE (.e .lp)) (regE .h) (hE.ne (by decide)) (hE.ne (by decide))
    (hE.ne (by decide)) ν σ5 (by simp [σ5]) (by simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply, hE.eq_iff, v0])
    (by simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply, hE.eq_iff, v0]; omega) (by omega)
  rw [show σ5.val (regE (.e .lp)) + hc ν = hc ν by
    simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply, hE.eq_iff, v0]] at e6
  set σ6 := (σ5.setv (regE .hcx) 0).setv (regE (.e .lp)) (hc ν) with hσ6
  -- 4. `N := 2^ν`
  have hσ6nu : σ6.val (regE .nu) = ν := by simp [σ6, σ5, σ4, σ3, σ2, Function.update_apply, hE.eq_iff]
  have e7 := pow2W_spec cap (regE .nN) (regE .nu) (regE .nu2) (regE .t) (by simp [List.nodup_cons, hE.eq_iff]) σ6
    (by simp [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hE.eq_iff, v0])
    (by simp [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hE.eq_iff, v0])
    (by simp [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hE.eq_iff, v0])
    (by rw [hσ6nu, hN]; rw [hcapE]; omega)
  rw [hσ6nu, hN] at e7
  set σ7 := σ6.setv (regE .nN) N with hσ7
  have v7 : ∀ r, r ∉ [VReg.nn, .nu, .hcx, .e .lb, .e .lp, .nN] → σ7.val (regE r) = 0 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hE.eq_iff, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2.1, hr.2.2.2.2.2, v0]
  have st7 : ∀ x, σ7.st x = if x = S2 then u else σ0.st x := by
    intro x; by_cases hx : x = S2
    · subst hx; simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1]
    · simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hx]
  have sh7 : ∀ x, σ7.sh x = 0 := by intro x; simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, h0]
  -- 5. the table
  have hlbp : 2 ^ (hc n + hc ν + 1) ≥ 1 := Nat.one_le_two_pow
  obtain ⟨τ8, e8, h8T, h8Th, hse8, -, -⟩ := pointsW_spec cap S2 S3 S4 S5
    (by simp [List.nodup_cons, S2, S3, S4, S5, bs, Fin.ext_iff]) regE hE σ7 u (hc n) (hc ν) N
    ⟨by rw [st7, if_pos rfl], sh7 _, ⟨0, by rw [st7, if_neg (dS 4 2 _ _ (by omega))]; exact st0 _ (by simp [S4, bs])⟩,
      sh7 _, sh7 _, by simp [σ7, σ6, σ5, σ4, Function.update_apply, hE.eq_iff],
      by simp [σ7, σ6, Function.update_apply, hE.eq_iff],
      fun r hr => v7 _ (by
        have h1 : r ≠ .lb := by intro h; subst h; simp [scratchE] at hr
        have h2 : r ≠ .lp := by intro h; subst h; simp [scratchE] at hr
        simp [h1, h2]),
      v7 _ (by simp), v7 _ (by simp), v7 _ (by simp)⟩
    (by rw [st7, if_neg (dS 3 2 _ _ (by omega))]; exact st0 _ (by simp [S3, bs]))
    (by rw [st7, if_neg (dS 5 2 _ _ (by omega))]; exact st0 _ (by simp [S5, bs])) (sh7 _)
    (by simp [σ7]) (fun r hr => v7 _ (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> simp))
    (by rw [hcapE]; omega)
  -- 6. the hierarchy clock
  have n8 : ∀ r, τ8.val r = σ7.val r := fun r => hse8.val (by simp)
  have e9 := htW_spec cap c k regE hE τ8 N (by rw [n8]; simp [σ7])
    (fun q hq => by
      rw [n8]; apply v7
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
    (by rw [hcapE]; omega)
  set τ9 := τ8.setv (regE .ht) (htVal c k N) with hτ9
  -- 7. the witness prefix
  have s8 : ∀ x, x ∉ [S3, S4, S5] → τ8.st x = σ7.st x ∧ τ8.sh x = σ7.sh x := fun x hx => ⟨hse8.st hx, hse8.sh hx⟩
  obtain ⟨τ10, e10, h10W, h10Wh, hse10⟩ := wpW_spec cap S1 S6 (dS 1 6 _ _ (by omega)) regE hE τ9 y (htVal c k N)
    (by simp only [τ9, WState.setv_st]; rw [(s8 S1 (by simp [S1, S3, S4, S5, bs, Fin.ext_iff])).1, st7,
          if_neg (dS 1 2 _ _ (by omega))]; simp [σ0, bodyStart, S1, bs])
    (by simp only [τ9, WState.setv_sh]; rw [(s8 S1 (by simp [S1, S3, S4, S5, bs, Fin.ext_iff])).2, sh7])
    (by simp only [τ9, WState.setv_st]; rw [(s8 S6 (by simp [S6, S3, S4, S5, bs, Fin.ext_iff])).1, st7,
          if_neg (dS 6 2 _ _ (by omega))]; exact st0 _ (by simp [S6, bs]))
    (by simp only [τ9, WState.setv_sh]; rw [(s8 S6 (by simp [S6, S3, S4, S5, bs, Fin.ext_iff])).2, sh7])
    (by simp [τ9])
    (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> (simp [τ9, Function.update_apply, hE.eq_iff]; rw [n8]; exact v7 _ (by simp)))
    (by rw [hcapE]; omega)
  -- assembly
  rw [show σ2.val (regE .nn) = n by simp [σ2, σ1, Function.update_apply, hE.eq_iff]] at e3
  rw [show σ4.val (regE .nu) = ν by simp [σ4, σ3, σ2, Function.update_apply, hE.eq_iff]] at e5
  have s10 : ∀ x, x ∉ [S1, S6] → τ10.st x = τ9.st x ∧ τ10.sh x = τ9.sh x := fun x hx => ⟨hse10.st hx, hse10.sh hx⟩
  refine ⟨τ10, WXExec.mono (WXExec.seq (WXExec.wm e1) (WXExec.seq e2 (WXExec.seq (WXExec.wm e3)
    (WXExec.seq (WXExec.wm e4) (WXExec.seq (WXExec.wm e5) (WXExec.seq (WXExec.wm e6) (WXExec.seq e7
    (WXExec.seq (WXExec.wm e8) (WXExec.seq e9 (WXExec.wm e10)))))))))) ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the cost
    have hcost : bodyCost G c k n = (45 * n + 5) + (n + 2) * (stepCost G n + 10) + 2 * (18 * n + 3 + 30 * n + 20 * n + 1) +
        (ν * (18 * N + 11) + 7 * ν + 7) + ((N + 1) * (pointCost n (hc n) (hc ν) N + 10) + 30 * N + 20) +
        (100 * (c + 1) * (k + 3) * (N + 2) ^ (k + 2) + 10) + (60 * htVal c k N + 30) + 20 := by
      simp only [bodyCost, hν, hN]
    rw [hcost]
    simp only [← hn]
    omega
  · rw [(s10 S5 (by simp [S5, S1, S6, bs, Fin.ext_iff])).1]; simp only [τ9, WState.setv_st]
    rw [h8T]; simp only [bodyTable, ← hn, hν, hN]
  · rw [(s10 S5 (by simp [S5, S1, S6, bs, Fin.ext_iff])).2]; simp only [τ9, WState.setv_sh]; exact h8Th
  · rw [h10W, hν, hN]
  · exact h10Wh
  · intro x hx
    have hx1 : x ∉ [S1, S6] := by simp [S1, S6, bs, Fin.ext_iff]; omega
    have hx2 : x ∉ [S3, S4, S5] := by simp [S3, S4, S5, bs, Fin.ext_iff]; omega
    rw [(s10 x hx1).1, (s10 x hx1).2]; simp only [τ9, WState.setv_st, WState.setv_sh]
    rw [(s8 x hx2).1, (s8 x hx2).2, st7, if_neg (by intro h; subst h; simp [S2, bs] at hx), sh7]
    exact ⟨st0 x (by omega), rfl⟩

end NearCubicGates.Close.Succinct
