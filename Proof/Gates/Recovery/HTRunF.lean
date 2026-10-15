import Proof.Gates.Recovery.HTLayout

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Recovery.HT

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP NearCubicGates.Close.Recovery.HTParts
open NearCubicGates.Close.CheckedPCPP.ClauseFront (named)

/-- The end state of the fit test. -/
def fitState {ns : ℕ} (σ : WState ns 64) (Rv n cd pl : ℕ) : WState ns 64 :=
  let cl := ((Rv + 2) ^ cd - 1).size
  let S := Rv + cl + pl
  ((((((σ.setv rR Rv).setv rC2 (2 * n)).setv pX (Rv + 2)).setv rCL cl).setv rS S).setv rS2 (2 * S)).setv rF
    (if 2 * S ≤ 2 * n then 1 else 0)

/-- Fit test, part 1. -/
theorem fit1_exec (tK tE tH cap : ℕ) (σ : WState (NS tK tE tH) 64) (Rv : ℕ) (w : List Bool)
    (hP3 : σ.st (P3 tK tE tH) = List.replicate Rv true) (hP3h : σ.sh (P3 tK tE tH) = 0)
    (hP2 : σ.st (P2 tK tE tH) = frame w) (hP2h : σ.sh (P2 tK tE tH) = 0)
    (hO : σ.st (OUT tK tE tH) = []) (hOh : σ.sh (OUT tK tE tH) = 0)
    (hz : ∀ r : Fin 64, 18 ≤ r.val → σ.val r = 0) (hX : Rv + 2 * w.length + 4 ≤ cap) :
    WXExec cap (fitW1 tK tE tH) σ ((σ.setv rR Rv).setv rC2 (2 * w.length)) (100 * (Rv + w.length + 1)) := by
  set n := w.length with hn
  have z : ∀ r : Fin 64, 18 ≤ r.val → σ.val r = 0 := hz
  have d1 : P3 tK tE tH ≠ OUT tK tE tH := by hdst
  have d2 : P2 tK tE tH ≠ OUT tK tE tH := by hdst
  have d3 : P2 tK tE tH ≠ P3 tK tE tH := by hdst
  have d1' := Ne.symm d1
  have d2' := Ne.symm d2
  have d3' := Ne.symm d3
  have fm : ∀ l : List Bool, (l.flatMap fun _ => ([] : List Bool)) = [] := by
    intro l; induction l with
    | nil => rfl
    | cons a l ih => simp [ih]
  have hfr : ∀ u : List Bool, frame u = marks u ++ [false] := by
    intro u; induction u with
    | nil => rfl
    | cons a u ih => simp [frame, marks] at ih ⊢; exact ih
  -- 1. R
  have x1 := oneLoop_spec (cap := cap) (src := P3 tK tE tH) (dst := OUT tK tE tH) (OP := opOUT) (SC := rR) d1
    (by decide) (emits_none cap) [] rfl Rv [] σ (by rw [hP3]; simp) (by rw [hP3h]; rfl) (by rw [hO, hOh]; rfl)
    (by rw [z opOUT (by decide)]; simp) (by rw [z rR (by decide)]; omega)
  obtain ⟨s1, hs1, e1⟩ := named (WXExec.wm x1)
  have hs1' : s1 = (σ.seth (P3 tK tE tH) Rv).setv rR Rv := by
    rw [hs1]; simp [adv, appendO_nil, hP3h, z rR (by decide), fm]
  clear hs1
  have x2 := addR_spec cap (A := rR) (B := rT1) (T := rT) (by decide) (by decide) (by decide) s1
    (by simp (config := { decide := true }) [hs1', Function.update_apply, z rT (by decide)])
    (by simp (config := { decide := true }) [hs1', Function.update_apply, z rT1 (by decide)]; omega)
  obtain ⟨s2, hs2, e2⟩ := named x2
  have x3 := wrewind_spec (cap := cap) (P3 tK tE tH) rT1 Rv s2
    (by simp (config := { decide := true }) [hs2, hs1', Function.update_apply, z rT1 (by decide)])
    (by simp (config := { decide := true }) [hs2, hs1', Function.update_apply, z rT1 (by decide)]; omega)
  obtain ⟨s3, hs3, e3⟩ := named (WXExec.wm x3)
  -- 2. 2n
  have x4 := pairLoop_spec (cap := cap) (src := P2 tK tE tH) (dst := OUT tK tE tH) (OP := opOUT) (SC := rC2) d2
    (by decide) (emits_none cap) (emits_none cap) [false] rfl w [] s3
    (by simp (config := { decide := true }) [hs3, hs2, hs1', hP2, hfr, Function.update_apply, d3])
    (by simp (config := { decide := true }) [hs3, hs2, hs1', Function.update_apply, d3, hP2h])
    (by simp (config := { decide := true }) [hs3, hs2, hs1', Function.update_apply, d1, d2, d1', d2', hO, hOh])
    (by simp (config := { decide := true }) [hs3, hs2, hs1', Function.update_apply, z opOUT (by decide), fm])
    (by simp (config := { decide := true }) [hs3, hs2, hs1', Function.update_apply, z rC2 (by decide)]; omega)
  obtain ⟨s4, hs4, e4⟩ := named (WXExec.wm x4)
  have fm2 : (w.flatMap fun _ => ([] : List Bool) ++ []) = [] := by simp
  have hs4' : s4 = (s3.seth (P2 tK tE tH) (2 * n)).setv rC2 (2 * n) := by
    rw [hs4, fm2]
    simp (config := { decide := true }) [adv, appendO_nil, hs3, hs2, hs1', Function.update_apply, d3, hP2h,
      z rC2 (by decide)]
    rfl
  clear hs4
  have x5 := addR_spec cap (A := rC2) (B := rT1) (T := rT) (by decide) (by decide) (by decide) s4
    (by simp (config := { decide := true }) [hs4', hs3, hs2, hs1', Function.update_apply, z rT (by decide)])
    (by simp (config := { decide := true }) [hs4', hs3, hs2, hs1', Function.update_apply]; omega)
  obtain ⟨s5, hs5, e5⟩ := named x5
  have x6 := wrewind_spec (cap := cap) (P2 tK tE tH) rT1 (2 * n) s5
    (by simp (config := { decide := true }) [hs5, hs4', hs3, hs2, hs1', Function.update_apply])
    (by simp (config := { decide := true }) [hs5, hs4', hs3, hs2, hs1', Function.update_apply]; omega)
  obtain ⟨s6, hs6, e6⟩ := named (WXExec.wm x6)

  have hs6' : s6 = (σ.setv rR Rv).setv rC2 (2 * n) := by
    rw [hs6, hs5, hs4', hs3, hs2, hs1']
    refine WState.eq ?_ ?_ ?_ ?_
    · funext j
      by_cases j1 : j = P2 tK tE tH
      · simp [j1, Function.update_apply, d3, hP2h]
      · by_cases j2 : j = P3 tK tE tH
        · simp [j2, Function.update_apply, d3', hP3h]
        · simp [Function.update_apply, j1, j2]
    · rfl
    · funext q
      by_cases q1 : q = rT1
      · simp (config := { decide := true }) [q1, Function.update_apply, z rT1 (by decide)]
      · simp (config := { decide := true }) [Function.update_apply, q1]
    · rfl
  have whole := WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5 e6))))
  refine WXExec.mono (WXExec.cast cap whole hs6' le_rfl) ?_
  simp (config := { decide := true }) [hs5, hs4', hs3, hs2, hs1', Function.update_apply, z rT1 (by decide),
    z rC2 (by decide)]
  omega

/-- Fit test, part 2. -/
theorem fit2_exec (tK tE tH cd cap : ℕ) (s6 : WState (NS tK tE tH) 64) (Rv : ℕ) (hR6 : s6.val rR = Rv)
    (hz : ∀ r : Fin 64, 22 ≤ r.val → s6.val r = 0) (hW : 2 * (Rv + 2) ^ cd + (Rv + 2) ^ cd * (Rv + 2) ^ cd ≤ cap)
    (hX : (Rv + 2) ^ cd + Rv + 4 ≤ cap) :
    WXExec cap (fitW2 tK tE tH cd) s6 ((s6.setv pX (Rv + 2)).setv rCL ((Rv + 2) ^ cd - 1).size)
      (cd * (40 * (Rv + 2) ^ cd * (Rv + 2) ^ cd + 40 * (Rv + 2) ^ cd + 20) + (Rv + 2) ^ cd * (12 * (Rv + 2) ^ cd + 30)
        + 18 * Rv + 40) := by
  set V := (Rv + 2) ^ cd with hV
  have hV1 : 1 ≤ V := Nat.one_le_pow _ _ (by omega)
  set cl := (V - 1).size with hcl
  have hclV : cl ≤ V := by
    rw [hcl]; have := Nat.size_le.mpr (show V - 1 < 2 ^ V by have := Nat.lt_two_pow_self (n := V); omega); omega
  have z : ∀ r : Fin 64, 22 ≤ r.val → s6.val r = 0 := hz
  -- 3. V = (R + 2)^d, cl
  have x7 := addR_spec cap (A := rR) (B := pX) (T := pT) (by decide) (by decide) (by decide) s6
    (by simp (config := { decide := true }) [Function.update_apply, hR6, z pT (by decide)])
    (by simp (config := { decide := true }) [Function.update_apply, hR6, z pX (by decide)]; omega)
  obtain ⟨s7, hs7, e7⟩ := named x7
  have x8 := WXExec.inc (cap := cap) pX s7
    (by simp (config := { decide := true }) [hs7, Function.update_apply, hR6, z pX (by decide)]; omega)
  obtain ⟨s8, hs8, e8⟩ := named x8
  have x9 := WXExec.inc (cap := cap) pX s8
    (by simp (config := { decide := true }) [hs8, hs7, Function.update_apply, hR6, z pX (by decide)]; omega)
  obtain ⟨s9, hs9, e9⟩ := named x9
  have x10 := WXExec.inc (cap := cap) pY s9
    (by simp (config := { decide := true }) [hs9, hs8, hs7, Function.update_apply, hR6, z pY (by decide)]; omega)
  obtain ⟨s10, hs10, e10⟩ := named x10
  have hpX : s10.val pX = Rv + 2 := by
    simp (config := { decide := true }) [hs10, hs9, hs8, hs7, Function.update_apply, hR6, z pX (by decide)]
  have hpY : s10.val pY = 1 := by
    simp (config := { decide := true }) [hs10, hs9, hs8, hs7, Function.update_apply, hR6, z pY (by decide)]
  have x11 := EncSetup.powW_spec (cap := cap) (X := pX) (Y := pY) (Z := pZ) (A2 := pA2) (T := pT) (by decide) V cd s10
    (by simp (config := { decide := true }) [hs10, hs9, hs8, hs7, Function.update_apply, hR6, z pZ (by decide)])
    (by simp (config := { decide := true }) [hs10, hs9, hs8, hs7, Function.update_apply, hR6, z pA2 (by decide)])
    (by simp (config := { decide := true }) [hs10, hs9, hs8, hs7, Function.update_apply, hR6, z pT (by decide)])
    (by rw [hpX, hpY, Nat.one_mul]) (by rw [hpX]; omega) hW
  obtain ⟨s11, hs11, e11⟩ := named x11
  have x12 := WXExec.dec (cap := cap) pY s11 (by simp [hs11, hpX, hpY]; omega)
  obtain ⟨s12, hs12, e12⟩ := named x12
  have x13 := sizeW_exec (cap := cap) (X := pY) (H := rH) (B := rB) (C := rCL) (by decide) V (by omega) (V - 1) s12
    (by omega) (by simp [hs12, hs11, hpX, hpY, hV])
    (by simp (config := { decide := true }) [hs12, hs11, hs10, hs9, hs8, hs7, Function.update_apply, hR6,
      z rH (by decide)])
    (by simp (config := { decide := true }) [hs12, hs11, hs10, hs9, hs8, hs7, Function.update_apply, hR6,
      z rB (by decide)])
    (by simp (config := { decide := true }) [hs12, hs11, hs10, hs9, hs8, hs7, Function.update_apply, hR6,
      z rCL (by decide)]; omega)
  obtain ⟨s13, hs13, e13⟩ := named x13
  have hs13' : s13 = (s6.setv pX (Rv + 2)).setv rCL cl := by
    rw [hs13, hs12, hs11, hs10, hs9, hs8, hs7]
    refine WState.eq rfl rfl ?_ rfl
    funext q
    by_cases q1 : q = pY
    · simp (config := { decide := true }) [q1, Function.update_apply, hR6, z pY (by decide)]
    · by_cases q2 : q = pX
      · simp (config := { decide := true }) [q2, Function.update_apply, hR6, z pX (by decide)]
      · by_cases q3 : q = rCL
        · simp (config := { decide := true }) [q3, Function.update_apply, hR6, z rCL (by decide), hpX, hpY, hcl]
        · simp (config := { decide := true }) [Function.update_apply, hR6, q1, q2, q3]
  have whole := WXExec.seq e7 (WXExec.seq e8 (WXExec.seq e9 (WXExec.seq e10 (WXExec.seq e11 (WXExec.seq e12 e13)))))
  refine WXExec.mono (WXExec.cast cap whole hs13' le_rfl) ?_
  have hsz : (V - 1).size ≤ V := hclV
  have hm := Nat.mul_le_mul_right (12 * V + 30) hsz
  simp (config := { decide := true }) [hs7, hR6, EncSetup.powCost]
  nlinarith

/-- Fit test, part 3. -/
theorem fit3_exec (tK tE tH pl cap : ℕ) (s13 : WState (NS tK tE tH) 64) (Rv cl n : ℕ) (hR : s13.val rR = Rv)
    (hCL : s13.val rCL = cl) (hC2 : s13.val rC2 = 2 * n) (hT : s13.val rT = 0)
    (hz : ∀ r : Fin 64, 30 ≤ r.val → s13.val r = 0) (hX : 4 * (Rv + cl + pl + n + 2) ≤ cap) :
    WXExec cap (fitW3 tK tE tH pl) s13 (((s13.setv rS (Rv + cl + pl)).setv rS2 (2 * (Rv + cl + pl))).setv rF
      (if 2 * (Rv + cl + pl) ≤ 2 * n then 1 else 0)) (200 * (Rv + cl + pl + n + 1)) := by
  have z : ∀ r : Fin 64, 30 ≤ r.val → s13.val r = 0 := hz
  -- 4. S = R + cl + pl, the comparison
  set S := Rv + cl + pl with hS
  have hs13' : s13 = s13 := rfl
  have x14 := addR_spec cap (A := rR) (B := rS) (T := rT) (by decide) (by decide) (by decide) s13
    (by simp (config := { decide := true }) [Function.update_apply, hT])
    (by simp (config := { decide := true }) [Function.update_apply, z rS (by decide)]; omega)
  obtain ⟨s14, hs14, e14⟩ := named x14
  have x15 := addR_spec cap (A := rCL) (B := rS) (T := rT) (by decide) (by decide) (by decide) s14
    (by simp (config := { decide := true }) [hs14, hs13', Function.update_apply, hT])
    (by simp (config := { decide := true }) [hs14, hs13', Function.update_apply, z rS (by decide)]; omega)
  obtain ⟨s15, hs15, e15⟩ := named x15
  have x16 := incN_exec (cap := cap) rS pl s15
    (by simp (config := { decide := true }) [hs15, hs14, hs13', Function.update_apply, z rS (by decide)]; omega)
  obtain ⟨s16, hs16, e16⟩ := named x16
  have hS16 : s16.val rS = S := by
    simp (config := { decide := true }) [hs16, hs15, hs14, hs13', Function.update_apply, z rS (by decide)]; omega
  have x17 := addR_spec cap (A := rS) (B := rS2) (T := rT) (by decide) (by decide) (by decide) s16
    (by simp (config := { decide := true }) [hs16, hs15, hs14, hs13', Function.update_apply, hT])
    (by rw [hS16]; simp (config := { decide := true }) [hs16, hs15, hs14, hs13', Function.update_apply,
      z rS2 (by decide)]; omega)
  obtain ⟨s17, hs17, e17⟩ := named x17
  have x18 := addR_spec cap (A := rS) (B := rS2) (T := rT) (by decide) (by decide) (by decide) s17
    (by simp (config := { decide := true }) [hs17, hs16, hs15, hs14, hs13', Function.update_apply, hT])
    (by simp (config := { decide := true }) [hs17, Function.update_apply]; rw [hS16]
        simp (config := { decide := true }) [hs16, hs15, hs14, hs13', Function.update_apply, z rS2 (by decide)]
        omega)
  obtain ⟨s18, hs18, e18⟩ := named x18
  have hS18 : s18.val rS2 = 2 * S := by
    simp (config := { decide := true }) [hs18, hs17, Function.update_apply]; rw [hS16]
    simp (config := { decide := true }) [hs16, hs15, hs14, hs13', Function.update_apply, z rS2 (by decide)]; omega
  have hC18 : s18.val rC2 = 2 * n := by
    simp (config := { decide := true }) [hs18, hs17, hs16, hs15, hs14, Function.update_apply, hC2]
  have x19 := leW_exec (cap := cap) (A := rS2) (B := rC2) (U := rU) (K := rK) (T := rT) (F := rF) (by decide)
    (2 * S) (2 * n) (by omega) s18 hS18 hC18
    (by simp (config := { decide := true }) [hs18, hs17, hs16, hs15, hs14, hs13', Function.update_apply,
      z rU (by decide)])
    (by simp (config := { decide := true }) [hs18, hs17, hs16, hs15, hs14, hs13', Function.update_apply,
      z rK (by decide)])
    (by simp (config := { decide := true }) [hs18, hs17, hs16, hs15, hs14, hs13', Function.update_apply,
      hT])
    (by simp (config := { decide := true }) [hs18, hs17, hs16, hs15, hs14, hs13', Function.update_apply,
      z rF (by decide)])
  obtain ⟨s19, hs19, e19⟩ := named x19
  have whole := WXExec.seq e14 (WXExec.seq e15 (WXExec.seq e16 (WXExec.seq e17 (WXExec.seq e18 e19))))
  refine WXExec.mono (WXExec.cast cap whole ?_ le_rfl) ?_
  · rw [hs19, hs18, hs17, hs16, hs15, hs14]
    refine WState.eq rfl rfl ?_ rfl
    funext q
    by_cases q1 : q = rF
    · simp (config := { decide := true }) [q1, Function.update_apply]
    · by_cases q2 : q = rS2
      · simp (config := { decide := true }) [q2, Function.update_apply, z rS2 (by decide), z rS (by decide), hR, hCL]
        omega
      · by_cases q3 : q = rS
        · simp (config := { decide := true }) [q3, Function.update_apply, z rS (by decide), hR, hCL]
          omega
        · by_cases q4 : q = rT
          · simp (config := { decide := true }) [q4, Function.update_apply, hT]
          · simp (config := { decide := true }) [Function.update_apply, q1, q2, q3, q4]
  · simp (config := { decide := true }) [hs17, hs16, hs15, hs14, Function.update_apply, z rS (by decide),
      z rS2 (by decide), hR, hCL]
    omega

/-- **The fit test.** -/
theorem fit_exec (tK tE tH cd pl cap : ℕ) (σ : WState (NS tK tE tH) 64) (Rv : ℕ) (w : List Bool)
    (hP3 : σ.st (P3 tK tE tH) = List.replicate Rv true) (hP3h : σ.sh (P3 tK tE tH) = 0)
    (hP2 : σ.st (P2 tK tE tH) = frame w) (hP2h : σ.sh (P2 tK tE tH) = 0)
    (hO : σ.st (OUT tK tE tH) = []) (hOh : σ.sh (OUT tK tE tH) = 0)
    (hz : ∀ r : Fin 64, 18 ≤ r.val → σ.val r = 0)
    (hcap : ((Rv + 2) ^ cd + Rv + 2 * w.length + pl + 4) ^ 2 ≤ cap) :
    WXExec cap (fitW tK tE tH cd pl) σ (fitState σ Rv w.length cd pl) (200 * (cd + pl + 1) * (cap + 1) ^ 2) := by
  set V := (Rv + 2) ^ cd with hV
  set n := w.length with hn
  have hV1 : 1 ≤ V := Nat.one_le_pow _ _ (by omega)
  have hX : V + Rv + 2 * n + pl + 4 ≤ cap := le_trans (Nat.le_self_pow (by norm_num) _) hcap
  have hW : 2 * V + V * V ≤ cap := by nlinarith
  have hX4 : 4 * (V + Rv + 2 * n + pl + 4) ≤ cap := by nlinarith
  set cl := (V - 1).size with hcl
  have hclV : cl ≤ V := by
    rw [hcl]; have := Nat.size_le.mpr (show V - 1 < 2 ^ V by have := Nat.lt_two_pow_self (n := V); omega); omega
  have e1 := fit1_exec tK tE tH cap σ Rv w hP3 hP3h hP2 hP2h hO hOh hz (by omega)
  set σ1 := (σ.setv rR Rv).setv rC2 (2 * n) with hσ1
  have e2 := fit2_exec tK tE tH cd cap σ1 Rv (by simp (config := { decide := true }) [hσ1, Function.update_apply])
    (fun r hr => by
      have h1 : r ≠ rR := fun e => by rw [e] at hr; simp at hr
      have h2 : r ≠ rC2 := fun e => by rw [e] at hr; simp at hr
      simp [hσ1, Function.update_apply, h1, h2, hz r (by omega)]) hW (by omega)
  set σ2 := (σ1.setv pX (Rv + 2)).setv rCL cl with hσ2
  have e3 := fit3_exec tK tE tH pl cap σ2 Rv cl n
    (by simp (config := { decide := true }) [hσ2, hσ1, Function.update_apply])
    (by simp (config := { decide := true }) [hσ2, hσ1, Function.update_apply])
    (by simp (config := { decide := true }) [hσ2, hσ1, Function.update_apply])
    (by simp (config := { decide := true }) [hσ2, hσ1, Function.update_apply, hz rT (by decide)])
    (fun r hr => by
      have h1 : r ≠ rR := fun e => by rw [e] at hr; simp at hr
      have h2 : r ≠ rC2 := fun e => by rw [e] at hr; simp at hr
      have h3 : r ≠ pX := fun e => by rw [e] at hr; simp at hr
      have h4 : r ≠ rCL := fun e => by rw [e] at hr; simp at hr
      simp [hσ2, hσ1, Function.update_apply, h1, h2, h3, h4, hz r (by omega)])
    (by omega)
  refine WXExec.mono (WXExec.seq e1 (WXExec.seq e2 e3)) ?_
  have hc1 : V ≤ cap := by omega
  have hq : (cap + 1) ^ 2 = cap * cap + 2 * cap + 1 := by ring
  have hVV : V * V ≤ cap * cap := Nat.mul_le_mul hc1 hc1
  have hcd : cd * (40 * V * V + 40 * V + 20) ≤ cd * (100 * (cap + 1) ^ 2) := Nat.mul_le_mul_left _ (by nlinarith)
  have hsz : V * (12 * V + 30) ≤ 42 * (cap + 1) ^ 2 := by nlinarith
  have hpl : pl ≤ pl * (cap + 1) ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
  have h5 : 5 * (cap + 1) ≤ (cap + 1) ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right _ (by omega)
  have hcl' : cl ≤ cap := by omega
  rw [← hV, ← hn]
  nlinarith

end NearCubicGates.Close.Recovery.HT
