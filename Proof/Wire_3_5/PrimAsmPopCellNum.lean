import Proof.Wire_3_5.PrimAsmPopNums
import Proof.Wire_3_5.PrimAsmPopRecW

/-! # PA (d)-SYM, part 14: the POP cell's numbers stage (one register file)

The POP cell writes the POP record (`PopRecW.popRecW`, registers `X = P 0 … P 63`) after computing the record's
per-call numbers from the list's numbers already in `X` (`S`, `J`, `M`, `L`, the labels' `r4`, `G`, `off`, `Lg`, the walk
length `n`) and the label bound `Mlab` (`P 180`): the degree `d = 3·listBound` (`PopParams.lbW`), the table word's length
`lw` and the capacity `c = 4(lw + L + 1)` (`lwW`), the label sum `CAP` and `LL = |labels at level 2|` (`Emit.labsW` on a
dummy stream), `Q = (8L+2)^d` (`Arith.powW`), and Route B's `R`, `Lg`, `cap` (`PopNums.numOps`).

The cell's registers `P : Fin 200 ↪ Fin nr`: `0–63` X; `64–95` Y (the level loops); `96–135` Zn (numOps); `136–148` the
label block; `149–156` Zc; `157`, `158` the power's scratch and counter; `160`, `161` the arithmetic scratch; `162–170`
Zv; `180` Mlab.

Paper quantities of the main type: the list's degree and capacity (`PopParams.lbP_eq`, `capP_eq`) and Route B's
capacities (`PopNums.numOps_capacities`) in the record's registers. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.PopCellNum
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.LevelW NearCubicWires.WireExponent3_5.PrimAsm.PopParams
open NearCubicWires.WireExponent3_5.PrimAsm.Arith

/-- A block of `k` consecutive registers from `off` inside `N`. -/
def shiftE (off k N : ℕ) (h : off + k ≤ N) : Fin k ↪ Fin N :=
  ⟨fun i => ⟨off + i.val, by omega⟩, fun i j hij => Fin.ext (by simpa using congrArg Fin.val hij)⟩

section Phases
variable {ns nr : ℕ} (cap : ℕ) (P : Fin 200 ↪ Fin nr)

/-- The level loops' registers. -/
def Ye : Fin 32 ↪ Fin nr := (shiftE 64 32 200 (by norm_num)).trans P

theorem Ye_apply (i : Fin 32) : Ye P i = P ⟨64 + i.val, by omega⟩ := rfl

/-- **Phase 1**: `d = 3·(Σ_{j<J} 4·W'_j + 1)` into `P 97` (`Y 0 := S`, `Y 1 := J` kept). -/
def ph1 : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (P 20) (P 64) (P 160))
  (.seq (FinalPass.Hash4.wcopyR (P 21) (P 65) (P 160))
  (.seq (lbW (Ye P))
  (.seq (ParseNat.addTo (P 88) (P 97) (P 160))
  (.seq (ParseNat.addTo (P 88) (P 97) (P 160))
  (.seq (ParseNat.addTo (P 88) (P 97) (P 160))
  (WM.clear (P 88)))))))

theorem ph1_spec (σ : WState ns nr) (Sv J : ℕ) (h20 : σ.val (P 20) = Sv) (h21 : σ.val (P 21) = J)
    (hz : ∀ j : Fin 200, 64 ≤ j.val → j.val ≤ 97 → σ.val (P j) = 0) (h160 : σ.val (P 160) = 0)
    (hcap : lvCap Sv J J ≤ cap) (hac : 3 * (lbSumF Sv J + 1) ≤ cap) (hJc : J ≤ cap) (hSc : Sv ≤ cap) :
    ∃ n, WExec cap (ph1 P) σ (((σ.setv (P 64) Sv).setv (P 65) J).setv (P 97) (3 * (lbSumF Sv J + 1))) n ∧
      n ≤ J * (lvlBound cap + 4) + 40 * J + 18 * Sv + 200 * (lbSumF Sv J + 1) + 100 := by
  have hR : ∀ i j : Fin 200, P i = P j ↔ i = j := fun i j => P.injective.eq_iff
  have hne : ∀ {i j : Fin 200}, i ≠ j → P i ≠ P j := fun h => P.injective.ne h
  have z : ∀ j : Fin 200, 64 ≤ j.val → j.val ≤ 97 → σ.val (P j) = 0 := hz
  have e1 := FinalPass.Hash4.wcopyR_spec cap (P 20) (P 64) (P 160) (hne (by decide)) (hne (by decide))
    (hne (by decide)) σ (z 64 (by decide) (by decide)) h160 (by omega)
  rw [h20] at e1
  have e2 := FinalPass.Hash4.wcopyR_spec cap (P 21) (P 65) (P 160) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (σ.setv (P 64) Sv) (by simp [hR, z 65 (by decide) (by decide)]) (by simp [hR, h160])
    (by simp [hR, h21]; omega)
  rw [show (σ.setv (P 64) Sv).val (P 21) = J by simp [hR, h21]] at e2
  set τ := (σ.setv (P 64) Sv).setv (P 65) J with hτ
  obtain ⟨n3, e3, b3⟩ := lbW_spec cap (Ye P) τ Sv J 0 (by rw [Ye_apply]; simp [hτ, hR])
    (by rw [Ye_apply]; simp [hτ, hR])
    (fun i h2 h23 => by
      rw [Ye_apply]
      have h64 : (⟨64 + i.val, by omega⟩ : Fin 200) ≠ 64 := Fin.ne_of_val_ne (by simp; omega)
      have h65 : (⟨64 + i.val, by omega⟩ : Fin 200) ≠ 65 := Fin.ne_of_val_ne (by simp; omega)
      rw [hτ, wsetv_val_ne _ _ (hne h65), wsetv_val_ne _ _ (hne h64)]
      exact z _ (by simp) (by simp; omega))
    (by rw [Ye_apply]; simp [hτ, hR, z 91 (by decide) (by decide)])
    (by rw [Ye_apply]; simp [hτ, hR, z 92 (by decide) (by decide)])
    (by rw [Ye_apply]; simp [hτ, hR, z 88 (by decide) (by decide)]) hcap (by omega) hJc
  have hY24 : Ye P 24 = P 88 := rfl
  rw [hY24, Nat.zero_add] at e3
  have e4 := ParseNat.addTo_spec cap (P 88) (P 97) (P 160) (hne (by decide)) (hne (by decide)) (hne (by decide))
    (τ.setv (P 88) (lbSumF Sv J + 1)) (by simp [hτ, hR, h160]) (by simp; omega)
    (by simp [hτ, hR, z 97 (by decide) (by decide)]; omega)
  rw [show (τ.setv (P 88) (lbSumF Sv J + 1)).val (P 97) + (τ.setv (P 88) (lbSumF Sv J + 1)).val (P 88) =
    lbSumF Sv J + 1 by simp [hτ, hR, z 97 (by decide) (by decide)],
    show (τ.setv (P 88) (lbSumF Sv J + 1)).val (P 88) = lbSumF Sv J + 1 by simp] at e4
  have e5 := ParseNat.addTo_spec cap (P 88) (P 97) (P 160) (hne (by decide)) (hne (by decide)) (hne (by decide))
    ((τ.setv (P 88) (lbSumF Sv J + 1)).setv (P 97) (lbSumF Sv J + 1)) (by simp [hτ, hR, h160]) (by simp [hR]; omega)
    (by simp [hR]; omega)
  rw [show ((τ.setv (P 88) (lbSumF Sv J + 1)).setv (P 97) (lbSumF Sv J + 1)).val (P 97) +
      ((τ.setv (P 88) (lbSumF Sv J + 1)).setv (P 97) (lbSumF Sv J + 1)).val (P 88) = 2 * (lbSumF Sv J + 1) by
      simp [hR]; omega,
    show ((τ.setv (P 88) (lbSumF Sv J + 1)).setv (P 97) (lbSumF Sv J + 1)).val (P 88) = lbSumF Sv J + 1 by simp [hR],
    wsetv_setv] at e5
  have e6 := ParseNat.addTo_spec cap (P 88) (P 97) (P 160) (hne (by decide)) (hne (by decide)) (hne (by decide))
    ((τ.setv (P 88) (lbSumF Sv J + 1)).setv (P 97) (2 * (lbSumF Sv J + 1))) (by simp [hτ, hR, h160])
    (by simp [hR]; omega) (by simp [hR]; omega)
  rw [show ((τ.setv (P 88) (lbSumF Sv J + 1)).setv (P 97) (2 * (lbSumF Sv J + 1))).val (P 97) +
      ((τ.setv (P 88) (lbSumF Sv J + 1)).setv (P 97) (2 * (lbSumF Sv J + 1))).val (P 88) = 3 * (lbSumF Sv J + 1) by
      simp [hR]; omega,
    show ((τ.setv (P 88) (lbSumF Sv J + 1)).setv (P 97) (2 * (lbSumF Sv J + 1))).val (P 88) = lbSumF Sv J + 1 by
      simp [hR], wsetv_setv] at e6
  have e7 := wclear_spec cap (P 88) (lbSumF Sv J + 1)
    ((τ.setv (P 88) (lbSumF Sv J + 1)).setv (P 97) (3 * (lbSumF Sv J + 1))) (by simp [hR]) (by simp [hR]; omega)
  refine ⟨_, WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5
    (WExec.seq e6 e7)))))) ?_ le_rfl, ?_⟩
  · apply WState.eq
    · rfl
    · rfl
    · funext x
      simp only [hτ, WState.setv_val, Function.update_apply]
      by_cases x88 : x = P 88
      · subst x88; simp [hR, z 88 (by decide) (by decide)]
      · simp [x88]
    · rfl
  · omega

end Phases

section Phases2
variable {ns nr : ℕ} (cap : ℕ) (P : Fin 200 ↪ Fin nr)

/-- **Phase 2**: `lw = |levelWord|` into `P 104` and `P 150` (`Y 25 := M`, `Y 26 := L` kept). -/
def ph2 : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (P 44) (P 89) (P 160))
  (.seq (FinalPass.Hash4.wcopyR (P 45) (P 90) (P 160))
  (.seq (lwW (Ye P))
  (.seq (ParseNat.addTo (P 88) (P 104) (P 160))
  (.seq (ParseNat.addTo (P 88) (P 150) (P 160))
  (WM.clear (P 88))))))

theorem ph2_spec (σ : WState ns nr) (Sv J M L : ℕ) (h64 : σ.val (P 64) = Sv) (h65 : σ.val (P 65) = J)
    (h44 : σ.val (P 44) = M) (h45 : σ.val (P 45) = L)
    (hz : ∀ j : Fin 200, 66 ≤ j.val → j.val ≤ 95 → σ.val (P j) = 0) (h104 : σ.val (P 104) = 0)
    (h150 : σ.val (P 150) = 0) (h160 : σ.val (P 160) = 0)
    (hcap : lvCap Sv J J ≤ cap) (hac : lwSumF Sv J L + M + 2 ≤ cap) (hJc : J + 1 ≤ cap) (hMc : M ≤ cap)
    (hLc : L ≤ cap) :
    ∃ n, WExec cap (ph2 P) σ ((((σ.setv (P 89) M).setv (P 90) L).setv (P 104) (lwSumF Sv J L + M + 2)).setv (P 150)
      (lwSumF Sv J L + M + 2)) n ∧
      n ≤ (J + 1) * (lvlBound cap + 4) + 40 * J + 40 * M + 18 * L + 100 * (lwSumF Sv J L + M + 2) + 100 := by
  have hR : ∀ i j : Fin 200, P i = P j ↔ i = j := fun i j => P.injective.eq_iff
  have hne : ∀ {i j : Fin 200}, i ≠ j → P i ≠ P j := fun h => P.injective.ne h
  have z : ∀ j : Fin 200, 66 ≤ j.val → j.val ≤ 95 → σ.val (P j) = 0 := hz
  obtain ⟨lw, hlw⟩ : ∃ x, x = lwSumF Sv J L + M + 2 := ⟨_, rfl⟩
  rw [← hlw] at hac ⊢
  have e1 := FinalPass.Hash4.wcopyR_spec cap (P 44) (P 89) (P 160) (hne (by decide)) (hne (by decide))
    (hne (by decide)) σ (z 89 (by decide) (by decide)) h160 (by omega)
  rw [h44] at e1
  have e2 := FinalPass.Hash4.wcopyR_spec cap (P 45) (P 90) (P 160) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (σ.setv (P 89) M) (by simp [hR, z 90 (by decide) (by decide)]) (by simp [hR, h160])
    (by simp [hR, h45]; omega)
  rw [show (σ.setv (P 89) M).val (P 45) = L by simp [hR, h45]] at e2
  set τ := (σ.setv (P 89) M).setv (P 90) L with hτ
  obtain ⟨n3, e3, b3⟩ := lwW_spec cap (Ye P) τ Sv J L M 0 (by rw [Ye_apply]; simp [hτ, hR, h64])
    (by rw [Ye_apply]; simp [hτ, hR, h65])
    (fun i h2 h23 => by
      rw [Ye_apply]
      have h89 : (⟨64 + i.val, by omega⟩ : Fin 200) ≠ 89 := Fin.ne_of_val_ne (by simp; omega)
      have h90 : (⟨64 + i.val, by omega⟩ : Fin 200) ≠ 90 := Fin.ne_of_val_ne (by simp; omega)
      rw [hτ, wsetv_val_ne _ _ (hne h90), wsetv_val_ne _ _ (hne h89)]
      exact z _ (by simp; omega) (by simp; omega))
    (by rw [Ye_apply]; simp [hτ, hR, z 91 (by decide) (by decide)])
    (by rw [Ye_apply]; simp [hτ, hR, z 92 (by decide) (by decide)])
    (by rw [Ye_apply]; simp [hτ, hR, z 88 (by decide) (by decide)])
    (by rw [Ye_apply]; simp [hτ, hR]) (by rw [Ye_apply]; simp [hτ, hR]) hcap (by omega) hJc
  have hY24 : Ye P 24 = P 88 := rfl
  rw [hY24, Nat.zero_add, ← hlw] at e3
  have e4 := ParseNat.addTo_spec cap (P 88) (P 104) (P 160) (hne (by decide)) (hne (by decide)) (hne (by decide))
    (τ.setv (P 88) lw) (by simp [hτ, hR, h160]) (by simp; omega) (by simp [hτ, hR, h104]; omega)
  rw [show (τ.setv (P 88) lw).val (P 104) + (τ.setv (P 88) lw).val (P 88) = lw by simp [hτ, hR, h104],
    show (τ.setv (P 88) lw).val (P 88) = lw by simp] at e4
  have e5 := ParseNat.addTo_spec cap (P 88) (P 150) (P 160) (hne (by decide)) (hne (by decide)) (hne (by decide))
    ((τ.setv (P 88) lw).setv (P 104) lw) (by simp [hτ, hR, h160]) (by simp [hR]; omega)
    (by simp [hτ, hR, h150]; omega)
  rw [show ((τ.setv (P 88) lw).setv (P 104) lw).val (P 150) + ((τ.setv (P 88) lw).setv (P 104) lw).val (P 88) = lw by
    simp [hτ, hR, h150], show ((τ.setv (P 88) lw).setv (P 104) lw).val (P 88) = lw by simp [hR]] at e5
  have e6 := wclear_spec cap (P 88) lw (((τ.setv (P 88) lw).setv (P 104) lw).setv (P 150) lw) (by simp [hR])
    (by simp [hR]; omega)
  refine ⟨_, WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 e6))))) ?_ le_rfl, ?_⟩
  · apply WState.eq
    · rfl
    · rfl
    · funext x
      simp only [hτ, WState.setv_val, Function.update_apply]
      by_cases x88 : x = P 88
      · subst x88; simp [hR, z 88 (by decide) (by decide)]
      · simp [x88]
    · rfl
  · omega

/-- The label block inside the cell's registers (`LReg`: `0` the dummy output counter, `1 r4`, `2 G`, `3 off`,
`4 Lg`, `11` the label sum). -/
def Le : Emit.LReg nr := (shiftE 136 13 200 (by norm_num)).trans P

theorem Le_apply (i : Fin 13) : Le P i = P ⟨136 + i.val, by omega⟩ := rfl

/-- **Phase 3**: the label sum `CAP = 5 + labAdd labs` into `P 99` and `LL = |labs at level 2|` into `P 100` (the
labels written on the dummy stream `D`). -/
def ph3 (D : Fin (ns + 1)) : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (P 1) (P 137) (P 160))
  (.seq (FinalPass.Hash4.wcopyR (P 2) (P 138) (P 160))
  (.seq (FinalPass.Hash4.wcopyR (P 3) (P 139) (P 160))
  (.seq (FinalPass.Hash4.wcopyR (P 4) (P 140) (P 160))
  (.seq (StarNums.incN (P 147) 5)
  (.seq (Emit.labsW D (Le P))
  (.seq (ParseNat.addTo (P 147) (P 99) (P 160))
  (ParseNat.addTo (P 136) (P 100) (P 160))))))))

theorem ph3_spec (D : Fin (ns + 1)) (σ : WState ns nr) (r4 G off Lg Mlab : ℕ) (h1 : σ.val (P 1) = r4)
    (h2 : σ.val (P 2) = G) (h3 : σ.val (P 3) = off) (h4 : σ.val (P 4) = Lg)
    (hz : ∀ j : Fin 200, 136 ≤ j.val → j.val ≤ 148 → σ.val (P j) = 0) (h99 : σ.val (P 99) = 0)
    (h100 : σ.val (P 100) = 0) (h160 : σ.val (P 160) = 0) (hD : σ.sh D = (σ.st D).length)
    (hM : off + Lg + (r4 + 4) * G ≤ Mlab)
    (hcap : Lg * (4 * (4 * Mlab + 4)) + 5 + Lg * (4 * (2 * Mlab + 10)) + 4 * (4 * Mlab + 4) +
      4 * (2 * Mlab + 10) + 7 * Mlab + r4 + G + off + Lg + 20 ≤ cap)
    (hac : FiltRec.labSum (Emit.sliceLabs r4 G off Lg) + ((Emit.sliceLabs r4 G off Lg).flatMap FiltRec.labE).length ≤ cap) :
    ∃ n, WExec cap (ph3 P D) σ
      (((((((((appendO σ D (P 136) ((Emit.sliceLabs r4 G off Lg).flatMap FiltRec.labE)).setv (P 137) r4).setv (P 138) G).setv
        (P 139) off).setv (P 140) Lg).setv (P 147) (FiltRec.labSum (Emit.sliceLabs r4 G off Lg))).setv (P 99)
        (FiltRec.labSum (Emit.sliceLabs r4 G off Lg))).setv (P 100)
        ((Emit.sliceLabs r4 G off Lg).flatMap FiltRec.labE).length)) n ∧
      n ≤ 18 * (r4 + G + off + Lg) + Emit.labsCost r4 G off Lg + 18 * cap + 100 := by
  have hR : ∀ i j : Fin 200, P i = P j ↔ i = j := fun i j => P.injective.eq_iff
  have hne : ∀ {i j : Fin 200}, i ≠ j → P i ≠ P j := fun h => P.injective.ne h
  have z : ∀ j : Fin 200, 136 ≤ j.val → j.val ≤ 148 → σ.val (P j) = 0 := hz
  have hlabs : 5 + Emit.labAdd (Emit.sliceLabs r4 G off Lg) = FiltRec.labSum (Emit.sliceLabs r4 G off Lg) := by
    unfold FiltRec.labSum Emit.labAdd; rfl
  obtain ⟨CAP, hCAP⟩ : ∃ x, x = FiltRec.labSum (Emit.sliceLabs r4 G off Lg) := ⟨_, rfl⟩
  obtain ⟨LL, hLL⟩ : ∃ x, x = ((Emit.sliceLabs r4 G off Lg).flatMap FiltRec.labE).length := ⟨_, rfl⟩
  rw [← hCAP, ← hLL] at hac ⊢
  rw [← hCAP] at hlabs
  have e1 := FinalPass.Hash4.wcopyR_spec cap (P 1) (P 137) (P 160) (hne (by decide)) (hne (by decide))
    (hne (by decide)) σ (z 137 (by decide) (by decide)) h160 (by omega)
  rw [h1] at e1
  have e2 := FinalPass.Hash4.wcopyR_spec cap (P 2) (P 138) (P 160) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (σ.setv (P 137) r4) (by simp [hR, z 138 (by decide) (by decide)]) (by simp [hR, h160])
    (by simp [hR, h2]; omega)
  rw [show (σ.setv (P 137) r4).val (P 2) = G by simp [hR, h2]] at e2
  have e3 := FinalPass.Hash4.wcopyR_spec cap (P 3) (P 139) (P 160) (hne (by decide)) (hne (by decide))
    (hne (by decide)) ((σ.setv (P 137) r4).setv (P 138) G) (by simp [hR, z 139 (by decide) (by decide)])
    (by simp [hR, h160]) (by simp [hR, h3]; omega)
  rw [show ((σ.setv (P 137) r4).setv (P 138) G).val (P 3) = off by simp [hR, h3]] at e3
  have e4 := FinalPass.Hash4.wcopyR_spec cap (P 4) (P 140) (P 160) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (((σ.setv (P 137) r4).setv (P 138) G).setv (P 139) off)
    (by simp [hR, z 140 (by decide) (by decide)]) (by simp [hR, h160]) (by simp [hR, h4]; omega)
  rw [show (((σ.setv (P 137) r4).setv (P 138) G).setv (P 139) off).val (P 4) = Lg by simp [hR, h4]] at e4
  set τ := (((σ.setv (P 137) r4).setv (P 138) G).setv (P 139) off).setv (P 140) Lg with hτ
  have e5 := StarNums.incN_spec cap (P 147) 5 τ (by simp [hτ, hR, z 147 (by decide) (by decide)]; omega)
  rw [show τ.val (P 147) + 5 = 5 by simp [hτ, hR, z 147 (by decide) (by decide)]] at e5
  have e6 := Emit.labsW_spec cap D (Le P) (τ.setv (P 147) 5) r4 G off Lg 5
    (by rw [Le_apply]; simp [hτ, hR]) (by rw [Le_apply]; simp [hτ, hR]) (by rw [Le_apply]; simp [hτ, hR])
    (by rw [Le_apply]; simp [hτ, hR]) (by rw [Le_apply]; simp [hτ, hR, z 141 (by decide) (by decide)])
    (by rw [Le_apply]; simp [hτ, hR, z 142 (by decide) (by decide)])
    (by rw [Le_apply]; simp [hτ, hR, z 143 (by decide) (by decide)])
    (by rw [Le_apply]; simp [hτ, hR, z 144 (by decide) (by decide)])
    (by rw [Le_apply]; simp [hτ, hR, z 145 (by decide) (by decide)])
    (by rw [Le_apply]; simp [hτ, hR, z 146 (by decide) (by decide)])
    (by rw [Le_apply]; simp [hτ, hR, z 148 (by decide) (by decide)]) (by rw [Le_apply]; simp [hτ, hR])
    (by simp [hτ, hD]) Mlab hM (by rw [Le_apply]; simp [hτ, hR, z 136 (by decide) (by decide)]; omega)
  have hL0 : Le P 0 = P 136 := rfl
  have hL11 : Le P 11 = P 147 := rfl
  rw [hL0, hL11, hlabs] at e6
  set ρ := (appendO (τ.setv (P 147) 5) D (P 136) ((Emit.sliceLabs r4 G off Lg).flatMap FiltRec.labE)).setv (P 147) CAP
    with hρ
  have hρ136 : ρ.val (P 136) = LL := by simp [hρ, hτ, hR, z 136 (by decide) (by decide), hLL]
  have e7 := ParseNat.addTo_spec cap (P 147) (P 99) (P 160) (hne (by decide)) (hne (by decide)) (hne (by decide)) ρ
    (by simp [hρ, hτ, hR, h160]) (by simp [hρ]; omega) (by simp [hρ, hτ, hR, h99]; omega)
  rw [show ρ.val (P 99) + ρ.val (P 147) = CAP by simp [hρ, hτ, hR, h99], show ρ.val (P 147) = CAP by simp [hρ]] at e7
  have hρ100 : ρ.val (P 100) = 0 := by simp [hρ, hτ, hR, h100]
  have r136 : (ρ.setv (P 99) CAP).val (P 136) = LL := by
    rw [wsetv_val_ne _ _ (hne (by decide : (136 : Fin 200) ≠ 99)), hρ136]
  have r100 : (ρ.setv (P 99) CAP).val (P 100) = 0 := by
    rw [wsetv_val_ne _ _ (hne (by decide : (100 : Fin 200) ≠ 99)), hρ100]
  have e8 := ParseNat.addTo_spec cap (P 136) (P 100) (P 160) (hne (by decide)) (hne (by decide)) (hne (by decide))
    (ρ.setv (P 99) CAP) (by simp [hρ, hτ, hR, h160]) (by rw [r136]; omega) (by rw [r136, r100]; omega)
  rw [r136, r100, Nat.zero_add] at e8
  refine ⟨_, WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6
    (WExec.seq e7 e8))))))) ?_ le_rfl, ?_⟩
  · simp only [hρ, hτ]
    rw [← appendO_setv _ D (P 136) (P 147) (hne (by decide)), wsetv_setv]
    rw [appendO_setv _ D (P 136) (P 147) (hne (by decide))]
    apply WState.eq
    · simp [appendO]
    · simp [appendO]
    · funext x
      simp only [appendO, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
      by_cases x136 : x = P 136
      · subst x136; simp [hR, z 136 (by decide) (by decide)]
      · by_cases x137 : x = P 137
        · subst x137; simp [hR]
        · by_cases x138 : x = P 138
          · subst x138; simp [hR]
          · by_cases x139 : x = P 139
            · subst x139; simp [hR]
            · by_cases x140 : x = P 140
              · subst x140; simp [hR]
              · simp [x136, x137, x138, x139, x140]
    · simp [appendO]
  · have hsc : r4 + G + off + Lg ≤ cap := by omega
    omega

end Phases2

section Phases4
variable {ns nr : ℕ} (cap : ℕ) (P : Fin 200 ↪ Fin nr)

/-- The small arithmetic block (`0 L`, `1 lw`, `2 c`, `3 8L+2`, `4`, `5` constants). -/
def Zce : Fin 8 ↪ Fin nr := (shiftE 149 8 200 (by norm_num)).trans P

/-- `c = 4·lw + 4L + 4`, `X = 8L + 2`. -/
def cOps : List (AOp 8) := [.inc 4 4, .inc 5 8, .mul 1 4 2, .mul 0 4 2, .inc 2 4, .mul 0 5 3, .inc 3 2]

theorem cOps_vals (w : Fin 8 → ℕ) (h2 : w 2 = 0) (h3 : w 3 = 0) (h4 : w 4 = 0) (h5 : w 5 = 0) :
    evalL w cOps 2 = 4 * (w 1 + w 0 + 1) ∧ evalL w cOps 3 = 8 * w 0 + 2 := by
  simp only [cOps, evalL, AOp.eval, Function.update_apply]
  simp (config := { decide := true }) only [↓reduceIte, Fin.isValue]
  simp only [h2, h3, h4, h5]
  constructor <;> ring

theorem cOps_eq (w : Fin 8 → ℕ) (h2 : w 2 = 0) (h3 : w 3 = 0) (h4 : w 4 = 0) (h5 : w 5 = 0) (j : Fin 8) :
    evalL w cOps j = ![w 0, w 1, 4 * (w 1 + w 0 + 1), 8 * w 0 + 2, 4, 8, w 6, w 7] j := by
  simp only [cOps, evalL, AOp.eval, Function.update_apply]
  fin_cases j <;> simp (config := { decide := true }) [h2, h3, h4, h5] <;> ring

/-- The power's registers: `0 = X` (`P 152`), `1 = Q` (`P 105`), `2` scratch (`P 157`). -/
def Z3e : Fin 3 ↪ Fin nr := (⟨![152, 105, 157], by decide⟩ : Fin 3 ↪ Fin 200).trans P

/-- **Phase 4**: `c` into `P 151`, `X = 8L + 2` into `P 152`, `Q = X^d` into `P 105`. -/
def ph4 : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (P 45) (P 149) (P 160))
  (.seq (progL (Zce P) (P 160) (P 161) cOps)
  (powW (Z3e P) (P 158) (P 160) (P 161) (P 97)))

theorem ph4_spec (σ : WState ns nr) (L lw d : ℕ) (h45 : σ.val (P 45) = L) (h150 : σ.val (P 150) = lw)
    (h97 : σ.val (P 97) = d) (hz : ∀ j : Fin 200, (j.val = 149 ∨ (151 ≤ j.val ∧ j.val ≤ 158)) → σ.val (P j) = 0)
    (h105 : σ.val (P 105) = 0) (h160 : σ.val (P 160) = 0) (h161 : σ.val (P 161) = 0)
    (hcap : (8 * L + 2) ^ d * (8 * L + 2) + 2 ≤ cap) (hc : 4 * (lw + L + 1) + 8 ≤ cap) (hdc : d ≤ cap)
    (hlw : lw ≤ cap) :
    ∃ n, WExec cap (ph4 P) σ
      ((setZ (Zce P) (σ.setv (P 149) L) (evalL (fun i => (σ.setv (P 149) L).val (Zce P i)) cOps)).setv (P 105)
        ((8 * L + 2) ^ d)) n ∧
      n ≤ 18 * L + 400 * (cap + 1) * (cap + 1) + d * (40 * (cap + 1) * (cap + 1) + 20) + 20 * cap + 30 := by
  have hR : ∀ i j : Fin 200, P i = P j ↔ i = j := fun i j => P.injective.eq_iff
  have hne : ∀ {i j : Fin 200}, i ≠ j → P i ≠ P j := fun h => P.injective.ne h
  have hX : 8 * L + 2 ≤ (8 * L + 2) ^ d * (8 * L + 2) := Nat.le_mul_of_pos_left _ (pow_pos (by omega) d)
  have hLc : L ≤ cap := by omega
  have e1 := FinalPass.Hash4.wcopyR_spec cap (P 45) (P 149) (P 160) (hne (by decide)) (hne (by decide))
    (hne (by decide)) σ (hz 149 (Or.inl rfl)) h160 (by rw [h45]; exact hLc)
  rw [h45] at e1
  set τ := σ.setv (P 149) L with hτ
  set w : Fin 8 → ℕ := fun i => τ.val (Zce P i) with hw
  have hZ : ∀ i, Zce P i ≠ P 160 ∧ Zce P i ≠ P 161 := fun i =>
    ⟨hne (Fin.ne_of_val_ne (by simp [shiftE]; omega)), hne (Fin.ne_of_val_ne (by simp [shiftE]; omega))⟩
  have hw0 : w 0 = L := by simp [hw, hτ, Zce, shiftE]
  have hw1 : w 1 = lw := by
    simp only [hw, hτ, Zce, shiftE, Function.Embedding.trans_apply, Function.Embedding.coeFn_mk]
    rw [wsetv_val_ne _ _ (hne (by decide))]; exact h150
  have hwz : ∀ i : Fin 8, 2 ≤ i.val → w i = 0 := fun i hi => by
    simp only [hw, hτ, Zce, shiftE, Function.Embedding.trans_apply, Function.Embedding.coeFn_mk]
    rw [wsetv_val_ne _ _ (hne (Fin.ne_of_val_ne (by simp; omega)))]
    exact hz _ (Or.inr ⟨by simp; omega, by simp; omega⟩)
  obtain ⟨hc2, hc3⟩ := cOps_vals w (hwz 2 (by decide)) (hwz 3 (by decide)) (hwz 4 (by decide)) (hwz 5 (by decide))
  rw [hw0, hw1] at hc2
  rw [hw0] at hc3
  have hself : setZ (Zce P) τ w = τ := setZ_self τ w fun _ => rfl
  obtain ⟨n2, e2, b2⟩ := progL_spec cap (Zce P) (P 160) (P 161) hZ (hne (by decide)) cOps τ w
    (by simp [hτ, hR, h160]) (by simp [hτ, hR, h161]) (fun o ho => by
      simp only [cOps, List.mem_cons, List.mem_nil_iff, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [AOp.dist] <;> decide)
    (fun i => by
      rw [cOps_eq w (hwz 2 (by decide)) (hwz 3 (by decide)) (hwz 4 (by decide)) (hwz 5 (by decide)) i]
      fin_cases i <;> simp [hw0, hw1, hwz 6 (by decide), hwz 7 (by decide)] <;> omega)
  rw [hself] at e2
  set τ2 := setZ (Zce P) τ (evalL w cOps) with hτ2
  have r152 : τ2.val (P 152) = 8 * L + 2 := by rw [hτ2]; exact (setZ_val_Z τ _ 3).trans hc3
  have hout : ∀ j : Fin 200, (j.val < 149 ∨ 157 ≤ j.val) → τ2.val (P j) = τ.val (P j) := fun j hj => by
    rw [hτ2]; exact setZ_val_other τ _ (P j) fun i => hne (Fin.ne_of_val_ne (by simp [shiftE]; omega))
  obtain ⟨n3, e3, b3⟩ := powW_spec cap (Z3e P) (P 158) (P 160) (P 161) (P 97)
    (fun i => by fin_cases i <;> exact ⟨hne (by decide), hne (by decide), hne (by decide), hne (by decide)⟩)
    (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)) τ2 (8 * L + 2) d
    r152 (by rw [show Z3e P 1 = P 105 from rfl, hout 105 (Or.inl (by decide))]; simp [hτ, hR, h105])
    (by rw [show Z3e P 2 = P 157 from rfl, hout 157 (Or.inr (by decide))]; simp [hτ, hR, hz 157 (Or.inr ⟨by decide, by decide⟩)])
    (by rw [hout 97 (Or.inl (by decide))]; simp [hτ, hR, h97])
    (by rw [hout 158 (Or.inr (by decide))]; simp [hτ, hR, hz 158 (Or.inr ⟨by decide, by decide⟩)])
    (by rw [hout 160 (Or.inr (by decide))]; simp [hτ, hR, h160])
    (by rw [hout 161 (Or.inr (by decide))]; simp [hτ, hR, h161]) hcap (by omega) hdc
  refine ⟨_, WExec.seq e1 (WExec.seq e2 e3), ?_⟩
  have hcost : costL cap cOps ≤ 400 * (cap + 1) * (cap + 1) := by
    simp only [cOps, costL, AOp.cost]
    nlinarith
  omega

end Phases4

section Phases5
variable {ns nr : ℕ} (cap : ℕ) (P : Fin 200 ↪ Fin nr)

/-- The capacity program's registers (`PopNums`). -/
def Zne : Fin 40 ↪ Fin nr := (shiftE 96 40 200 (by norm_num)).trans P

/-- The capacity program's inputs. -/
def vIn (L d c CAP LL M Mlab n lw Q : ℕ) : Fin 40 → ℕ := fun i =>
  if i.val = 0 then L else if i.val = 1 then d else if i.val = 2 then c else if i.val = 3 then CAP
  else if i.val = 4 then LL else if i.val = 5 then M else if i.val = 6 then Mlab else if i.val = 7 then n
  else if i.val = 8 then lw else if i.val = 9 then Q else 0

theorem vIn_zero (L d c CAP LL M Mlab n lw Q : ℕ) (i : Fin 40) (hi : 10 ≤ i.val) :
    vIn L d c CAP LL M Mlab n lw Q i = 0 := by
  unfold vIn; split_ifs <;> omega

/-- **Phase 5**: the capacity program's inputs copied in, then `PopNums.numOps`. -/
def ph5 : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (P 45) (P 96) (P 160))
  (.seq (FinalPass.Hash4.wcopyR (P 151) (P 98) (P 160))
  (.seq (FinalPass.Hash4.wcopyR (P 44) (P 101) (P 160))
  (.seq (FinalPass.Hash4.wcopyR (P 180) (P 102) (P 160))
  (.seq (FinalPass.Hash4.wcopyR (P 52) (P 103) (P 160))
  (progL (Zne P) (P 160) (P 161) PopNums.numOps)))))

theorem ph5_spec (σ : WState ns nr) (L d c CAP LL M Mlab n lw Q : ℕ) (h45 : σ.val (P 45) = L)
    (h151 : σ.val (P 151) = c) (h44 : σ.val (P 44) = M) (h180 : σ.val (P 180) = Mlab) (h52 : σ.val (P 52) = n)
    (h97 : σ.val (P 97) = d) (h99 : σ.val (P 99) = CAP) (h100 : σ.val (P 100) = LL) (h104 : σ.val (P 104) = lw)
    (h105 : σ.val (P 105) = Q) (hz : ∀ j : Fin 200, (j.val = 96 ∨ j.val = 98 ∨ (101 ≤ j.val ∧ j.val ≤ 103) ∨
      (106 ≤ j.val ∧ j.val ≤ 135)) → σ.val (P j) = 0) (h160 : σ.val (P 160) = 0) (h161 : σ.val (P 161) = 0)
    (hin : L + c + M + Mlab + n ≤ cap)
    (hcap : ∀ i, evalL (vIn L d c CAP LL M Mlab n lw Q) PopNums.numOps i ≤ cap) :
    ∃ m, WExec cap (ph5 P) σ
      (setZ (Zne P) ((((((σ.setv (P 96) L).setv (P 98) c).setv (P 101) M).setv (P 102) Mlab).setv (P 103) n))
        (evalL (vIn L d c CAP LL M Mlab n lw Q) PopNums.numOps)) m ∧
      m ≤ 18 * (L + c + M + Mlab + n) + costL cap PopNums.numOps + 30 := by
  have hR : ∀ i j : Fin 200, P i = P j ↔ i = j := fun i j => P.injective.eq_iff
  have hne : ∀ {i j : Fin 200}, i ≠ j → P i ≠ P j := fun h => P.injective.ne h
  have e1 := FinalPass.Hash4.wcopyR_spec cap (P 45) (P 96) (P 160) (hne (by decide)) (hne (by decide))
    (hne (by decide)) σ (hz 96 (Or.inl rfl)) h160 (by omega)
  rw [h45] at e1
  have e2 := FinalPass.Hash4.wcopyR_spec cap (P 151) (P 98) (P 160) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (σ.setv (P 96) L) (by simp [hR, hz 98 (Or.inr (Or.inl rfl))]) (by simp [hR, h160])
    (by simp [hR, h151]; omega)
  rw [show (σ.setv (P 96) L).val (P 151) = c by simp [hR, h151]] at e2
  have e3 := FinalPass.Hash4.wcopyR_spec cap (P 44) (P 101) (P 160) (hne (by decide)) (hne (by decide))
    (hne (by decide)) ((σ.setv (P 96) L).setv (P 98) c)
    (by simp [hR, hz 101 (Or.inr (Or.inr (Or.inl ⟨by decide, by decide⟩)))]) (by simp [hR, h160])
    (by simp [hR, h44]; omega)
  rw [show ((σ.setv (P 96) L).setv (P 98) c).val (P 44) = M by simp [hR, h44]] at e3
  have e4 := FinalPass.Hash4.wcopyR_spec cap (P 180) (P 102) (P 160) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (((σ.setv (P 96) L).setv (P 98) c).setv (P 101) M)
    (by simp [hR, hz 102 (Or.inr (Or.inr (Or.inl ⟨by decide, by decide⟩)))]) (by simp [hR, h160])
    (by simp [hR, h180]; omega)
  rw [show (((σ.setv (P 96) L).setv (P 98) c).setv (P 101) M).val (P 180) = Mlab by simp [hR, h180]] at e4
  have e5 := FinalPass.Hash4.wcopyR_spec cap (P 52) (P 103) (P 160) (hne (by decide)) (hne (by decide))
    (hne (by decide)) ((((σ.setv (P 96) L).setv (P 98) c).setv (P 101) M).setv (P 102) Mlab)
    (by simp [hR, hz 103 (Or.inr (Or.inr (Or.inl ⟨by decide, by decide⟩)))]) (by simp [hR, h160])
    (by simp [hR, h52]; omega)
  rw [show ((((σ.setv (P 96) L).setv (P 98) c).setv (P 101) M).setv (P 102) Mlab).val (P 52) = n by
    simp [hR, h52]] at e5
  set τ := ((((σ.setv (P 96) L).setv (P 98) c).setv (P 101) M).setv (P 102) Mlab).setv (P 103) n with hτ
  have hZ : ∀ i, Zne P i ≠ P 160 ∧ Zne P i ≠ P 161 := fun i =>
    ⟨hne (Fin.ne_of_val_ne (by simp [shiftE]; omega)), hne (Fin.ne_of_val_ne (by simp [shiftE]; omega))⟩
  have hv : (fun i => τ.val (Zne P i)) = vIn L d c CAP LL M Mlab n lw Q := by
    funext i
    simp only [Zne, shiftE, Function.Embedding.trans_apply, Function.Embedding.coeFn_mk, vIn]
    fin_cases i <;> simp [hτ, hR, h97, h99, h100, h104, h105] <;>
      exact hz _ (Or.inr (Or.inr (Or.inr ⟨by decide, by decide⟩)))
  have hself : setZ (Zne P) τ (vIn L d c CAP LL M Mlab n lw Q) = τ := by
    rw [← hv]; exact setZ_self τ _ fun _ => rfl
  obtain ⟨m6, e6, b6⟩ := progL_spec cap (Zne P) (P 160) (P 161) hZ (hne (by decide)) PopNums.numOps τ
    (vIn L d c CAP LL M Mlab n lw Q) (by simp [hτ, hR, h160]) (by simp [hτ, hR, h161])
    (fun o ho => by
      simp only [PopNums.numOps, PopNums.constOps, PopNums.blOps, PopNums.rOps, PopNums.pwOps, List.cons_append,
        List.nil_append, List.mem_cons, List.mem_nil_iff, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [AOp.dist] <;> decide)
    hcap
  rw [hself] at e6
  refine ⟨_, WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 e6)))), ?_⟩
  omega

end Phases5

section Phases6
variable {ns nr : ℕ} (cap : ℕ) (P : Fin 200 ↪ Fin nr)

/-- The visit sizes' registers (`0 J`, `1 L`, `2 n`, `5 VW`, `7 TW`, `8` the constant `2`). -/
def Zve : Fin 9 ↪ Fin nr := (shiftE 162 9 200 (by norm_num)).trans P

/-- `VW = (J+1)(2L+1)`, `TW = n·(1 + VW)`. -/
def vOps : List (AOp 9) :=
  [.add 0 3, .inc 3 1, .inc 8 2, .mul 1 8 4, .inc 4 1, .mul 3 4 5, .add 5 6, .inc 6 1, .mul 2 6 7]

theorem vOps_eq (w : Fin 9 → ℕ) (hz : ∀ i : Fin 9, 3 ≤ i.val → w i = 0) (j : Fin 9) :
    evalL w vOps j = ![w 0, w 1, w 2, w 0 + 1, 2 * w 1 + 1, (w 0 + 1) * (2 * w 1 + 1),
      (w 0 + 1) * (2 * w 1 + 1) + 1, w 2 * ((w 0 + 1) * (2 * w 1 + 1) + 1), 2] j := by
  have h3 := hz 3 (by decide); have h4 := hz 4 (by decide); have h5 := hz 5 (by decide)
  have h6 := hz 6 (by decide); have h7 := hz 7 (by decide); have h8 := hz 8 (by decide)
  simp only [vOps, evalL, AOp.eval, Function.update_apply]
  fin_cases j <;> simp (config := { decide := true }) only [↓reduceIte, Fin.isValue, Fin.mk_one, Fin.zero_eta,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.reduceFinMk] <;>
    simp only [h3, h4, h5, h6, h7, h8] <;> ring

/-- Phase 6, part A: the visit sizes. -/
def ph6A : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (P 21) (P 162) (P 160))
  (.seq (FinalPass.Hash4.wcopyR (P 45) (P 163) (P 160))
  (.seq (FinalPass.Hash4.wcopyR (P 52) (P 164) (P 160))
  (progL (Zve P) (P 160) (P 161) vOps)))

/-- Phase 6, part B: `4L`, `d`, `c + 1` into `X`. -/
def ph6B : WM ns nr :=
  .seq (ParseNat.addTo (P 45) (P 13) (P 160)) (.seq (ParseNat.addTo (P 45) (P 13) (P 160))
  (.seq (ParseNat.addTo (P 45) (P 13) (P 160)) (.seq (ParseNat.addTo (P 45) (P 13) (P 160))
  (.seq (ParseNat.addTo (P 97) (P 14) (P 160)) (.seq (ParseNat.addTo (P 151) (P 51) (P 160))
  (StarNums.incN (P 51) 1))))))

/-- Phase 6, part C: `R`, `Lg`, `cap`, `VW`, `TW` into `X`. -/
def ph6C : WM ns nr :=
  .seq (ParseNat.addTo (P 108) (P 54) (P 160)) (.seq (ParseNat.addTo (P 118) (P 55) (P 160))
  (.seq (ParseNat.addTo (P 110) (P 56) (P 160)) (.seq (ParseNat.addTo (P 167) (P 57) (P 160))
  (ParseNat.addTo (P 169) (P 58) (P 160)))))

/-- **Phase 6**: the visit sizes, then the record's numbers into `X`. -/
def ph6 : WM ns nr := .seq (ph6A P) (.seq (ph6B P) (ph6C P))

end Phases6

section Phases6s
variable {ns nr : ℕ} (cap : ℕ) (P : Fin 200 ↪ Fin nr)

/-- The state after phase 6's visit sizes (`J`, `L`, `n` copied, the sizes computed). -/
noncomputable def ph6mid (σ : WState ns nr) (J L n : ℕ) : WState ns nr :=
  setZ (Zve P) (((σ.setv (P 162) J).setv (P 163) L).setv (P 164) n)
    (evalL (fun i => (((σ.setv (P 162) J).setv (P 163) L).setv (P 164) n).val (Zve P i)) vOps)

theorem ph6mid_rd (σ : WState ns nr) (J L n : ℕ) (j : Fin 200) (hj : j.val < 162) :
    (ph6mid P σ J L n).val (P j) = σ.val (P j) := by
  have hne : ∀ {i j : Fin 200}, i ≠ j → P i ≠ P j := fun h => P.injective.ne h
  rw [ph6mid, setZ_val_other (Z := Zve P) _ _ _ fun i => hne (Fin.ne_of_val_ne (by simp [shiftE]; omega))]
  rw [wsetv_val_ne _ _ (hne (Fin.ne_of_val_ne (show j.val ≠ 164 by omega))),
    wsetv_val_ne _ _ (hne (Fin.ne_of_val_ne (show j.val ≠ 163 by omega))),
    wsetv_val_ne _ _ (hne (Fin.ne_of_val_ne (show j.val ≠ 162 by omega)))]

theorem ph6mid_w (σ : WState ns nr) (J L n : ℕ) (zz : ∀ j : Fin 200, 162 ≤ j.val → j.val ≤ 170 → σ.val (P j) = 0) :
    let w : Fin 9 → ℕ := fun i => (((σ.setv (P 162) J).setv (P 163) L).setv (P 164) n).val (Zve P i)
    w 0 = J ∧ w 1 = L ∧ w 2 = n ∧ ∀ i : Fin 9, 3 ≤ i.val → w i = 0 := by
  have hne : ∀ {i j : Fin 200}, i ≠ j → P i ≠ P j := fun h => P.injective.ne h
  intro w
  refine ⟨by simp [w, Zve, shiftE], by simp [w, Zve, shiftE], by simp [w, Zve, shiftE], fun i hi => ?_⟩
  simp only [w, Zve, shiftE, Function.Embedding.trans_apply, Function.Embedding.coeFn_mk]
  rw [wsetv_val_ne _ _ (hne (Fin.ne_of_val_ne (by simp; omega))),
    wsetv_val_ne _ _ (hne (Fin.ne_of_val_ne (by simp; omega))),
    wsetv_val_ne _ _ (hne (Fin.ne_of_val_ne (by simp; omega)))]
  exact zz _ (by simp) (by simp; omega)

theorem ph6mid_167 (σ : WState ns nr) (J L n : ℕ) (zz : ∀ j : Fin 200, 162 ≤ j.val → j.val ≤ 170 → σ.val (P j) = 0) :
    (ph6mid P σ J L n).val (P 167) = (J + 1) * (2 * L + 1) := by
  obtain ⟨hw0, hw1, _, hwz⟩ := ph6mid_w P σ J L n zz
  rw [ph6mid]
  refine (setZ_val_Z _ _ 5).trans ?_
  rw [vOps_eq _ hwz 5]
  simp [hw0, hw1]

theorem ph6mid_169 (σ : WState ns nr) (J L n : ℕ) (zz : ∀ j : Fin 200, 162 ≤ j.val → j.val ≤ 170 → σ.val (P j) = 0) :
    (ph6mid P σ J L n).val (P 169) = n * ((J + 1) * (2 * L + 1) + 1) := by
  obtain ⟨hw0, hw1, hw2, hwz⟩ := ph6mid_w P σ J L n zz
  rw [ph6mid]
  refine (setZ_val_Z _ _ 7).trans ?_
  rw [vOps_eq _ hwz 7]
  simp [hw0, hw1, hw2]

theorem ph6A_spec (σ : WState ns nr) (J L n : ℕ) (h21 : σ.val (P 21) = J) (h45 : σ.val (P 45) = L)
    (h52 : σ.val (P 52) = n) (zz : ∀ j : Fin 200, 162 ≤ j.val → j.val ≤ 170 → σ.val (P j) = 0)
    (h160 : σ.val (P 160) = 0) (h161 : σ.val (P 161) = 0) (hcJ : J ≤ cap) (hcL : L ≤ cap) (hcn : n ≤ cap)
    (h2c : 2 ≤ cap) (hcV : (J + 1) * (2 * L + 1) + 1 ≤ cap) (hcT : n * ((J + 1) * (2 * L + 1) + 1) ≤ cap) :
    ∃ m, WExec cap (ph6A P) σ (ph6mid P σ J L n) m ∧ m ≤ costL cap vOps + 18 * (J + L + n) + 12 := by
  have hR : ∀ i j : Fin 200, P i = P j ↔ i = j := fun i j => P.injective.eq_iff
  have hne : ∀ {i j : Fin 200}, i ≠ j → P i ≠ P j := fun h => P.injective.ne h
  have hJ1 : J + 1 ≤ (J + 1) * (2 * L + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hL1 : 2 * L + 1 ≤ (J + 1) * (2 * L + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have e1 := FinalPass.Hash4.wcopyR_spec cap (P 21) (P 162) (P 160) (hne (by decide)) (hne (by decide))
    (hne (by decide)) σ (zz 162 (by decide) (by decide)) h160 (by rw [h21]; exact hcJ)
  rw [h21] at e1
  have e2 := FinalPass.Hash4.wcopyR_spec cap (P 45) (P 163) (P 160) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (σ.setv (P 162) J) (by simp [hR, zz 163 (by decide) (by decide)]) (by simp [hR, h160])
    (by simp [hR, h45]; omega)
  rw [show (σ.setv (P 162) J).val (P 45) = L by simp [hR, h45]] at e2
  have e3 := FinalPass.Hash4.wcopyR_spec cap (P 52) (P 164) (P 160) (hne (by decide)) (hne (by decide))
    (hne (by decide)) ((σ.setv (P 162) J).setv (P 163) L) (by simp [hR, zz 164 (by decide) (by decide)])
    (by simp [hR, h160]) (by simp [hR, h52]; omega)
  rw [show ((σ.setv (P 162) J).setv (P 163) L).val (P 52) = n by simp [hR, h52]] at e3
  have hZ : ∀ i, Zve P i ≠ P 160 ∧ Zve P i ≠ P 161 := fun i =>
    ⟨hne (Fin.ne_of_val_ne (by simp [shiftE]; omega)), hne (Fin.ne_of_val_ne (by simp [shiftE]; omega))⟩
  obtain ⟨hw0, hw1, hw2, hwz⟩ := ph6mid_w P σ J L n zz
  set τ := ((σ.setv (P 162) J).setv (P 163) L).setv (P 164) n with hτ
  have hself : setZ (Zve P) τ (fun i => τ.val (Zve P i)) = τ := setZ_self τ _ fun _ => rfl
  obtain ⟨m4, e4, b4⟩ := progL_spec cap (Zve P) (P 160) (P 161) hZ (hne (by decide)) vOps τ (fun i => τ.val (Zve P i))
    (by simp [hτ, hR, h160]) (by simp [hτ, hR, h161])
    (fun o ho => by
      simp only [vOps, List.mem_cons, List.mem_nil_iff, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [AOp.dist] <;> decide)
    (fun i => by
      rw [vOps_eq _ hwz i]
      fin_cases i <;> simp [hw0, hw1, hw2] <;> omega)
  rw [hself] at e4
  exact ⟨_, WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4)), by omega⟩

theorem ph6B_spec (ρ : WState ns nr) (L d c : ℕ) (h45 : ρ.val (P 45) = L) (h97 : ρ.val (P 97) = d)
    (h151 : ρ.val (P 151) = c) (h13 : ρ.val (P 13) = 0) (h14 : ρ.val (P 14) = 0) (h51 : ρ.val (P 51) = 0)
    (h160 : ρ.val (P 160) = 0) (hcL : 4 * L ≤ cap) (hcd : d ≤ cap) (hcc : c + 1 ≤ cap) :
    ∃ m, WExec cap (ph6B P) ρ (((ρ.setv (P 13) (4 * L)).setv (P 14) d).setv (P 51) (c + 1)) m ∧
      m ≤ 18 * (4 * L + d + c) + 50 := by
  have hR : ∀ i j : Fin 200, P i = P j ↔ i = j := fun i j => P.injective.eq_iff
  have hne : ∀ {i j : Fin 200}, i ≠ j → P i ≠ P j := fun h => P.injective.ne h
  have e1 := ParseNat.addTo_spec cap (P 45) (P 13) (P 160) (hne (by decide)) (hne (by decide)) (hne (by decide)) ρ
    h160 (by rw [h45]; omega) (by rw [h45, h13]; omega)
  rw [h45, h13, Nat.zero_add] at e1
  have e2 := ParseNat.addTo_spec cap (P 45) (P 13) (P 160) (hne (by decide)) (hne (by decide)) (hne (by decide))
    (ρ.setv (P 13) L) (by simp [hR, h160]) (by simp [hR, h45]; omega) (by simp [hR, h45]; omega)
  rw [show (ρ.setv (P 13) L).val (P 13) + (ρ.setv (P 13) L).val (P 45) = L + L by simp [hR, h45],
    show (ρ.setv (P 13) L).val (P 45) = L by simp [hR, h45], wsetv_setv] at e2
  have e3 := ParseNat.addTo_spec cap (P 45) (P 13) (P 160) (hne (by decide)) (hne (by decide)) (hne (by decide))
    (ρ.setv (P 13) (L + L)) (by simp [hR, h160]) (by simp [hR, h45]; omega) (by simp [hR, h45]; omega)
  rw [show (ρ.setv (P 13) (L + L)).val (P 13) + (ρ.setv (P 13) (L + L)).val (P 45) = L + L + L by simp [hR, h45],
    show (ρ.setv (P 13) (L + L)).val (P 45) = L by simp [hR, h45], wsetv_setv] at e3
  have e4 := ParseNat.addTo_spec cap (P 45) (P 13) (P 160) (hne (by decide)) (hne (by decide)) (hne (by decide))
    (ρ.setv (P 13) (L + L + L)) (by simp [hR, h160]) (by simp [hR, h45]; omega) (by simp [hR, h45]; omega)
  rw [show (ρ.setv (P 13) (L + L + L)).val (P 13) + (ρ.setv (P 13) (L + L + L)).val (P 45) = 4 * L by
      simp [hR, h45]; ring,
    show (ρ.setv (P 13) (L + L + L)).val (P 45) = L by simp [hR, h45], wsetv_setv] at e4
  have e5 := ParseNat.addTo_spec cap (P 97) (P 14) (P 160) (hne (by decide)) (hne (by decide)) (hne (by decide))
    (ρ.setv (P 13) (4 * L)) (by simp [hR, h160]) (by simp [hR, h97]; omega) (by simp [hR, h97, h14]; omega)
  rw [show (ρ.setv (P 13) (4 * L)).val (P 14) + (ρ.setv (P 13) (4 * L)).val (P 97) = d by simp [hR, h97, h14],
    show (ρ.setv (P 13) (4 * L)).val (P 97) = d by simp [hR, h97]] at e5
  have e6 := ParseNat.addTo_spec cap (P 151) (P 51) (P 160) (hne (by decide)) (hne (by decide)) (hne (by decide))
    ((ρ.setv (P 13) (4 * L)).setv (P 14) d) (by simp [hR, h160]) (by simp [hR, h151]; omega)
    (by simp [hR, h151, h51]; omega)
  rw [show ((ρ.setv (P 13) (4 * L)).setv (P 14) d).val (P 51) + ((ρ.setv (P 13) (4 * L)).setv (P 14) d).val (P 151) =
      c by simp [hR, h151, h51],
    show ((ρ.setv (P 13) (4 * L)).setv (P 14) d).val (P 151) = c by simp [hR, h151]] at e6
  have e7 := StarNums.incN_spec cap (P 51) 1 (((ρ.setv (P 13) (4 * L)).setv (P 14) d).setv (P 51) c) (by simp; omega)
  rw [wsetv_setv, show (((ρ.setv (P 13) (4 * L)).setv (P 14) d).setv (P 51) c).val (P 51) + 1 = c + 1 by simp] at e7
  exact ⟨_, WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6 e7))))), by omega⟩

theorem ph6C_spec (κ : WState ns nr) (R Lg cp VW TW : ℕ) (h108 : κ.val (P 108) = R) (h118 : κ.val (P 118) = Lg)
    (h110 : κ.val (P 110) = cp) (h167 : κ.val (P 167) = VW) (h169 : κ.val (P 169) = TW)
    (hz : ∀ j : Fin 200, 54 ≤ j.val → j.val ≤ 58 → κ.val (P j) = 0) (h160 : κ.val (P 160) = 0)
    (hcR : R ≤ cap) (hcLg : Lg ≤ cap) (hccp : cp ≤ cap) (hcV : VW ≤ cap) (hcT : TW ≤ cap) :
    ∃ m, WExec cap (ph6C P) κ (((((κ.setv (P 54) R).setv (P 55) Lg).setv (P 56) cp).setv (P 57) VW).setv (P 58) TW) m ∧
      m ≤ 18 * (R + Lg + cp + VW + TW) + 30 := by
  have hR : ∀ i j : Fin 200, P i = P j ↔ i = j := fun i j => P.injective.eq_iff
  have hne : ∀ {i j : Fin 200}, i ≠ j → P i ≠ P j := fun h => P.injective.ne h
  have z54 := hz 54 (by decide) (by decide); have z55 := hz 55 (by decide) (by decide)
  have z56 := hz 56 (by decide) (by decide); have z57 := hz 57 (by decide) (by decide)
  have z58 := hz 58 (by decide) (by decide)
  have e1 := ParseNat.addTo_spec cap (P 108) (P 54) (P 160) (hne (by decide)) (hne (by decide)) (hne (by decide)) κ
    h160 (by rw [h108]; omega) (by rw [h108, z54]; omega)
  rw [h108, z54, Nat.zero_add] at e1
  have e2 := ParseNat.addTo_spec cap (P 118) (P 55) (P 160) (hne (by decide)) (hne (by decide)) (hne (by decide))
    (κ.setv (P 54) R) (by simp [hR, h160]) (by simp [hR, h118]; omega) (by simp [hR, h118, z55]; omega)
  rw [show (κ.setv (P 54) R).val (P 55) + (κ.setv (P 54) R).val (P 118) = Lg by simp [hR, h118, z55],
    show (κ.setv (P 54) R).val (P 118) = Lg by simp [hR, h118]] at e2
  have e3 := ParseNat.addTo_spec cap (P 110) (P 56) (P 160) (hne (by decide)) (hne (by decide)) (hne (by decide))
    ((κ.setv (P 54) R).setv (P 55) Lg) (by simp [hR, h160]) (by simp [hR, h110]; omega) (by simp [hR, h110, z56]; omega)
  rw [show ((κ.setv (P 54) R).setv (P 55) Lg).val (P 56) + ((κ.setv (P 54) R).setv (P 55) Lg).val (P 110) = cp by
      simp [hR, h110, z56],
    show ((κ.setv (P 54) R).setv (P 55) Lg).val (P 110) = cp by simp [hR, h110]] at e3
  have e4 := ParseNat.addTo_spec cap (P 167) (P 57) (P 160) (hne (by decide)) (hne (by decide)) (hne (by decide))
    (((κ.setv (P 54) R).setv (P 55) Lg).setv (P 56) cp) (by simp [hR, h160]) (by simp [hR, h167]; omega)
    (by simp [hR, h167, z57]; omega)
  rw [show (((κ.setv (P 54) R).setv (P 55) Lg).setv (P 56) cp).val (P 57) +
      (((κ.setv (P 54) R).setv (P 55) Lg).setv (P 56) cp).val (P 167) = VW by simp [hR, h167, z57],
    show (((κ.setv (P 54) R).setv (P 55) Lg).setv (P 56) cp).val (P 167) = VW by simp [hR, h167]] at e4
  have e5 := ParseNat.addTo_spec cap (P 169) (P 58) (P 160) (hne (by decide)) (hne (by decide)) (hne (by decide))
    ((((κ.setv (P 54) R).setv (P 55) Lg).setv (P 56) cp).setv (P 57) VW) (by simp [hR, h160])
    (by simp [hR, h169]; omega) (by simp [hR, h169, z58]; omega)
  rw [show ((((κ.setv (P 54) R).setv (P 55) Lg).setv (P 56) cp).setv (P 57) VW).val (P 58) +
      ((((κ.setv (P 54) R).setv (P 55) Lg).setv (P 56) cp).setv (P 57) VW).val (P 169) = TW by simp [hR, h169, z58],
    show ((((κ.setv (P 54) R).setv (P 55) Lg).setv (P 56) cp).setv (P 57) VW).val (P 169) = TW by
      simp [hR, h169]] at e5
  exact ⟨_, WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5))), by omega⟩

/-- **Phase 6, run.** -/
theorem ph6_spec (σ : WState ns nr) (J L n d c R Lg cp : ℕ) (h21 : σ.val (P 21) = J) (h45 : σ.val (P 45) = L)
    (h52 : σ.val (P 52) = n) (h97 : σ.val (P 97) = d) (h151 : σ.val (P 151) = c) (h108 : σ.val (P 108) = R)
    (h118 : σ.val (P 118) = Lg) (h110 : σ.val (P 110) = cp)
    (h13 : σ.val (P 13) = 0) (h14 : σ.val (P 14) = 0) (h51 : σ.val (P 51) = 0)
    (hz58 : ∀ j : Fin 200, 54 ≤ j.val → j.val ≤ 58 → σ.val (P j) = 0)
    (zz : ∀ j : Fin 200, 162 ≤ j.val → j.val ≤ 170 → σ.val (P j) = 0) (h160 : σ.val (P 160) = 0)
    (h161 : σ.val (P 161) = 0)
    (hcJ : J ≤ cap) (hcL : 4 * L ≤ cap) (hcn : n ≤ cap) (hcd : d ≤ cap) (hcc : c + 1 ≤ cap) (hcR : R ≤ cap)
    (hcLg : Lg ≤ cap) (hccp : cp ≤ cap) (h2c : 2 ≤ cap) (hcV : (J + 1) * (2 * L + 1) + 1 ≤ cap)
    (hcT : n * ((J + 1) * (2 * L + 1) + 1) ≤ cap) :
    ∃ m, WExec cap (ph6 P) σ
      (((((((((ph6mid P σ J L n).setv (P 13) (4 * L)).setv (P 14) d).setv (P 51) (c + 1)).setv (P 54) R).setv (P 55)
        Lg).setv (P 56) cp).setv (P 57) ((J + 1) * (2 * L + 1))).setv (P 58) (n * ((J + 1) * (2 * L + 1) + 1))) m ∧
      m ≤ costL cap vOps + 18 * (J + L + n + 4 * L + d + c + R + Lg + cp + (J + 1) * (2 * L + 1) +
        n * ((J + 1) * (2 * L + 1) + 1)) + 100 := by
  have hR : ∀ i j : Fin 200, P i = P j ↔ i = j := fun i j => P.injective.eq_iff
  obtain ⟨m1, e1, b1⟩ := ph6A_spec cap P σ J L n h21 h45 h52 zz h160 h161 hcJ (by omega) hcn h2c hcV hcT
  have rd := ph6mid_rd P σ J L n
  obtain ⟨m2, e2, b2⟩ := ph6B_spec cap P (ph6mid P σ J L n) L d c (by rw [rd 45 (by decide), h45])
    (by rw [rd 97 (by decide), h97]) (by rw [rd 151 (by decide), h151]) (by rw [rd 13 (by decide), h13])
    (by rw [rd 14 (by decide), h14]) (by rw [rd 51 (by decide), h51]) (by rw [rd 160 (by decide), h160]) hcL hcd hcc
  obtain ⟨m3, e3, b3⟩ := ph6C_spec cap P
    ((((ph6mid P σ J L n).setv (P 13) (4 * L)).setv (P 14) d).setv (P 51) (c + 1)) R Lg cp
    ((J + 1) * (2 * L + 1)) (n * ((J + 1) * (2 * L + 1) + 1))
    (by simp [hR]; rw [rd 108 (by decide), h108]) (by simp [hR]; rw [rd 118 (by decide), h118])
    (by simp [hR]; rw [rd 110 (by decide), h110]) (by simp [hR]; exact ph6mid_167 P σ J L n zz)
    (by simp [hR]; exact ph6mid_169 P σ J L n zz)
    (fun j h1 h2 => by
      have n13 : j ≠ 13 := Fin.ne_of_val_ne (show j.val ≠ 13 by omega)
      have n14 : j ≠ 14 := Fin.ne_of_val_ne (show j.val ≠ 14 by omega)
      have n51 : j ≠ 51 := Fin.ne_of_val_ne (show j.val ≠ 51 by omega)
      simp [hR, n13, n14, n51]; rw [rd j (by omega)]; exact hz58 j h1 h2)
    (by simp [hR]; rw [rd 160 (by decide), h160]) hcR hcLg hccp (by omega) hcT
  exact ⟨_, WExec.seq e1 (WExec.seq e2 e3), by omega⟩

end Phases6s

section Reads
variable {ns nr : ℕ} (P : Fin 200 ↪ Fin nr)

/-- The state after phase 4. -/
noncomputable def st4 (κ : WState ns nr) (L Q : ℕ) : WState ns nr :=
  (setZ (Zce P) (κ.setv (P 149) L) (evalL (fun i => (κ.setv (P 149) L).val (Zce P i)) cOps)).setv (P 105) Q

theorem st4_rd (κ : WState ns nr) (L Q : ℕ) (j : Fin 200) (hj : j.val < 149 ∨ 157 ≤ j.val) (h105 : j.val ≠ 105) :
    (st4 P κ L Q).val (P j) = κ.val (P j) := by
  have hne : ∀ {i j : Fin 200}, i ≠ j → P i ≠ P j := fun h => P.injective.ne h
  rw [st4, wsetv_val_ne _ _ (hne (Fin.ne_of_val_ne (show j.val ≠ 105 by omega))),
    setZ_val_other (Z := Zce P) _ _ _ fun i => hne (Fin.ne_of_val_ne (by simp [shiftE]; omega)),
    wsetv_val_ne _ _ (hne (Fin.ne_of_val_ne (show j.val ≠ 149 by omega)))]

theorem st4_105 (κ : WState ns nr) (L Q : ℕ) : (st4 P κ L Q).val (P 105) = Q := by
  simp [st4]

theorem st4_151 (κ : WState ns nr) (L Q lw : ℕ) (h150 : κ.val (P 150) = lw)
    (hz : ∀ j : Fin 200, 151 ≤ j.val → j.val ≤ 154 → κ.val (P j) = 0) :
    (st4 P κ L Q).val (P 151) = 4 * (lw + L + 1) := by
  have hR : ∀ i j : Fin 200, P i = P j ↔ i = j := fun i j => P.injective.eq_iff
  have hne : ∀ {i j : Fin 200}, i ≠ j → P i ≠ P j := fun h => P.injective.ne h
  rw [st4, wsetv_val_ne _ _ (hne (by decide))]
  refine (setZ_val_Z _ _ 2).trans ?_
  rw [cOps_eq _ (by simp [Zce, shiftE, hR, hz 151 (by decide) (by decide)])
    (by simp [Zce, shiftE, hR, hz 152 (by decide) (by decide)]) (by simp [Zce, shiftE, hR, hz 153 (by decide) (by decide)])
    (by simp [Zce, shiftE, hR, hz 154 (by decide) (by decide)]) 2]
  simp [Zce, shiftE, hR, h150]

/-- The state after phase 5. -/
noncomputable def st5 (τ : WState ns nr) (L c M Mlab n : ℕ) (vn : Fin 40 → ℕ) : WState ns nr :=
  setZ (Zne P) (((((τ.setv (P 96) L).setv (P 98) c).setv (P 101) M).setv (P 102) Mlab).setv (P 103) n) vn

theorem st5_rd (τ : WState ns nr) (L c M Mlab n : ℕ) (vn : Fin 40 → ℕ) (j : Fin 200)
    (hj : j.val < 96 ∨ 136 ≤ j.val) : (st5 P τ L c M Mlab n vn).val (P j) = τ.val (P j) := by
  have hne : ∀ {i j : Fin 200}, i ≠ j → P i ≠ P j := fun h => P.injective.ne h
  rw [st5, setZ_val_other (Z := Zne P) _ _ _ fun i => hne (Fin.ne_of_val_ne (by simp [shiftE]; omega)),
    wsetv_val_ne _ _ (hne (Fin.ne_of_val_ne (show j.val ≠ 103 by omega))),
    wsetv_val_ne _ _ (hne (Fin.ne_of_val_ne (show j.val ≠ 102 by omega))),
    wsetv_val_ne _ _ (hne (Fin.ne_of_val_ne (show j.val ≠ 101 by omega))),
    wsetv_val_ne _ _ (hne (Fin.ne_of_val_ne (show j.val ≠ 98 by omega))),
    wsetv_val_ne _ _ (hne (Fin.ne_of_val_ne (show j.val ≠ 96 by omega)))]

theorem st5_Zn (τ : WState ns nr) (L c M Mlab n : ℕ) (vn : Fin 40 → ℕ) (i : Fin 40) :
    (st5 P τ L c M Mlab n vn).val (P ⟨96 + i.val, by omega⟩) = vn i :=
  setZ_val_Z _ _ i

end Reads

section NumB
variable {ns nr : ℕ} (cap : ℕ) (P : Fin 200 ↪ Fin nr)

/-- The register an operation writes. -/
def tgt {k : ℕ} : AOp k → Fin k
  | .add _ b => b
  | .inc a _ => a
  | .mul _ _ c => c

theorem evalL_keep {k : ℕ} (os : List (AOp k)) (v : Fin k → ℕ) (i : Fin k) (h : ∀ o ∈ os, tgt o ≠ i) :
    evalL v os i = v i := by
  induction os generalizing v with
  | nil => rfl
  | cons o os ih =>
    simp only [evalL]
    rw [ih (o.eval v) (fun o' ho' => h o' (List.mem_cons_of_mem o ho'))]
    have hne := h o List.mem_cons_self
    cases o <;> simp only [AOp.eval, tgt] at hne ⊢ <;> exact Function.update_of_ne (Ne.symm hne) _ _

theorem numOps_tgt : ∀ o ∈ PopNums.numOps, 10 ≤ (tgt o).val := by decide

theorem numOps_keep (v : Fin 40 → ℕ) (i : Fin 40) (hi : i.val < 10) : evalL v PopNums.numOps i = v i :=
  evalL_keep _ v i fun o ho h => by have := numOps_tgt o ho; rw [h] at this; omega

/-- Phases 4–6. -/
def popNumB : WM ns nr := .seq (.seq (ph4 P) (ph5 P)) (ph6 P)

/-- The record's numbers phase 6 writes into `X`, else the old value. -/
def xNew (L d c R Lg cp J n i old : ℕ) : ℕ :=
  if i = 13 then 4 * L else if i = 14 then d else if i = 51 then c + 1 else if i = 54 then R
  else if i = 55 then Lg else if i = 56 then cp else if i = 57 then (J + 1) * (2 * L + 1)
  else if i = 58 then n * ((J + 1) * (2 * L + 1) + 1) else old

theorem chain_rd (ρ : WState ns nr) (L d c R Lg cp J n : ℕ) (i : Fin 200) :
    ((((((((ρ.setv (P 13) (4 * L)).setv (P 14) d).setv (P 51) (c + 1)).setv (P 54) R).setv (P 55) Lg).setv (P 56)
      cp).setv (P 57) ((J + 1) * (2 * L + 1))).setv (P 58) (n * ((J + 1) * (2 * L + 1) + 1))).val (P i) =
      xNew L d c R Lg cp J n i.val (ρ.val (P i)) := by
  have hR : ∀ i j : Fin 200, P i = P j ↔ i = j := fun i j => P.injective.eq_iff
  unfold xNew
  split_ifs with a13 a14 a51 a54 a55 a56 a57 a58
  · have : i = 13 := Fin.ext a13
    subst this; simp [hR]
  · have : i = 14 := Fin.ext a14
    subst this; simp [hR]
  · have : i = 51 := Fin.ext a51
    subst this; simp [hR]
  · have : i = 54 := Fin.ext a54
    subst this; simp [hR]
  · have : i = 55 := Fin.ext a55
    subst this; simp [hR]
  · have : i = 56 := Fin.ext a56
    subst this; simp [hR]
  · have : i = 57 := Fin.ext a57
    subst this; simp [hR]
  · have : i = 58 := Fin.ext a58
    subst this; simp [hR]
  · have n13 : i ≠ 13 := Fin.ne_of_val_ne a13
    have n14 : i ≠ 14 := Fin.ne_of_val_ne a14
    have n51 : i ≠ 51 := Fin.ne_of_val_ne a51
    have n54 : i ≠ 54 := Fin.ne_of_val_ne a54
    have n55 : i ≠ 55 := Fin.ne_of_val_ne a55
    have n56 : i ≠ 56 := Fin.ne_of_val_ne a56
    have n57 : i ≠ 57 := Fin.ne_of_val_ne a57
    have n58 : i ≠ 58 := Fin.ne_of_val_ne a58
    simp only [WState.setv_val, Function.update_apply, hR, n13, n14, n51, n54, n55, n56, n57, n58, if_false]

/-- Phases 4 and 5. -/
theorem popNum45 (κ : WState ns nr) (L n d M Mlab CAP LL lw : ℕ)
    (h45 : κ.val (P 45) = L) (h52 : κ.val (P 52) = n) (h97 : κ.val (P 97) = d) (h44 : κ.val (P 44) = M)
    (h180 : κ.val (P 180) = Mlab) (h99 : κ.val (P 99) = CAP) (h100 : κ.val (P 100) = LL)
    (h104 : κ.val (P 104) = lw) (h150 : κ.val (P 150) = lw)
    (hzS : ∀ j : Fin 200, (j.val = 96 ∨ j.val = 98 ∨ (101 ≤ j.val ∧ j.val ≤ 103) ∨ (105 ≤ j.val ∧ j.val ≤ 135) ∨
      j.val = 149 ∨ (151 ≤ j.val ∧ j.val ≤ 158) ∨ (162 ≤ j.val ∧ j.val ≤ 170)) → κ.val (P j) = 0)
    (h160 : κ.val (P 160) = 0) (h161 : κ.val (P 161) = 0)
    (hQc : (8 * L + 2) ^ d * (8 * L + 2) + 2 ≤ cap) (hc4 : 4 * (lw + L + 1) + 8 ≤ cap) (hdc : d ≤ cap)
    (hlwc : lw ≤ cap) (hin : L + 4 * (lw + L + 1) + M + Mlab + n ≤ cap)
    (hnum : ∀ i, evalL (vIn L d (4 * (lw + L + 1)) CAP LL M Mlab n lw ((8 * L + 2) ^ d)) PopNums.numOps i ≤ cap) :
    ∃ m, WExec cap (.seq (ph4 P) (ph5 P)) κ
      (st5 P (st4 P κ L ((8 * L + 2) ^ d)) L (4 * (lw + L + 1)) M Mlab n
        (evalL (vIn L d (4 * (lw + L + 1)) CAP LL M Mlab n lw ((8 * L + 2) ^ d)) PopNums.numOps)) m ∧
      m ≤ (18 * L + 400 * (cap + 1) * (cap + 1) + d * (40 * (cap + 1) * (cap + 1) + 20) + 20 * cap + 30) + 1 +
        (18 * (L + 4 * (lw + L + 1) + M + Mlab + n) + costL cap PopNums.numOps + 30) := by
  obtain ⟨m4, e4, b4⟩ := ph4_spec cap P κ L lw d h45 h150 h97 (fun j hj => hzS j (by omega))
    (hzS 105 (by decide)) h160 h161 hQc (by omega) hdc hlwc
  have e4' : WExec cap (ph4 P) κ (st4 P κ L ((8 * L + 2) ^ d)) m4 := e4
  have r4 := st4_rd P κ L ((8 * L + 2) ^ d)
  obtain ⟨m5, e5, b5⟩ := ph5_spec cap P (st4 P κ L ((8 * L + 2) ^ d)) L d (4 * (lw + L + 1)) CAP LL M Mlab n lw
    ((8 * L + 2) ^ d)
    (by rw [r4 45 (Or.inl (by decide)) (by decide), h45])
    (st4_151 P κ L _ lw h150 fun j h1 h2 => hzS j (by omega))
    (by rw [r4 44 (Or.inl (by decide)) (by decide), h44])
    (by rw [r4 180 (Or.inr (by decide)) (by decide), h180]) (by rw [r4 52 (Or.inl (by decide)) (by decide), h52])
    (by rw [r4 97 (Or.inl (by decide)) (by decide), h97]) (by rw [r4 99 (Or.inl (by decide)) (by decide), h99])
    (by rw [r4 100 (Or.inl (by decide)) (by decide), h100]) (by rw [r4 104 (Or.inl (by decide)) (by decide), h104])
    (st4_105 P κ L _)
    (fun j hj => by
      rw [r4 j (Or.inl (by omega)) (by omega)]
      exact hzS j (by omega))
    (by rw [r4 160 (Or.inr (by decide)) (by decide), h160]) (by rw [r4 161 (Or.inr (by decide)) (by decide), h161])
    hin hnum
  exact ⟨_, WExec.seq e4' e5, by omega⟩

theorem st45_rd (κ : WState ns nr) (L Q c M Mlab n : ℕ) (vn : Fin 40 → ℕ) (j : Fin 200)
    (hj : j.val < 96 ∨ 157 ≤ j.val) (h105 : j.val ≠ 105) :
    (st5 P (st4 P κ L Q) L c M Mlab n vn).val (P j) = κ.val (P j) := by
  rw [st5_rd P _ L c M Mlab n vn j (by omega), st4_rd P κ L Q j (by omega) h105]

theorem setZ_sh {k : ℕ} (Z : Fin k ↪ Fin nr) (σ : WState ns nr) (v : Fin k → ℕ) : (setZ Z σ v).sh = σ.sh := rfl

theorem setZ_st {k : ℕ} (Z : Fin k ↪ Fin nr) (σ : WState ns nr) (v : Fin k → ℕ) : (setZ Z σ v).st = σ.st := rfl

theorem st45_sh (κ : WState ns nr) (L Q c M Mlab n : ℕ) (vn : Fin 40 → ℕ) :
    (st5 P (st4 P κ L Q) L c M Mlab n vn).sh = κ.sh := by
  simp only [st5, st4, setZ_sh, WState.setv_sh]

theorem st45_st (κ : WState ns nr) (L Q c M Mlab n : ℕ) (vn : Fin 40 → ℕ) :
    (st5 P (st4 P κ L Q) L c M Mlab n vn).st = κ.st := by
  simp only [st5, st4, setZ_st, WState.setv_st]

theorem st45_Zn (κ : WState ns nr) (L Q c M Mlab n : ℕ) (vn : Fin 40 → ℕ) (i : Fin 40) (j : Fin 200)
    (hj : j.val = 96 + i.val) : (st5 P (st4 P κ L Q) L c M Mlab n vn).val (P j) = vn i := by
  have : j = ⟨96 + i.val, by omega⟩ := Fin.ext hj
  rw [this]
  exact st5_Zn P _ L c M Mlab n vn i

theorem vIn_one (L d c CAP LL M Mlab n lw Q : ℕ) : vIn L d c CAP LL M Mlab n lw Q 1 = d := by
  simp [vIn]

/-- Phase 6 with the record's numbers read in `X`. -/
theorem popNum6 (σ : WState ns nr) (J L n d c R Lg cp : ℕ) (h21 : σ.val (P 21) = J) (h45 : σ.val (P 45) = L)
    (h52 : σ.val (P 52) = n) (h97 : σ.val (P 97) = d) (h151 : σ.val (P 151) = c) (h108 : σ.val (P 108) = R)
    (h118 : σ.val (P 118) = Lg) (h110 : σ.val (P 110) = cp)
    (h13 : σ.val (P 13) = 0) (h14 : σ.val (P 14) = 0) (h51 : σ.val (P 51) = 0)
    (hz58 : ∀ j : Fin 200, 54 ≤ j.val → j.val ≤ 58 → σ.val (P j) = 0)
    (zz : ∀ j : Fin 200, 162 ≤ j.val → j.val ≤ 170 → σ.val (P j) = 0) (h160 : σ.val (P 160) = 0)
    (h161 : σ.val (P 161) = 0)
    (hcJ : J ≤ cap) (hcL : 4 * L ≤ cap) (hcn : n ≤ cap) (hcd : d ≤ cap) (hcc : c + 1 ≤ cap) (hcR : R ≤ cap)
    (hcLg : Lg ≤ cap) (hccp : cp ≤ cap) (h2c : 2 ≤ cap) (hcV : (J + 1) * (2 * L + 1) + 1 ≤ cap)
    (hcT : n * ((J + 1) * (2 * L + 1) + 1) ≤ cap) :
    ∃ m τ, WExec cap (ph6 P) σ τ m ∧
      (∀ i : Fin 200, i.val < 64 → τ.val (P i) = xNew L d c R Lg cp J n i.val (σ.val (P i))) ∧
      τ.sh = σ.sh ∧ τ.st = σ.st ∧
      m ≤ costL cap vOps + 18 * (J + L + n + 4 * L + d + c + R + Lg + cp + (J + 1) * (2 * L + 1) +
        n * ((J + 1) * (2 * L + 1) + 1)) + 100 := by
  obtain ⟨m, e, b⟩ := ph6_spec cap P σ J L n d c R Lg cp h21 h45 h52 h97 h151 h108 h118 h110 h13 h14 h51 hz58 zz
    h160 h161 hcJ hcL hcn hcd hcc hcR hcLg hccp h2c hcV hcT
  refine ⟨m, _, e, fun i hi => ?_, by simp only [WState.setv_sh, ph6mid, setZ_sh],
    by simp only [WState.setv_st, ph6mid, setZ_st], b⟩
  rw [chain_rd P _ L d c R Lg cp J n i, ph6mid_rd P σ J L n i (by omega)]

theorem popNumB_spec (κ : WState ns nr) (J L n d M Mlab CAP LL lw : ℕ) (h21 : κ.val (P 21) = J)
    (h45 : κ.val (P 45) = L) (h52 : κ.val (P 52) = n) (h97 : κ.val (P 97) = d) (h44 : κ.val (P 44) = M)
    (h180 : κ.val (P 180) = Mlab) (h99 : κ.val (P 99) = CAP) (h100 : κ.val (P 100) = LL)
    (h104 : κ.val (P 104) = lw) (h150 : κ.val (P 150) = lw)
    (hzX : ∀ j : Fin 200, (j.val = 13 ∨ j.val = 14 ∨ j.val = 51 ∨ (54 ≤ j.val ∧ j.val ≤ 58)) → κ.val (P j) = 0)
    (hzS : ∀ j : Fin 200, (j.val = 96 ∨ j.val = 98 ∨ (101 ≤ j.val ∧ j.val ≤ 103) ∨ (105 ≤ j.val ∧ j.val ≤ 135) ∨
      j.val = 149 ∨ (151 ≤ j.val ∧ j.val ≤ 158) ∨ (162 ≤ j.val ∧ j.val ≤ 170)) → κ.val (P j) = 0)
    (h160 : κ.val (P 160) = 0) (h161 : κ.val (P 161) = 0)
    (hQc : (8 * L + 2) ^ d * (8 * L + 2) + 2 ≤ cap) (hc4 : 4 * (lw + L + 1) + 8 ≤ cap) (hdc : d ≤ cap)
    (hlwc : lw ≤ cap) (hin : L + 4 * (lw + L + 1) + M + Mlab + n ≤ cap)
    (hnum : ∀ i, evalL (vIn L d (4 * (lw + L + 1)) CAP LL M Mlab n lw ((8 * L + 2) ^ d)) PopNums.numOps i ≤ cap)
    (hcJ : J ≤ cap) (hcL : 4 * L ≤ cap) (hcn : n ≤ cap) (h2c : 2 ≤ cap)
    (hcV : (J + 1) * (2 * L + 1) + 1 ≤ cap) (hcT : n * ((J + 1) * (2 * L + 1) + 1) ≤ cap) :
    ∃ m τ, WExec cap (popNumB P) κ τ m ∧
      (∀ i : Fin 200, i.val < 64 → τ.val (P i) =
        xNew L d (4 * (lw + L + 1))
          (evalL (vIn L d (4 * (lw + L + 1)) CAP LL M Mlab n lw ((8 * L + 2) ^ d)) PopNums.numOps 12)
          (evalL (vIn L d (4 * (lw + L + 1)) CAP LL M Mlab n lw ((8 * L + 2) ^ d)) PopNums.numOps 22)
          (evalL (vIn L d (4 * (lw + L + 1)) CAP LL M Mlab n lw ((8 * L + 2) ^ d)) PopNums.numOps 14) J n i.val
          (κ.val (P i))) ∧
      τ.sh = κ.sh ∧ τ.st = κ.st ∧
      m ≤ (18 * L + 400 * (cap + 1) * (cap + 1) + d * (40 * (cap + 1) * (cap + 1) + 20) + 20 * cap + 30) + 1 +
        (18 * (L + 4 * (lw + L + 1) + M + Mlab + n) + costL cap PopNums.numOps + 30) + 1 +
        (costL cap vOps + 18 * (J + L + n + 4 * L + d + 4 * (lw + L + 1) + 3 * cap + (J + 1) * (2 * L + 1) +
          n * ((J + 1) * (2 * L + 1) + 1)) + 100) := by
  obtain ⟨m45, e45, b45⟩ := popNum45 cap P κ L n d M Mlab CAP LL lw h45 h52 h97 h44 h180 h99 h100 h104 h150 hzS h160
    h161 hQc hc4 hdc hlwc hin hnum
  have zκ := st45_rd P κ L ((8 * L + 2) ^ d) (4 * (lw + L + 1)) M Mlab n
    (evalL (vIn L d (4 * (lw + L + 1)) CAP LL M Mlab n lw ((8 * L + 2) ^ d)) PopNums.numOps)
  have zn := st45_Zn P κ L ((8 * L + 2) ^ d) (4 * (lw + L + 1)) M Mlab n
    (evalL (vIn L d (4 * (lw + L + 1)) CAP LL M Mlab n lw ((8 * L + 2) ^ d)) PopNums.numOps)
  have hv1 : evalL (vIn L d (4 * (lw + L + 1)) CAP LL M Mlab n lw ((8 * L + 2) ^ d)) PopNums.numOps 1 = d := by
    rw [numOps_keep _ 1 (by decide), vIn_one]
  have z151 : (st5 P (st4 P κ L ((8 * L + 2) ^ d)) L (4 * (lw + L + 1)) M Mlab n
      (evalL (vIn L d (4 * (lw + L + 1)) CAP LL M Mlab n lw ((8 * L + 2) ^ d)) PopNums.numOps)).val (P 151) =
      4 * (lw + L + 1) := by
    rw [st5_rd P _ _ _ M Mlab n _ 151 (Or.inr (by decide))]
    exact st4_151 P κ L _ lw h150 fun j h1 h2 => hzS j (by omega)
  obtain ⟨m6, τ, e6, r6, s6, t6, b6⟩ := popNum6 cap P _ J L n d (4 * (lw + L + 1))
    (evalL (vIn L d (4 * (lw + L + 1)) CAP LL M Mlab n lw ((8 * L + 2) ^ d)) PopNums.numOps 12)
    (evalL (vIn L d (4 * (lw + L + 1)) CAP LL M Mlab n lw ((8 * L + 2) ^ d)) PopNums.numOps 22)
    (evalL (vIn L d (4 * (lw + L + 1)) CAP LL M Mlab n lw ((8 * L + 2) ^ d)) PopNums.numOps 14)
    (by rw [zκ 21 (Or.inl (by decide)) (by decide), h21]) (by rw [zκ 45 (Or.inl (by decide)) (by decide), h45])
    (by rw [zκ 52 (Or.inl (by decide)) (by decide), h52]) ((zn 1 97 (by decide)).trans hv1) z151
    (zn 12 108 (by decide)) (zn 22 118 (by decide)) (zn 14 110 (by decide))
    (by rw [zκ 13 (Or.inl (by decide)) (by decide)]; exact hzX 13 (by decide))
    (by rw [zκ 14 (Or.inl (by decide)) (by decide)]; exact hzX 14 (by decide))
    (by rw [zκ 51 (Or.inl (by decide)) (by decide)]; exact hzX 51 (by decide))
    (fun j h1 h2 => by rw [zκ j (Or.inl (by omega)) (by omega)]; exact hzX j (by omega))
    (fun j h1 h2 => by rw [zκ j (Or.inr (by omega)) (by omega)]; exact hzS j (by omega))
    (by rw [zκ 160 (Or.inr (by decide)) (by decide), h160]) (by rw [zκ 161 (Or.inr (by decide)) (by decide), h161])
    hcJ hcL hcn hdc (by omega) (hnum 12) (hnum 22) (hnum 14) h2c hcV hcT
  have c12 := hnum 12
  have c22 := hnum 22
  have c14 := hnum 14
  refine ⟨_, τ, WExec.seq e45 e6, fun i hi => ?_, s6.trans (st45_sh P κ L _ _ M Mlab n _),
    t6.trans (st45_st P κ L _ _ M Mlab n _), by omega⟩
  rw [r6 i hi, zκ i (Or.inl (by omega)) (by omega)]

end NumB

section NumA
variable {ns nr : ℕ} (cap : ℕ) (P : Fin 200 ↪ Fin nr)

/-- Phases 1–3. -/
def popNumA (D : Fin (ns + 1)) : WM ns nr := .seq (ph1 P) (.seq (ph2 P) (ph3 P D))

/-- The state after phases 1 and 2. -/
def st12 (σ : WState ns nr) (Sv J d M L lw : ℕ) : WState ns nr :=
  ((((((σ.setv (P 64) Sv).setv (P 65) J).setv (P 97) d).setv (P 89) M).setv (P 90) L).setv (P 104) lw).setv (P 150) lw

/-- The state after phases 1–3. -/
def stA (σ : WState ns nr) (D : Fin (ns + 1)) (Sv J d M L lw r4 G off Lg CAP : ℕ) (w : List Bool) : WState ns nr :=
  (((((((appendO (st12 P σ Sv J d M L lw) D (P 136) w).setv (P 137) r4).setv (P 138) G).setv (P 139) off).setv (P 140)
    Lg).setv (P 147) CAP).setv (P 99) CAP).setv (P 100) w.length

theorem st12_rd (σ : WState ns nr) (Sv J d M L lw : ℕ) (j : Fin 200)
    (hj : j.val ≠ 64 ∧ j.val ≠ 65 ∧ j.val ≠ 97 ∧ j.val ≠ 89 ∧ j.val ≠ 90 ∧ j.val ≠ 104 ∧ j.val ≠ 150) :
    (st12 P σ Sv J d M L lw).val (P j) = σ.val (P j) := by
  have hne : ∀ {i j : Fin 200}, i ≠ j → P i ≠ P j := fun h => P.injective.ne h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hj
  rw [st12, wsetv_val_ne _ _ (hne (Fin.ne_of_val_ne (show j.val ≠ 150 from a7))),
    wsetv_val_ne _ _ (hne (Fin.ne_of_val_ne (show j.val ≠ 104 from a6))),
    wsetv_val_ne _ _ (hne (Fin.ne_of_val_ne (show j.val ≠ 90 from a5))),
    wsetv_val_ne _ _ (hne (Fin.ne_of_val_ne (show j.val ≠ 89 from a4))),
    wsetv_val_ne _ _ (hne (Fin.ne_of_val_ne (show j.val ≠ 97 from a3))),
    wsetv_val_ne _ _ (hne (Fin.ne_of_val_ne (show j.val ≠ 65 from a2))),
    wsetv_val_ne _ _ (hne (Fin.ne_of_val_ne (show j.val ≠ 64 from a1)))]

theorem stA_rd (σ : WState ns nr) (D : Fin (ns + 1)) (Sv J d M L lw r4 G off Lg CAP : ℕ) (w : List Bool)
    (j : Fin 200) (hj : j.val < 64 ∨ j.val = 96 ∨ j.val = 98 ∨ (101 ≤ j.val ∧ j.val ≤ 103) ∨
      (105 ≤ j.val ∧ j.val ≤ 135) ∨ j.val = 149 ∨ 151 ≤ j.val) :
    (stA P σ D Sv J d M L lw r4 G off Lg CAP w).val (P j) = σ.val (P j) := by
  have hne : ∀ {i j : Fin 200}, i ≠ j → P i ≠ P j := fun h => P.injective.ne h
  rw [stA, wsetv_val_ne _ _ (hne (Fin.ne_of_val_ne (show j.val ≠ 100 by omega))),
    wsetv_val_ne _ _ (hne (Fin.ne_of_val_ne (show j.val ≠ 99 by omega))),
    wsetv_val_ne _ _ (hne (Fin.ne_of_val_ne (show j.val ≠ 147 by omega))),
    wsetv_val_ne _ _ (hne (Fin.ne_of_val_ne (show j.val ≠ 140 by omega))),
    wsetv_val_ne _ _ (hne (Fin.ne_of_val_ne (show j.val ≠ 139 by omega))),
    wsetv_val_ne _ _ (hne (Fin.ne_of_val_ne (show j.val ≠ 138 by omega))),
    wsetv_val_ne _ _ (hne (Fin.ne_of_val_ne (show j.val ≠ 137 by omega))), appendO_val, Function.update_apply,
    if_neg (hne (Fin.ne_of_val_ne (show j.val ≠ 136 by omega))),
    st12_rd P σ Sv J d M L lw j (by omega)]

theorem stA_97 (σ : WState ns nr) (D : Fin (ns + 1)) (Sv J d M L lw r4 G off Lg CAP : ℕ) (w : List Bool) :
    (stA P σ D Sv J d M L lw r4 G off Lg CAP w).val (P 97) = d := by
  have hR : ∀ i j : Fin 200, P i = P j ↔ i = j := fun i j => P.injective.eq_iff
  simp [stA, st12, hR]

theorem stA_99 (σ : WState ns nr) (D : Fin (ns + 1)) (Sv J d M L lw r4 G off Lg CAP : ℕ) (w : List Bool) :
    (stA P σ D Sv J d M L lw r4 G off Lg CAP w).val (P 99) = CAP := by
  have hR : ∀ i j : Fin 200, P i = P j ↔ i = j := fun i j => P.injective.eq_iff
  simp [stA, hR]

theorem stA_100 (σ : WState ns nr) (D : Fin (ns + 1)) (Sv J d M L lw r4 G off Lg CAP : ℕ) (w : List Bool) :
    (stA P σ D Sv J d M L lw r4 G off Lg CAP w).val (P 100) = w.length := by
  simp [stA]

theorem stA_104 (σ : WState ns nr) (D : Fin (ns + 1)) (Sv J d M L lw r4 G off Lg CAP : ℕ) (w : List Bool) :
    (stA P σ D Sv J d M L lw r4 G off Lg CAP w).val (P 104) = lw := by
  have hR : ∀ i j : Fin 200, P i = P j ↔ i = j := fun i j => P.injective.eq_iff
  simp [stA, st12, hR]

theorem stA_150 (σ : WState ns nr) (D : Fin (ns + 1)) (Sv J d M L lw r4 G off Lg CAP : ℕ) (w : List Bool) :
    (stA P σ D Sv J d M L lw r4 G off Lg CAP w).val (P 150) = lw := by
  have hR : ∀ i j : Fin 200, P i = P j ↔ i = j := fun i j => P.injective.eq_iff
  simp [stA, st12, hR]

theorem stA_sh (σ : WState ns nr) (D : Fin (ns + 1)) (Sv J d M L lw r4 G off Lg CAP : ℕ) (w : List Bool)
    (T : Fin (ns + 1)) (hT : T ≠ D) : (stA P σ D Sv J d M L lw r4 G off Lg CAP w).sh T = σ.sh T := by
  simp [stA, st12, Function.update_apply, hT]

theorem stA_st (σ : WState ns nr) (D : Fin (ns + 1)) (Sv J d M L lw r4 G off Lg CAP : ℕ) (w : List Bool)
    (T : Fin (ns + 1)) (hT : T ≠ D) : (stA P σ D Sv J d M L lw r4 G off Lg CAP w).st T = σ.st T := by
  simp [stA, st12, Function.update_apply, hT]

/-- A bound on phases 1–3's cost. -/
def numABound (cap Sv J M L r4 G off Lg : ℕ) : ℕ :=
  (J * (lvlBound cap + 4) + 40 * J + 18 * Sv + 200 * (lbSumF Sv J + 1) + 100) + 1 +
    (((J + 1) * (lvlBound cap + 4) + 40 * J + 40 * M + 18 * L + 100 * (lwSumF Sv J L + M + 2) + 100) + 1 +
      (18 * (r4 + G + off + Lg) + Emit.labsCost r4 G off Lg + 18 * cap + 100))

theorem popNumA_spec (D : Fin (ns + 1)) (σ : WState ns nr) (Sv J M L r4 G off Lg Mlab : ℕ)
    (h20 : σ.val (P 20) = Sv) (h21 : σ.val (P 21) = J) (h44 : σ.val (P 44) = M) (h45 : σ.val (P 45) = L)
    (h1 : σ.val (P 1) = r4) (h2 : σ.val (P 2) = G) (h3 : σ.val (P 3) = off) (h4 : σ.val (P 4) = Lg)
    (hz : ∀ j : Fin 200, 64 ≤ j.val → j.val ≤ 170 → σ.val (P j) = 0) (hD : σ.sh D = (σ.st D).length)
    (hM : off + Lg + (r4 + 4) * G ≤ Mlab)
    (hcap : lvCap Sv J J ≤ cap) (hac1 : 3 * (lbSumF Sv J + 1) ≤ cap) (hJc : J + 1 ≤ cap) (hSc : Sv ≤ cap)
    (hac2 : lwSumF Sv J L + M + 2 ≤ cap) (hMc : M ≤ cap) (hLc : L ≤ cap)
    (hcap3 : Lg * (4 * (4 * Mlab + 4)) + 5 + Lg * (4 * (2 * Mlab + 10)) + 4 * (4 * Mlab + 4) +
      4 * (2 * Mlab + 10) + 7 * Mlab + r4 + G + off + Lg + 20 ≤ cap)
    (hac3 : FiltRec.labSum (Emit.sliceLabs r4 G off Lg) +
      ((Emit.sliceLabs r4 G off Lg).flatMap FiltRec.labE).length ≤ cap) :
    ∃ m, WExec cap (popNumA P D) σ
      (stA P σ D Sv J (3 * (lbSumF Sv J + 1)) M L (lwSumF Sv J L + M + 2) r4 G off Lg
        (FiltRec.labSum (Emit.sliceLabs r4 G off Lg)) ((Emit.sliceLabs r4 G off Lg).flatMap FiltRec.labE)) m ∧
      m ≤ numABound cap Sv J M L r4 G off Lg := by
  have hR : ∀ i j : Fin 200, P i = P j ↔ i = j := fun i j => P.injective.eq_iff
  have hne : ∀ {i j : Fin 200}, i ≠ j → P i ≠ P j := fun h => P.injective.ne h
  obtain ⟨m1, e1, b1⟩ := ph1_spec cap P σ Sv J h20 h21 (fun j a b => hz j a (by omega))
    (hz 160 (by decide) (by decide)) hcap hac1 (by omega) hSc
  obtain ⟨m2, e2, b2⟩ := ph2_spec cap P (((σ.setv (P 64) Sv).setv (P 65) J).setv (P 97) (3 * (lbSumF Sv J + 1)))
    Sv J M L (by simp [hR]) (by simp [hR]) (by simp [hR, h44]) (by simp [hR, h45])
    (fun j a b => by
      rw [wsetv_val_ne _ _ (hne (Fin.ne_of_val_ne (show j.val ≠ 97 by omega))),
        wsetv_val_ne _ _ (hne (Fin.ne_of_val_ne (show j.val ≠ 65 by omega))),
        wsetv_val_ne _ _ (hne (Fin.ne_of_val_ne (show j.val ≠ 64 by omega)))]
      exact hz j (by omega) (by omega))
    (by simp [hR, hz 104 (by decide) (by decide)]) (by simp [hR, hz 150 (by decide) (by decide)])
    (by simp [hR, hz 160 (by decide) (by decide)]) hcap hac2 hJc hMc hLc
  obtain ⟨m3, e3, b3⟩ := ph3_spec cap P D (st12 P σ Sv J (3 * (lbSumF Sv J + 1)) M L (lwSumF Sv J L + M + 2))
    r4 G off Lg Mlab
    (by rw [st12_rd P σ _ _ _ _ _ _ 1 (by decide), h1]) (by rw [st12_rd P σ _ _ _ _ _ _ 2 (by decide), h2])
    (by rw [st12_rd P σ _ _ _ _ _ _ 3 (by decide), h3]) (by rw [st12_rd P σ _ _ _ _ _ _ 4 (by decide), h4])
    (fun j a b => by rw [st12_rd P σ _ _ _ _ _ _ j (by omega)]; exact hz j (by omega) (by omega))
    (by rw [st12_rd P σ _ _ _ _ _ _ 99 (by decide)]; exact hz 99 (by decide) (by decide))
    (by rw [st12_rd P σ _ _ _ _ _ _ 100 (by decide)]; exact hz 100 (by decide) (by decide))
    (by rw [st12_rd P σ _ _ _ _ _ _ 160 (by decide)]; exact hz 160 (by decide) (by decide))
    (by simp only [st12, WState.setv_sh, WState.setv_st]; exact hD) hM hcap3 hac3
  refine ⟨m1 + 1 + (m2 + 1 + m3), ?_, ?_⟩
  · unfold stA
    exact WExec.seq e1 (WExec.seq e2 e3)
  · unfold numABound
    omega

end NumA

section NumW
variable {ns nr : ℕ} (cap : ℕ) (P : Fin 200 ↪ Fin nr)

theorem vIn_0 (L d c CAP LL M Mlab n lw Q : ℕ) : vIn L d c CAP LL M Mlab n lw Q 0 = L := by
  simp [vIn]

theorem vIn_1 (L d c CAP LL M Mlab n lw Q : ℕ) : vIn L d c CAP LL M Mlab n lw Q 1 = d := by
  simp [vIn]

theorem vIn_2 (L d c CAP LL M Mlab n lw Q : ℕ) : vIn L d c CAP LL M Mlab n lw Q 2 = c := by
  simp [vIn]

theorem vIn_3 (L d c CAP LL M Mlab n lw Q : ℕ) : vIn L d c CAP LL M Mlab n lw Q 3 = CAP := by
  simp [vIn]

theorem vIn_4 (L d c CAP LL M Mlab n lw Q : ℕ) : vIn L d c CAP LL M Mlab n lw Q 4 = LL := by
  simp [vIn]

theorem vIn_5 (L d c CAP LL M Mlab n lw Q : ℕ) : vIn L d c CAP LL M Mlab n lw Q 5 = M := by
  simp [vIn]

theorem vIn_6 (L d c CAP LL M Mlab n lw Q : ℕ) : vIn L d c CAP LL M Mlab n lw Q 6 = Mlab := by
  simp [vIn]

theorem vIn_7 (L d c CAP LL M Mlab n lw Q : ℕ) : vIn L d c CAP LL M Mlab n lw Q 7 = n := by
  simp [vIn]

theorem vIn_8 (L d c CAP LL M Mlab n lw Q : ℕ) : vIn L d c CAP LL M Mlab n lw Q 8 = lw := by
  simp [vIn]

theorem vIn_9 (L d c CAP LL M Mlab n lw Q : ℕ) : vIn L d c CAP LL M Mlab n lw Q 9 = Q := by
  simp [vIn]

/-- **The program's outputs are Route B's capacities** at the cell's inputs (`PopNums.numOps_capacities`). -/
theorem vIn_caps (L d c CAP LL M Mlab n lw : ℕ) :
    evalL (vIn L d c CAP LL M Mlab n lw ((8 * L + 2) ^ d)) PopNums.numOps 12 =
        PopCap.popKc L d c CAP (PopNums.blF L d c CAP LL lw M) + 1 ∧
      evalL (vIn L d c CAP LL M Mlab n lw ((8 * L + 2) ^ d)) PopNums.numOps 22 =
        PopCap.popKc L d c CAP (PopNums.blF L d c CAP LL lw M) + 1 + 1 ∧
      evalL (vIn L d c CAP LL M Mlab n lw ((8 * L + 2) ^ d)) PopNums.numOps 14 =
        PopCap.popCapB n (PopCap.popKc L d c CAP (PopNums.blF L d c CAP LL lw M) + 1) (PopCap.popPW L d Mlab) := by
  obtain ⟨h10, h12, h22, h13, h14⟩ := PopNums.numOps_capacities (vIn L d c CAP LL M Mlab n lw ((8 * L + 2) ^ d))
    (vIn_zero L d c CAP LL M Mlab n lw _) (by rw [vIn_9, vIn_0, vIn_1])
  simp only [vIn_0, vIn_1, vIn_2, vIn_3, vIn_4, vIn_5, vIn_6, vIn_7, vIn_8] at h10 h12 h13 h14
  rw [h10] at h12
  rw [h13, h12] at h14
  rw [h22, h12]
  exact ⟨rfl, rfl, h14⟩

/-- The whole numbers stage. -/
def popNumW (D : Fin (ns + 1)) : WM ns nr := .seq (popNumA P D) (popNumB P)

/-- A bound on phases 4–6's cost. -/
def numBBound (cap J L n d M Mlab lw : ℕ) : ℕ :=
  (18 * L + 400 * (cap + 1) * (cap + 1) + d * (40 * (cap + 1) * (cap + 1) + 20) + 20 * cap + 30) + 1 +
    (18 * (L + 4 * (lw + L + 1) + M + Mlab + n) + costL cap PopNums.numOps + 30) + 1 +
    (costL cap vOps + 18 * (J + L + n + 4 * L + d + 4 * (lw + L + 1) + 3 * cap + (J + 1) * (2 * L + 1) +
      n * ((J + 1) * (2 * L + 1) + 1)) + 100)

/-- **The POP cell's numbers stage**: from the list's numbers in `X`, the record's numbers — `Lp = 4L`, the degree
`d = 3·(lbSum + 1)`, `c + 1` with `c = 4(lw + L + 1)`, Route B's `R = popKc … + 1`, `Lg = R + 1`, `cap = popCapB n R PW`,
the visit sizes — land in `X` (`xNew`); the other `X` registers and every stream but the dummy `D` are kept. -/
theorem popNumW_spec (D : Fin (ns + 1)) (σ : WState ns nr) (Sv J M L r4 G off Lg Mlab n d lw CAP LL c R : ℕ)
    (hd : d = 3 * (lbSumF Sv J + 1)) (hlw : lw = lwSumF Sv J L + M + 2)
    (hCAP : CAP = FiltRec.labSum (Emit.sliceLabs r4 G off Lg))
    (hLL : LL = ((Emit.sliceLabs r4 G off Lg).flatMap FiltRec.labE).length) (hc : c = 4 * (lw + L + 1))
    (hR : R = PopCap.popKc L d c CAP (PopNums.blF L d c CAP LL lw M) + 1)
    (h20 : σ.val (P 20) = Sv) (h21 : σ.val (P 21) = J) (h44 : σ.val (P 44) = M) (h45 : σ.val (P 45) = L)
    (h1 : σ.val (P 1) = r4) (h2 : σ.val (P 2) = G) (h3 : σ.val (P 3) = off) (h4 : σ.val (P 4) = Lg)
    (h52 : σ.val (P 52) = n) (h180 : σ.val (P 180) = Mlab)
    (hzX : ∀ j : Fin 200, (j.val = 13 ∨ j.val = 14 ∨ j.val = 51 ∨ (54 ≤ j.val ∧ j.val ≤ 58)) → σ.val (P j) = 0)
    (hz : ∀ j : Fin 200, 64 ≤ j.val → j.val ≤ 170 → σ.val (P j) = 0) (hD : σ.sh D = (σ.st D).length)
    (hM : off + Lg + (r4 + 4) * G ≤ Mlab)
    (hcap : lvCap Sv J J ≤ cap) (hdc : d ≤ cap) (hJc : J + 1 ≤ cap) (hSc : Sv ≤ cap) (hlwc : lw ≤ cap)
    (hMc : M ≤ cap) (hcL : 4 * L ≤ cap)
    (hcap3 : Lg * (4 * (4 * Mlab + 4)) + 5 + Lg * (4 * (2 * Mlab + 10)) + 4 * (4 * Mlab + 4) +
      4 * (2 * Mlab + 10) + 7 * Mlab + r4 + G + off + Lg + 20 ≤ cap) (hac3 : CAP + LL ≤ cap)
    (hQc : (8 * L + 2) ^ d * (8 * L + 2) + 2 ≤ cap) (hc4 : c + 8 ≤ cap) (hin : L + c + M + Mlab + n ≤ cap)
    (hnum : ∀ i, evalL (vIn L d c CAP LL M Mlab n lw ((8 * L + 2) ^ d)) PopNums.numOps i ≤ cap)
    (h2c : 2 ≤ cap) (hcV : (J + 1) * (2 * L + 1) + 1 ≤ cap) (hcT : n * ((J + 1) * (2 * L + 1) + 1) ≤ cap) :
    ∃ m τ, WExec cap (popNumW P D) σ τ m ∧
      (∀ i : Fin 200, i.val < 64 →
        τ.val (P i) = xNew L d c R (R + 1) (PopCap.popCapB n R (PopCap.popPW L d Mlab)) J n i.val (σ.val (P i))) ∧
      (∀ T, T ≠ D → τ.sh T = σ.sh T ∧ τ.st T = σ.st T) ∧
      m ≤ numABound cap Sv J M L r4 G off Lg + 1 + numBBound cap J L n d M Mlab lw := by
  subst hc hR
  obtain ⟨w, hw⟩ : ∃ w, w = (Emit.sliceLabs r4 G off Lg).flatMap FiltRec.labE := ⟨_, rfl⟩
  rw [← hw] at hLL
  obtain ⟨mA, eA, bA⟩ := popNumA_spec cap P D σ Sv J M L r4 G off Lg Mlab h20 h21 h44 h45 h1 h2 h3 h4 hz hD hM hcap
    (by rw [← hd]; exact hdc) hJc hSc (by rw [← hlw]; exact hlwc) hMc (by omega) hcap3
    (by rw [← hCAP, ← hw, ← hLL]; exact hac3)
  rw [← hd, ← hlw, ← hCAP, ← hw] at eA
  have rκ := stA_rd P σ D Sv J d M L lw r4 G off Lg CAP w
  obtain ⟨mB, τ, eB, rB, sB, tB, bB⟩ := popNumB_spec cap P (stA P σ D Sv J d M L lw r4 G off Lg CAP w)
    J L n d M Mlab CAP LL lw
    ((rκ 21 (by decide)).trans h21) ((rκ 45 (by decide)).trans h45) ((rκ 52 (by decide)).trans h52)
    (stA_97 P σ D Sv J d M L lw r4 G off Lg CAP w) ((rκ 44 (by decide)).trans h44)
    ((rκ 180 (by decide)).trans h180) (stA_99 P σ D Sv J d M L lw r4 G off Lg CAP w)
    ((stA_100 P σ D Sv J d M L lw r4 G off Lg CAP w).trans hLL.symm)
    (stA_104 P σ D Sv J d M L lw r4 G off Lg CAP w) (stA_150 P σ D Sv J d M L lw r4 G off Lg CAP w)
    (fun j hj => (rκ j (Or.inl (by omega))).trans (hzX j hj))
    (fun j hj => (rκ j (by omega)).trans (hz j (by omega) (by omega)))
    ((rκ 160 (by decide)).trans (hz 160 (by decide) (by decide)))
    ((rκ 161 (by decide)).trans (hz 161 (by decide) (by decide)))
    hQc hc4 hdc hlwc hin hnum (by omega) hcL (by omega) h2c hcV hcT
  obtain ⟨c12, c22, c14⟩ := vIn_caps L d (4 * (lw + L + 1)) CAP LL M Mlab n lw
  refine ⟨mA + 1 + mB, τ, WExec.seq eA eB, fun i hi => ?_, fun T hT => ⟨?_, ?_⟩, ?_⟩
  · rw [rB i hi, rκ i (Or.inl hi), c12, c22, c14]
  · rw [sB, stA_sh P σ D Sv J d M L lw r4 G off Lg CAP w T hT]
  · rw [tB, stA_st P σ D Sv J d M L lw r4 G off Lg CAP w T hT]
  · unfold numBBound
    omega

end NumW

end NearCubicWires.WireExponent3_5.PrimAsm.PopCellNum
