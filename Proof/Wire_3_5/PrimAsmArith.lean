import Proof.Wire_3_5.PrimAsmPopParams

/-! # PA (d), a straight-line unary arithmetic kit (for the call's numbers)

The per-call numbers of the POP row (`PopCap`'s bounds) and of the other writers are polynomials in a few registers.
This module compiles a list of monotone register operations (`b += a`, `a += m`, `c += a·b`) into C5's word language
and proves, once, that the program leaves the registers at the list's value (**`progL_spec`**), under the single
condition that the FINAL values fit the capacity (the operations only increase registers).

Paper quantity: none of its own; it computes the numbers named by `PopCap.popKc`, `popPW`, `popCapB` (next module). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.Arith
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat

/-- A monotone register operation on `k` registers. -/
inductive AOp (k : ℕ) where
  | add (a b : Fin k)
  | inc (a : Fin k) (m : ℕ)
  | mul (a b c : Fin k)

/-- Its effect. -/
def AOp.eval {k : ℕ} (v : Fin k → ℕ) : AOp k → Fin k → ℕ
  | .add a b => Function.update v b (v b + v a)
  | .inc a m => Function.update v a (v a + m)
  | .mul a b c => Function.update v c (v c + v a * v b)

/-- The effect of a list. -/
def evalL {k : ℕ} : (Fin k → ℕ) → List (AOp k) → Fin k → ℕ
  | v, [] => v
  | v, o :: os => evalL (o.eval v) os

/-- The operation's distinctness side condition. -/
def AOp.dist {k : ℕ} : AOp k → Prop
  | .add a b => a ≠ b
  | .inc _ _ => True
  | .mul a b c => a ≠ c ∧ b ≠ c

/-- A cost bound of an operation at capacity `cap`. -/
def AOp.cost {k : ℕ} (cap : ℕ) : AOp k → ℕ
  | .inc _ m => 4 * m
  | _ => 30 * (cap + 1) * (cap + 1)

/-- The cost bound of a list. -/
def costL {k : ℕ} (cap : ℕ) : List (AOp k) → ℕ
  | [] => 0
  | o :: os => o.cost cap + 1 + costL cap os

theorem eval_ge {k : ℕ} (v : Fin k → ℕ) (o : AOp k) (i : Fin k) : v i ≤ o.eval v i := by
  cases o with
  | add a b => simp only [AOp.eval, Function.update_apply]; split_ifs with h <;> [subst h; skip] <;> omega
  | inc a m => simp only [AOp.eval, Function.update_apply]; split_ifs with h <;> [subst h; skip] <;> omega
  | mul a b c => simp only [AOp.eval, Function.update_apply]; split_ifs with h <;> [subst h; skip] <;> omega

theorem evalL_ge {k : ℕ} : ∀ (os : List (AOp k)) (v : Fin k → ℕ) (i : Fin k), v i ≤ evalL v os i
  | [], _, _ => le_rfl
  | o :: os, v, i => le_trans (eval_ge v o i) (evalL_ge os (o.eval v) i)

section Compile
variable {k ns nr : ℕ} (cap : ℕ) (Z : Fin k ↪ Fin nr) (T0 T1 : Fin nr)

/-- The operation in C5's word language (`T0`, `T1` scratch). -/
def AOp.wm : AOp k → WM ns nr
  | .add a b => ParseNat.addTo (Z a) (Z b) T0
  | .inc a m => StarNums.incN (Z a) m
  | .mul a b c => .seq (FinalPass.Hash4.wcopyR (Z b) T1 T0) (.whr T1 (.seq (.dec T1) (ParseNat.addTo (Z a) (Z c) T0)))

/-- The list in C5's word language. -/
def progL : List (AOp k) → WM ns nr
  | [] => .skip
  | o :: os => .seq (o.wm Z T0 T1) (progL os)

/-- The state with the registers `Z` set to `v`. -/
noncomputable def setZ (σ : WState ns nr) (v : Fin k → ℕ) : WState ns nr :=
  ⟨σ.sh, σ.st, fun r => if h : ∃ i, Z i = r then v h.choose else σ.val r, σ.cell⟩

variable {Z}

theorem setZ_val_Z (σ : WState ns nr) (v : Fin k → ℕ) (i : Fin k) : (setZ Z σ v).val (Z i) = v i := by
  have h : ∃ j, Z j = Z i := ⟨i, rfl⟩
  simp only [setZ, dif_pos h]
  exact congrArg v (Z.injective h.choose_spec)

theorem setZ_val_other (σ : WState ns nr) (v : Fin k → ℕ) (r : Fin nr) (hr : ∀ i, Z i ≠ r) :
    (setZ Z σ v).val r = σ.val r := by
  have h : ¬ ∃ i, Z i = r := fun ⟨i, hi⟩ => hr i hi
  simp only [setZ, dif_neg h]

theorem setZ_setv (σ : WState ns nr) (v : Fin k → ℕ) (i : Fin k) (x : ℕ) :
    (setZ Z σ v).setv (Z i) x = setZ Z σ (Function.update v i x) := by
  apply WState.eq
  · rfl
  · rfl
  · funext r
    by_cases hr : ∃ j, Z j = r
    · obtain ⟨j, rfl⟩ := hr
      rw [setZ_val_Z]
      by_cases hji : j = i
      · subst hji; simp
      · rw [wsetv_val_ne _ _ (Z.injective.ne hji), setZ_val_Z, Function.update_of_ne hji]
    · have hne : ∀ j, Z j ≠ r := fun j hj => hr ⟨j, hj⟩
      rw [setZ_val_other _ _ _ hne, wsetv_val_ne _ _ (Ne.symm (hne i)), setZ_val_other _ _ _ hne]
  · rfl

theorem setZ_setv_other (σ : WState ns nr) (v : Fin k → ℕ) (r : Fin nr) (hr : ∀ i, Z i ≠ r) (x : ℕ) :
    (setZ Z σ v).setv r x = setZ Z (σ.setv r x) v := by
  apply WState.eq
  · rfl
  · rfl
  · funext q
    by_cases hq : ∃ j, Z j = q
    · obtain ⟨j, rfl⟩ := hq
      rw [wsetv_val_ne _ _ (hr j), setZ_val_Z, setZ_val_Z]
    · have hne : ∀ j, Z j ≠ q := fun j hj => hq ⟨j, hj⟩
      rw [setZ_val_other _ _ _ hne]
      by_cases hqr : q = r
      · subst hqr; simp
      · rw [wsetv_val_ne _ _ hqr, wsetv_val_ne _ _ hqr, setZ_val_other _ _ _ hne]
  · rfl

theorem setZ_self (σ : WState ns nr) (v : Fin k → ℕ) (hv : ∀ i, σ.val (Z i) = v i) : setZ Z σ v = σ := by
  apply WState.eq
  · rfl
  · rfl
  · funext r
    by_cases hr : ∃ j, Z j = r
    · obtain ⟨j, rfl⟩ := hr
      rw [setZ_val_Z, hv]
    · rw [setZ_val_other _ _ _ fun j hj => hr ⟨j, hj⟩]
  · rfl

variable (Z)

/-- **One operation, run.** -/
theorem op_spec (σ : WState ns nr) (v : Fin k → ℕ) (o : AOp k) (hTZ : ∀ i, Z i ≠ T0 ∧ Z i ≠ T1) (hT : T0 ≠ T1)
    (h0 : σ.val T0 = 0) (h1 : σ.val T1 = 0) (hd : o.dist) (hc : ∀ i, o.eval v i ≤ cap) :
    ∃ n, WExec cap (o.wm Z T0 T1) (setZ Z σ v) (setZ Z σ (o.eval v)) n ∧ n ≤ o.cost cap := by
  have hv : ∀ i, v i ≤ cap := fun i => le_trans (eval_ge v o i) (hc i)
  have hT0 : (setZ Z σ v).val T0 = 0 := by rw [setZ_val_other _ _ _ fun i => (hTZ i).1]; exact h0
  have hT1 : (setZ Z σ v).val T1 = 0 := by rw [setZ_val_other _ _ _ fun i => (hTZ i).2]; exact h1
  cases o with
  | add a b =>
    have hcb := hc b
    simp only [AOp.eval, Function.update_self] at hcb
    have e := ParseNat.addTo_spec cap (Z a) (Z b) T0 (Z.injective.ne hd) (hTZ a).1 (hTZ b).1 (setZ Z σ v) hT0
      (by rw [setZ_val_Z]; exact hv a) (by rw [setZ_val_Z, setZ_val_Z]; exact hcb)
    rw [setZ_val_Z, setZ_val_Z, setZ_setv] at e
    refine ⟨_, e, ?_⟩
    show 18 * v a + 3 ≤ 30 * (cap + 1) * (cap + 1)
    have := hv a
    have : cap + 1 ≤ (cap + 1) * (cap + 1) := Nat.le_mul_self _
    nlinarith
  | inc a m =>
    have hca := hc a
    simp only [AOp.eval, Function.update_self] at hca
    have e := StarNums.incN_spec cap (Z a) m (setZ Z σ v) (by rw [setZ_val_Z]; exact hca)
    rw [setZ_val_Z, setZ_setv] at e
    exact ⟨_, e, le_rfl⟩
  | mul a b c =>
    obtain ⟨hac, hbc⟩ := hd
    have hcc := hc c
    simp only [AOp.eval, Function.update_self] at hcc
    have e1 := FinalPass.Hash4.wcopyR_spec cap (Z b) T1 T0 (hTZ b).2 (hTZ b).1 (Ne.symm hT) (setZ Z σ v) hT1 hT0
      (by rw [setZ_val_Z]; exact hv b)
    rw [setZ_val_Z] at e1
    let S' : ℕ → WState ns nr := fun i => (setZ Z σ (Function.update v c (v c + i * v a))).setv T1 (v b - i)
    have hS0 : S' 0 = (setZ Z σ v).setv T1 (v b) := by
      simp only [S', Nat.zero_mul, Nat.add_zero, Nat.sub_zero, Function.update_eq_self]
    have hloop := UnionMachine.Round.wloop cap T1 (ParseNat.addTo (Z a) (Z c) T0) (18 * v a + 3) (v b) S'
      (fun i _ => by simp [S'])
      (hv b)
      (fun i hi => by
        have hin : (S' i).setv T1 (v b - i - 1) =
            (setZ Z σ (Function.update v c (v c + i * v a))).setv T1 (v b - i - 1) := by
          simp only [S', wsetv_setv]
        rw [hin]
        have hle : v c + (i + 1) * v a ≤ cap := by
          have : (i + 1) * v a ≤ v a * v b := by
            rw [Nat.mul_comm (v a) (v b)]; exact Nat.mul_le_mul_right _ (by omega)
          omega
        have hva : ((setZ Z σ (Function.update v c (v c + i * v a))).setv T1 (v b - i - 1)).val (Z a) = v a := by
          rw [wsetv_val_ne _ _ (hTZ a).2, setZ_val_Z, Function.update_of_ne hac]
        have hvc : ((setZ Z σ (Function.update v c (v c + i * v a))).setv T1 (v b - i - 1)).val (Z c) =
            v c + i * v a := by
          rw [wsetv_val_ne _ _ (hTZ c).2, setZ_val_Z, Function.update_self]
        have e := ParseNat.addTo_spec cap (Z a) (Z c) T0 (Z.injective.ne hac) (hTZ a).1 (hTZ c).1
          ((setZ Z σ (Function.update v c (v c + i * v a))).setv T1 (v b - i - 1))
          (by rw [wsetv_val_ne _ _ hT, setZ_val_other _ _ _ fun j => (hTZ j).1]; exact h0)
          (by rw [hva]; exact hv a)
          (by rw [hva, hvc]; rw [Nat.succ_mul] at hle; omega)
        rw [hva, hvc] at e
        refine WExec.cast cap e ?_ le_rfl
        simp only [S']
        rw [← wsetv_comm _ _ _ (hTZ c).2, setZ_setv, Function.update_idem,
          show v c + i * v a + v a = v c + (i + 1) * v a by ring, show v b - i - 1 = v b - (i + 1) by omega])
    rw [hS0] at hloop
    have hfin : S' (v b) = setZ Z σ (Function.update v c (v c + v a * v b)) := by
      simp only [S', Nat.sub_self]
      rw [setZ_setv_other _ _ _ fun j => (hTZ j).2, LevelW.setv_eq_self (by exact h1), Nat.mul_comm (v b)]
    rw [hfin] at hloop
    refine ⟨_, WExec.seq e1 hloop, ?_⟩
    show 18 * v b + 3 + 1 + (v b * (18 * v a + 3 + 4) + 1) ≤ 30 * (cap + 1) * (cap + 1)
    have ha := hv a
    have hb := hv b
    have : v b * (18 * v a + 7) ≤ cap * (18 * cap + 7) := Nat.mul_le_mul hb (by omega)
    nlinarith

/-- **A list of operations, run**: the registers `Z` end at the list's value, if its final values fit. -/
theorem progL_spec (hTZ : ∀ i, Z i ≠ T0 ∧ Z i ≠ T1) (hT : T0 ≠ T1) :
    ∀ (os : List (AOp k)) (σ : WState ns nr) (v : Fin k → ℕ), σ.val T0 = 0 → σ.val T1 = 0 → (∀ o ∈ os, o.dist) →
      (∀ i, evalL v os i ≤ cap) →
      ∃ n, WExec cap (progL Z T0 T1 os) (setZ Z σ v) (setZ Z σ (evalL v os)) n ∧ n ≤ costL cap os
  | [], σ, v, _, _, _, _ => ⟨0, WExec.skip _, le_rfl⟩
  | o :: os, σ, v, h0, h1, hd, hc => by
    obtain ⟨n1, e1, b1⟩ := op_spec cap Z T0 T1 σ v o hTZ hT h0 h1 (hd o List.mem_cons_self)
      (fun i => le_trans (evalL_ge os (o.eval v) i) (hc i))
    obtain ⟨n2, e2, b2⟩ := progL_spec hTZ hT os σ (o.eval v) h0 h1 (fun o' ho' => hd o' (List.mem_cons_of_mem o ho'))
      (fun i => hc i)
    exact ⟨_, WExec.seq e1 e2, by unfold costL; omega⟩

end Compile

/-! ## One multiplication on plain states -/

theorem mul_spec {k ns nr : ℕ} (cap : ℕ) (Z : Fin k ↪ Fin nr) (T0 T1 : Fin nr) (hTZ : ∀ i, Z i ≠ T0 ∧ Z i ≠ T1)
    (hT : T0 ≠ T1) (σ : WState ns nr) (a b c : Fin k) (hac : a ≠ c) (hbc : b ≠ c) (h0 : σ.val T0 = 0)
    (h1 : σ.val T1 = 0) (hall : ∀ i, σ.val (Z i) ≤ cap) (hcap : σ.val (Z c) + σ.val (Z a) * σ.val (Z b) ≤ cap) :
    ∃ n, WExec cap ((AOp.mul a b c).wm Z T0 T1) σ (σ.setv (Z c) (σ.val (Z c) + σ.val (Z a) * σ.val (Z b))) n ∧
      n ≤ 30 * (cap + 1) * (cap + 1) := by
  have hself : setZ Z σ (fun i => σ.val (Z i)) = σ := setZ_self σ _ fun _ => rfl
  obtain ⟨n, e, hn⟩ := op_spec cap Z T0 T1 σ (fun i => σ.val (Z i)) (AOp.mul a b c) hTZ hT h0 h1 ⟨hac, hbc⟩
    (fun i => by
      simp only [AOp.eval, Function.update_apply]
      split_ifs with h
      · subst h; exact hcap
      · exact hall i)
  rw [hself] at e
  simp only [AOp.eval] at e
  rw [← setZ_setv, hself] at e
  exact ⟨n, e, hn⟩

/-! ## Powers with a register exponent -/

section Pow
variable {ns nr : ℕ} (cap : ℕ) (Z : Fin 3 ↪ Fin nr) (K T0 T1 : Fin nr)

/-- **`Q := X^d`** (`Z 0 = X`, `Z 1 = Q` from `0`, `Z 2` scratch; `K` the exponent counter, `d` read from `D`). -/
def powW (D : Fin nr) : WM ns nr :=
  .seq (.inc (Z 1))
  (.seq (FinalPass.Hash4.wcopyR D K T0)
  (.whr K (.seq (.dec K)
    (.seq ((AOp.mul (0 : Fin 3) 1 2).wm Z T0 T1) (.seq (WM.clear (Z 1)) (WM.move (Z 2) (Z 1)))))))

theorem powW_spec (D : Fin nr) (hTZ : ∀ i, Z i ≠ T0 ∧ Z i ≠ T1 ∧ Z i ≠ K ∧ Z i ≠ D) (hT : T0 ≠ T1)
    (hK0 : K ≠ T0) (hK1 : K ≠ T1) (hKD : K ≠ D) (hD0 : D ≠ T0)
    (σ : WState ns nr) (x d : ℕ) (hx : σ.val (Z 0) = x) (hq : σ.val (Z 1) = 0) (ht : σ.val (Z 2) = 0)
    (hd : σ.val D = d) (hk : σ.val K = 0) (h0 : σ.val T0 = 0) (h1 : σ.val T1 = 0)
    (hc : x ^ d * x + 2 ≤ cap) (hx1 : 1 ≤ x) (hdc : d ≤ cap) :
    ∃ n, WExec cap (powW Z K T0 T1 D) σ (σ.setv (Z 1) (x ^ d)) n ∧
      n ≤ d * (40 * (cap + 1) * (cap + 1) + 20) + 20 * cap + 20 := by
  have hR : ∀ i j : Fin 3, Z i = Z j ↔ i = j := fun i j => Z.injective.eq_iff
  have hne : ∀ {i j : Fin 3}, i ≠ j → Z i ≠ Z j := fun h => Z.injective.ne h
  have hpow : ∀ i ≤ d, x ^ i ≤ x ^ d := fun i hi => Nat.pow_le_pow_right hx1 hi
  have hxd : x ^ d ≤ x ^ d * x := Nat.le_mul_of_pos_right _ hx1
  have hxx : x ≤ x ^ d * x := Nat.le_mul_of_pos_left x (pow_pos hx1 d)
  have e1 := WExec.inc (cap := cap) (Z 1) σ (by rw [hq]; omega)
  rw [hq, Nat.zero_add] at e1
  have e2 := FinalPass.Hash4.wcopyR_spec cap D K T0 (Ne.symm hKD) hD0 hK0 (σ.setv (Z 1) 1)
    (by rw [wsetv_val_ne _ _ (Ne.symm (hTZ 1).2.2.1)]; exact hk) (by rw [wsetv_val_ne _ _ (Ne.symm (hTZ 1).1)]; exact h0)
    (by rw [wsetv_val_ne _ _ (Ne.symm (hTZ 1).2.2.2)]; omega)
  rw [wsetv_val_ne _ _ (Ne.symm (hTZ 1).2.2.2), hd] at e2
  let S' : ℕ → WState ns nr := fun i => (σ.setv (Z 1) (x ^ i)).setv K (d - i)
  have hS0 : S' 0 = (σ.setv (Z 1) 1).setv K d := by simp only [S', pow_zero, Nat.sub_zero]
  have hloop := UnionMachine.Round.wloop cap K
    (.seq ((AOp.mul (0 : Fin 3) 1 2).wm Z T0 T1) (.seq (WM.clear (Z 1)) (WM.move (Z 2) (Z 1))))
    (40 * (cap + 1) * (cap + 1)) d S'
    (fun i _ => by simp [S'])
    hdc
    (fun i hi => by
      have hi' : i + 1 ≤ d := hi
      have hxi : x * x ^ i = x ^ (i + 1) := by rw [pow_succ, Nat.mul_comm]
      have hpi := hpow i (by omega)
      have hpi1 := hpow (i + 1) hi'
      set ρ := (σ.setv (Z 1) (x ^ i)).setv K (d - i - 1) with hρ
      have hin : (S' i).setv K (d - i - 1) = ρ := by simp only [S', hρ, wsetv_setv]
      rw [hin]
      have hρ0 : ρ.val (Z 0) = x := by simp [hρ, hR, (hTZ 0).2.2.1, hx]
      have hρ1 : ρ.val (Z 1) = x ^ i := by simp [hρ, (hTZ 1).2.2.1]
      have hρ2 : ρ.val (Z 2) = 0 := by simp [hρ, hR, (hTZ 2).2.2.1, ht]
      obtain ⟨n1, e3, b3⟩ := mul_spec cap Z T0 T1 (fun j => ⟨(hTZ j).1, (hTZ j).2.1⟩) hT ρ 0 1 2 (by decide) (by decide)
        (by simp [hρ, Ne.symm (hTZ 1).1, hK0.symm, h0]) (by simp [hρ, Ne.symm (hTZ 1).2.1, hK1.symm, h1])
        (fun j => by
          fin_cases j
          · show ρ.val (Z 0) ≤ cap; rw [hρ0]; omega
          · show ρ.val (Z 1) ≤ cap; rw [hρ1]; omega
          · show ρ.val (Z 2) ≤ cap; rw [hρ2]; omega)
        (by rw [hρ0, hρ1, hρ2, hxi]; omega)
      rw [hρ0, hρ1, hρ2, Nat.zero_add, hxi] at e3
      have e4 := wclear_spec cap (Z 1) (x ^ i) (ρ.setv (Z 2) (x ^ (i + 1))) (by simp [hR, hρ1]) (by simp [hR, hρ1]; omega)
      have e5 := wmove_spec cap (Z 2) (Z 1) (hne (by decide)) (x ^ (i + 1)) ((ρ.setv (Z 2) (x ^ (i + 1))).setv (Z 1) 0)
        (by simp [hR]) (by simp [hR]; omega) (by simp [hR]; omega)
      refine WExec.mono (WExec.cast cap (WExec.seq e3 (WExec.seq e4 e5)) ?_ le_rfl) ?_
      · apply WState.eq
        · rfl
        · rfl
        · funext r
          simp only [S', hρ, WState.setv_val, Function.update_apply]
          by_cases r1 : r = Z 1
          · subst r1; simp [hR, (hTZ 1).2.2.1]
          · by_cases r2 : r = Z 2
            · subst r2; simp [hR, (hTZ 2).2.2.1, ht]
            · by_cases rK : r = K
              · subst rK; simp [r1, r2]; omega
              · simp [r1, r2, rK]
        · rfl
      · have hsq : cap + 1 ≤ (cap + 1) * (cap + 1) := Nat.le_mul_self _
        have : 3 * x ^ i + 1 + 1 + (7 * x ^ (i + 1) + 1) ≤ 10 * (cap + 1) := by omega
        nlinarith)
  rw [hS0] at hloop
  simp only [S', Nat.sub_self] at hloop
  refine ⟨_, WExec.cast cap (WExec.seq e1 (WExec.seq e2 hloop)) ?_ le_rfl, ?_⟩
  · rw [LevelW.setv_eq_self (show (σ.setv (Z 1) (x ^ d)).val K = 0 by
      rw [wsetv_val_ne _ _ (Ne.symm (hTZ 1).2.2.1)]; exact hk)]
  · have hsq : cap + 1 ≤ (cap + 1) * (cap + 1) := Nat.le_mul_self _
    nlinarith

end Pow

end NearCubicWires.WireExponent3_5.PrimAsm.Arith
