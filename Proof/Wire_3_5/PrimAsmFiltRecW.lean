import Proof.Wire_3_5.PrimAsmEmit

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.FiltRecW
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec NearCubicWires.WireExponent3_5.PrimAsm.Emit

variable {ns nr : ℕ} (cap : ℕ)

abbrev FReg (nr : ℕ) := Fin 20 ↪ Fin nr

/-- The label registers inside `FReg`. -/
def lR : Fin 13 ↪ Fin 20 := ⟨fun i => ⟨i.val, by omega⟩, fun i j h => Fin.ext (by simpa using congrArg Fin.val h)⟩

section Prog
variable (O S : Fin (ns + 1)) (F : FReg nr)

/-- `A` copies of `u` then the constant `v`. -/
def repThen (A : Fin 20) (u v : List Bool) : WM ns nr := .seq (repRegW O (F 0) (F A) (F 19) (F 9) u) (emitW O (F 0) v)

/-- Phase A: the bank's first fields. -/
def phaseA : WM ns nr :=
  .seq (repThen O F 13 (m3 false) (m2 false ++ [true, false]))
  (.seq (repThen O F 13 (m3 false) (m2 false ++ [true, false]))
  (.seq (emitW O (F 0) ((m2 false ++ [true, false]) ++ (m2 false ++ [true, false]) ++ (m2 false ++ [true, false]) ++ (m2 true ++ [true, false]) ++ (m2 false ++ [true, false])))
  (.seq (repThen O F 13 (m3 false) (m2 false ++ [true, false]))
  (.seq (repThen O F 13 (m3 false) (m2 false ++ [true, false]))
  (repThen O F 14 (m2 true) (m2 false ++ [true, false]))))))

/-- Phase B: the labels, their log, the empty field. -/
def phaseB : WM ns nr :=
  .seq (incN (F 11) 5)
  (.seq (labsW O (lR.trans F))
  (.seq (emitW O (F 0) (m2 false ++ [true, false]))
  (.seq (repW O (F 0) (F 11) (m2 false))
  (emitW O (F 0) ([true, false] ++ [true, false])))))

/-- Phase C: the table word. -/
def phaseC : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (F 17) (F 19) (F 9))
  (.seq (copyLoop O S (F 0) (F 18) (F 19))
  (emitW O (F 0) [true, false]))

/-- Phase D: the evaluator's other data fields and the record's end. -/
def phaseD : WM ns nr :=
  .seq (repThen O F 15 (m2 true) (m2 false ++ [true, false]))
  (.seq (repThen O F 16 (m2 false) [true, false])
  (.seq (emitW O (F 0) (m2 true ++ [true, false]))
  (.seq (repThen O F 16 (m2 false) [true, false])
  (.seq (repThen O F 16 (m2 false) [true, false])
  (.seq (repThen O F 16 (m2 false) [true, false])
  (.seq (repThen O F 16 (m2 false) [true, false])
  (.seq (repThen O F 16 (m2 false) [true, false])
  (.seq (repThen O F 16 (m2 false) [true, false])
  (.seq (repThen O F 16 (m2 false) [true, false])
  (emitW O (F 0) [false]))))))))))

/-- **The FILTER row's input word.** -/
def filtRecW : WM ns nr := .seq (phaseA O F) (.seq (phaseB O F) (.seq (phaseC O S F) (phaseD O F)))

/-- The program's state: the output extended by `u`, the table stream (and its counter) advanced by `s`. -/
def fSt (σ : WState ns nr) (u : List Bool) (s : ℕ) : WState ns nr :=
  ((appendO σ O (F 0) u).seth S (σ.sh S + s)).setv (F 18) (σ.val (F 18) + s)

section FSt
variable {O S F}

theorem fSt_val (σ : WState ns nr) (u : List Bool) (s : ℕ) (j : Fin nr) :
    (fSt O S F σ u s).val j = if j = F 18 then σ.val (F 18) + s else if j = F 0 then σ.val (F 0) + u.length
      else σ.val j := by
  simp only [fSt, WState.setv_val, WState.seth_val, appendO_val, Function.update_apply]

theorem fSt_shO (hOS : O ≠ S) (σ : WState ns nr) (u : List Bool) (s : ℕ) :
    (fSt O S F σ u s).sh O = σ.sh O + u.length := by simp [fSt, Function.update_apply, hOS]

theorem fSt_stO (σ : WState ns nr) (u : List Bool) (s : ℕ) :
    (fSt O S F σ u s).st O = σ.st O ++ u := by simp [fSt, Function.update_apply]

theorem fSt_append (hOS : O ≠ S) (σ : WState ns nr) (u v : List Bool) (s : ℕ) :
    appendO (fSt O S F σ u s) O (F 0) v = fSt O S F σ (u ++ v) s := by
  have hR : ∀ i j : Fin 20, F i = F j ↔ i = j := fun i j => F.injective.eq_iff
  unfold fSt
  rw [appendO_setv _ O (F 0) (F 18) (by simp [hR])]
  congr 1
  unfold appendO
  apply WState.eq
  · funext j
    by_cases hjO : j = O
    · subst hjO; simp [Function.update_apply, hOS]; omega
    · by_cases hjS : j = S
      · subst hjS; simp [Function.update_apply, hjO, Ne.symm hOS]
      · simp [Function.update_apply, hjO, hjS]
  · simp [Function.update_apply, hOS]
  · simp [Function.update_apply, Nat.add_assoc]
  · simp

theorem fSt_zero (σ : WState ns nr) : fSt O S F σ [] 0 = σ := by
  unfold fSt; rw [appendO_nil, Nat.add_zero, Nat.add_zero]
  apply WState.eq
  · funext j; by_cases hj : j = S
    · subst hj; simp
    · simp [Function.update_apply, hj]
  · simp
  · simp
  · simp

end FSt

end Prog

section Spec
variable (O S : Fin (ns + 1)) (F : FReg nr)

theorem repThen_spec (hOS : O ≠ S) (σ : WState ns nr) (u0 : List Bool) (s : ℕ) (A : Fin 20) (hA : A ≠ 19)
    (hA9 : A ≠ 9) (hA0 : A ≠ 0) (hA18 : A ≠ 18) (u v : List Bool) (n : ℕ) (hn : σ.val (F A) = n)
    (h19 : σ.val (F 19) = 0) (h9 : σ.val (F 9) = 0) (ho : σ.sh O = (σ.st O).length)
    (hc : σ.val (F 0) + u0.length + n * u.length + v.length ≤ cap) (hncap : n ≤ cap) :
    WExec cap (repThen O F A u v) (fSt O S F σ u0 s) (fSt O S F σ (u0 ++ (reps n u ++ v)) s)
      (18 * n + 3 + 1 + (n * (8 * u.length + 4) + 1) + 1 + 8 * v.length) := by
  have hR : ∀ i j : Fin 20, F i = F j ↔ i = j := fun i j => F.injective.eq_iff
  have hvA : (fSt O S F σ u0 s).val (F A) = n := by rw [fSt_val]; simp [hR, hA0, hA18, hn]
  have h1 := repRegW_spec cap O (F 0) (F A) (F 19) (F 9) (by simp [hR, hA]) (by simp [hR, hA9]) (by simp [hR])
    (by simp [hR]) u (fSt O S F σ u0 s) (by rw [fSt_val]; simp [hR, h19]) (by rw [fSt_val]; simp [hR, h9])
    (by rw [fSt_shO hOS, fSt_stO, ho]; simp) (by rw [hvA]; exact hncap)
    (by rw [hvA, fSt_val]; simp [hR]; omega)
  rw [hvA, fSt_append hOS] at h1
  have h2 := Emit.emitW_spec cap O (F 0) v (fSt O S F σ (u0 ++ reps n u) s)
    (by rw [fSt_shO hOS, fSt_stO, ho]; simp) (by rw [fSt_val]; simp [hR, reps]; omega)
  rw [fSt_append hOS, List.append_assoc] at h2
  exact WExec.seq h1 h2

theorem reps_length (n : ℕ) (u : List Bool) : (reps n u).length = n * u.length := by
  induction n with
  | zero => simp
  | succ n ih => rw [reps_succ, List.length_append, ih, Nat.succ_mul]

theorem emitF (hOS : O ≠ S) (σ : WState ns nr) (u : List Bool) (s : ℕ) (v : List Bool)
    (ho : σ.sh O = (σ.st O).length) (hc : σ.val (F 0) + u.length + v.length ≤ cap) :
    WExec cap (Emit.emitW O (F 0) v) (fSt O S F σ u s) (fSt O S F σ (u ++ v) s) (8 * v.length) := by
  have hR : ∀ i j : Fin 20, F i = F j ↔ i = j := fun i j => F.injective.eq_iff
  have h := Emit.emitW_spec cap O (F 0) v (fSt O S F σ u s) (by rw [fSt_shO hOS, fSt_stO, ho]; simp)
    (by rw [fSt_val]; simp [hR]; omega)
  rwa [fSt_append hOS] at h

theorem emitF11 (hOS : O ≠ S) (σ : WState ns nr) (u : List Bool) (x : ℕ) (v : List Bool)
    (ho : σ.sh O = (σ.st O).length) (hc : σ.val (F 0) + u.length + v.length ≤ cap) :
    WExec cap (Emit.emitW O (F 0) v) ((fSt O S F σ u 0).setv (F 11) x) ((fSt O S F σ (u ++ v) 0).setv (F 11) x)
      (8 * v.length) := by
  have hR : ∀ i j : Fin 20, F i = F j ↔ i = j := fun i j => F.injective.eq_iff
  have h := Emit.emitW_spec cap O (F 0) v ((fSt O S F σ u 0).setv (F 11) x) (by simp [fSt, Function.update_apply, hOS, ho])
    (by simp only [WState.setv_val, Function.update_apply]; rw [fSt_val]; simp [hR]; omega)
  rwa [appendO_setv _ O (F 0) (F 11) (by simp [hR]), fSt_append hOS] at h

theorem fSt_copy (hOS : O ≠ S) (σ : WState ns nr) (u v : List Bool) (n m : ℕ) (h19 : σ.val (F 19) = 0) :
    ((((appendO ((fSt O S F σ u 0).setv (F 19) n) O (F 0) v).seth S
      (((fSt O S F σ u 0).setv (F 19) n).sh S + m)).setv (F 18)
      (((fSt O S F σ u 0).setv (F 19) n).val (F 18) + m)).setv (F 19) 0) = fSt O S F σ (u ++ v) m := by
  have hR : ∀ i j : Fin 20, F i = F j ↔ i = j := fun i j => F.injective.eq_iff
  unfold fSt appendO
  apply WState.eq
  · funext j
    by_cases hjO : j = O
    · subst hjO; simp [Function.update_apply, hOS]; omega
    · by_cases hjS : j = S
      · subst hjS; simp [Function.update_apply, Ne.symm hOS]
      · simp [Function.update_apply, hjO, hjS]
  · simp [Function.update_apply, hOS]
  · funext j
    simp only [WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all <;> omega
  · simp

theorem fSt_setv_zero (σ : WState ns nr) (u : List Bool) (s : ℕ) (j : Fin 20) (hj0 : j ≠ 0) (hj18 : j ≠ 18)
    (h : σ.val (F j) = 0) : (fSt O S F σ u s).setv (F j) 0 = fSt O S F σ u s := by
  have hR : ∀ i j : Fin 20, F i = F j ↔ i = j := fun i j => F.injective.eq_iff
  unfold fSt appendO
  apply WState.eq
  · simp
  · simp
  · funext x
    simp only [WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  · simp

/-- The phases' output words. -/
def pieceA (Lp d : ℕ) : List Bool := ((reps Lp (m3 false) ++ (m2 false ++ [true, false])) ++ (reps Lp (m3 false) ++ (m2 false ++ [true, false])) ++ ((m2 false ++ [true, false]) ++ (m2 false ++ [true, false]) ++ (m2 false ++ [true, false]) ++ (m2 true ++ [true, false]) ++ (m2 false ++ [true, false])) ++ (reps Lp (m3 false) ++ (m2 false ++ [true, false])) ++ (reps Lp (m3 false) ++ (m2 false ++ [true, false])) ++ (reps d (m2 true) ++ (m2 false ++ [true, false])))

def pieceB (labs : List ℕ) (cap1 : ℕ) : List Bool := labs.flatMap labE ++ (m2 false ++ [true, false]) ++ reps cap1 (m2 false) ++ ([true, false] ++ [true, false])

def pieceC (w : List Bool) : List Bool := w.flatMap m2 ++ [true, false]

def pieceD (thr c : ℕ) : List Bool := ((reps thr (m2 true) ++ (m2 false ++ [true, false])) ++ (reps (c + 1) (m2 false) ++ [true, false]) ++ (m2 true ++ [true, false]) ++ (reps (c + 1) (m2 false) ++ [true, false]) ++ (reps (c + 1) (m2 false) ++ [true, false]) ++ (reps (c + 1) (m2 false) ++ [true, false]) ++ (reps (c + 1) (m2 false) ++ [true, false]) ++ (reps (c + 1) (m2 false) ++ [true, false]) ++ (reps (c + 1) (m2 false) ++ [true, false]) ++ (reps (c + 1) (m2 false) ++ [true, false]) ++ [false])

theorem phaseA_spec (hOS : O ≠ S) (σ : WState ns nr) (u0 : List Bool)
    (h19 : σ.val (F 19) = 0) (h9 : σ.val (F 9) = 0) (ho : σ.sh O = (σ.st O).length) (Lp d : ℕ) (h13 : σ.val (F 13) = Lp) (h14 : σ.val (F 14) = d)
    (hcap : σ.val (F 0) + u0.length + 4 * (8 * Lp + 6) + 30 + 4 * d + 6 + Lp + d + 10 ≤ cap) :
    ∃ n, WExec cap (phaseA O F) (fSt O S F σ u0 0) (fSt O S F σ (u0 ++ pieceA Lp d) 0) n ∧ n ≤ 400 * (Lp + d + 10) := by
  have hR : ∀ i j : Fin 20, F i = F j ↔ i = j := fun i j => F.injective.eq_iff
  obtain ⟨u1, hu1⟩ : ∃ x : List Bool, x = u0 ++ (reps Lp (m3 false) ++ (m2 false ++ [true, false])) := ⟨_, rfl⟩
  have hl1 : u1.length = (u0).length + ((reps Lp (m3 false) ++ (m2 false ++ [true, false]))).length := by rw [hu1, List.length_append]
  obtain ⟨u2, hu2⟩ : ∃ x : List Bool, x = u1 ++ (reps Lp (m3 false) ++ (m2 false ++ [true, false])) := ⟨_, rfl⟩
  have hl2 : u2.length = (u1).length + ((reps Lp (m3 false) ++ (m2 false ++ [true, false]))).length := by rw [hu2, List.length_append]
  obtain ⟨u3, hu3⟩ : ∃ x : List Bool, x = u2 ++ ((m2 false ++ [true, false]) ++ (m2 false ++ [true, false]) ++ (m2 false ++ [true, false]) ++ (m2 true ++ [true, false]) ++ (m2 false ++ [true, false])) := ⟨_, rfl⟩
  have hl3 : u3.length = (u2).length + (((m2 false ++ [true, false]) ++ (m2 false ++ [true, false]) ++ (m2 false ++ [true, false]) ++ (m2 true ++ [true, false]) ++ (m2 false ++ [true, false]))).length := by rw [hu3, List.length_append]
  obtain ⟨u4, hu4⟩ : ∃ x : List Bool, x = u3 ++ (reps Lp (m3 false) ++ (m2 false ++ [true, false])) := ⟨_, rfl⟩
  have hl4 : u4.length = (u3).length + ((reps Lp (m3 false) ++ (m2 false ++ [true, false]))).length := by rw [hu4, List.length_append]
  obtain ⟨u5, hu5⟩ : ∃ x : List Bool, x = u4 ++ (reps Lp (m3 false) ++ (m2 false ++ [true, false])) := ⟨_, rfl⟩
  have hl5 : u5.length = (u4).length + ((reps Lp (m3 false) ++ (m2 false ++ [true, false]))).length := by rw [hu5, List.length_append]
  obtain ⟨u6, hu6⟩ : ∃ x : List Bool, x = u5 ++ (reps d (m2 true) ++ (m2 false ++ [true, false])) := ⟨_, rfl⟩
  have hl6 : u6.length = (u5).length + ((reps d (m2 true) ++ (m2 false ++ [true, false]))).length := by rw [hu6, List.length_append]
  simp only [reps_length, m2, m3, List.length_append, List.length_cons, List.length_nil] at hl1 hl2 hl3 hl4 hl5 hl6
  have e1 := repThen_spec cap O S F hOS σ u0 0 13 (by decide) (by decide) (by decide) (by decide) (m3 false) (m2 false ++ [true, false]) Lp h13 h19 h9 ho
    (by simp only [reps_length, m2, m3, List.length_append, List.length_cons, List.length_nil]; omega) (by omega)
  rw [← hu1] at e1
  have e2 := repThen_spec cap O S F hOS σ u1 0 13 (by decide) (by decide) (by decide) (by decide) (m3 false) (m2 false ++ [true, false]) Lp h13 h19 h9 ho
    (by simp only [reps_length, m2, m3, List.length_append, List.length_cons, List.length_nil]; omega) (by omega)
  rw [← hu2] at e2
  have e3 := emitF cap O S F hOS σ u2 0 ((m2 false ++ [true, false]) ++ (m2 false ++ [true, false]) ++ (m2 false ++ [true, false]) ++ (m2 true ++ [true, false]) ++ (m2 false ++ [true, false])) ho (by simp only [m2, List.length_append, List.length_cons, List.length_nil]; omega)
  rw [← hu3] at e3
  have e4 := repThen_spec cap O S F hOS σ u3 0 13 (by decide) (by decide) (by decide) (by decide) (m3 false) (m2 false ++ [true, false]) Lp h13 h19 h9 ho
    (by simp only [reps_length, m2, m3, List.length_append, List.length_cons, List.length_nil]; omega) (by omega)
  rw [← hu4] at e4
  have e5 := repThen_spec cap O S F hOS σ u4 0 13 (by decide) (by decide) (by decide) (by decide) (m3 false) (m2 false ++ [true, false]) Lp h13 h19 h9 ho
    (by simp only [reps_length, m2, m3, List.length_append, List.length_cons, List.length_nil]; omega) (by omega)
  rw [← hu5] at e5
  have e6 := repThen_spec cap O S F hOS σ u5 0 14 (by decide) (by decide) (by decide) (by decide) (m2 true) (m2 false ++ [true, false]) d h14 h19 h9 ho
    (by simp only [reps_length, m2, m3, List.length_append, List.length_cons, List.length_nil]; omega) (by omega)
  rw [← hu6] at e6
  have hfin : u6 = u0 ++ pieceA Lp d := by
    rw [hu6, hu5, hu4, hu3, hu2, hu1]; unfold pieceA; simp only [List.append_assoc]
  rw [hfin] at e6
  refine ⟨_, WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 e6)))), ?_⟩
  simp only [reps_length, m2, m3, List.length_append, List.length_cons, List.length_nil]
  omega

theorem phaseB_spec (hOS : O ≠ S) (σ : WState ns nr) (u0 : List Bool)
    (h9 : σ.val (F 9) = 0) (ho : σ.sh O = (σ.st O).length) (r4 G off Lg : ℕ) (h1 : σ.val (F 1) = r4) (h2 : σ.val (F 2) = G)
    (h3 : σ.val (F 3) = off) (h4 : σ.val (F 4) = Lg) (h5 : σ.val (F 5) = 0) (h6 : σ.val (F 6) = 0)
    (h7 : σ.val (F 7) = 0) (h8 : σ.val (F 8) = 0) (h10 : σ.val (F 10) = 0) (h11 : σ.val (F 11) = 0)
    (h12 : σ.val (F 12) = 0) (M : ℕ) (hM : off + Lg + (r4 + 4) * G ≤ M) (LL CAP : ℕ)
    (hLL : ((sliceLabs r4 G off Lg).flatMap labE).length = LL) (hCAP : labSum (sliceLabs r4 G off Lg) = CAP)
    (hcap : σ.val (F 0) + u0.length + LL + 4 * CAP + 10 +
      Lg * (4 * (4 * M + 4)) + Lg * (4 * (2 * M + 10)) + 4 * (4 * M + 4) + 4 * (2 * M + 10) + 7 * M + r4 + G + off +
      Lg + CAP + 40 ≤ cap) :
    ∃ n, WExec cap (phaseB O F) (fSt O S F σ u0 0)
      (fSt O S F σ (u0 ++ pieceB (sliceLabs r4 G off Lg) (labSum (sliceLabs r4 G off Lg))) 0) n ∧
      n ≤ 100 * (labSum (sliceLabs r4 G off Lg) + 10) + labsCost r4 G off Lg := by
  have hR : ∀ i j : Fin 20, F i = F j ↔ i = j := fun i j => F.injective.eq_iff
  subst hLL hCAP
  obtain ⟨u8, hu8⟩ : ∃ x : List Bool, x = u0 ++ ((sliceLabs r4 G off Lg).flatMap labE) := ⟨_, rfl⟩
  have hl8 : u8.length = (u0).length + (((sliceLabs r4 G off Lg).flatMap labE)).length := by rw [hu8, List.length_append]
  obtain ⟨u9, hu9⟩ : ∃ x : List Bool, x = u8 ++ (m2 false ++ [true, false]) := ⟨_, rfl⟩
  have hl9 : u9.length = (u8).length + ((m2 false ++ [true, false])).length := by rw [hu9, List.length_append]
  obtain ⟨u10, hu10⟩ : ∃ x : List Bool, x = u9 ++ (reps (labSum (sliceLabs r4 G off Lg)) (m2 false)) := ⟨_, rfl⟩
  have hl10 : u10.length = (u9).length + ((reps (labSum (sliceLabs r4 G off Lg)) (m2 false))).length := by rw [hu10, List.length_append]
  obtain ⟨u11, hu11⟩ : ∃ x : List Bool, x = u10 ++ ([true, false] ++ [true, false]) := ⟨_, rfl⟩
  have hl11 : u11.length = (u10).length + (([true, false] ++ [true, false])).length := by rw [hu11, List.length_append]
  simp only [reps_length, m2, m3, List.length_append, List.length_cons, List.length_nil] at hl8 hl9 hl10 hl11
  have e7 := Emit.incN_spec cap (F 11) 5 (fSt O S F σ u0 0) (by rw [fSt_val]; simp [hR, h11]; omega)
  rw [show (fSt O S F σ u0 0).val (F 11) + 5 = 5 by rw [fSt_val]; simp [hR, h11]] at e7
  have hlR : ∀ i : Fin 13, (lR.trans F) i = F ⟨i.val, by omega⟩ := fun i => rfl
  have e8 := labsW_spec cap O (lR.trans F) ((fSt O S F σ u0 0).setv (F 11) 5) r4 G off Lg 5
    (by rw [hlR]; simp [fSt_val, hR, h1]) (by rw [hlR]; simp [fSt_val, hR, h2]) (by rw [hlR]; simp [fSt_val, hR, h3])
    (by rw [hlR]; simp [fSt_val, hR, h4]) (by rw [hlR]; simp [fSt_val, hR, h5]) (by rw [hlR]; simp [fSt_val, hR, h6])
    (by rw [hlR]; simp [fSt_val, hR, h7]) (by rw [hlR]; simp [fSt_val, hR, h8]) (by rw [hlR]; simp [fSt_val, hR, h9])
    (by rw [hlR]; simp [fSt_val, hR, h10]) (by rw [hlR]; simp [fSt_val, hR, h12]) (by rw [hlR]; simp [fSt_val, hR])
    (by simp [fSt, Function.update_apply, hOS, ho]) M hM
    (by rw [hlR]; simp only [WState.setv_val, Function.update_apply]; rw [fSt_val]; simp [hR]; omega)
  rw [hlR 0, hlR 11] at e8
  simp only [show (⟨(0 : Fin 13).val, by omega⟩ : Fin 20) = 0 from rfl,
    show (⟨(11 : Fin 13).val, by omega⟩ : Fin 20) = 11 from rfl] at e8
  rw [appendO_setv _ O (F 0) (F 11) (by simp [hR]), fSt_append hOS, wsetv_setv, ← hu8] at e8
  have hls : 5 + labAdd (sliceLabs r4 G off Lg) = labSum (sliceLabs r4 G off Lg) := by unfold labSum labAdd; rfl
  rw [hls] at e8
  have e9 := emitF11 cap O S F hOS σ u8 (labSum (sliceLabs r4 G off Lg)) (m2 false ++ [true, false]) ho
    (by simp only [m2, List.length_append, List.length_cons, List.length_nil]; omega)
  rw [← hu9] at e9
  have e10 := Emit.repW_spec cap O (F 0) (F 11) (by simp [hR]) (m2 false) (labSum (sliceLabs r4 G off Lg))
    ((fSt O S F σ u9 0).setv (F 11) (labSum (sliceLabs r4 G off Lg)))
    (by simp) (by simp [fSt, Function.update_apply, hOS, ho])
    (by simp only [WState.setv_val, Function.update_apply]; rw [fSt_val]; simp [hR, m2]; omega) (by omega)
  rw [appendO_setv _ O (F 0) (F 11) (by simp [hR]), fSt_append hOS, wsetv_setv, ← hu10,
    fSt_setv_zero O S F σ u10 0 11 (by decide) (by decide) h11] at e10
  have e11 := emitF cap O S F hOS σ u10 0 ([true, false] ++ [true, false]) ho (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  rw [← hu11] at e11
  have hfin : u11 = u0 ++ pieceB (sliceLabs r4 G off Lg) (labSum (sliceLabs r4 G off Lg)) := by
    rw [hu11, hu10, hu9, hu8]; unfold pieceB; simp only [List.append_assoc]
  rw [hfin] at e11
  refine ⟨_, WExec.seq e7 (WExec.seq e8 (WExec.seq e9 (WExec.seq e10 e11))), ?_⟩
  simp only [reps_length, m2, m3, List.length_append, List.length_cons, List.length_nil]
  omega

theorem phaseC_spec (hOS : O ≠ S) (σ : WState ns nr) (u0 : List Bool)
    (h19 : σ.val (F 19) = 0) (h9 : σ.val (F 9) = 0) (ho : σ.sh O = (σ.st O).length) (w : List Bool) (h17 : σ.val (F 17) = w.length)
    (hw : ∀ i < w.length, readTapeBit (σ.st S) (σ.sh S + i) = w.getD i false)
    (hcap : σ.val (F 0) + u0.length + 4 * w.length + 2 + w.length + σ.val (F 18) + 5 ≤ cap) :
    ∃ n, WExec cap (phaseC O S F) (fSt O S F σ u0 0) (fSt O S F σ (u0 ++ pieceC w) w.length) n ∧
      n ≤ 100 * (w.length + 1) := by
  have hR : ∀ i j : Fin 20, F i = F j ↔ i = j := fun i j => F.injective.eq_iff
  have hm2 : (w.flatMap m2).length = 4 * w.length := by rw [List.length_flatMap]; simp [m2]; omega
  have e12 := FinalPass.Hash4.wcopyR_spec cap (F 17) (F 19) (F 9) (by simp [hR]) (by simp [hR]) (by simp [hR])
    (fSt O S F σ u0 0) (by rw [fSt_val]; simp [hR, h19]) (by rw [fSt_val]; simp [hR, h9])
    (by rw [fSt_val]; simp [hR, h17]; omega)
  rw [show (fSt O S F σ u0 0).val (F 17) = w.length by rw [fSt_val]; simp [hR, h17]] at e12
  have e13 := Emit.copyLoop_spec cap O S hOS (F 0) (F 18) (F 19) (by simp [hR]) (by simp [hR]) (by simp [hR]) w
    ((fSt O S F σ u0 0).setv (F 19) w.length) (by simp)
    (by intro i hi; simp [fSt, Function.update_apply, Ne.symm hOS]; exact hw i hi)
    (by simp [fSt, Function.update_apply, hOS, ho])
    (by simp only [WState.setv_val, Function.update_apply]; rw [fSt_val]; simp [hR]; omega)
    (by simp only [WState.setv_val, Function.update_apply]; rw [fSt_val]; simp [hR]; omega) (by omega)
  rw [fSt_copy O S F hOS σ u0 (w.flatMap m2) w.length w.length h19] at e13
  have e14 := emitF cap O S F hOS σ (u0 ++ w.flatMap m2) w.length [true, false] ho
    (by simp only [List.length_append, List.length_cons, List.length_nil, hm2]; omega)
  rw [List.append_assoc] at e14
  rw [show w.flatMap m2 ++ [true, false] = pieceC w from rfl] at e14
  refine ⟨_, WExec.seq e12 (WExec.seq e13 e14), ?_⟩
  simp only [List.length_cons, List.length_nil]
  omega

theorem phaseD_spec (hOS : O ≠ S) (σ : WState ns nr) (u0 : List Bool)
    (h19 : σ.val (F 19) = 0) (h9 : σ.val (F 9) = 0) (ho : σ.sh O = (σ.st O).length) (s thr c : ℕ) (h15 : σ.val (F 15) = thr) (h16 : σ.val (F 16) = c + 1)
    (hcap : σ.val (F 0) + u0.length + 4 * thr + 6 + 8 * (4 * (c + 1) + 2) + 7 + thr + c + 10 ≤ cap) :
    ∃ n, WExec cap (phaseD O F) (fSt O S F σ u0 s) (fSt O S F σ (u0 ++ pieceD thr c) s) n ∧
      n ≤ 600 * (thr + c + 10) := by
  have hR : ∀ i j : Fin 20, F i = F j ↔ i = j := fun i j => F.injective.eq_iff
  obtain ⟨u15, hu15⟩ : ∃ x : List Bool, x = u0 ++ (reps thr (m2 true) ++ (m2 false ++ [true, false])) := ⟨_, rfl⟩
  have hl15 : u15.length = (u0).length + ((reps thr (m2 true) ++ (m2 false ++ [true, false]))).length := by rw [hu15, List.length_append]
  obtain ⟨u16, hu16⟩ : ∃ x : List Bool, x = u15 ++ (reps (c + 1) (m2 false) ++ [true, false]) := ⟨_, rfl⟩
  have hl16 : u16.length = (u15).length + ((reps (c + 1) (m2 false) ++ [true, false])).length := by rw [hu16, List.length_append]
  obtain ⟨u17, hu17⟩ : ∃ x : List Bool, x = u16 ++ (m2 true ++ [true, false]) := ⟨_, rfl⟩
  have hl17 : u17.length = (u16).length + ((m2 true ++ [true, false])).length := by rw [hu17, List.length_append]
  obtain ⟨u18, hu18⟩ : ∃ x : List Bool, x = u17 ++ (reps (c + 1) (m2 false) ++ [true, false]) := ⟨_, rfl⟩
  have hl18 : u18.length = (u17).length + ((reps (c + 1) (m2 false) ++ [true, false])).length := by rw [hu18, List.length_append]
  obtain ⟨u19, hu19⟩ : ∃ x : List Bool, x = u18 ++ (reps (c + 1) (m2 false) ++ [true, false]) := ⟨_, rfl⟩
  have hl19 : u19.length = (u18).length + ((reps (c + 1) (m2 false) ++ [true, false])).length := by rw [hu19, List.length_append]
  obtain ⟨u20, hu20⟩ : ∃ x : List Bool, x = u19 ++ (reps (c + 1) (m2 false) ++ [true, false]) := ⟨_, rfl⟩
  have hl20 : u20.length = (u19).length + ((reps (c + 1) (m2 false) ++ [true, false])).length := by rw [hu20, List.length_append]
  obtain ⟨u21, hu21⟩ : ∃ x : List Bool, x = u20 ++ (reps (c + 1) (m2 false) ++ [true, false]) := ⟨_, rfl⟩
  have hl21 : u21.length = (u20).length + ((reps (c + 1) (m2 false) ++ [true, false])).length := by rw [hu21, List.length_append]
  obtain ⟨u22, hu22⟩ : ∃ x : List Bool, x = u21 ++ (reps (c + 1) (m2 false) ++ [true, false]) := ⟨_, rfl⟩
  have hl22 : u22.length = (u21).length + ((reps (c + 1) (m2 false) ++ [true, false])).length := by rw [hu22, List.length_append]
  obtain ⟨u23, hu23⟩ : ∃ x : List Bool, x = u22 ++ (reps (c + 1) (m2 false) ++ [true, false]) := ⟨_, rfl⟩
  have hl23 : u23.length = (u22).length + ((reps (c + 1) (m2 false) ++ [true, false])).length := by rw [hu23, List.length_append]
  obtain ⟨u24, hu24⟩ : ∃ x : List Bool, x = u23 ++ (reps (c + 1) (m2 false) ++ [true, false]) := ⟨_, rfl⟩
  have hl24 : u24.length = (u23).length + ((reps (c + 1) (m2 false) ++ [true, false])).length := by rw [hu24, List.length_append]
  obtain ⟨u25, hu25⟩ : ∃ x : List Bool, x = u24 ++ [false] := ⟨_, rfl⟩
  have hl25 : u25.length = (u24).length + ([false]).length := by rw [hu25, List.length_append]
  simp only [reps_length, m2, m3, List.length_append, List.length_cons, List.length_nil] at hl15 hl16 hl17 hl18 hl19 hl20 hl21 hl22 hl23 hl24 hl25
  have e15 := repThen_spec cap O S F hOS σ u0 s 15 (by decide) (by decide) (by decide) (by decide) (m2 true) (m2 false ++ [true, false]) thr h15 h19 h9 ho
    (by simp only [reps_length, m2, m3, List.length_append, List.length_cons, List.length_nil]; omega) (by omega)
  rw [← hu15] at e15
  have e16 := repThen_spec cap O S F hOS σ u15 s 16 (by decide) (by decide) (by decide) (by decide) (m2 false) [true, false] (c + 1) h16 h19 h9 ho
    (by simp only [reps_length, m2, m3, List.length_append, List.length_cons, List.length_nil]; omega) (by omega)
  rw [← hu16] at e16
  have e17 := emitF cap O S F hOS σ u16 s (m2 true ++ [true, false]) ho (by simp only [m2, List.length_append, List.length_cons, List.length_nil]; omega)
  rw [← hu17] at e17
  have e18 := repThen_spec cap O S F hOS σ u17 s 16 (by decide) (by decide) (by decide) (by decide) (m2 false) [true, false] (c + 1) h16 h19 h9 ho
    (by simp only [reps_length, m2, m3, List.length_append, List.length_cons, List.length_nil]; omega) (by omega)
  rw [← hu18] at e18
  have e19 := repThen_spec cap O S F hOS σ u18 s 16 (by decide) (by decide) (by decide) (by decide) (m2 false) [true, false] (c + 1) h16 h19 h9 ho
    (by simp only [reps_length, m2, m3, List.length_append, List.length_cons, List.length_nil]; omega) (by omega)
  rw [← hu19] at e19
  have e20 := repThen_spec cap O S F hOS σ u19 s 16 (by decide) (by decide) (by decide) (by decide) (m2 false) [true, false] (c + 1) h16 h19 h9 ho
    (by simp only [reps_length, m2, m3, List.length_append, List.length_cons, List.length_nil]; omega) (by omega)
  rw [← hu20] at e20
  have e21 := repThen_spec cap O S F hOS σ u20 s 16 (by decide) (by decide) (by decide) (by decide) (m2 false) [true, false] (c + 1) h16 h19 h9 ho
    (by simp only [reps_length, m2, m3, List.length_append, List.length_cons, List.length_nil]; omega) (by omega)
  rw [← hu21] at e21
  have e22 := repThen_spec cap O S F hOS σ u21 s 16 (by decide) (by decide) (by decide) (by decide) (m2 false) [true, false] (c + 1) h16 h19 h9 ho
    (by simp only [reps_length, m2, m3, List.length_append, List.length_cons, List.length_nil]; omega) (by omega)
  rw [← hu22] at e22
  have e23 := repThen_spec cap O S F hOS σ u22 s 16 (by decide) (by decide) (by decide) (by decide) (m2 false) [true, false] (c + 1) h16 h19 h9 ho
    (by simp only [reps_length, m2, m3, List.length_append, List.length_cons, List.length_nil]; omega) (by omega)
  rw [← hu23] at e23
  have e24 := repThen_spec cap O S F hOS σ u23 s 16 (by decide) (by decide) (by decide) (by decide) (m2 false) [true, false] (c + 1) h16 h19 h9 ho
    (by simp only [reps_length, m2, m3, List.length_append, List.length_cons, List.length_nil]; omega) (by omega)
  rw [← hu24] at e24
  have e25 := emitF cap O S F hOS σ u24 s [false] ho (by simp only [List.length_cons, List.length_nil]; omega)
  rw [← hu25] at e25
  have hfin : u25 = u0 ++ pieceD thr c := by
    rw [hu25, hu24, hu23, hu22, hu21, hu20, hu19, hu18, hu17, hu16, hu15]; unfold pieceD; simp only [List.append_assoc]
  rw [hfin] at e25
  refine ⟨_, WExec.seq e15 (WExec.seq e16 (WExec.seq e17 (WExec.seq e18 (WExec.seq e19 (WExec.seq e20 (WExec.seq e21
    (WExec.seq e22 (WExec.seq e23 (WExec.seq e24 e25))))))))), ?_⟩
  simp only [reps_length, m2, m3, List.length_append, List.length_cons, List.length_nil]
  omega

theorem wexec_start {P : WM ns nr} {σ σ' τ : WState ns nr} {n : ℕ} (h : WExec cap P σ τ n) (e : σ = σ') :
    WExec cap P σ' τ n := by subst e; exact h

theorem filtEmit_split (Lp d cap1 thr c : ℕ) (w : List Bool) (labs : List ℕ) :
    filtEmit Lp d cap1 thr c w labs = pieceA Lp d ++ (pieceB labs cap1 ++ (pieceC w ++ pieceD thr c)) := by
  unfold filtEmit pieceA pieceB pieceC pieceD; simp only [List.append_assoc]

theorem A_len (Lp d : ℕ) : (pieceA Lp d).length = 4 * (8 * Lp + 6) + 30 + (4 * d + 6) := by
  unfold pieceA; simp only [reps_length, m2, m3, List.length_append, List.length_cons, List.length_nil]; omega

theorem B_len (labs : List ℕ) (cap1 : ℕ) :
    (pieceB labs cap1).length = (labs.flatMap labE).length + 6 + 4 * cap1 + 4 := by
  unfold pieceB; simp only [reps_length, m2, List.length_append, List.length_cons, List.length_nil]; omega

theorem C_len (w : List Bool) : (pieceC w).length = 4 * w.length + 2 := by
  unfold pieceC; rw [List.length_append, List.length_flatMap]; simp [m2]; omega

theorem D_len (thr c : ℕ) : (pieceD thr c).length = 4 * thr + 6 + 6 + 8 * (4 * (c + 1) + 2) + 1 := by
  unfold pieceD; simp only [reps_length, m2, List.length_append, List.length_cons, List.length_nil]; omega

/-- A simple bound on the program's cost. -/
def filtBound (Lp d thr c tw cap1 r4 G off Lg : ℕ) : ℕ :=
  1000 * (Lp + d + thr + c + tw + cap1 + 20) + labsCost r4 G off Lg

/-- **The FILTER row's input word, written**: from the call's numbers in registers and the table word `w` at the
cursor of stream `S`, the program appends `filtEmit (4L) d (labSum labs) thr c w labs` to `O`
(`= frame (filtRecC tbl thr L true labs)` by `FiltRec.filtEmit_eq`), with `labs = sliceLabs (4·row) G off Lg`. -/
theorem filtRecW_spec (hOS : O ≠ S) (σ : WState ns nr) (Lp d thr c r4 G off Lg : ℕ) (w : List Bool)
    (h13 : σ.val (F 13) = Lp) (h14 : σ.val (F 14) = d) (h15 : σ.val (F 15) = thr) (h16 : σ.val (F 16) = c + 1)
    (h17 : σ.val (F 17) = w.length) (h1 : σ.val (F 1) = r4) (h2 : σ.val (F 2) = G) (h3 : σ.val (F 3) = off)
    (h4 : σ.val (F 4) = Lg) (h5 : σ.val (F 5) = 0) (h6 : σ.val (F 6) = 0) (h7 : σ.val (F 7) = 0)
    (h8 : σ.val (F 8) = 0) (h9 : σ.val (F 9) = 0) (h10 : σ.val (F 10) = 0) (h11 : σ.val (F 11) = 0)
    (h12 : σ.val (F 12) = 0) (h19 : σ.val (F 19) = 0) (ho : σ.sh O = (σ.st O).length)
    (hw : ∀ i < w.length, readTapeBit (σ.st S) (σ.sh S + i) = w.getD i false) (M : ℕ)
    (hM : off + Lg + (r4 + 4) * G ≤ M) (LL CAP : ℕ)
    (hLL : ((sliceLabs r4 G off Lg).flatMap labE).length = LL) (hCAP : labSum (sliceLabs r4 G off Lg) = CAP)
    (cA : σ.val (F 0) + 4 * (8 * Lp + 6) + 30 + 4 * d + 6 + Lp + d + 10 ≤ cap)
    (cB : σ.val (F 0) + (4 * (8 * Lp + 6) + 30 + (4 * d + 6)) + LL + 4 * CAP + 10 +
      Lg * (4 * (4 * M + 4)) + Lg * (4 * (2 * M + 10)) + 4 * (4 * M + 4) + 4 * (2 * M + 10) + 7 * M + r4 + G + off +
      Lg + CAP + 40 ≤ cap)
    (cC : σ.val (F 0) + (4 * (8 * Lp + 6) + 30 + (4 * d + 6) + (LL + 6 + 4 * CAP + 4)) +
      4 * w.length + 2 + w.length + σ.val (F 18) + 5 ≤ cap)
    (cD : σ.val (F 0) + (4 * (8 * Lp + 6) + 30 + (4 * d + 6) + (LL + 6 + 4 * CAP + 4) + (4 * w.length + 2)) +
      4 * thr + 6 + 8 * (4 * (c + 1) + 2) + 7 + thr + c + 10 ≤ cap) :
    ∃ n, WExec cap (filtRecW O S F) σ
      (fSt O S F σ (filtEmit Lp d (labSum (sliceLabs r4 G off Lg)) thr c w (sliceLabs r4 G off Lg)) w.length) n ∧
      n ≤ filtBound Lp d thr c w.length (labSum (sliceLabs r4 G off Lg)) r4 G off Lg := by
  have hlA := A_len Lp d
  have hlB := B_len (sliceLabs r4 G off Lg) (labSum (sliceLabs r4 G off Lg))
  rw [hLL, hCAP] at hlB
  have hlC := C_len w
  have cA' : σ.val (F 0) + ([] : List Bool).length + 4 * (8 * Lp + 6) + 30 + 4 * d + 6 + Lp + d + 10 ≤ cap := by
    rw [List.length_nil, Nat.add_zero]; exact cA
  have cB' : σ.val (F 0) + ([] ++ pieceA Lp d).length + LL + 4 * CAP + 10 +
      Lg * (4 * (4 * M + 4)) + Lg * (4 * (2 * M + 10)) + 4 * (4 * M + 4) + 4 * (2 * M + 10) + 7 * M + r4 + G + off +
      Lg + CAP + 40 ≤ cap := by
    rw [List.nil_append, hlA]; exact cB
  have cC' : σ.val (F 0) + ([] ++ pieceA Lp d ++ pieceB (sliceLabs r4 G off Lg) (labSum (sliceLabs r4 G off Lg))).length +
      4 * w.length + 2 + w.length + σ.val (F 18) + 5 ≤ cap := by
    rw [List.nil_append, List.length_append, hlA, hCAP, hlB]; exact cC
  have cD' : σ.val (F 0) + ([] ++ pieceA Lp d ++ pieceB (sliceLabs r4 G off Lg) (labSum (sliceLabs r4 G off Lg)) ++
      pieceC w).length + 4 * thr + 6 + 8 * (4 * (c + 1) + 2) + 7 + thr + c + 10 ≤ cap := by
    rw [List.nil_append, List.length_append, List.length_append, hlA, hCAP, hlB, hlC]; exact cD
  obtain ⟨nA, eA, bA⟩ := phaseA_spec cap O S F hOS σ [] h19 h9 ho Lp d h13 h14 cA'
  obtain ⟨nB, eB, bB⟩ := phaseB_spec cap O S F hOS σ ([] ++ pieceA Lp d) h9 ho r4 G off Lg h1 h2 h3 h4 h5 h6 h7 h8 h10
    h11 h12 M hM LL CAP hLL hCAP cB'
  obtain ⟨nC, eC, bC⟩ := phaseC_spec cap O S F hOS σ _ h19 h9 ho w h17 hw cC'
  obtain ⟨nD, eD, bD⟩ := phaseD_spec cap O S F hOS σ _ h19 h9 ho w.length thr c h15 h16 cD'
  have hall := wexec_start cap (WExec.seq eA (WExec.seq eB (WExec.seq eC eD))) (fSt_zero σ)
  refine ⟨_, WExec.cast cap hall ?_ le_rfl, ?_⟩
  · rw [filtEmit_split]
    simp only [List.nil_append, List.append_assoc]
  · unfold filtBound
    rw [hCAP] at bB ⊢
    clear * - bA bB bC bD
    omega

end Spec

end NearCubicWires.WireExponent3_5.PrimAsm.FiltRecW
