import Proof.Gates.WorkerArith.HeaderDefs

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.WorkerArith

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming

variable {ns nr : ℕ}

theorem wnR_apply (H : Fin 14 ↪ Fin nr) (k : Fin 14) (hk : k.val < 5 ∨ k = 12) (i : Fin 8) :
    wnR H k hk i = H (wIdx k i) := rfl

/-- One `natWord` of a register onto the I-stream. -/
theorem wn_step (cap : ℕ) (VI : Fin (ns + 1)) (H : Fin 14 ↪ Fin nr) (k : Fin 14) (hk : k.val < 5 ∨ k = 12)
    (τ : WState ns nr) (hz : ∀ i : Fin 14, 6 ≤ i.val → i.val ≤ 11 → τ.val (H i) = 0)
    (ho : τ.sh VI = (τ.st VI).length)
    (hc : τ.val (H k) + τ.val (H 5) + 6 * natBitLength (τ.val (H k)) + 6 ≤ cap) :
    WExec cap (writeNatM VI (wnR H k hk)) τ (appendO τ VI (H 5) (marks (natWord (τ.val (H k)))))
      ((natBitLength (τ.val (H k)) + 10) * (100 * τ.val (H k) + 200)) :=
  writeNatM_spec cap VI (wnR H k hk) τ (hz 6 (by decide) (by decide)) (hz 7 (by decide) (by decide))
    (hz 8 (by decide) (by decide)) (hz 9 (by decide) (by decide)) (hz 10 (by decide) (by decide))
    (hz 11 (by decide) (by decide)) ho hc

theorem dupN_spec (cap : ℕ) (A C D : Fin nr) (hAC : A ≠ C) (hAD : A ≠ D) (hCD : C ≠ D) :
    ∀ (n a : ℕ) (τ : WState ns nr), τ.val C = a → τ.val D = 0 → a + n * τ.val A ≤ cap →
      WExec cap (dupN A C D n) τ (τ.setv C (a + n * τ.val A)) (n * (18 * τ.val A + 4))
  | 0, a, τ, hC, _, _ => by
    simp only [dupN, Nat.zero_mul, Nat.add_zero]
    rw [show τ.setv C a = τ by rw [← hC]; cases τ; simp [WState.setv]]
    exact WExec.skip τ
  | n + 1, a, τ, hC, hD, hc => by
    have e1 := Codec.dupR_spec cap A C D hAC hAD hCD τ hD (by rw [hC]; nlinarith)
    rw [hC] at e1
    have e2 := dupN_spec cap A C D hAC hAD hCD n (a + τ.val A) (τ.setv C (a + τ.val A)) (by simp)
      (by simp [Function.update_of_ne (Ne.symm hCD), hD]) (by simp [Function.update_of_ne hAC]; nlinarith)
    simp only [WState.setv_val, Function.update_of_ne hAC] at e2
    refine WExec.cast cap (WExec.seq e1 e2) ?_ (by ring_nf; omega)
    rw [show (τ.setv C (a + τ.val A)).setv C (a + τ.val A + n * τ.val A) = τ.setv C (a + (n + 1) * τ.val A) by
      cases τ; simp only [WState.setv, Function.update_idem]; congr 2; ring]

theorem appendO_val_ne (τ : WState ns nr) (o : Fin (ns + 1)) (OP r : Fin nr) (u : List Bool) (h : r ≠ OP) :
    (appendO τ o OP u).val r = τ.val r := by simp [appendO, Function.update_of_ne h]

theorem appendO_ready (τ : WState ns nr) (o : Fin (ns + 1)) (OP : Fin nr) (u : List Bool)
    (h : τ.sh o = (τ.st o).length) : (appendO τ o OP u).sh o = ((appendO τ o OP u).st o).length := by
  simp [appendO, h]

theorem headerW_spec (cap : ℕ) (VI : Fin (ns + 1)) (H : Fin 14 ↪ Fin nr) (S : ℕ) (σ : WState ns nr) :
    HeaderSpec cap VI H S σ := by
  intro ho hz h0 h2 h3 h4 h1 hc
  have hne : ∀ {a b : Fin 14}, a ≠ b → H a ≠ H b := fun h e => h (H.injective e)
  have n0 := nbl_le (σ.val (H 0)); have n1 := nbl_le (σ.val (H 1)); have n2 := nbl_le (σ.val (H 2))
  have n3 := nbl_le (σ.val (H 3)); have n4 := nbl_le (σ.val (H 4)); have n5 := nbl_le (10 * σ.val (H 1))
  have hwl : ∀ x, x ≤ S → (marks (natWord x)).length ≤ 4 * S + 6 := fun x hx => by
    rw [Codec.marks_length, natWord_len_c]; have := nbl_le x; omega
  -- the five words
  have zk : ∀ (u : List Bool) (i : Fin 14), 6 ≤ i.val → i.val ≤ 11 → (appendO σ VI (H 5) u).val (H i) = 0 :=
    fun u i a b => by rw [appendO_val_ne _ _ _ _ _ (hne (Fin.ne_of_val_ne (by omega)))]; exact hz i a
  have vk : ∀ (u : List Bool) (i : Fin 14), i ≠ 5 → (appendO σ VI (H 5) u).val (H i) = σ.val (H i) :=
    fun u i a => appendO_val_ne _ _ _ _ _ (hne a)
  have v5 : ∀ (u : List Bool), (appendO σ VI (H 5) u).val (H 5) = σ.val (H 5) + u.length := fun u => by simp [appendO]
  have e0 := wn_step cap VI H 0 (Or.inl (by decide)) σ (fun i a b => hz i a) ho (by omega)
  have e1 := wn_step cap VI H 1 (Or.inl (by decide)) (appendO σ VI (H 5) (marks (natWord (σ.val (H 0)))))
    (zk _) (appendO_ready _ _ _ _ ho) (by rw [vk _ 1 (by decide), v5]; have := hwl _ h0; omega)
  rw [vk _ 1 (by decide), appendO_append, ← Codec.marksApp] at e1
  have e2 := wn_step cap VI H 2 (Or.inl (by decide))
    (appendO σ VI (H 5) (marks (natWord (σ.val (H 0)) ++ natWord (σ.val (H 1)))))
    (zk _) (appendO_ready _ _ _ _ ho) (by
      rw [vk _ 2 (by decide), v5, Codec.marks_length, List.length_append, natWord_len_c, natWord_len_c]; omega)
  rw [vk _ 2 (by decide), appendO_append, ← Codec.marksApp] at e2
  have e3 := wn_step cap VI H 3 (Or.inl (by decide))
    (appendO σ VI (H 5) (marks (natWord (σ.val (H 0)) ++ natWord (σ.val (H 1)) ++ natWord (σ.val (H 2)))))
    (zk _) (appendO_ready _ _ _ _ ho) (by
      rw [vk _ 3 (by decide), v5, Codec.marks_length]; simp only [List.length_append, natWord_len_c]; omega)
  rw [vk _ 3 (by decide), appendO_append, ← Codec.marksApp] at e3
  have e4 := wn_step cap VI H 4 (Or.inl (by decide))
    (appendO σ VI (H 5) (marks (natWord (σ.val (H 0)) ++ natWord (σ.val (H 1)) ++ natWord (σ.val (H 2)) ++
      natWord (σ.val (H 3)))))
    (zk _) (appendO_ready _ _ _ _ ho) (by
      rw [vk _ 4 (by decide), v5, Codec.marks_length]; simp only [List.length_append, natWord_len_c]; omega)
  rw [vk _ 4 (by decide), appendO_append, ← Codec.marksApp] at e4
  set u5 := natWord (σ.val (H 0)) ++ natWord (σ.val (H 1)) ++ natWord (σ.val (H 2)) ++ natWord (σ.val (H 3)) ++
    natWord (σ.val (H 4)) with hu5
  have hu5l : u5.length ≤ 10 * S + 15 := by
    simp only [hu5, List.length_append, natWord_len_c]; omega
  -- `10 M`
  have e5 := dupN_spec cap (H 1) (H 12) (H 13) (hne (by decide)) (hne (by decide)) (hne (by decide)) 10 0
    (appendO σ VI (H 5) (marks u5)) (by rw [appendO_val_ne _ _ _ _ _ (hne (by decide))]; exact hz 12 (by decide))
    (by rw [appendO_val_ne _ _ _ _ _ (hne (by decide))]; exact hz 13 (by decide))
    (by rw [vk _ 1 (by decide)]; omega)
  rw [vk _ 1 (by decide), Nat.zero_add] at e5
  set τ6 := (appendO σ VI (H 5) (marks u5)).setv (H 12) (10 * σ.val (H 1)) with hτ6
  have e6 := wn_step cap VI H 12 (Or.inr rfl) τ6
    (fun i a b => by
      rw [hτ6, WState.setv_val, Function.update_of_ne (hne (Fin.ne_of_val_ne (by omega)))]; exact zk _ i a b)
    (by simp only [hτ6, WState.setv]; exact appendO_ready _ _ _ _ ho)
    (by simp only [hτ6, WState.setv_val, Function.update_self, Function.update_of_ne (hne (show (5 : Fin 14) ≠ 12 by decide))]
        rw [v5, Codec.marks_length]; omega)
  simp only [hτ6, WState.setv_val, Function.update_self] at e6
  have e7 := wclear_spec (cap := cap) (H 12) (10 * σ.val (H 1))
    (appendO τ6 VI (H 5) (marks (natWord (10 * σ.val (H 1)))))
    (by rw [appendO_val_ne _ _ _ _ _ (hne (by decide))]; simp [hτ6])
    (by rw [appendO_val_ne _ _ _ _ _ (hne (by decide))]; simp [hτ6]; omega)
  have hend : (appendO τ6 VI (H 5) (marks (natWord (10 * σ.val (H 1))))).setv (H 12) 0 =
      appendO σ VI (H 5) (marks (headerWord (σ.val (H 0)) (σ.val (H 1)) (σ.val (H 2)) (σ.val (H 3)) (σ.val (H 4)))) := by
    have : (appendO τ6 VI (H 5) (marks (natWord (10 * σ.val (H 1))))).setv (H 12) 0 =
        appendO (appendO σ VI (H 5) (marks u5)) VI (H 5) (marks (natWord (10 * σ.val (H 1)))) := by
      refine WState.eq rfl rfl ?_ rfl
      funext r
      by_cases r12 : r = H 12
      · subst r12
        simp [appendO, hτ6, Function.update_of_ne (hne (show (12 : Fin 14) ≠ 5 by decide)), hz 12 (by decide)]
      · by_cases r5 : r = H 5
        · subst r5; simp [appendO, hτ6, Function.update_of_ne (hne (show (5 : Fin 14) ≠ 12 by decide))]
        · simp [appendO, hτ6, Function.update_of_ne r12, Function.update_of_ne r5]
    rw [this, appendO_append, ← Codec.marksApp]; rfl
  rw [hend] at e7
  refine WExec.mono (WExec.seq e0 (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5
    (WExec.seq e6 e7))))))) ?_
  unfold headerCost
  have c0 := nbl_mul_le (σ.val (H 0)) S 100 200 10 h0
  have c1 := nbl_mul_le (σ.val (H 1)) S 100 200 10 (by omega)
  have c2 := nbl_mul_le (σ.val (H 2)) S 100 200 10 h2
  have c3 := nbl_mul_le (σ.val (H 3)) S 100 200 10 h3
  have c4 := nbl_mul_le (σ.val (H 4)) S 100 200 10 h4
  have c5 := nbl_mul_le (10 * σ.val (H 1)) S 100 200 10 h1
  have hS : S + 1 ≤ (S + 1) ^ 2 := by nlinarith
  nlinarith

theorem closeW_spec (cap : ℕ) (VI : Fin (ns + 1)) (OP : Fin nr) (σ : WState ns nr) : CloseSpec cap VI OP σ := by
  intro ho hc
  have e := emitC_spec (cap := cap) VI OP false σ ho hc
  refine WExec.cast cap e ?_ le_rfl
  simp [appendO, ho]

end NearCubicGates.Close.WorkerArith
