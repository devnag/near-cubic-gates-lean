import Proof.Gates.WorkerArith.TermD

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.WorkerArith

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.RepairOrdinary.Streaming
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearCubicGates.Close.Interfaces (Counter Call callWord outputWord bitWord ratWord NCircuit circuitWord listWord)
open NearCubicGates.Close.Codec (oneCallOf pairCallOf cwPrefix rowPrefix emptyCW)

variable {ns nr : ℕ}

/-- The canonical state after a call writer: the call stream holds the frame, `R 23 = a`, `R 24 = b`, the heads of
`CW`/`SUP` at `hc`/`hs`. -/
def canonRho (E : TermEnv ns nr) (σ : WState ns nr) (a b hc hs : ℕ) (c : Call) : WState ns nr :=
  appendO (((((σ.sets E.S1 []).setv (E.R 23) a).setv (E.R 24) b).seth E.CW hc).seth E.SUP hs) E.S1 (E.R 17)
    (frame (callWord c))

theorem finPre_of {E : TermEnv ns nr} {t : ℕ} {tmap : Fin t → Fin (ns + 1)} {q : ℕ} {Cs : ℕ → NCircuit q} {N : ℕ}
    {rows : ℕ → List ℕ} {Rn : ℕ} {w pre rest : List Bool} {σ : WState ns nr}
    (hB : TermBase E tmap Cs N rows Rn w pre rest σ) (c : Call) (Z a b hc hs : ℕ)
    (hcw : hc ≤ σ.val (E.R 7)) (hsu : hs ≤ σ.val (E.R 8)) (ha : a ≤ Z) (hb : b ≤ Z) :
    FinPre E σ (canonRho E σ a b hc hs c) c Z := by
  obtain ⟨⟨cS, c1, -, -, -, -, -, -⟩, ⟨s1, -, -, -, -, -, -⟩, -, -, -, -, -, -⟩ := hB.dis
  have h17a : E.R 17 ≠ E.R 23 := R_ne E (by decide)
  have h17b : E.R 17 ≠ E.R 24 := R_ne E (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨fun x hx => ?_, fun r hr => ?_, ?_⟩, ?_, ?_⟩
  · simp [canonRho, appendO]
  · simp [canonRho, appendO, Function.update_of_ne (Ne.symm s1), Function.update_of_ne (Ne.symm c1), hB.h1]
  · simp [canonRho, appendO, Function.update_of_ne h17a, Function.update_of_ne h17b, hB.z 17 (by decide) (by decide)]
  · simp [canonRho, appendO, Function.update_of_ne c1]
  · simp [canonRho, appendO, Function.update_of_ne c1, Function.update_of_ne cS, hcw]
  · simp [canonRho, appendO, Function.update_of_ne s1]
  · simp [canonRho, appendO, Function.update_of_ne s1, hsu]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    obtain ⟨x1, x2, x3⟩ := hx
    simp [canonRho, appendO, Function.update_of_ne x1, Function.update_of_ne x2, Function.update_of_ne x3]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨r1, r2, r3⟩ := hr
    simp [canonRho, appendO, Function.update_of_ne r1, Function.update_of_ne r2, Function.update_of_ne r3]
  · simp [canonRho, appendO]
  · simp [canonRho, appendO, Function.update_of_ne h17a, Function.update_of_ne (R_ne E (show (23 : Fin 40) ≠ 24 by decide)), ha]
  · simp [canonRho, appendO, Function.update_of_ne h17b, hb]

theorem rwC_7 (R : Fin 40 ↪ Fin nr) : rwC R 7 = R 17 := rfl
theorem rwC_12 (R : Fin 40 ↪ Fin nr) : rwC R 12 = R 7 := rfl
theorem rwC_13 (R : Fin 40 ↪ Fin nr) : rwC R 13 = R 23 := rfl
theorem rwC_14 (R : Fin 40 ↪ Fin nr) : rwC R 14 = R 24 := rfl
theorem rwC_15 (R : Fin 40 ↪ Fin nr) : rwC R 15 = R 6 := rfl

theorem writer_cost_le (Z B x : ℕ) (hx : x ≤ 1000 * (Z + 13) ^ 2 * (B + 1)) :
    20010000 * (Z + 13) ^ 4 * (B + 1) + x ≤ writerCost Z B := by
  unfold writerCost
  have h1 : (Z + 13) ^ 2 ≤ (Z + 13) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : (Z + 13) ^ 2 * (B + 1) ≤ (Z + 13) ^ 4 * (B + 1) := Nat.mul_le_mul_right _ h1
  nlinarith

theorem B_le_parB (Z B : ℕ) : B ≤ parB Z B := by
  unfold parB; have : 1 ≤ (Z + 13) ^ 2 := Nat.one_le_pow _ _ (by omega)
  nlinarith

theorem sq_le_parB (Z B : ℕ) : 100 * (Z + 13) ^ 2 ≤ parB Z B := by
  unfold parB; nlinarith

theorem oneAux_exec (cap : ℕ) {E : TermEnv ns nr} {t : ℕ} {tmap : Fin t → Fin (ns + 1)} {q : ℕ}
    {Cs : ℕ → NCircuit q} {N : ℕ} {rows : ℕ → List ℕ} {Rn : ℕ} {ω : ℚ} {w pre rest : List Bool} {Z B V : ℕ}
    {σ : WState ns nr} (hB : TermBase E tmap Cs N rows Rn w pre rest σ) (hFit : TermFit cap Cs N rows Rn ω w Z B V)
    (xi : Fin 40) (hxi : xi = 2 ∨ xi = 5) (hj : σ.val (E.R xi) < N) (hjZ : σ.val (E.R xi) ≤ Z)
    (h7 : σ.val (E.R 7) ≤ Z) :
    WExec cap (oneAuxW E (E.R xi) ω) (σ.sets E.S1 [])
      (canonRho E σ (σ.val (E.R xi)) 0 (cwPrefix Cs (σ.val (E.R xi) + 1)).length 0
        (oneCallOf Cs (σ.val (E.R xi)) [] ω)) (writerCost Z B) := by
  obtain ⟨⟨cS, c1, -, -, -, -, -, -⟩, ⟨s1, -, -, -, -, -, -⟩, -, -, -, -, -, -⟩ := hB.dis
  set j := σ.val (E.R xi) with hjd
  have hxn : ∀ k : Fin 40, 6 ≤ k.val → xi ≠ k := fun k hk h => by rcases hxi with rfl | rfl <;> subst h <;> simp at hk
  set σ0 := σ.sets E.S1 [] with hσ0
  have e1 := Codec.dupR_spec cap (E.R xi) (E.R 23) (E.R 38) (R_ne E (hxn 23 (by decide))) (R_ne E (hxn 38 (by decide)))
    (R_ne E (by decide)) σ0 (by simp [hσ0]; exact hB.z 38 (by decide) (by decide))
    (by simp [hσ0, hB.z 23 (by decide) (by decide)]; have := hFit.capV; omega)
  rw [show σ0.val (E.R 23) = 0 from hB.z 23 (by decide) (by decide), Nat.zero_add,
    show σ0.val (E.R xi) = j from rfl] at e1
  set σ1 := σ0.setv (E.R 23) j with hσ1
  have v1 : ∀ k : Fin 40, k ≠ 23 → σ1.val (E.R k) = σ.val (E.R k) := fun k hk => by
    simp [hσ1, hσ0, Function.update_of_ne (R_ne E hk)]
  obtain ⟨restC, hrc⟩ := hB.cw
  have hcwj := hFit.cwZ j hj
  have hcl := callWord_one_le Cs j [] ω Z hFit.qZ hcwj (by rw [listWord_nil_len]; omega) hFit.ωZ
  have hfl : (frame (callWord (oneCallOf Cs j [] ω))).length ≤ 30 * Z + 100 := by rw [frame_len']; omega
  have hV := hFit.VZ
  have hcV := hFit.capV
  have hn0 : (natWord 0).length = 3 := rfl
  have e2 := callOneW_class cap (rwC E.R) E.CW E.S1 E.SUP c1 s1 (Ne.symm cS) Cs N j hj [] 0 (by simp)
    (Codec.parNone E.S1 (E.R 17)) ω B V (σ.val (E.R 7)) (16 * (natWord 0).length) 0
    hFit.fit hFit.cb hFit.copy (by have := hFit.NZ; omega) (by omega)
    (by have := nbl_le q; have := hFit.qZ; omega) restC σ1
    (by simp [hσ1, hσ0, Function.update_of_ne c1, hrc]) (by simp [hσ1, hσ0, hB.cwh])
    (by simp [hσ1, hσ0, hB.h1])
    (rwC_z E σ1 (fun i a b => by rw [v1 i (Fin.ne_of_val_ne (by omega))]; exact hB.z i a (by omega)))
    (by rw [rwC_15, v1 6 (by decide), hB.hq]) (by rw [rwC_13]; simp [hσ1])
    (by rw [rwC_12, v1 7 (by decide)])
    (by rw [rwC_7, v1 17 (by decide), hB.z 17 (by decide) (by decide)]; omega)
    (fun τ _ _ hτo hτs hτsh hτV => by
      rw [seth_self τ E.SUP 0 (by rw [hτsh]; simp [hσ1, hσ0, Function.update_of_ne s1, hB.suph])]
      have := hτV; rw [Codec.marks_length, listWord_nil_len] at this
      exact Codec.parNone_spec cap E.S1 (E.R 17) τ hτo (by rw [hn0]; rw [rwC_7] at this; omega))
    (Z + 12) (parB Z B) (by have := hFit.qZ; omega) (by omega) (by omega) (by rw [hn0]; omega)
    (by rw [emptyCW_length]; omega) (by have := hFit.ωZ; omega) (B_le_parB Z B)
    ((hFit.ccB j hj).trans (B_le_parB Z B)) (by rw [hn0]; have := sq_le_parB Z B; nlinarith)
  refine WExec.cast cap (WExec.seq e1 e2) ?_ ?_
  · simp only [canonRho]
    rw [setv_self _ (E.R 24) 0 (by simp [hσ1, hσ0, Function.update_of_ne (R_ne E (show (24 : Fin 40) ≠ 23 by decide)),
      hB.z 24 (by decide) (by decide)])]
    rfl
  · have := callOne_cost_fit Z B
    have hx : 18 * j + 3 + 1 ≤ 1000 * (Z + 13) ^ 2 * (B + 1) := by
      have : 1 ≤ B + 1 := by omega
      nlinarith
    have := writer_cost_le Z B _ hx
    omega

theorem pair_exec (cap : ℕ) {E : TermEnv ns nr} {t : ℕ} {tmap : Fin t → Fin (ns + 1)} {q : ℕ}
    {Cs : ℕ → NCircuit q} {N : ℕ} {rows : ℕ → List ℕ} {Rn : ℕ} {ω : ℚ} {w pre rest : List Bool} {Z B V : ℕ}
    {σ : WState ns nr} (hB : TermBase E tmap Cs N rows Rn w pre rest σ) (hFit : TermFit cap Cs N rows Rn ω w Z B V)
    (hi : σ.val (E.R 2) < N) (hj : σ.val (E.R 5) < N) (hiZ : σ.val (E.R 2) ≤ Z) (hjZ : σ.val (E.R 5) ≤ Z)
    (h7 : σ.val (E.R 7) ≤ Z) :
    WExec cap (pairW E ω) (σ.sets E.S1 [])
      (canonRho E σ (σ.val (E.R 2)) (σ.val (E.R 5)) (cwPrefix Cs (σ.val (E.R 5) + 1)).length 0
        (pairCallOf Cs (σ.val (E.R 2)) (σ.val (E.R 5)) ω)) (writerCost Z B) := by
  obtain ⟨⟨cS, c1, -, -, -, -, -, -⟩, ⟨s1, -, -, -, -, -, -⟩, -, -, -, -, -, -⟩ := hB.dis
  set i := σ.val (E.R 2) with hid
  set j := σ.val (E.R 5) with hjd
  set σ0 := σ.sets E.S1 [] with hσ0
  have hcV := hFit.capV
  have e1 := Codec.dupR_spec cap (E.R 2) (E.R 23) (E.R 38) (R_ne E (by decide)) (R_ne E (by decide))
    (R_ne E (by decide)) σ0 (by simp [hσ0]; exact hB.z 38 (by decide) (by decide))
    (by simp [hσ0, hB.z 23 (by decide) (by decide)]; omega)
  rw [show σ0.val (E.R 23) = 0 from hB.z 23 (by decide) (by decide), Nat.zero_add,
    show σ0.val (E.R 2) = i from rfl] at e1
  set σ1 := σ0.setv (E.R 23) i with hσ1
  have e2 := Codec.dupR_spec cap (E.R 5) (E.R 24) (E.R 38) (R_ne E (by decide)) (R_ne E (by decide))
    (R_ne E (by decide)) σ1 (by simp [hσ1, hσ0, Function.update_of_ne (R_ne E (show (38 : Fin 40) ≠ 23 by decide))]; exact hB.z 38 (by decide) (by decide))
    (by simp [hσ1, hσ0, Function.update_of_ne (R_ne E (show (24 : Fin 40) ≠ 23 by decide)),
          Function.update_of_ne (R_ne E (show (5 : Fin 40) ≠ 23 by decide)), hB.z 24 (by decide) (by decide)]; omega)
  rw [show σ1.val (E.R 24) = 0 by simp [hσ1, hσ0, Function.update_of_ne (R_ne E (show (24 : Fin 40) ≠ 23 by decide)),
      hB.z 24 (by decide) (by decide)], Nat.zero_add,
    show σ1.val (E.R 5) = j by simp [hσ1, hσ0, Function.update_of_ne (R_ne E (show (5 : Fin 40) ≠ 23 by decide)), hjd]] at e2
  set σ2 := σ1.setv (E.R 24) j with hσ2
  have v2 : ∀ k : Fin 40, k ≠ 23 → k ≠ 24 → σ2.val (E.R k) = σ.val (E.R k) := fun k a b => by
    simp [hσ2, hσ1, hσ0, Function.update_of_ne (R_ne E a), Function.update_of_ne (R_ne E b)]
  obtain ⟨restC, hrc⟩ := hB.cw
  have hcl := callWord_pair_le Cs i j ω Z hFit.qZ (hFit.cwZ i hi) (hFit.cwZ j hj) hFit.ωZ
  have hfl : (frame (callWord (pairCallOf Cs i j ω))).length ≤ 30 * Z + 100 := by rw [frame_len']; omega
  have hV := hFit.VZ
  have hn0 : (natWord 0).length = 3 := rfl
  have e3 := callPairW_class cap (rwC E.R) E.CW E.S1 c1 Cs N i j hi hj ω B V (σ.val (E.R 7))
    hFit.fit hFit.cb hFit.copy (by have := hFit.NZ; omega) (by omega)
    (by have := nbl_le q; have := hFit.qZ; omega) restC σ2
    (by simp [hσ2, hσ1, hσ0, Function.update_of_ne c1, hrc]) (by simp [hσ2, hσ1, hσ0, hB.cwh])
    (by obtain ⟨r, hr⟩ := hB.cw; have := hB.cwL; omega)
    (by simp [hσ2, hσ1, hσ0, hB.h1])
    (rwC_z E σ2 (fun k a b => by
      rw [v2 k (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega))]; exact hB.z k a (by omega)))
    (by rw [rwC_15, v2 6 (by decide) (by decide), hB.hq])
    (by rw [rwC_13]; simp [hσ2, hσ1, Function.update_of_ne (R_ne E (show (23 : Fin 40) ≠ 24 by decide))])
    (by rw [rwC_14]; simp [hσ2])
    (by rw [rwC_12, v2 7 (by decide) (by decide)])
    (by rw [rwC_7, v2 17 (by decide) (by decide), hB.z 17 (by decide) (by decide)]; omega)
    (Z + 12) (parB Z B) (by have := hFit.qZ; omega) (by omega) (by omega) (by omega)
    (by simp only [List.length_append, hn0]; have := hFit.ωZ; omega) (B_le_parB Z B)
    ((hFit.ccB i hi).trans (B_le_parB Z B)) ((hFit.ccB j hj).trans (B_le_parB Z B))
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) ?_ ?_
  · simp only [canonRho]
    rw [seth_self _ E.SUP 0 (by simp [hσ2, hσ1, hσ0, Function.update_of_ne cS.symm, Function.update_of_ne s1,
      hB.suph])]
    rfl
  · have := callOne_cost_fit Z B
    have hx : 18 * i + 3 + 1 + (18 * j + 3 + 1) ≤ 1000 * (Z + 13) ^ 2 * (B + 1) := by
      have : 1 ≤ B + 1 := by omega
      nlinarith
    have := writer_cost_le Z B _ hx
    omega

end NearCubicGates.Close.WorkerArith
