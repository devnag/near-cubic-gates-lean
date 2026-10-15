import Proof.Gates.WorkerArith.TermE

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

section Canon
variable {E : TermEnv ns nr} {t : ℕ} {tmap : Fin t → Fin (ns + 1)} {q : ℕ} {Cs : ℕ → NCircuit q} {N : ℕ}
  {rows : ℕ → List ℕ} {Rn : ℕ} {ω : ℚ} {w pre rest : List Bool} {Z B V : ℕ} {σ : WState ns nr}

def preOne (E : TermEnv ns nr) (σ : WState ns nr) (j b : ℕ) : WState ns nr :=
  ((σ.sets E.S1 []).setv (E.R 23) j).setv (E.R 24) b

theorem preOne_val (j b : ℕ) (k : Fin 40) (a : k ≠ 23) (d : k ≠ 24) : (preOne E σ j b).val (E.R k) = σ.val (E.R k) := by
  simp [preOne, Function.update_of_ne (R_ne E a), Function.update_of_ne (R_ne E d)]

/-- **The single-call writer to the canonical end state**, generic in the parity writer. -/
theorem callOne_canon (cap : ℕ) (hB : TermBase E tmap Cs N rows Rn w pre rest σ)
    (hFit : TermFit cap Cs N rows Rn ω w Z B V) (j b hs : ℕ) (hj : j < N) (h7 : σ.val (E.R 7) ≤ Z)
    (ps : List ℕ) (tg : ℕ) (ht : tg = if ps = [] then 0 else 2) (parW : WM ns nr) (cp : ℕ) (hcp : cp ≤ parB Z B)
    (hps : (listWord natWord ps).length ≤ 2 * Z + 10)
    (hpar : ∀ τ : WState ns nr, (∀ k : Fin 16, k ≠ 7 → τ.val (rwC E.R k) = (preOne E σ j b).val (rwC E.R k)) →
      (∀ r, (∀ k : Fin 16, r ≠ rwC E.R k) → τ.val r = (preOne E σ j b).val r) → τ.sh E.S1 = (τ.st E.S1).length →
      τ.st E.SUP = (preOne E σ j b).st E.SUP → τ.sh E.SUP = (preOne E σ j b).sh E.SUP →
      τ.val (rwC E.R 7) + (marks (listWord natWord ps)).length ≤ V →
      WExec cap parW τ (appendO (τ.seth E.SUP hs) E.S1 (rwC E.R 7) (marks (listWord natWord ps))) cp) :
    WExec cap (Codec.callOneW E.CW E.S1 (rwC E.R) tg parW ω) (preOne E σ j b)
      (canonRho E σ j b (cwPrefix Cs (j + 1)).length hs (oneCallOf Cs j ps ω)) (20010000 * (Z + 13) ^ 4 * (B + 1)) := by
  obtain ⟨⟨cS, c1, -, -, -, -, -, -⟩, ⟨s1, -, -, -, -, -, -⟩, -, -, -, -, -, -⟩ := hB.dis
  obtain ⟨restC, hrc⟩ := hB.cw
  have hcl := callWord_one_le Cs j ps ω Z hFit.qZ (hFit.cwZ j hj) hps hFit.ωZ
  have hfl : (frame (callWord (oneCallOf Cs j ps ω))).length ≤ 30 * Z + 100 := by rw [frame_len']; omega
  have hV := hFit.VZ
  have hcV := hFit.capV
  have hn : (natWord tg).length ≤ 5 := by rw [ht]; split_ifs <;> decide
  have e := callOneW_class cap (rwC E.R) E.CW E.S1 E.SUP c1 s1 (Ne.symm cS) Cs N j hj ps tg ht parW ω B V
    (σ.val (E.R 7)) cp hs hFit.fit hFit.cb hFit.copy (by have := hFit.NZ; omega) (by omega)
    (by have := nbl_le q; have := hFit.qZ; omega) restC (preOne E σ j b)
    (by simp [preOne, Function.update_of_ne c1, hrc]) (by simp [preOne, hB.cwh]) (by simp [preOne, hB.h1])
    (rwC_z E _ (fun i a d => by
      rw [preOne_val j b i (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega))]; exact hB.z i a (by omega)))
    (by rw [rwC_15, preOne_val j b 6 (by decide) (by decide), hB.hq])
    (by rw [rwC_13]; simp [preOne, Function.update_of_ne (R_ne E (show (23 : Fin 40) ≠ 24 by decide))])
    (by rw [rwC_12, preOne_val j b 7 (by decide) (by decide)])
    (by rw [rwC_7, preOne_val j b 17 (by decide) (by decide), hB.z 17 (by decide) (by decide)]; omega)
    hpar (Z + 12) (parB Z B) (by have := hFit.qZ; omega) (by omega) (by have := hFit.NZ; omega) (by omega)
    (by rw [emptyCW_length]; omega) (by have := hFit.ωZ; omega) (B_le_parB Z B)
    ((hFit.ccB j hj).trans (B_le_parB Z B)) hcp
  refine WExec.mono (WExec.cast cap e ?_ le_rfl) (callOne_cost_fit Z B)
  simp only [canonRho, preOne]
  rfl

theorem row_sizes (ps : List ℕ) (Z : ℕ) (h : (listWord natWord ps).length ≤ Z) :
    ps.length ≤ Z ∧ ∀ x ∈ ps, natBitLength x ≤ Z := by
  rw [listWord_len] at h
  refine ⟨(flatMap_len_ge natWord natWord_len_pos ps).trans (by omega), fun x hx => ?_⟩
  have := mem_flatMap_len natWord hx
  rw [natWord_len_c] at this; omega

theorem rowPrefix_succ_le (rows : ℕ → List ℕ) {r R : ℕ} (h : r < R) :
    (rowPrefix rows (r + 1)).length ≤ (rowPrefix rows R).length := by
  have := congrArg List.length (Codec.rowPrefix_split rows h)
  rw [Codec.rowPrefix_succ]
  simp only [List.length_append] at this ⊢; omega

/-- The state after `ltSubW` in `sysAuxW`. -/
def midSA (E : TermEnv ns nr) (σ : WState ns nr) (j u q : ℕ) : WState ns nr :=
  (((σ.sets E.S1 []).setv (E.R 23) j).setv (E.R 24) (u - q)).setv (E.R 34) (q - u)

/-- The systematic coordinate `u < q`: parity list `[u]`. -/
theorem sysA_exec (cap : ℕ) (hB : TermBase E tmap Cs N rows Rn w pre rest σ)
    (hFit : TermFit cap Cs N rows Rn ω w Z B V) (xs : Fin 40) (hxs : xs = 2 ∨ xs = 5) (j u : ℕ) (hj : j < N)
    (hxu : σ.val (E.R xs) = u) (hlt : u < q) (h7 : σ.val (E.R 7) ≤ Z) :
    WExec cap (.seq (WM.clear (E.R 34)) (.seq (Codec.dupR (E.R xs) (E.R 24) (E.R 38))
        (Codec.callOneW E.CW E.S1 (rwC E.R) 2 (Codec.parSys E.S1 (rwC E.R)) ω))) (midSA E σ j u q)
      (canonRho E σ j u (cwPrefix Cs (j + 1)).length 0 (oneCallOf Cs j (sysList q rows u) ω))
      (20010000 * (Z + 13) ^ 4 * (B + 1) + 100 * (Z + 1)) := by
  obtain ⟨⟨cS, c1, -, -, -, -, -, -⟩, ⟨s1, -, -, -, -, -, -⟩, -, -, -, -, -, -⟩ := hB.dis
  have hxn : ∀ k : Fin 40, 6 ≤ k.val → xs ≠ k := fun k hk h => by rcases hxs with rfl | rfl <;> subst h <;> simp at hk
  have hqZ := hFit.qZ
  have hcV := hFit.capV
  have hsl : sysList q rows u = [u] := by unfold sysList; rw [if_pos hlt]
  rw [hsl]
  have a1 := wclear_spec (cap := cap) (E.R 34) (q - u) (midSA E σ j u q) (by simp [midSA]) (by simp [midSA]; omega)
  have hm : (midSA E σ j u q).setv (E.R 34) 0 = ((σ.sets E.S1 []).setv (E.R 23) j).setv (E.R 24) 0 := by
    refine WState.eq rfl rfl ?_ rfl
    funext r
    by_cases r34 : r = E.R 34
    · subst r34; simp [midSA, Function.update_of_ne (R_ne E (show (34 : Fin 40) ≠ 24 by decide)),
        Function.update_of_ne (R_ne E (show (34 : Fin 40) ≠ 23 by decide)), hB.z 34 (by decide) (by decide)]
    by_cases r24 : r = E.R 24
    · subst r24; simp [midSA, Function.update_of_ne (R_ne E (show (24 : Fin 40) ≠ 34 by decide))]; omega
    simp [midSA, Function.update_of_ne r34, Function.update_of_ne r24]
  rw [hm] at a1
  have a2 := Codec.dupR_spec cap (E.R xs) (E.R 24) (E.R 38) (R_ne E (hxn 24 (by decide))) (R_ne E (hxn 38 (by decide)))
    (R_ne E (by decide)) (((σ.sets E.S1 []).setv (E.R 23) j).setv (E.R 24) 0)
    (by simp [Function.update_of_ne (R_ne E (show (38 : Fin 40) ≠ 24 by decide)),
          Function.update_of_ne (R_ne E (show (38 : Fin 40) ≠ 23 by decide))]; exact hB.z 38 (by decide) (by decide))
    (by simp [Function.update_of_ne (R_ne E (hxn 24 (by decide))), Function.update_of_ne (R_ne E (hxn 23 (by decide))),
          hxu]; omega)
  have hm2 : (((σ.sets E.S1 []).setv (E.R 23) j).setv (E.R 24) 0).setv (E.R 24)
      ((((σ.sets E.S1 []).setv (E.R 23) j).setv (E.R 24) 0).val (E.R 24) +
        (((σ.sets E.S1 []).setv (E.R 23) j).setv (E.R 24) 0).val (E.R xs)) = preOne E σ j u := by
    refine WState.eq rfl rfl ?_ rfl
    funext r
    simp only [preOne, WState.setv_val, WState.sets]
    by_cases r24 : r = E.R 24
    · subst r24; simp [Function.update_of_ne (R_ne E (hxn 24 (by decide))),
        Function.update_of_ne (R_ne E (hxn 23 (by decide))), hxu]
    simp [Function.update_of_ne r24]
  rw [hm2, show (((σ.sets E.S1 []).setv (E.R 23) j).setv (E.R 24) 0).val (E.R xs) = u by
    simp [Function.update_of_ne (R_ne E (hxn 24 (by decide))), Function.update_of_ne (R_ne E (hxn 23 (by decide))), hxu]] at a2
  have a3 := callOne_canon cap hB hFit j u 0 hj h7 [u] 2 (by simp) (Codec.parSys E.S1 (rwC E.R))
    (16 * (natWord 1).length + 1 + (natBitLength u + 10) * (100 * u + 200))
    (by have := nbl_mul_le u Z 100 200 10 (by omega); have h1 : (natWord 1).length = 3 := rfl
        have := sq_le_parB Z B; unfold parB at this ⊢
        have h2 : (Z + 1) ^ 2 ≤ (Z + 13) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        nlinarith)
    (listWord_single_le u Z (by omega)) (fun τ hk _ ho _ hsh hV => by
    rw [seth_self τ E.SUP 0 (by rw [hsh]; simp [preOne, Function.update_of_ne s1, hB.suph])]
    have hu14 : τ.val (rwC E.R 14) = u := by
      rw [hk 14 (by decide), rwC_14]; simp [preOne]
    have hz : ∀ k : Fin 16, 1 ≤ k.val → k.val ≤ 6 → τ.val (rwC E.R k) = 0 := fun k a d => by
      rw [hk k (Fin.ne_of_val_ne (by omega)), rwC_apply]
      have hk1 : 11 ≤ (cIdx k).val ∧ (cIdx k).val ≤ 16 := by fin_cases k <;> simp_all [cIdx]
      rw [preOne_val j u _ (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega))]
      exact hB.z _ (by omega) (by omega)
    have hl := listWord_single_le u Z (by omega)
    rw [Codec.marks_length] at hV
    exact Codec.parSys_spec cap E.S1 (rwC E.R) u τ ho hu14 hz (by
      have := nbl_le u; have h1 : (natWord 1).length = 3 := rfl; have := hFit.VZ; omega))
  exact WExec.mono (WExec.seq a1 (WExec.seq a2 a3)) (by omega)

theorem rwC_ne_8 (R : Fin 40 ↪ Fin nr) (k : Fin 16) : R 8 ≠ rwC R k := by
  rw [rwC_apply]; intro h; have := R.injective h; fin_cases k <;> simp [cIdx] at this <;> exact absurd this (by decide)

theorem rwC_ne_37 (R : Fin 40 ↪ Fin nr) (k : Fin 16) : R 37 ≠ rwC R k := by
  rw [rwC_apply]; intro h; have := R.injective h; fin_cases k <;> simp [cIdx] at this <;> exact absurd this (by decide)

/-- The parity writer of a row, as `callOne_canon` asks it. -/
theorem parRow_par (cap : ℕ) (hB : TermBase E tmap Cs N rows Rn w pre rest σ)
    (hFit : TermFit cap Cs N rows Rn ω w Z B V) (j r : ℕ) (hr : r < Rn) (h8 : σ.val (E.R 8) ≤ Z) :
    ∀ τ : WState ns nr, (∀ k : Fin 16, k ≠ 7 → τ.val (rwC E.R k) = (preOne E σ j r).val (rwC E.R k)) →
      (∀ x, (∀ k : Fin 16, x ≠ rwC E.R k) → τ.val x = (preOne E σ j r).val x) → τ.sh E.S1 = (τ.st E.S1).length →
      τ.st E.SUP = (preOne E σ j r).st E.SUP → τ.sh E.SUP = (preOne E σ j r).sh E.SUP →
      τ.val (rwC E.R 7) + (marks (listWord natWord (rows r))).length ≤ V →
      WExec cap (Codec.parRow E.SUP E.S1 (rwC E.R) (E.R 8)) τ
        (appendO (τ.seth E.SUP (rowPrefix rows (r + 1)).length) E.S1 (rwC E.R 7) (marks (listWord natWord (rows r))))
        (4000 * (Z + 1) ^ 2 * (B + 1)) := by
  intro τ hk hx ho hst hsh hV
  obtain ⟨-, ⟨s1, -, -, -, -, -, -⟩, -, -, -, -, -, -⟩ := hB.dis
  obtain ⟨restS, hrs⟩ := hB.sup
  have hrz := row_sizes (rows r) Z ((hFit.rowZ r hr).trans le_rfl)
  have hcV := hFit.capV
  have hRZ := hFit.RZ
  exact parRow_class cap E.SUP E.S1 s1 (rwC E.R) (E.R 8) (rwC_ne_8 E.R) rows Rn r hr B V (σ.val (E.R 8)) hFit.rowB
    hFit.rowfit (by omega) (by omega) (by have := nbl_le (rows r).length; omega) restS τ
    (by rw [hst]; simp [preOne, Function.update_of_ne s1, hrs]) (by rw [hsh]; simp [preOne, hB.suph]) ho
    (fun k a b c d e => by
      rw [hk k a, rwC_apply]
      have hk1 : 10 ≤ (cIdx k).val ∧ (cIdx k).val ≤ 21 := by fin_cases k <;> simp_all [cIdx]
      rw [preOne_val j r _ (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega))]
      exact hB.z _ hk1.1 (by omega))
    (by rw [hk 14 (by decide), rwC_14]; simp [preOne])
    (by rw [hx _ (rwC_ne_8 E.R), preOne_val j r 8 (by decide) (by decide)]) hV Z B h8 (by omega) le_rfl hrz.1 hrz.2

/-- A row `u − q`: parity list `rows (u − q)`. -/
theorem sysBC_exec (cap : ℕ) (hB : TermBase E tmap Cs N rows Rn w pre rest σ)
    (hFit : TermFit cap Cs N rows Rn ω w Z B V) (j u : ℕ) (hj : j < N) (hge : q ≤ u) (hu : u < q + Rn)
    (h7 : σ.val (E.R 7) ≤ Z) (h8 : σ.val (E.R 8) ≤ Z) :
    WExec cap (.seq (rowNonemptyW E.SUP (rwC E.R) (E.R 8) (E.R 37))
        (.ifr (E.R 37)
          (.seq (WM.clear (E.R 37))
            (Codec.callOneW E.CW E.S1 (rwC E.R) 2 (Codec.parRow E.SUP E.S1 (rwC E.R) (E.R 8)) ω))
          (Codec.callOneW E.CW E.S1 (rwC E.R) 0 (Codec.parRow E.SUP E.S1 (rwC E.R) (E.R 8)) ω)))
      (midSA E σ j u q)
      (canonRho E σ j (u - q) (cwPrefix Cs (j + 1)).length (rowPrefix rows (u - q + 1)).length
        (oneCallOf Cs j (sysList q rows u) ω))
      (20010000 * (Z + 13) ^ 4 * (B + 1) + 200 * (Z + 1) ^ 2 * (B + 1)) := by
  obtain ⟨-, ⟨s1, -, -, -, -, -, -⟩, -, -, -, -, -, -⟩ := hB.dis
  obtain ⟨restS, hrs⟩ := hB.sup
  set r := u - q with hrd
  have hr : r < Rn := by omega
  have hRZ := hFit.RZ
  have hcV := hFit.capV
  have hsl : sysList q rows u = rows r := by unfold sysList; rw [if_neg (by omega)]
  rw [hsl]
  have hm0 : (midSA E σ j u q).val (E.R 34) = 0 := by simp [midSA]; omega
  have hmv : ∀ k : Fin 40, k ≠ 23 → k ≠ 24 → k ≠ 34 → (midSA E σ j u q).val (E.R k) = σ.val (E.R k) := fun k a b d => by
    simp [midSA, Function.update_of_ne (R_ne E a), Function.update_of_ne (R_ne E b), Function.update_of_ne (R_ne E d)]
  have b1 := rowNonemptyW_spec cap E.SUP (rwC E.R) (E.R 8) (E.R 37) (rwC_ne_8 E.R) (rwC_ne_37 E.R) (R_ne E (by decide))
    rows Rn r hr B hFit.rowB hFit.rowfit (σ.val (E.R 8)) (by omega) restS (midSA E σ j u q)
    (by simp [midSA, Function.update_of_ne s1, hrs]) (by simp [midSA, hB.suph]) hB.supL
    (rwC_z E _ (fun i a d => by
      rw [hmv i (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega))]
      exact hB.z i a (by omega)))
    (by rw [rwC_14]; simp [midSA, Function.update_of_ne (R_ne E (show (24 : Fin 40) ≠ 34 by decide)), ← hrd])
    (hmv 8 (by decide) (by decide) (by decide)) (by rw [hmv 37 (by decide) (by decide) (by decide)]; exact hB.z 37 (by decide) (by decide))
  have hseth : (midSA E σ j u q).seth E.SUP 0 = midSA E σ j u q := seth_self _ _ _ (by simp [midSA, hB.suph])
  rw [hseth] at b1
  have hpre : (midSA E σ j u q).setv (E.R 37) 0 = preOne E σ j r := by
    refine WState.eq rfl rfl ?_ rfl
    funext x
    by_cases x37 : x = E.R 37
    · subst x37; simp [midSA, preOne, Function.update_of_ne (R_ne E (show (37 : Fin 40) ≠ 24 by decide)),
        Function.update_of_ne (R_ne E (show (37 : Fin 40) ≠ 23 by decide)), hB.z 37 (by decide) (by decide)]
    by_cases x34 : x = E.R 34
    · subst x34; simp [midSA, preOne, Function.update_of_ne (R_ne E (show (34 : Fin 40) ≠ 37 by decide)),
        Function.update_of_ne (R_ne E (show (34 : Fin 40) ≠ 24 by decide)),
        Function.update_of_ne (R_ne E (show (34 : Fin 40) ≠ 23 by decide)), hB.z 34 (by decide) (by decide)]; omega
    simp [midSA, preOne, Function.update_of_ne x37, Function.update_of_ne x34, ← hrd]
  have hcp : 4000 * (Z + 1) ^ 2 * (B + 1) ≤ parB Z B := by
    unfold parB
    have h2 : (Z + 1) ^ 2 ≤ (Z + 13) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h2)
  have hps : (listWord natWord (rows r)).length ≤ 2 * Z + 10 := by have := hFit.rowZ r hr; omega
  have hbc : (r + 1) * (B + 30) ≤ 30 * (Z + 1) ^ 2 * (B + 1) := by
    have h1 : r + 1 ≤ (Z + 1) ^ 2 := by nlinarith
    have h2 : B + 30 ≤ 30 * (B + 1) := by omega
    calc (r + 1) * (B + 30) ≤ (Z + 1) ^ 2 * (30 * (B + 1)) := Nat.mul_le_mul h1 h2
      _ = 30 * (Z + 1) ^ 2 * (B + 1) := by ring
  have hZ1 : 60 * (σ.val (E.R 8) + 1) ≤ 60 * (Z + 1) ^ 2 * (B + 1) := by
    have : σ.val (E.R 8) + 1 ≤ (Z + 1) ^ 2 * (B + 1) := by nlinarith
    nlinarith
  by_cases hne : rows r = []
  · -- an empty row: tag 0
    have hfl : (decide (rows r ≠ [])).toNat = 0 := by simp [hne]
    rw [hfl, hpre] at b1
    have a := callOne_canon cap hB hFit j r (rowPrefix rows (r + 1)).length hj h7 (rows r) 0 (by simp [hne])
      (Codec.parRow E.SUP E.S1 (rwC E.R) (E.R 8)) _ hcp hps (parRow_par cap hB hFit j r hr h8)
    have e2 := WExec.ifrF (r := E.R 37) (P := .seq (WM.clear (E.R 37))
        (Codec.callOneW E.CW E.S1 (rwC E.R) 2 (Codec.parRow E.SUP E.S1 (rwC E.R) (E.R 8)) ω))
      (by simp [preOne, Function.update_of_ne (R_ne E (show (37 : Fin 40) ≠ 24 by decide)),
            Function.update_of_ne (R_ne E (show (37 : Fin 40) ≠ 23 by decide)), hB.z 37 (by decide) (by decide)]) a
    exact WExec.mono (WExec.seq b1 e2) (by
      have e1 : 200 * (Z + 1) ^ 2 * (B + 1) = 200 * ((Z + 1) ^ 2 * (B + 1)) := by ring
      have e2 : 30 * (Z + 1) ^ 2 * (B + 1) = 30 * ((Z + 1) ^ 2 * (B + 1)) := by ring
      have e3 : 60 * (Z + 1) ^ 2 * (B + 1) = 60 * ((Z + 1) ^ 2 * (B + 1)) := by ring
      omega)
  · -- a nonempty row: tag 2
    have hfl : (decide (rows r ≠ [])).toNat = 1 := by simp [hne]
    rw [hfl] at b1
    have c1 := wclear_spec (cap := cap) (E.R 37) 1 ((midSA E σ j u q).setv (E.R 37) 1) (by simp) (by simp; omega)
    rw [show ((midSA E σ j u q).setv (E.R 37) 1).setv (E.R 37) 0 = (midSA E σ j u q).setv (E.R 37) 0 by
      simp [WState.setv], hpre] at c1
    have a := callOne_canon cap hB hFit j r (rowPrefix rows (r + 1)).length hj h7 (rows r) 2 (by simp [hne])
      (Codec.parRow E.SUP E.S1 (rwC E.R) (E.R 8)) _ hcp hps (parRow_par cap hB hFit j r hr h8)
    have e2 := WExec.ifrT (r := E.R 37) (Q := Codec.callOneW E.CW E.S1 (rwC E.R) 0
        (Codec.parRow E.SUP E.S1 (rwC E.R) (E.R 8)) ω) (by simp) (WExec.seq c1 a)
    exact WExec.mono (WExec.seq b1 e2) (by
      have e1 : 200 * (Z + 1) ^ 2 * (B + 1) = 200 * ((Z + 1) ^ 2 * (B + 1)) := by ring
      have e2 : 30 * (Z + 1) ^ 2 * (B + 1) = 30 * ((Z + 1) ^ 2 * (B + 1)) := by ring
      have e3 : 60 * (Z + 1) ^ 2 * (B + 1) = 60 * ((Z + 1) ^ 2 * (B + 1)) := by ring
      omega)

theorem sysAux_exec (cap : ℕ) (hB : TermBase E tmap Cs N rows Rn w pre rest σ)
    (hFit : TermFit cap Cs N rows Rn ω w Z B V) (xs xa : Fin 40) (hx : (xs = 2 ∧ xa = 5) ∨ (xs = 5 ∧ xa = 2))
    (hu : σ.val (E.R xs) < q + Rn) (hj : σ.val (E.R xa) < N) (huZ : σ.val (E.R xs) ≤ Z) (hjZ : σ.val (E.R xa) ≤ Z)
    (h7 : σ.val (E.R 7) ≤ Z) (h8 : σ.val (E.R 8) ≤ Z) :
    ∃ b hs, WExec cap (sysAuxW E (E.R xs) (E.R xa) ω) (σ.sets E.S1 [])
        (canonRho E σ (σ.val (E.R xa)) b (cwPrefix Cs (σ.val (E.R xa) + 1)).length hs
          (oneCallOf Cs (σ.val (E.R xa)) (sysList q rows (σ.val (E.R xs))) ω)) (writerCost Z B) ∧
      b ≤ Z ∧ hs ≤ σ.val (E.R 8) := by
  set u := σ.val (E.R xs) with hud
  set j := σ.val (E.R xa) with hjd
  have hxs : xs = 2 ∨ xs = 5 := by rcases hx with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
  have hxsn : ∀ k : Fin 40, 6 ≤ k.val → xs ≠ k := fun k hk h => by rcases hxs with rfl | rfl <;> subst h <;> simp at hk
  have hxan : ∀ k : Fin 40, 6 ≤ k.val → xa ≠ k := fun k hk h => by
    rcases hx with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> subst h <;> simp at hk
  have hsa : xs ≠ xa := by rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hcV := hFit.capV
  have hqZ := hFit.qZ
  set σ0 := σ.sets E.S1 [] with hσ0
  have e1 := Codec.dupR_spec cap (E.R xa) (E.R 23) (E.R 38) (R_ne E (hxan 23 (by decide))) (R_ne E (hxan 38 (by decide)))
    (R_ne E (by decide)) σ0 (by simp [hσ0]; exact hB.z 38 (by decide) (by decide))
    (by simp [hσ0, hB.z 23 (by decide) (by decide)]; omega)
  rw [show σ0.val (E.R 23) = 0 from hB.z 23 (by decide) (by decide), Nat.zero_add,
    show σ0.val (E.R xa) = j from rfl] at e1
  have e2 := Worker.ltSubW_spec (cap := cap) (E.R xs) (E.R 6) (E.R 24) (E.R 34) (E.R 35) (E.R 36)
    (by simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
        exact ⟨⟨R_ne E (hxsn 6 (by decide)), R_ne E (hxsn 24 (by decide)), R_ne E (hxsn 34 (by decide)),
          R_ne E (hxsn 35 (by decide)), R_ne E (hxsn 36 (by decide))⟩, ⟨R_ne E (by decide), R_ne E (by decide),
          R_ne E (by decide), R_ne E (by decide)⟩, ⟨R_ne E (by decide), R_ne E (by decide), R_ne E (by decide)⟩,
          ⟨R_ne E (by decide), R_ne E (by decide)⟩, R_ne E (by decide), fun h => h⟩)
    (σ0.setv (E.R 23) j)
    (by simp [hσ0, Function.update_of_ne (R_ne E (show (24 : Fin 40) ≠ 23 by decide)), hB.z 24 (by decide) (by decide)])
    (by simp [hσ0, Function.update_of_ne (R_ne E (show (34 : Fin 40) ≠ 23 by decide)), hB.z 34 (by decide) (by decide)])
    (by simp [hσ0, Function.update_of_ne (R_ne E (show (35 : Fin 40) ≠ 23 by decide)), hB.z 35 (by decide) (by decide)])
    (by simp [hσ0, Function.update_of_ne (R_ne E (show (36 : Fin 40) ≠ 23 by decide)), hB.z 36 (by decide) (by decide)])
    (by simp [hσ0, Function.update_of_ne (R_ne E (hxsn 23 (by decide))),
          Function.update_of_ne (R_ne E (show (6 : Fin 40) ≠ 23 by decide)), hB.hq]; omega)
  have hv6 : (σ0.setv (E.R 23) j).val (E.R 6) = q := by
    simp [hσ0, Function.update_of_ne (R_ne E (show (6 : Fin 40) ≠ 23 by decide)), hB.hq]
  have hvs : (σ0.setv (E.R 23) j).val (E.R xs) = u := by
    simp [hσ0, Function.update_of_ne (R_ne E (hxsn 23 (by decide))), hud]
  rw [hv6, hvs] at e2
  have hmid : ((σ0.setv (E.R 23) j).setv (E.R 24) (u - q)).setv (E.R 34) (q - u) = midSA E σ j u q := rfl
  rw [hmid] at e2
  have hx' : σ.val (E.R xs) = u := rfl
  by_cases hlt : u < q
  · have a := sysA_exec cap hB hFit xs hxs j u hj hx' hlt h7
    refine ⟨u, 0, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.ifrT (by simp [midSA]; omega) a))) ?_, huZ, by omega⟩
    have hx : 18 * j + 3 + 1 + (18 * u + 3 + 1 + (18 * q + 3 + 1 + (8 * q + 1))) + 1 + 1 + 100 * (Z + 1) ≤
        1000 * (Z + 13) ^ 2 * (B + 1) := by
      have : 1 ≤ B + 1 := by omega
      nlinarith
    have := writer_cost_le Z B _ hx
    omega
  · have a := sysBC_exec cap hB hFit j u hj (by omega) hu h7 h8
    refine ⟨u - q, (rowPrefix rows (u - q + 1)).length,
      WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.ifrF (by simp [midSA]; omega) a))) ?_, by omega, ?_⟩
    · have hx : 18 * j + 3 + 1 + (18 * u + 3 + 1 + (18 * q + 3 + 1 + (8 * q + 1))) + 1 + 1 +
          200 * (Z + 1) ^ 2 * (B + 1) ≤ 1000 * (Z + 13) ^ 2 * (B + 1) := by
        have : 1 ≤ B + 1 := by omega
        have h2 : (Z + 1) ^ 2 ≤ (Z + 13) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        nlinarith
      have := writer_cost_le Z B _ hx
      omega
    · exact (rowPrefix_succ_le rows (show u - q < Rn by omega)).trans hB.supL

end Canon

end NearCubicGates.Close.WorkerArith
