import Proof.Gates.Expand.Inst
import Proof.Gates.Expand.Fam4

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.Expand

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.WordPrograms.BinW (numOn_sets_ne numOn_sets_self numOn_setv)
open NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Tabulator
open StablePartition.Workspace (overlay)

variable {ns nr : ℕ}

structure Lay (ns nr : ℕ) where
  U : Fin 10 ↪ Fin (ns + 1)
  R : Fin 12 ↪ Fin nr
  UF : Fin 12 ↪ Fin (ns + 1)
  RF : Fin 14 ↪ Fin nr
  X : Fin 4 ↪ Fin (ns + 1)
  Y : Fin 8 ↪ Fin nr
  dUUF : ∀ i j, U i ≠ UF j
  dUX : ∀ i j, U i ≠ X j
  dUFX : ∀ i j, UF i ≠ X j
  dRRF : ∀ i j, R i ≠ RF j
  dRY : ∀ i j, R i ≠ Y j
  dRFY : ∀ i j, RF i ≠ Y j

/-- The value record of a family record. -/
def valRec (V W : ℕ) {V' : ℕ} (F : Formula V') (rec : ℕ) : ℕ :=
  rec * 2 ^ W + (valAlg W (rec % 2 ^ V)).eval F

section Prog
variable (L : Lay ns nr)

def valBody : WMX ns nr :=
  .seq (BinW.copy (L.U 9) (L.UF 3) (L.R 2) (L.R 3)) (.seq (andX (L.U 9) (L.UF 10) (L.R 2) (L.R 3))
    (.seq (evalPass L.U L.R (L.Y 0) (L.Y 1) (valH L.U L.R))
      (.seq (BinW.mul (L.UF 3) (L.U 6) (L.UF 6) (L.UF 5) (L.RF 0) (L.RF 1) (L.RF 11))
        (.seq (BinW.add (L.UF 6) (L.U 2) (L.RF 0) (L.RF 1)) (appendRecX (L.UF 6) (L.X 0) (L.RF 4) (L.Y 2))))))

/-- The values phase. -/
def valPhase : WMX ns nr :=
  .seq (recLoop (L.UF 2) (L.UF 3) (L.RF 2) (L.RF 3) (valBody L)) (closeOutX (L.X 0) (L.Y 2))

end Prog

section BodySpec
variable {L : Lay ns nr}

theorem Lay.uN (L : Lay ns nr) {i j : Fin 10} (h : i ≠ j) : L.U i ≠ L.U j := fun e => h (L.U.injective e)
theorem Lay.rN (L : Lay ns nr) {i j : Fin 12} (h : i ≠ j) : L.R i ≠ L.R j := fun e => h (L.R.injective e)
theorem Lay.ufN (L : Lay ns nr) {i j : Fin 12} (h : i ≠ j) : L.UF i ≠ L.UF j := fun e => h (L.UF.injective e)
theorem Lay.rfN (L : Lay ns nr) {i j : Fin 14} (h : i ≠ j) : L.RF i ≠ L.RF j := fun e => h (L.RF.injective e)

theorem Lay.notMem_evS (L : Lay ns nr) (j : Fin 12) : L.UF j ∉ evS L.U := by
  intro h; simp only [evS, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h <;> exact L.dUUF _ _ h.symm

theorem Lay.notMem_evSX (L : Lay ns nr) (j : Fin 4) : L.X j ∉ evS L.U := by
  intro h; simp only [evS, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h <;> exact L.dUX _ _ h.symm

theorem Lay.notMem_evR (L : Lay ns nr) (j : Fin 14) : L.RF j ∉ evR L.R ++ [L.R 11] :=
  NearCubicGates.Close.Expand.notMem_evR (fun i => L.dRRF i j)

theorem Lay.notMem_evRY (L : Lay ns nr) (j : Fin 8) : L.Y j ∉ evR L.R ++ [L.R 11] :=
  NearCubicGates.Close.Expand.notMem_evR (fun i => L.dRY i j)

def valBodyCost (Wb : ℕ) (c : ℕ) : ℕ :=
  (41 * Wb + 3) + 1 + ((41 * Wb + 3) + 1 + (c + 1 + (NearCubicWires.WireExponent3_5.UnionMachine.RegRat.mulCost Wb
    + 1 + ((41 * Wb + 3) + 1 + (40 * Wb + 11)))))

/-- **One family record** of the values phase. -/
theorem valBody_spec (cap Wb W V : ℕ) (r : FormulaReq) (rec : ℕ) (out L0 : List Bool) (σ : WState ns nr)
    (hE : ∃ t, EvAt L.U L.R Wb (2 ^ W) (2 ^ W - 1) t (frame (formulaWord r)) 0 [] σ) (h11 : σ.val (L.R 11) = 0)
    (hRL : σ.val (L.Y 0) = 2 * (formulaWord r).length + 1) (hRL2 : σ.val (L.Y 1) = 0)
    (hWK : NumOn σ (L.UF 3) Wb rec) (hMk : NumOn σ (L.UF 10) Wb (2 ^ V - 1))
    (h5 : ∃ x, NumOn σ (L.UF 5) Wb x) (h6 : ∃ x, NumOn σ (L.UF 6) Wb x)
    (hR0 : σ.val (L.RF 0) = 0) (hR1 : σ.val (L.RF 1) = 0) (hR4 : σ.val (L.RF 4) = 0) (hR11 : σ.val (L.RF 11) = 0)
    (hO : OutOn σ (L.X 0) (L.Y 2) out L0)
    (hW : VOK Wb W) (hVW : V < Wb) (hWlt : 2 ^ W < 2 ^ Wb) (hrec : (rec + 1) * 2 ^ W ≤ 2 ^ Wb)
    (hdepth : (2 ^ W) ^ ((toks r.2).length + 2) ≤ 2 ^ Wb) (hcap : 2 * Wb + 1 ≤ cap)
    (hcapL : 2 ^ ((formulaWord r).length + 4) ≤ cap) (hcapO : out.length + 2 * Wb + 2 ≤ cap) :
    Runs cap (valBody L) σ (valBodyCost Wb (evalCost Wb (hcost Wb (tokBits r.2) (maxExp r.2) r.1) r.1
        (toks r.2).length (formulaWord r).length))
      (fun τ => (∃ t, EvAt L.U L.R Wb (2 ^ W) (2 ^ W - 1) t (frame (formulaWord r)) 0 [] τ) ∧
        τ.val (L.R 11) = 0 ∧ τ.val (L.Y 0) = σ.val (L.Y 0) ∧ τ.val (L.Y 1) = 0 ∧
        (∃ x, NumOn τ (L.UF 5) Wb x) ∧ (∃ x, NumOn τ (L.UF 6) Wb x) ∧
        τ.val (L.RF 0) = 0 ∧ τ.val (L.RF 1) = 0 ∧ τ.val (L.RF 4) = 0 ∧ τ.val (L.RF 11) = 0 ∧
        OutOn τ (L.X 0) (L.Y 2) (out ++ frame (binary Wb (valRec V W r.2 rec))) L0 ∧
        SameExcept σ τ (L.U 9 :: L.UF 5 :: L.UF 6 :: L.X 0 :: evS L.U)
          (L.RF 0 :: L.RF 1 :: L.RF 11 :: L.Y 2 :: (evR L.R ++ [L.R 11]))) := by
  obtain ⟨t0, hE⟩ := hE
  have hWb := hW.wb
  have hTW : 2 ^ W ≤ 2 ^ Wb := Nat.pow_le_pow_right (by norm_num) hWb
  have hrecW : rec < 2 ^ Wb := by
    have : rec + 1 ≤ (rec + 1) * 2 ^ W := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos W)
    omega

  have c1 := BinW.copy_spec cap Wb (L.dUUF 9 3) (L.rN (by decide : (2 : Fin 12) ≠ 3)) σ t0 rec hE.ev.pt hWK
    (hE.ev.reg 2) (hE.ev.reg 3) hcap
  set σ1 := σ.sets (L.U 9) (frame (binary Wb rec)) with hσ1
  have hM1 : NumOn σ1 (L.UF 10) Wb (2 ^ V - 1) := numOn_sets_ne hMk (fun e => L.dUUF 9 10 e.symm) _
  have a2 := WXExec.wm (andW_spec cap Wb (L.dUUF 9 10) (L.rN (by decide : (2 : Fin 12) ≠ 3)) σ1 rec _
    (numOn_sets_self σ _ Wb rec hE.ev.pt.2) hM1 (by simpa [hσ1] using hE.ev.reg 2) (by simpa [hσ1] using hE.ev.reg 3)
    hcap)
  rw [Nat.and_two_pow_sub_one_eq_mod] at a2
  set s := rec % 2 ^ V with hs
  set σ2 := σ1.sets (L.U 9) (frame (binary Wb s)) with hσ2
  have f12 : SameExcept σ σ2 [L.U 9] [] :=
    SameExcept.trans (sameExcept_sets σ (by simp) _) (sameExcept_sets σ1 (by simp) _)
  have nin9 : ∀ i : Fin 10, i ≠ 9 → L.U i ∉ [L.U 9] := by
    intro i hi hm; simp only [List.mem_singleton] at hm; exact hi (L.U.injective hm)
  have hE2 : EvAt L.U L.R Wb (2 ^ W) (2 ^ W - 1) s (frame (formulaWord r)) 0 [] σ2 := by
    refine ⟨⟨fun i hi => ?_, f12.numOn (nin9 6 (by decide)) hE.ev.mm, f12.numOn (nin9 7 (by decide)) hE.ev.km,
      f12.numOn (nin9 8 (by decide)) hE.ev.one, numOn_sets_self σ1 _ Wb s (by simpa [hσ1] using hE.ev.pt.2),
      fun j hj => by rw [f12.val (by simp)]; exact hE.ev.zero j hj⟩,
      by rw [f12.st (nin9 0 (by decide))]; exact hE.inp, by rw [f12.sh (nin9 0 (by decide))]; exact hE.hd,
      f12.numOn (nin9 1 (by decide)) hE.stk⟩
    obtain ⟨x, hx⟩ := hE.ev.num i hi
    refine ⟨x, f12.numOn (fun hm => ?_) hx⟩
    simp only [List.mem_singleton] at hm
    have := L.U.injective hm; subst this; simp at hi
  -- the value pass
  have hsV : s < 2 ^ V := Nat.mod_lt _ (Nat.two_pow_pos V)
  have hsW : s < 2 ^ Wb := lt_of_lt_of_le hsV (Nat.pow_le_pow_right (by norm_num) hVW.le)
  have hev := evalPass_spec cap Wb (2 ^ W) (2 ^ W - 1) s (hcost Wb (tokBits r.2) (maxExp r.2) r.1) (valAlg W s)
    (valAlg_closed W s) (two_le_pow hW.w1) (valH L.U L.R) rfl r
    (fun tok htok => valHs L.U L.R cap Wb W s (tokBits r.2) (maxExp r.2) r.1 hW hsW hcap
      (le_trans (Nat.pow_le_pow_right (by norm_num) (by have := tokBits_le r; omega)) hcapL) tok
      (toks_ok r.2 tok htok))
    (L.Y 0) (L.Y 1) (fun j => L.dRY j 0) (fun j => L.dRY j 1) (fun e => absurd (L.Y.injective e) (by decide))
    σ2 hE2 (by rw [f12.val (by simp)]; exact h11) (by rw [f12.val (by simp)]; exact hRL)
    (by rw [f12.val (by simp)]; exact hRL2) hdepth hcap hcapL
  refine Runs.seqE c1 (Runs.seqE a2 (Runs.seq hev (fun τ3 ⟨hE3, hA3, h113, hRL3, hRL23, f3⟩ => ?_)))
  -- E := WK · 2^W + A
  have f23 : SameExcept σ τ3 (L.U 9 :: evS L.U) (evR L.R ++ [L.R 11]) :=
    SameExcept.trans (f12.weaken (fun x hx => by simp at hx ⊢; tauto) (fun r hr => by simp at hr))
      (f3.weaken (fun x hx => by simp at hx ⊢; tauto) (fun r hr => hr))
  have ninU : ∀ j : Fin 12, L.UF j ∉ L.U 9 :: evS L.U := by
    intro j hm; rcases List.mem_cons.mp hm with hm | hm
    · exact L.dUUF 9 j hm.symm
    · exact L.notMem_evS j hm
  have ninX : ∀ j : Fin 4, L.X j ∉ L.U 9 :: evS L.U := by
    intro j hm; rcases List.mem_cons.mp hm with hm | hm
    · exact L.dUX 9 j hm.symm
    · exact L.notMem_evSX j hm
  obtain ⟨x5, h5⟩ := h5
  obtain ⟨x6, h6⟩ := h6
  have hWK3 := f23.numOn (ninU 3) hWK
  have h53 := f23.numOn (ninU 5) h5
  have h63 := f23.numOn (ninU 6) h6
  have hmm3 : NumOn τ3 (L.U 6) Wb (2 ^ W) := hE3.ev.mm
  have hf : (valAlg W s).eval r.2 < 2 ^ W := (valAlg W s).eval_lt (valAlg_closed W s) r.2
  have m4 := BinW.mul_spec cap Wb (L.dUUF 6 3).symm (L.ufN (by decide : (3 : Fin 12) ≠ 6))
    (L.ufN (by decide : (3 : Fin 12) ≠ 5)) (L.dUUF 6 6) (L.dUUF 6 5) (L.ufN (by decide : (6 : Fin 12) ≠ 5))
    (L.rfN (by decide : (0 : Fin 14) ≠ 1)) (L.rfN (by decide : (0 : Fin 14) ≠ 11)) (L.rfN (by decide : (1 : Fin 14) ≠ 11))
    τ3 rec (2 ^ W) x6 x5 hWK3 hmm3 h63 h53
    (by rw [f23.val (L.notMem_evR 0)]; exact hR0) (by rw [f23.val (L.notMem_evR 1)]; exact hR1)
    (by rw [f23.val (L.notMem_evR 11)]; exact hR11) (by nlinarith) hWlt hcap
  set τ4 := (τ3.sets (L.UF 6) (frame (binary Wb (rec * 2 ^ W)))).sets (L.UF 5) (frame (binary Wb 0)) with hτ4
  have f34 : SameExcept τ3 τ4 [L.UF 5, L.UF 6] [] :=
    SameExcept.trans (sameExcept_sets _ (by simp) _) (sameExcept_sets _ (by simp) _)
  have hE4 : NumOn τ4 (L.UF 6) Wb (rec * 2 ^ W) :=
    numOn_sets_ne (numOn_sets_self τ3 _ Wb _ h63.2) (L.ufN (by decide : (6 : Fin 12) ≠ 5)) _
  have hA4 : NumOn τ4 (L.U 2) Wb ((valAlg W s).eval r.2) :=
    f34.numOn (by simp [L.dUUF 2 5, L.dUUF 2 6]) hA3
  have a5 := BinW.add_spec cap Wb (L.dUUF 2 6).symm (L.rfN (by decide : (0 : Fin 14) ≠ 1)) τ4 _ _ hE4 hA4
    (by rw [f34.val (by simp), f23.val (L.notMem_evR 0)]; exact hR0)
    (by rw [f34.val (by simp), f23.val (L.notMem_evR 1)]; exact hR1) (by nlinarith) hcap
  set τ5 := τ4.sets (L.UF 6) (frame (binary Wb (rec * 2 ^ W + (valAlg W s).eval r.2))) with hτ5
  have f45 : SameExcept τ4 τ5 [L.UF 6] [] := sameExcept_sets _ (by simp) _
  have f35 : SameExcept τ3 τ5 [L.UF 5, L.UF 6] [] :=
    SameExcept.trans f34 (f45.weaken (fun x hx => by simp at hx ⊢; tauto) (fun r hr => hr))
  have hO5 : OutOn τ5 (L.X 0) (L.Y 2) out L0 :=
    ⟨by rw [f35.st (by simp [L.dUFX 5 0, L.dUFX 6 0, Ne.symm (L.dUFX 5 0), Ne.symm (L.dUFX 6 0)]),
        f23.st (ninX 0)]; exact hO.1,
      by rw [f35.sh (by simp [Ne.symm (L.dUFX 5 0), Ne.symm (L.dUFX 6 0)]), f23.sh (ninX 0)]; exact hO.2.1,
      by rw [f35.val (by simp), f23.val (L.notMem_evRY 2)]; exact hO.2.2⟩
  refine Runs.seqE m4 (Runs.seqE a5 ((appendNum cap Wb (L.dUFX 6 0) (L.dRFY 4 2) τ5 _ out L0
    (numOn_sets_self τ4 _ Wb _ hE4.2) (by rw [f35.val (by simp), f23.val (L.notMem_evR 4)]; exact hR4) hO5
    hcapO).post (fun τ6 ⟨hO6, f6⟩ => ?_)))
  have nX0 : ∀ i : Fin 10, L.U i ∉ [L.X 0] := by
    intro i hm; simp only [List.mem_singleton] at hm; exact L.dUX i 0 hm
  have f56 := f6
  refine ⟨⟨s, ?_⟩, ?_, ?_, ?_, ⟨0, ?_⟩, ⟨rec * 2 ^ W + (valAlg W s).eval r.2, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have fE : SameExcept τ3 τ6 [L.UF 5, L.UF 6, L.X 0] [L.Y 2] :=
      SameExcept.trans (f35.weaken (fun x hx => by simp at hx ⊢; tauto) (fun r hr => by simp at hr))
        (f56.weaken (fun x hx => by simp at hx ⊢; tauto) (fun r hr => by simp at hr ⊢; tauto))
    have nU : ∀ i : Fin 10, L.U i ∉ [L.UF 5, L.UF 6, L.X 0] := by
      intro i hm; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with hm | hm | hm
      · exact L.dUUF i 5 hm
      · exact L.dUUF i 6 hm
      · exact L.dUX i 0 hm
    have nR : ∀ j : Fin 12, L.R j ∉ [L.Y 2] := by
      intro j hm; simp only [List.mem_singleton] at hm; exact L.dRY j 2 hm
    exact ⟨⟨fun i hi => by obtain ⟨x, hx⟩ := hE3.ev.num i hi; exact ⟨x, fE.numOn (nU i) hx⟩,
      fE.numOn (nU 6) hE3.ev.mm, fE.numOn (nU 7) hE3.ev.km, fE.numOn (nU 8) hE3.ev.one, fE.numOn (nU 9) hE3.ev.pt,
      fun j hj => by rw [fE.val (nR j)]; exact hE3.ev.zero j hj⟩,
      by rw [fE.st (nU 0)]; exact hE3.inp, by rw [fE.sh (nU 0)]; exact hE3.hd, fE.numOn (nU 1) hE3.stk⟩
  · rw [f56.val (by simp; exact L.dRY 11 2), f35.val (by simp)]; exact h113
  · rw [f56.val (by simp), f35.val (by simp)]; exact hRL3
  · rw [f56.val (by simp), f35.val (by simp)]; exact hRL23
  · have h4 : NumOn τ4 (L.UF 5) Wb 0 := numOn_sets_self _ _ Wb 0 (by simpa using h53.2)
    have h5' : NumOn τ5 (L.UF 5) Wb 0 := numOn_sets_ne h4 (L.ufN (by decide : (5 : Fin 12) ≠ 6)) _
    exact f56.numOn (by simp [L.dUFX 5 0]) h5'
  · exact f56.numOn (by simp [L.dUFX 6 0]) (numOn_sets_self τ4 _ Wb _ hE4.2)
  · rw [f56.val (by simp; exact L.dRFY 0 2), f35.val (by simp), f23.val (L.notMem_evR 0)]; exact hR0
  · rw [f56.val (by simp; exact L.dRFY 1 2), f35.val (by simp), f23.val (L.notMem_evR 1)]; exact hR1
  · rw [f56.val (by simp; exact L.dRFY 4 2), f35.val (by simp), f23.val (L.notMem_evR 4)]; exact hR4
  · rw [f56.val (by simp; exact L.dRFY 11 2), f35.val (by simp), f23.val (L.notMem_evR 11)]; exact hR11
  · exact hO6
  · exact SameExcept.trans (SameExcept.trans
      (se_sub f23 (List.cons_subset_cons _ (fun x hx => by simp [hx])) (fun x hx => by simp [hx]))
      (se_sub f35 (by simp [List.cons_subset]) (by simp)))
      (se_sub f56 (by simp [List.cons_subset]) (by simp [List.cons_subset]))

end BodySpec

end NearCubicGates.Close.Expand
