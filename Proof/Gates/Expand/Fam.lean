import Proof.Gates.Expand.Setup
import Proof.Gates.WordPrograms.RegArith
import Proof.Gates.WordPrograms.RecLoopJ

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
open StablePartition.Workspace (overlay)

variable {ns nr : ℕ}

/-- The records emitted for the set `s` by the variables `v < j` (`dt = (d+1)·T` for level `d`). -/
def emitted (Wb dt s j : ℕ) : List Bool :=
  (((List.range j).filter fun v => Nat.size s ≤ v).map fun v => s + 2 ^ v + dt).flatMap
    fun x => frame (binary Wb x)

theorem emitted_succ (Wb dt s j : ℕ) :
    emitted Wb dt s (j + 1) = emitted Wb dt s j ++
      (if Nat.size s ≤ j then frame (binary Wb (s + 2 ^ j + dt)) else []) := by
  unfold emitted
  rw [List.range_succ, List.filter_append]
  by_cases h : Nat.size s ≤ j
  · simp [h]
  · simp [h]

section Body
variable (UF : Fin 12 ↪ Fin (ns + 1)) (RF : Fin 14 ↪ Fin nr)

/-- One variable `v` (`P = 2^v`): if `s < P`, emit `s + P + (d+1)·T`; then `P := 2P`. -/
def vStep : WMX ns nr :=
  .seq (BinW.lt (UF 4) (UF 5) (RF 0) (RF 1))
    (.seq (.ifr (RF 0) (.seq (WMX.dec (RF 0)) (.seq (BinW.copy (UF 6) (UF 4) (RF 0) (RF 1))
      (.seq (BinW.add (UF 6) (UF 5) (RF 0) (RF 1)) (.seq (BinW.add (UF 6) (UF 9) (RF 0) (RF 1))
        (appendRecX (UF 6) (UF 1) (RF 4) (RF 5)))))) WMX.skip)
      (BinW.shl (UF 5) (UF 7) (RF 0) (RF 1)))

/-- One record of CUR (in WK): `S := WK ∧ MASKV`, `P := 1`, then every variable. -/
def famBody : WMX ns nr :=
  .seq (BinW.copy (UF 4) (UF 3) (RF 0) (RF 1)) (.seq (andX (UF 4) (UF 10) (RF 0) (RF 1))
    (.seq (BinW.copy (UF 5) (UF 7) (RF 0) (RF 1)) (repK (RF 10) (RF 11) (vStep UF RF))))

/-- The state inside the variable loop of one record. -/
structure VS (Wb dt s j : ℕ) (out0 L0 : List Bool) (σ0 σ : WState ns nr) : Prop where
  S : NumOn σ (UF 4) Wb s
  P : NumOn σ (UF 5) Wb (2 ^ j)
  E : ∃ e, NumOn σ (UF 6) Wb e
  one : NumOn σ (UF 7) Wb 1
  dtn : NumOn σ (UF 9) Wb dt
  f : σ.val (RF 0) = 0
  r : σ.val (RF 1) = 0
  cs : σ.val (RF 4) = 0
  out : OutOn σ (UF 1) (RF 5) (out0 ++ emitted Wb dt s j) L0
  fr : SameExcept σ0 σ [UF 1, UF 4, UF 5, UF 6] [RF 0, RF 1, RF 4, RF 5, RF 10, RF 11]

def vStepCost (Wb : ℕ) : ℕ :=
  (41 * Wb + 3) + 1 + ((1 + 1 + ((41 * Wb + 3) + 1 + ((41 * Wb + 3) + 1 + ((41 * Wb + 3) + 1 + (40 * Wb + 11)))))
    + 1 + 1 + (41 * Wb + 8))

end Body

section BodySpec
variable {UF : Fin 12 ↪ Fin (ns + 1)} {RF : Fin 14 ↪ Fin nr}

theorem ufN {i j : Fin 12} (h : i ≠ j) : UF i ≠ UF j := fun e => h (UF.injective e)
theorem rfN {i j : Fin 14} (h : i ≠ j) : RF i ≠ RF j := fun e => h (RF.injective e)

theorem VS.setv {Wb dt s j : ℕ} {out0 L0 : List Bool} {σ0 σ : WState ns nr} (h : VS UF RF Wb dt s j out0 L0 σ0 σ)
    (k : Fin 14) (hk : k = 10 ∨ k = 11) (x : ℕ) : VS UF RF Wb dt s j out0 L0 σ0 (σ.setv (RF k) x) := by
  have hk0 : ∀ i : Fin 14, i = 0 ∨ i = 1 ∨ i = 4 ∨ i = 5 → RF i ≠ RF k := by
    intro i hi; apply rfN; rcases hi with rfl | rfl | rfl | rfl <;> rcases hk with rfl | rfl <;> decide
  obtain ⟨e, he⟩ := h.E
  refine ⟨numOn_setv h.S _ _, numOn_setv h.P _ _, ⟨e, numOn_setv he _ _⟩, numOn_setv h.one _ _, numOn_setv h.dtn _ _,
    ?_, ?_, ?_, ?_, ?_⟩
  · simp [Function.update_of_ne (hk0 0 (by decide)), h.f]
  · simp [Function.update_of_ne (hk0 1 (by decide)), h.r]
  · simp [Function.update_of_ne (hk0 4 (by decide)), h.cs]
  · exact ⟨by simpa using h.out.1, by simpa using h.out.2.1,
      by simp [Function.update_of_ne (hk0 5 (by decide)), h.out.2.2]⟩
  · exact SameExcept.trans h.fr (sameExcept_setv σ (by rcases hk with rfl | rfl <;> simp) x)

theorem vStep_spec (cap Wb dt s j : ℕ) (out0 L0 : List Bool) (σ0 σ : WState ns nr)
    (h : VS UF RF Wb dt s j out0 L0 σ0 σ) (hjW : j + 1 < Wb) (hs : s < 2 ^ Wb) (hsum : s + 2 ^ j + dt < 2 ^ Wb)
    (hcap : 2 * Wb + 1 ≤ cap) (hcapO : (out0 ++ emitted Wb dt s (j + 1)).length + 2 * Wb + 2 ≤ cap) :
    Runs cap (vStep UF RF) σ (vStepCost Wb) (fun τ => VS UF RF Wb dt s (j + 1) out0 L0 σ0 τ ∧
      τ.val (RF 10) = σ.val (RF 10) ∧ τ.val (RF 11) = σ.val (RF 11)) := by
  have hj2 : 2 ^ j < 2 ^ Wb := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hl := BinW.lt_spec cap Wb (ufN (by decide)) (rfN (by decide)) σ s (2 ^ j) h.S h.P h.f h.r hs hj2 hcap
  refine Runs.seqE hl ?_
  set σ1 := σ.setv (RF 0) (decide (s < 2 ^ j)).toNat with hσ1
  -- the conditional emission
  have hcond : Runs cap (.ifr (RF 0) (.seq (WMX.dec (RF 0)) (.seq (BinW.copy (UF 6) (UF 4) (RF 0) (RF 1))
      (.seq (BinW.add (UF 6) (UF 5) (RF 0) (RF 1)) (.seq (BinW.add (UF 6) (UF 9) (RF 0) (RF 1))
        (appendRecX (UF 6) (UF 1) (RF 4) (RF 5)))))) WMX.skip) σ1
      (1 + 1 + ((41 * Wb + 3) + 1 + ((41 * Wb + 3) + 1 + ((41 * Wb + 3) + 1 + (40 * Wb + 11)))) + 1)
      (fun τ => (∃ e, NumOn τ (UF 6) Wb e) ∧ NumOn τ (UF 4) Wb s ∧ NumOn τ (UF 5) Wb (2 ^ j) ∧
        NumOn τ (UF 7) Wb 1 ∧ NumOn τ (UF 9) Wb dt ∧ τ.val (RF 0) = 0 ∧ τ.val (RF 1) = 0 ∧ τ.val (RF 4) = 0 ∧
        OutOn τ (UF 1) (RF 5) (out0 ++ emitted Wb dt s (j + 1)) L0 ∧
        SameExcept σ τ [UF 1, UF 6] [RF 0, RF 5] ) := by
    refine Runs.ifr (fun hne => ?_) (fun h0 => ?_)
    · have hlt : s < 2 ^ j := by by_contra hc; simp [hσ1, hc] at hne
      have hd := WXExec.dec cap (RF 0) σ1 (by simp [hσ1, hlt]; omega)
      have e1 : σ1.setv (RF 0) (σ1.val (RF 0) - 1) = σ := by
        rw [hσ1, wsetv_setv]; simp [hlt]; rw [← h.f]; exact wsetv_same σ (RF 0)
      rw [e1] at hd
      refine Runs.seqE hd ?_
      obtain ⟨e0, he0⟩ := h.E
      have c1 := BinW.copy_spec cap Wb (ufN (by decide)) (rfN (by decide)) σ e0 s he0 h.S h.f h.r hcap
      set τ1 := σ.sets (UF 6) (frame (binary Wb s)) with hτ1
      have nE1 : NumOn τ1 (UF 6) Wb s := numOn_sets_self σ _ Wb s he0.2
      have nP1 : NumOn τ1 (UF 5) Wb (2 ^ j) := numOn_sets_ne h.P (ufN (by decide)) _
      have nD1 : NumOn τ1 (UF 9) Wb dt := numOn_sets_ne h.dtn (ufN (by decide)) _
      have a1 := BinW.add_spec cap Wb (ufN (by decide)) (rfN (by decide)) τ1 s (2 ^ j) nE1 nP1 h.f h.r (by omega) hcap
      set τ2 := τ1.sets (UF 6) (frame (binary Wb (s + 2 ^ j))) with hτ2
      have nE2 : NumOn τ2 (UF 6) Wb (s + 2 ^ j) := numOn_sets_self τ1 _ Wb _ nE1.2
      have nD2 : NumOn τ2 (UF 9) Wb dt := numOn_sets_ne nD1 (ufN (by decide)) _
      have a2 := BinW.add_spec cap Wb (ufN (by decide)) (rfN (by decide)) τ2 _ dt nE2 nD2 h.f h.r hsum hcap
      set τ3 := τ2.sets (UF 6) (frame (binary Wb (s + 2 ^ j + dt))) with hτ3
      have hO3 : OutOn τ3 (UF 1) (RF 5) (out0 ++ emitted Wb dt s j) L0 :=
        ⟨by simp [hτ3, hτ2, hτ1, Function.update_of_ne (ufN (by decide : (1 : Fin 12) ≠ 6)), h.out.1],
          by simpa [hτ3, hτ2, hτ1] using h.out.2.1, by simpa [hτ3, hτ2, hτ1] using h.out.2.2⟩
      have ap := appendRec_spec cap (ufN (by decide : (6 : Fin 12) ≠ 1)) (rfN (by decide : (4 : Fin 14) ≠ 5)) τ3 (binary Wb (s + 2 ^ j + dt)) []
        (out0 ++ emitted Wb dt s j) L0 (by simp [hτ3, BinW.frame_frameP]) (by simp [hτ3, hτ2, hτ1, he0.2])
        (by simp [hτ3, hτ2, hτ1, h.cs]) hO3 (by
          have := hcapO
          rw [emitted_succ, if_pos (Nat.size_le.mpr hlt)] at this
          simp [frame_length] at this ⊢; omega)
      rw [binary_length] at ap
      refine ⟨_, WXExec.seq c1 (WXExec.seq a1 (WXExec.seq a2 (WXExec.wm ap))), ?_⟩
      have hem : out0 ++ emitted Wb dt s (j + 1) = out0 ++ emitted Wb dt s j ++ frame (binary Wb (s + 2 ^ j + dt)) := by
        rw [emitted_succ, if_pos (Nat.size_le.mpr hlt), List.append_assoc]
      refine ⟨⟨s + 2 ^ j + dt, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact ⟨by simp [hτ3, Function.update_of_ne (ufN (by decide : (6 : Fin 12) ≠ 1))],
          by simp [hτ3, hτ2, hτ1, Function.update_of_ne (ufN (by decide : (6 : Fin 12) ≠ 1)), he0.2]⟩
      · exact ⟨by simp [hτ3, hτ2, hτ1, Function.update_of_ne (ufN (by decide : (4 : Fin 12) ≠ 1)),
            Function.update_of_ne (ufN (by decide : (4 : Fin 12) ≠ 6)), h.S.1],
          by simp [hτ3, hτ2, hτ1, Function.update_of_ne (ufN (by decide : (4 : Fin 12) ≠ 1)), h.S.2]⟩
      · exact ⟨by simp [hτ3, hτ2, hτ1, Function.update_of_ne (ufN (by decide : (5 : Fin 12) ≠ 1)),
            Function.update_of_ne (ufN (by decide : (5 : Fin 12) ≠ 6)), h.P.1],
          by simp [hτ3, hτ2, hτ1, Function.update_of_ne (ufN (by decide : (5 : Fin 12) ≠ 1)), h.P.2]⟩
      · exact ⟨by simp [hτ3, hτ2, hτ1, Function.update_of_ne (ufN (by decide : (7 : Fin 12) ≠ 1)),
            Function.update_of_ne (ufN (by decide : (7 : Fin 12) ≠ 6)), h.one.1],
          by simp [hτ3, hτ2, hτ1, Function.update_of_ne (ufN (by decide : (7 : Fin 12) ≠ 1)), h.one.2]⟩
      · exact ⟨by simp [hτ3, hτ2, hτ1, Function.update_of_ne (ufN (by decide : (9 : Fin 12) ≠ 1)),
            Function.update_of_ne (ufN (by decide : (9 : Fin 12) ≠ 6)), h.dtn.1],
          by simp [hτ3, hτ2, hτ1, Function.update_of_ne (ufN (by decide : (9 : Fin 12) ≠ 1)), h.dtn.2]⟩
      · simp [hτ3, hτ2, hτ1, Function.update_of_ne (rfN (by decide : (0 : Fin 14) ≠ 5)), h.f]
      · simp [hτ3, hτ2, hτ1, Function.update_of_ne (rfN (by decide : (1 : Fin 14) ≠ 5)), h.r]
      · simp [hτ3, hτ2, hτ1, Function.update_of_ne (rfN (by decide : (4 : Fin 14) ≠ 5)), h.cs]
      · rw [hem]; exact appendRec_out τ3 (UF 1) (RF 5) _ L0 _
      · refine ⟨fun x hx => ?_, fun r hr => ?_, rfl⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
          simp [hτ3, hτ2, hτ1, Function.update_of_ne hx.1, Function.update_of_ne hx.2]
        · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          simp [hτ3, hτ2, hτ1, Function.update_of_ne hr.2]
    · have hge : ¬ s < 2 ^ j := by intro hc; simp [hσ1, hc] at h0
      have e1 : σ1 = σ := by rw [hσ1]; simp [hge]; rw [← h.f]; exact wsetv_same σ (RF 0)
      rw [e1]
      refine (Runs.of (WXExec.skip cap σ) ⟨h.E, h.S, h.P, h.one, h.dtn, h.f, h.r, h.cs, ?_, SameExcept.refl σ _ _⟩).cost
        (by omega)
      rw [emitted_succ, if_neg (fun hc => hge (Nat.size_le.mp hc)), List.append_nil]
      exact h.out
  refine Runs.seq hcond (fun τ ⟨hE', hS', hP', h1', hD', hf', hr', hcs', hO', hfr'⟩ => ?_)
  obtain ⟨e', he'⟩ := hE'
  have hsh := BinW.shl_spec cap Wb (ufN (by decide)) (rfN (by decide)) τ _ 1 hP' h1' hf' hr' hcap
  rw [← NearCubicWires.WireExponent3_5.UnionMachine.Round.binary_mod] at hsh
  have hpow : 2 * 2 ^ j % 2 ^ Wb = 2 ^ (j + 1) := by
    rw [← pow_succ']; exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))
  rw [hpow] at hsh
  refine ⟨_, hsh, ⟨numOn_sets_ne hS' (ufN (by decide)) _, numOn_sets_self τ _ Wb _ hP'.2, ⟨e', numOn_sets_ne he' (ufN (by decide)) _⟩,
    numOn_sets_ne h1' (ufN (by decide)) _, numOn_sets_ne hD' (ufN (by decide)) _, by simpa using hf', by simpa using hr',
    by simpa using hcs', ⟨by simp [Function.update_of_ne (ufN (by decide : (1 : Fin 12) ≠ 5)), hO'.1],
      by simpa using hO'.2.1, by simpa using hO'.2.2⟩, ?_⟩, ?_, ?_⟩
  · have f1 : SameExcept σ τ [UF 1, UF 4, UF 5, UF 6] [RF 0, RF 1, RF 4, RF 5, RF 10, RF 11] :=
      hfr'.weaken (fun x hx => by simp at hx ⊢; tauto) (fun r hr => by simp at hr ⊢; tauto)
    have f0 : SameExcept σ σ1 [UF 1, UF 4, UF 5, UF 6] [RF 0, RF 1, RF 4, RF 5, RF 10, RF 11] :=
      sameExcept_setv σ (by simp) _
    exact SameExcept.trans (SameExcept.trans h.fr f1) (sameExcept_sets τ (by simp) _)
  · simp only [WState.sets_val]
    have := hfr'.val (r := RF 10) (by simp [rfN]); rw [this]
  · simp only [WState.sets_val]
    have := hfr'.val (r := RF 11) (by simp [rfN]); rw [this]

def famBodyCost (Wb V : ℕ) : ℕ :=
  (41 * Wb + 3) + 1 + ((41 * Wb + 3) + 1 + ((41 * Wb + 3) + 1 + (V * (vStepCost Wb + 8) + 7 * V + 3)))

theorem and_mask_pk (s d V : ℕ) (hs : s < 2 ^ V) : (s + d * 2 ^ V) &&& (2 ^ V - 1) = s := by
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs]

/-- **One record of a level**: from WK holding `s + d·T` (`s < T = 2^V`, the constants in place, NXT open with
`out0`), the body appends the children of `s` (`emitted … s V`) to NXT; WK, CUR and the loop registers untouched. -/
theorem famBody_spec (cap Wb V d dt s : ℕ) (out0 L0 : List Bool) (σ : WState ns nr)
    (hWK : NumOn σ (UF 3) Wb (s + d * 2 ^ V)) (hS : ∃ x, NumOn σ (UF 4) Wb x) (hP : ∃ x, NumOn σ (UF 5) Wb x)
    (hE : ∃ x, NumOn σ (UF 6) Wb x) (h1 : NumOn σ (UF 7) Wb 1) (hDT : NumOn σ (UF 9) Wb dt)
    (hM : NumOn σ (UF 10) Wb (2 ^ V - 1)) (hf : σ.val (RF 0) = 0) (hr : σ.val (RF 1) = 0)
    (hcs : σ.val (RF 4) = 0) (hRV : σ.val (RF 10) = V) (hRV2 : σ.val (RF 11) = 0)
    (hO : OutOn σ (UF 1) (RF 5) out0 L0) (hs : s < 2 ^ V) (hVW : V + 1 < Wb) (hsum : 2 ^ (V + 1) + dt < 2 ^ Wb)
    (hcap : 2 * Wb + 1 ≤ cap) (hcapV : 2 * V ≤ cap)
    (hcapO : (out0 ++ emitted Wb dt s V).length + 2 * Wb + 2 ≤ cap) :
    Runs cap (famBody UF RF) σ (famBodyCost Wb V) (fun τ => VS UF RF Wb dt s V out0 L0 σ τ ∧
      τ.val (RF 10) = V ∧ τ.val (RF 11) = 0) := by
  obtain ⟨x4, h4⟩ := hS
  obtain ⟨x5, h5⟩ := hP
  have hTW : 2 ^ V < 2 ^ Wb := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have c1 := BinW.copy_spec cap Wb (ufN (by decide : (4 : Fin 12) ≠ 3)) (rfN (by decide : (0 : Fin 14) ≠ 1)) σ x4 _ h4 hWK hf hr hcap
  set τ1 := σ.sets (UF 4) (frame (binary Wb (s + d * 2 ^ V))) with hτ1
  have n4 : NumOn τ1 (UF 4) Wb (s + d * 2 ^ V) := numOn_sets_self σ _ Wb _ h4.2
  have nM : NumOn τ1 (UF 10) Wb (2 ^ V - 1) := numOn_sets_ne hM (ufN (by decide : (10 : Fin 12) ≠ 4)) _
  have a1 := WXExec.wm (andW_spec cap Wb (ufN (by decide : (4 : Fin 12) ≠ 10)) (rfN (by decide : (0 : Fin 14) ≠ 1)) τ1 _ _ n4 nM
    (by simpa [hτ1] using hf) (by simpa [hτ1] using hr) hcap)
  rw [and_mask_pk s d V hs] at a1
  set τ2 := τ1.sets (UF 4) (frame (binary Wb s)) with hτ2
  have n5 : NumOn τ2 (UF 5) Wb x5 :=
    numOn_sets_ne (numOn_sets_ne h5 (ufN (by decide : (5 : Fin 12) ≠ 4)) _) (ufN (by decide : (5 : Fin 12) ≠ 4)) _
  have n1 : NumOn τ2 (UF 7) Wb 1 :=
    numOn_sets_ne (numOn_sets_ne h1 (ufN (by decide : (7 : Fin 12) ≠ 4)) _) (ufN (by decide : (7 : Fin 12) ≠ 4)) _
  have c2 := BinW.copy_spec cap Wb (ufN (by decide : (5 : Fin 12) ≠ 7)) (rfN (by decide : (0 : Fin 14) ≠ 1)) τ2 x5 1 n5 n1
    (by simpa [hτ2, hτ1] using hf) (by simpa [hτ2, hτ1] using hr) hcap
  set τ3 := τ2.sets (UF 5) (frame (binary Wb 1)) with hτ3
  have hVS0 : VS UF RF Wb dt s 0 out0 L0 σ τ3 := by
    obtain ⟨e, he⟩ := hE
    have hfr0 : SameExcept σ τ3 [UF 4, UF 5] [] :=
      SameExcept.trans (SameExcept.trans (sameExcept_sets σ (by simp) _) (sameExcept_sets _ (by simp) _))
        (sameExcept_sets _ (by simp) _)
    have hfr : SameExcept σ τ3 [UF 1, UF 4, UF 5, UF 6] [RF 0, RF 1, RF 4, RF 5, RF 10, RF 11] :=
      hfr0.weaken (fun x hx => by simp at hx ⊢; tauto) (fun r hr => by simp at hr)
    have n6 : UF 6 ∉ [UF 4, UF 5] := by simp [ufN (by decide : (6 : Fin 12) ≠ 4), ufN (by decide : (6 : Fin 12) ≠ 5)]
    have n7 : UF 7 ∉ [UF 4, UF 5] := by simp [ufN (by decide : (7 : Fin 12) ≠ 4), ufN (by decide : (7 : Fin 12) ≠ 5)]
    have n9 : UF 9 ∉ [UF 4, UF 5] := by simp [ufN (by decide : (9 : Fin 12) ≠ 4), ufN (by decide : (9 : Fin 12) ≠ 5)]
    have n1' : UF 1 ∉ [UF 4, UF 5] := by simp [ufN (by decide : (1 : Fin 12) ≠ 4), ufN (by decide : (1 : Fin 12) ≠ 5)]
    refine ⟨numOn_sets_ne (numOn_sets_self τ1 _ Wb s n4.2) (ufN (by decide : (4 : Fin 12) ≠ 5)) _, ?_,
      ⟨e, hfr0.numOn n6 he⟩, hfr0.numOn n7 h1, hfr0.numOn n9 hDT, by rw [hfr0.val (by simp)]; exact hf,
      by rw [hfr0.val (by simp)]; exact hr, by rw [hfr0.val (by simp)]; exact hcs, ?_, hfr⟩
    · simpa using numOn_sets_self τ2 _ Wb 1 n5.2
    · have he0 : emitted Wb dt s 0 = [] := by simp [emitted]
      rw [he0, List.append_nil]
      exact ⟨by rw [hfr0.st n1']; exact hO.1, by rw [hfr0.sh n1']; exact hO.2.1,
        by rw [hfr0.val (by simp)]; exact hO.2.2⟩
  have hrep := Runs.rep (cap := cap) (K := RF 10) (K2 := RF 11) (body := vStep UF RF) (rfN (by decide))
    (vStepCost Wb) V (fun j τ => VS UF RF Wb dt s j out0 L0 σ τ) hcapV
    (fun j τ v hτ => hτ.setv 10 (Or.inl rfl) v) (fun j τ v hτ => hτ.setv 11 (Or.inr rfl) v)
    (fun j hj τ hτ => vStep_spec cap Wb dt s j out0 L0 σ τ hτ (by omega) (lt_trans hs hTW)
      (by
        have : s + 2 ^ j < 2 ^ (V + 1) := by
          have h2 : 2 ^ j < 2 ^ V := Nat.pow_lt_pow_right (by norm_num) hj
          rw [pow_succ]; omega
        omega)
      hcap (by
        refine le_trans ?_ hcapO
        have : (emitted Wb dt s (j + 1)).length ≤ (emitted Wb dt s V).length := by
          unfold emitted
          simp only [List.length_flatMap, List.map_map]
          have hsub : List.Sublist ((List.range (j + 1)).filter (fun v => Nat.size s ≤ v))
              ((List.range V).filter (fun v => Nat.size s ≤ v)) := by
            apply List.Sublist.filter
            exact (List.range_sublist).mpr (by omega)
          exact List.Sublist.sum_le_sum (hsub.map _) (fun _ _ => Nat.zero_le _)
        simp only [List.length_append]; omega))
    τ3 hVS0 (by simp [hτ3, hτ2, hτ1, hRV]) (by simp [hτ3, hτ2, hτ1, hRV2])
  exact Runs.seqE c1 (Runs.seqE a1 (Runs.seqE c2 (hrep.cost (by omega))))

end BodySpec

/-! ## One level -/

/-- The records of level `d`: `s + d·2^V` for the sets `s` of size `d`. -/
def lvlRecs (V d : ℕ) : List ℕ := (level V d).map fun s => s + d * 2 ^ V

theorem emitted_level (Wb V d : ℕ) :
    (level V d).flatMap (fun s => emitted Wb ((d + 1) * 2 ^ V) s V) =
      (lvlRecs V (d + 1)).flatMap fun x => frame (binary Wb x) := by
  unfold emitted lvlRecs
  rw [show level V (d + 1) = (level V d).flatMap fun s =>
    ((List.range V).filter fun v => Nat.size s ≤ v).map fun v => s + 2 ^ v from rfl]
  rw [List.map_flatMap, List.flatMap_assoc]
  congr 1
  funext s
  rw [List.map_map]
  rfl

section Level
variable (UF : Fin 12 ↪ Fin (ns + 1)) (RF : Fin 14 ↪ Fin nr)

/-- One level step: `DT := DT + T`; the children of every CUR record into NXT; NXT appended to FAM and copied to
CUR. -/
def famLevel : WMX ns nr :=
  .seq (.seq (BinW.add (UF 9) (UF 8) (RF 0) (RF 1)) (recLoop (UF 0) (UF 3) (RF 2) (RF 3) (famBody UF RF)))
    (.seq (closeOutX (UF 1) (RF 5))
      (.seq (copyAll (UF 1) (UF 3) (UF 2) (RF 12) (RF 13) (RF 4) (RF 6))
        (.seq (copyAll (UF 1) (UF 3) (UF 0) (RF 12) (RF 13) (RF 4) (RF 7)) (closeOutX (UF 0) (RF 7)))))

/-- All records of levels `0 … j`, framed. -/
def famUpTo (Wb V j : ℕ) : List Bool := ((List.range (j + 1)).flatMap (lvlRecs V)).flatMap fun x => frame (binary Wb x)

theorem famUpTo_succ (Wb V j : ℕ) :
    famUpTo Wb V (j + 1) = famUpTo Wb V j ++ (lvlRecs V (j + 1)).flatMap fun x => frame (binary Wb x) := by
  unfold famUpTo
  rw [List.range_succ, List.flatMap_append, List.flatMap_append]
  simp

/-- The family phase between two levels. -/
structure FLS (Wb V j : ℕ) (outF L0F : List Bool) (σ0 σ : WState ns nr) : Prop where
  cur : ∃ junk, σ.st (UF 0) = recStream ((lvlRecs V j).map (binary Wb)) ++ junk
  curh : σ.sh (UF 0) = 0
  nxth : σ.sh (UF 1) = 0
  fam : OutOn σ (UF 2) (RF 6) (outF ++ famUpTo Wb V j) L0F
  wkh : σ.sh (UF 3) = 0
  wkl : (σ.st (UF 3)).length ≤ 2 * Wb + 1
  S : ∃ x, NumOn σ (UF 4) Wb x
  P : ∃ x, NumOn σ (UF 5) Wb x
  E : ∃ x, NumOn σ (UF 6) Wb x
  one : NumOn σ (UF 7) Wb 1
  T : NumOn σ (UF 8) Wb (2 ^ V)
  dtn : NumOn σ (UF 9) Wb (j * 2 ^ V)
  mask : NumOn σ (UF 10) Wb (2 ^ V - 1)
  regs : ∀ k : Fin 14, k ∈ ([0, 1, 2, 3, 4, 5, 7, 11, 12, 13] : List (Fin 14)) → σ.val (RF k) = 0
  rv : σ.val (RF 10) = V
  fr : SameExcept σ0 σ [UF 0, UF 1, UF 2, UF 3, UF 4, UF 5, UF 6, UF 9]
    [RF 0, RF 1, RF 2, RF 3, RF 4, RF 5, RF 6, RF 7, RF 10, RF 11, RF 12, RF 13]

end Level

end NearCubicGates.Close.Expand
