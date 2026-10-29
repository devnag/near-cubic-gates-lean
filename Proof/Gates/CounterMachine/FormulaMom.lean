import Proof.Gates.CounterMachine.FormulaAmp

/-! # RG machine, part 18: the moment formulas (table (b))

**`momDP_spec`**: `(E_j^r(y,x) − E_j^r(y,0^I))^{2k}` (digit moments, table (b) of `sec:algorithm`) and **`momPP_spec`**:
`(Φ^r(y,x) − Φ^r(y,0^I))^{2k}` with `Φ = M₁ K_J − A X` (defined there), each form printed on the variables from `0` (gates at
`(y,x)`) and from `G_r` (gates at `(y,0^I)`). The constants `M₁`, `A` follow the rates on the rate stream (`L[J−1]`,
`L[J]`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.CounterMachine

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Codec
open NearCubicGates.Close.Interfaces.Formats (Tok tokWord toks)

variable {ns nr : ℕ} (cap : ℕ)

section Mom
variable (Y : Fin 8 ↪ Fin (ns + 1)) (X : Fin 24 ↪ Fin nr) (F : Fin 24 ↪ Fin nr)

/-- The data of role `r`: gate count, stage lists, top coefficients, and its stream/register indices. -/
def FData.Gr (d : FData) (r : ℕ) : ℕ := if r = 0 then d.G0 else d.G1
def FData.Br (d : FData) (r : ℕ) : List (List ℤ) := if r = 0 then d.B0 else d.B1
def FData.Cr (d : FData) (r : ℕ) : List ℤ := if r = 0 then d.C0 else d.C1

/-- The digit-moment tokens of role `r`. -/
def mdToks (d : FData) (r j : ℕ) : List Tok :=
  digToks 0 (fun s => (d.Br r).getD s []) (fun i => (d.L.getD i 0 : ℤ)) j ++
    digToks (d.Gr r) (fun s => (d.Br r).getD s []) (fun i => (d.L.getD i 0 : ℤ)) j ++ [Tok.sub, Tok.pow (2 * d.k)]

/-- The tokens of `Φ^r` on the variables from `o`. -/
def phToks (d : FData) (r o : ℕ) : List Tok :=
  [Tok.const (d.L.getD (d.J - 1) 0 : ℤ)] ++ linToks o ((d.Br r).getD (d.J - 1) []) ++
    [Tok.mul, Tok.const (d.L.getD d.J 0 : ℤ)] ++ linToks o (d.Cr r) ++ [Tok.mul, Tok.sub]

/-- The `Φ`-moment tokens of role `r`. -/
def mpToks (d : FData) (r : ℕ) : List Tok := phToks d r 0 ++ phToks d r (d.Gr r) ++ [Tok.sub, Tok.pow (2 * d.k)]

/-- The registers of role `r`: gate count, stage-list bound, top-coefficient bound; streams. -/
def rG (r : ℕ) : Fin 24 := if r = 0 then 14 else 18
def rLB (r : ℕ) : Fin 24 := if r = 0 then 16 else 20
def rLS (r : ℕ) : Fin 24 := if r = 0 then 17 else 21
def rCW (r : ℕ) : Fin 8 := if r = 0 then 1 else 3
def rSC (r : ℕ) : Fin 8 := if r = 0 then 2 else 4

/-- The digit-moment printer of role `r` (`j` in `X 10`). -/
def momDP (r : ℕ) : WM ns nr :=
  .seq (copyR (X 10) (X 2) (F 8))
  (.seq (digP (Y 0) F (Y (rCW r)) (Y 5) (X (rG r)) (X 15) (X (rLB r)) (X 6) (X 2) (X 3))
  (.seq (digP (Y 0) F (Y (rCW r)) (Y 5) (X (rG r)) (X (rG r)) (X (rLB r)) (X 6) (X 2) (X 3))
  (.seq (WM.clear (X 2)) (.seq (litC (Y 0) F .sub) (powC (Y 0) F (X 22))))))

/-- What the formula state says about role `r`. -/
structure RoleFacts (σ : WState ns nr) (d : FData) (r : ℕ) {Λ0 : ℕ} : Prop where
  stB : ∃ rest, σ.st (Y (rCW r)) = encI (d.Br r).flatten ++ rest
  shB : σ.sh (Y (rCW r)) = 0
  stC : ∃ rest, σ.st (Y (rSC r)) = encI (d.Cr r) ++ rest
  shC : σ.sh (Y (rSC r)) = 0
  vG : σ.val (X (rG r)) = d.Gr r
  vL : (encI (d.Br r).flatten).length ≤ σ.val (X (rLB r))
  vS : (encI (d.Cr r)).length ≤ σ.val (X (rLS r))
  bB : ∀ b ∈ d.Br r, b.length = d.Gr r
  bC : (d.Cr r).length = d.Gr r
  lB : (d.Br r).length = d.J
  zB : ∀ b ∈ d.Br r, ∀ z ∈ b, natBitLength z.natAbs ≤ Λ0
  zC : ∀ z ∈ d.Cr r, natBitLength z.natAbs ≤ Λ0
  rLB : σ.val (X (rLB r)) ≤ Λ0
  rLS : σ.val (X (rLS r)) ≤ Λ0

theorem roleFacts_of {σ : WState ns nr} {d : FData} {Λ : ℕ} (hs : FState Y X F σ d) (hb : FBound d Λ)
    (hr : FBoundR X σ Λ) (r : ℕ) (hr2 : r < 2) : RoleFacts Y X σ d r (Λ0 := Λ) := by
  rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
  · exact ⟨hs.stB0, hs.sh 1 (by decide), hs.stC0, hs.sh 2 (by decide), hs.vG0, hs.vL0, hs.vS0, hb.b0, hb.c0, hb.lB0,
      fun b hb' z hz => hb.zB b (List.mem_append_left _ hb') z hz, fun z hz => hb.zC z (List.mem_append_left _ hz),
      hr 16 (by decide), hr 17 (by decide)⟩
  · exact ⟨hs.stB1, hs.sh 3 (by decide), hs.stC1, hs.sh 4 (by decide), hs.vG1, hs.vL1, hs.vS1, hb.b1, hb.c1, hb.lB1,
      fun b hb' z hz => hb.zB b (List.mem_append_right _ hb') z hz, fun z hz => hb.zC z (List.mem_append_right _ hz),
      hr 20 (by decide), hr 21 (by decide)⟩

theorem rG_ne (r : ℕ) : rG r ∉ ([2, 3, 6, 10, 15, 22] : List (Fin 24)) := by unfold rG; split <;> decide
theorem rLB_ne (r : ℕ) : rLB r ∉ ([2, 3, 6, 10, 15, 22] : List (Fin 24)) := by unfold rLB; split <;> decide
theorem rLS_ne (r : ℕ) : rLS r ∉ ([2, 3, 6, 10, 15, 22] : List (Fin 24)) := by unfold rLS; split <;> decide
theorem rCW_ne (r : ℕ) : rCW r ≠ 0 ∧ rCW r ≠ 5 ∧ rCW r ≠ 6 := by unfold rCW; split <;> decide
theorem rSC_ne (r : ℕ) : rSC r ≠ 0 ∧ rSC r ≠ 5 ∧ rSC r ≠ 6 := by unfold rSC; split <;> decide

theorem momDP_spec (d : FData) (Λ : ℕ) (σ : WState ns nr) (hs : FState Y X F σ d) (hb : FBound d Λ)
    (hr : FBoundR X σ Λ) (r j : ℕ) (hr2 : r < 2) (hj : j < d.J) (h10 : σ.val (X 10) = j)
    (h2G : 2 * d.Gr r ≤ Λ) (hcap : TCap cap F σ (mdToks d r j) Λ) :
    WExec cap (momDP Y X F r) σ (emitT (Y 0) F σ (mdToks d r j)) (25000 * (Λ + 1) ^ 3) := by
  have hFX := hs.disj
  have hXX : ∀ {a b : Fin 24}, a ≠ b → X a ≠ X b := fun h => X.injective.ne h
  have hY : ∀ {a b : Fin 8}, a ≠ b → Y a ≠ Y b := fun h => Y.injective.ne h
  have rf := roleFacts_of Y X F hs hb hr r hr2
  obtain ⟨rB, hB⟩ := rf.stB
  obtain ⟨rL, hLs⟩ := hs.stL
  have nG := rG_ne r
  have nL := rLB_ne r
  have nC := rCW_ne r
  have hne : ∀ (a : Fin 24) (l : List (Fin 24)), a ∉ l → ∀ b ∈ l, X a ≠ X b := fun a l h b hb e =>
    h (X.injective e ▸ hb)
  have nG2 : rG r ≠ 2 := fun e => nG (by simp [e])
  have nL2 : rLB r ≠ 2 := fun e => nL (by simp [e])
  unfold mdToks at hcap ⊢
  set Da := digToks 0 (fun s => (d.Br r).getD s []) (fun i => (d.L.getD i 0 : ℤ)) j
  set Db := digToks (d.Gr r) (fun s => (d.Br r).getD s []) (fun i => (d.L.getD i 0 : ℤ)) j
  have split : Da ++ Db ++ [Tok.sub, Tok.pow (2 * d.k)] = Da ++ (Db ++ ([Tok.sub] ++ [Tok.pow (2 * d.k)])) := by simp
  rw [split] at hcap ⊢
  have c1 := TCap.left cap F hcap
  have r1 := TCap.right cap (Y 0) F hcap
  have c2 := TCap.left cap F r1
  have r2 := TCap.right cap (Y 0) F r1
  have c3 := TCap.left cap F r2
  have c4 := TCap.right cap (Y 0) F r2
  -- X 2 := j
  have s1 := copyR_spec cap (v := X 10) (d := X 2) (t := F 8) (hXX (by decide)) (hFX 8 10).symm (hFX 8 2).symm σ
    (hs.rest.zero (Y 0) F 8 (by decide)) (by rw [hs.zero 2 (by decide), h10]; unfold TCap at hcap; have := hb.J; omega)
  rw [hs.zero 2 (by decide), h10, Nat.zero_add] at s1
  set σ1 := σ.setv (X 2) j with hσ1
  have v1 : ∀ i : Fin 24, i ≠ 2 → σ1.val (X i) = σ.val (X i) := fun i hi => by
    simp [hσ1, Function.update_of_ne (hXX hi)]
  have hR1 : TRest (Y 0) F σ1 := hs.rest.setv (Y 0) F (X 2) (fun i => hFX i 2) j
  have hSC : Y 0 ≠ Y (rCW r) := hY (Ne.symm nC.1)
  have hFS : Y 5 ≠ Y 0 := hY (by decide)
  have g3 : X (rG r) ≠ X 3 := hne _ _ nG 3 (by decide)
  have l3 : X (rLB r) ≠ X 3 := hne _ _ nL 3 (by decide)
  have hjL : j ≤ d.L.length := by have := hb.lL; omega
  have hlb : (encI ((d.Br r).take (j + 1)).flatten).length ≤ σ.val (X (rLB r)) :=
    le_trans (encI_take_mono (d.Br r) (show j + 1 ≤ (d.Br r).length by rw [rf.lB]; omega))
      (by rw [List.take_of_length_le le_rfl]; exact rf.vL)
  have hlbf : (encN (d.L.take j)).length ≤ σ.val (X 6) := le_trans (encN_take_le _ _) hs.vLF
  have s2 := digP_run cap (Y 0) F (Y (rCW r)) (Y 5) hSC hFS (X (rG r)) (X 15) (X (rLB r)) (X 6) (X 2) (X 3)
    (fun i => hFX i _) (fun i => hFX i _) (fun i => hFX i _) (fun i => hFX i _) (fun i => hFX i _) (fun i => hFX i _)
    (hXX (by decide)) (hXX (by decide)) g3 (hXX (by decide)) l3 (d.Gr r) j 0 (σ.val (X (rLB r))) (σ.val (X 6)) Λ
    (d.Br r) d.L rf.bB (by rw [rf.lB]; exact hj) hjL rB rL σ1 hR1 (by rw [hσ1]; exact hB)
    (by rw [hσ1]; exact rf.shB) (by rw [hσ1]; exact hLs) (by rw [hσ1]; exact hs.sh 5 (by decide))
    (by rw [v1 _ nG2]; exact rf.vG) (by rw [v1 _ (by decide)]; exact hs.vo0)
    (v1 _ nL2) (v1 _ (by decide)) (by simp [hσ1])
    (by rw [v1 _ (by decide)]; exact hs.zero 3 (by decide)) hlb hlbf (by have := hb.J; omega) (by omega)
    rf.rLB (hr 6 (by decide)) rf.zB hb.zL (c1.setv cap F (X 2) (fun i => hFX i 2) j)
  set σ2 := emitT (Y 0) F σ1 Da with hσ2
  have v2 : ∀ i, σ2.val (X i) = σ1.val (X i) := fun i => emitT_val_ne (Y 0) F _ (hFX 7 i).symm (hFX 16 i).symm σ1 Da
  have s3 := digP_run cap (Y 0) F (Y (rCW r)) (Y 5) hSC hFS (X (rG r)) (X (rG r)) (X (rLB r)) (X 6) (X 2) (X 3)
    (fun i => hFX i _) (fun i => hFX i _) (fun i => hFX i _) (fun i => hFX i _) (fun i => hFX i _) (fun i => hFX i _)
    (hXX (by decide)) (hXX (by decide)) g3 g3 l3 (d.Gr r) j (d.Gr r) (σ.val (X (rLB r))) (σ.val (X 6)) Λ
    (d.Br r) d.L rf.bB (by rw [rf.lB]; exact hj) hjL rB rL σ2 (hR1.emitT (Y 0) F Da)
    (by rw [hσ2, emitT_st_ne (Y 0) F _ hSC.symm, hσ1]; exact hB)
    (by rw [hσ2, emitT_sh_ne (Y 0) F _ hSC.symm, hσ1]; exact rf.shB)
    (by rw [hσ2, emitT_st_ne (Y 0) F _ hFS, hσ1]; exact hLs)
    (by rw [hσ2, emitT_sh_ne (Y 0) F _ hFS, hσ1]; exact hs.sh 5 (by decide))
    (by rw [v2, v1 _ nG2]; exact rf.vG)
    (by rw [v2, v1 _ nG2]; exact rf.vG)
    (by rw [v2, v1 _ nL2]) (by rw [v2, v1 _ (by decide)]) (by rw [v2]; simp [hσ1])
    (by rw [v2, v1 _ (by decide)]; exact hs.zero 3 (by decide)) hlb hlbf (by have := hb.J; omega) (by omega)
    rf.rLB (hr 6 (by decide)) rf.zB hb.zL
    (by have := c2.setv cap F (X 2) (fun i => hFX i 2) j
        rw [← emitT_setv (Y 0) F (X 2) (hFX 7 2).symm (hFX 16 2).symm] at this; exact this)
  set σ3 := emitT (Y 0) F σ2 Db with hσ3
  have hσ3' : σ3 = (emitT (Y 0) F σ (Da ++ Db)).setv (X 2) j := by
    rw [hσ3, hσ2, hσ1, emitT_setv (Y 0) F (X 2) (hFX 7 2).symm (hFX 16 2).symm,
      emitT_setv (Y 0) F (X 2) (hFX 7 2).symm (hFX 16 2).symm, emitT_append]
  have s4 := wclear_spec cap (X 2) j σ3 (by rw [hσ3']; simp) (by rw [hσ3']; simp; unfold TCap at hcap; have := hb.J; omega)
  have hσ4 : σ3.setv (X 2) 0 = emitT (Y 0) F σ (Da ++ Db) := by
    rw [hσ3', wsetv_setv]
    rw [show (0 : ℕ) = (emitT (Y 0) F σ (Da ++ Db)).val (X 2) by
      rw [emitT_val_ne (Y 0) F _ (hFX 7 2).symm (hFX 16 2).symm]; exact (hs.zero 2 (by decide)).symm, wsetv_same]
  rw [hσ4] at s4
  have hs4 := hs.emitT Y X F (Da ++ Db)
  have c3' : TCap cap F (emitT (Y 0) F σ (Da ++ Db)) [Tok.sub] Λ := by rw [← emitT_append]; exact c3
  have s5 := litC_spec cap (Y 0) F .sub _ hs4.rest (TCap.lit cap F c3').1 (TCap.lit cap F c3').2
  have hs5 := hs4.emitT Y X F [Tok.sub]
  have c4' : TCap cap F (emitT (Y 0) F (emitT (Y 0) F σ (Da ++ Db)) [Tok.sub]) [Tok.pow (2 * d.k)] Λ := by
    rw [← emitT_append]; exact c4
  have s6 := powC_spec cap (Y 0) F (X 22) (fun i => hFX i 22) _ hs5.rest
    (by rw [hs5.vK, show (natWord 6).length = 7 by decide]; unfold TCap at c4'; have := hb.k; omega)
    (TCap.lit cap F c4').2
  rw [hs5.vK] at s6
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 s6))))) ?_ ?_
  · rw [emitT_append, emitT_append]; simp [List.append_assoc]
  · have hp := printCost_le (2 * d.k) Λ hb.k
    have h2 : (Λ + 1) ^ 2 ≤ (Λ + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    rw [show (natWord 6).length = 7 by decide, tokWord_sub_length]
    have : 1 ≤ (Λ + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have hJ := hb.J
    have h3 : Λ + 1 ≤ (Λ + 1) ^ 3 := by
      have := Nat.pow_le_pow_right (show 1 ≤ Λ + 1 by omega) (show 1 ≤ 3 by omega); simpa using this
    omega

/-- `M₁ K_J` part of `Φ` (offset register `oR`). -/
def phiA (r : ℕ) (oR : Fin 24) : WM ns nr :=
  .seq (copyR (X 1) (X 2) (F 8)) (.seq (.dec (X 2)) (.seq (rateC (Y 0) F (Y 5) (X 6) (X 2))
    (.seq (stP (Y 0) (Y (rCW r)) F (X (rG r)) (X oR) (X (rLB r)) (X 2)) (WM.clear (X 2)))))

/-- `· A X − ·` part of `Φ`. -/
def phiB (r : ℕ) (oR : Fin 24) : WM ns nr :=
  .seq (litC (Y 0) F .mul) (.seq (rateC (Y 0) F (Y 5) (X 6) (X 1))
    (.seq (stP (Y 0) (Y (rSC r)) F (X (rG r)) (X oR) (X (rLS r)) (X 3)) (.seq (litC (Y 0) F .mul) (litC (Y 0) F .sub))))

theorem phiA_spec (d : FData) (Λ : ℕ) (σ : WState ns nr) (hs : FState Y X F σ d) (hb : FBound d Λ)
    (hr : FBoundR X σ Λ) (r : ℕ) (hr2 : r < 2) (oR : Fin 24) (hoR : oR ∉ ([1, 2, 3, 6] : List (Fin 24))) (o : ℕ)
    (hov : σ.val (X oR) = o) (hoG : o + d.Gr r ≤ Λ) (hJ1 : 1 ≤ d.J) (hLJ : d.J < d.L.length)
    (hcap : TCap cap F σ ([Tok.const (d.L.getD (d.J - 1) 0 : ℤ)] ++ linToks o ((d.Br r).getD (d.J - 1) [])) Λ) :
    WExec cap (phiA Y X F r oR) σ
      (emitT (Y 0) F σ ([Tok.const (d.L.getD (d.J - 1) 0 : ℤ)] ++ linToks o ((d.Br r).getD (d.J - 1) [])))
      (6000 * (Λ + 1) ^ 3) := by
  have hFX := hs.disj
  have hXX : ∀ {a b : Fin 24}, a ≠ b → X a ≠ X b := fun h => X.injective.ne h
  have hY : ∀ {a b : Fin 8}, a ≠ b → Y a ≠ Y b := fun h => Y.injective.ne h
  have rf := roleFacts_of Y X F hs hb hr r hr2
  obtain ⟨rB, hB⟩ := rf.stB
  obtain ⟨rL, hLs⟩ := hs.stL
  have nG := rG_ne r
  have nL := rLB_ne r
  have nC := rCW_ne r
  have nG2 : rG r ≠ 2 := fun e => nG (by simp [e])
  have nL2 : rLB r ≠ 2 := fun e => nL (by simp [e])
  have o2 : oR ≠ 2 := fun e => hoR (by simp [e])
  have hJΛ := hb.J
  have hJm1 : d.J - 1 < d.L.length := by omega
  have hgL : d.L.getD (d.J - 1) 0 = d.L[d.J - 1] := List.getD_eq_getElem _ _ hJm1
  have hJB : d.J - 1 < (d.Br r).length := by rw [rf.lB]; omega
  have hgB : (d.Br r).getD (d.J - 1) [] = (d.Br r)[d.J - 1] := List.getD_eq_getElem _ _ hJB
  rw [hgL, hgB] at hcap ⊢
  have c1 := TCap.left cap F hcap
  have c2 := TCap.right cap (Y 0) F hcap
  -- X 2 := J − 1
  have s1 := copyR_spec cap (v := X 1) (d := X 2) (t := F 8) (hXX (by decide)) (hFX 8 1).symm (hFX 8 2).symm σ
    (hs.rest.zero (Y 0) F 8 (by decide)) (by rw [hs.zero 2 (by decide), hs.vJ]; unfold TCap at hcap; omega)
  rw [hs.zero 2 (by decide), hs.vJ, Nat.zero_add] at s1
  have s2 := WExec.dec (cap := cap) (X 2) (σ.setv (X 2) d.J) (by simp; unfold TCap at hcap; omega)
  simp only [WState.setv_val, Function.update_self, wsetv_setv] at s2
  set τ := σ.setv (X 2) (d.J - 1) with hτ
  have vτ : ∀ i : Fin 24, i ≠ 2 → τ.val (X i) = σ.val (X i) := fun i hi => by
    simp [hτ, Function.update_of_ne (hXX hi)]
  have hRτ : TRest (Y 0) F τ := hs.rest.setv (Y 0) F (X 2) (fun i => hFX i 2) _
  have hFS : Y 5 ≠ Y 0 := hY (by decide)
  have s3 := rateC_spec cap (Y 0) F (Y 5) hFS (X 6) (X 2) (fun i => hFX i 6) (fun i => hFX i 2) (hXX (by decide))
    d.L rL (d.J - 1) (σ.val (X 6)) Λ hJm1 τ hRτ (by rw [hτ]; exact hLs) (by rw [hτ]; exact hs.sh 5 (by decide))
    (by simp [hτ]) (vτ 6 (by decide)) (le_trans (encN_take_le _ _) hs.vLF) (hr 6 (by decide)) (by omega) hb.zL
    (by rw [show τ.val (F 7) = σ.val (F 7) by simp [hτ, Function.update_of_ne (hFX 7 2)]]; unfold TCap at c1
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at c1
        rw [tokWord_const_nat] at c1; simp only [List.length_append] at c1 ⊢; omega)
    (by unfold TCap at hcap; have := hr 6 (by decide); omega)
    (fun x hx => by have := hb.zL x hx; unfold TCap at hcap; omega)
    (by rw [show τ.val (F 16) = σ.val (F 16) by simp [hτ, Function.update_of_ne (hFX 16 2)]]; unfold TCap at c1
        simp at c1; omega)
  set τ1 := emitT (Y 0) F τ [Tok.const (d.L[d.J - 1] : ℤ)] with hτ1
  have v1 : ∀ i : Fin 24, i ≠ 2 → τ1.val (X i) = σ.val (X i) := fun i hi => by
    rw [hτ1, emitT_val_ne (Y 0) F _ (hFX 7 i).symm (hFX 16 i).symm, vτ i hi]
  have hSC : Y 0 ≠ Y (rCW r) := hY (Ne.symm nC.1)
  have s4 := stP_run cap (Y 0) F (Y (rCW r)) hSC (X (rG r)) (X oR) (X (rLB r)) (X 2) (fun i => hFX i _)
    (fun i => hFX i _) (fun i => hFX i _) (fun i => hFX i _) (d.Gr r) (d.J - 1) o (σ.val (X (rLB r))) Λ (d.Br r)
    rf.bB hJB rB τ1 (hRτ.emitT (Y 0) F _) (by rw [hτ1, emitT_st_ne (Y 0) F _ hSC.symm, hτ]; exact hB)
    (by rw [hτ1, emitT_sh_ne (Y 0) F _ hSC.symm, hτ]; exact rf.shB) (by rw [v1 _ nG2]; exact rf.vG)
    (by rw [v1 _ o2]; exact hov) (v1 _ nL2)
    (by rw [hτ1, emitT_val_ne (Y 0) F _ (hFX 7 2).symm (hFX 16 2).symm]; simp [hτ])
    (le_trans (encI_take_mono (d.Br r) (show d.J - 1 + 1 ≤ (d.Br r).length by omega))
      (by rw [List.take_of_length_le le_rfl]; exact rf.vL))
    (by omega) hoG rf.rLB rf.zB (by
      have := c2.setv cap F (X 2) (fun i => hFX i 2) (d.J - 1)
      rw [← emitT_setv (Y 0) F (X 2) (hFX 7 2).symm (hFX 16 2).symm] at this; exact this)
  set τ2 := emitT (Y 0) F τ1 (linToks o (d.Br r)[d.J - 1]) with hτ2
  have s5 := wclear_spec cap (X 2) (d.J - 1) τ2
    (by rw [hτ2, hτ1, emitT_val_ne (Y 0) F _ (hFX 7 2).symm (hFX 16 2).symm,
          emitT_val_ne (Y 0) F _ (hFX 7 2).symm (hFX 16 2).symm]; simp [hτ])
    (by rw [hτ2, hτ1, emitT_val_ne (Y 0) F _ (hFX 7 2).symm (hFX 16 2).symm,
          emitT_val_ne (Y 0) F _ (hFX 7 2).symm (hFX 16 2).symm]; simp [hτ]; unfold TCap at hcap; omega)
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 s5)))) ?_ ?_
  · rw [hτ2, hτ1, hτ, emitT_setv (Y 0) F (X 2) (hFX 7 2).symm (hFX 16 2).symm,
      emitT_setv (Y 0) F (X 2) (hFX 7 2).symm (hFX 16 2).symm, wsetv_setv, emitT_append]
    rw [show (0 : ℕ) = (emitT (Y 0) F σ ([Tok.const (d.L[d.J - 1] : ℤ)] ++ linToks o (d.Br r)[d.J - 1])).val (X 2) by
      rw [emitT_val_ne (Y 0) F _ (hFX 7 2).symm (hFX 16 2).symm]; exact (hs.zero 2 (by decide)).symm, wsetv_same]
  · have h2 : (Λ + 1) ^ 2 ≤ (Λ + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    have h3 : Λ + 1 ≤ (Λ + 1) ^ 3 := by
      have := Nat.pow_le_pow_right (show 1 ≤ Λ + 1 by omega) (show 1 ≤ 3 by omega); simpa using this
    omega

theorem phiB_spec (d : FData) (Λ : ℕ) (σ : WState ns nr) (hs : FState Y X F σ d) (hb : FBound d Λ)
    (hr : FBoundR X σ Λ) (r : ℕ) (hr2 : r < 2) (oR : Fin 24) (hoR : oR ∉ ([1, 2, 3, 6] : List (Fin 24))) (o : ℕ)
    (hov : σ.val (X oR) = o) (hoG : o + d.Gr r ≤ Λ) (hLJ : d.J < d.L.length)
    (hcap : TCap cap F σ ([Tok.mul, Tok.const (d.L.getD d.J 0 : ℤ)] ++ linToks o (d.Cr r) ++ [Tok.mul, Tok.sub]) Λ) :
    WExec cap (phiB Y X F r oR) σ
      (emitT (Y 0) F σ ([Tok.mul, Tok.const (d.L.getD d.J 0 : ℤ)] ++ linToks o (d.Cr r) ++ [Tok.mul, Tok.sub]))
      (6000 * (Λ + 1) ^ 3) := by
  have hFX := hs.disj
  have hXX : ∀ {a b : Fin 24}, a ≠ b → X a ≠ X b := fun h => X.injective.ne h
  have hY : ∀ {a b : Fin 8}, a ≠ b → Y a ≠ Y b := fun h => Y.injective.ne h
  have rf := roleFacts_of Y X F hs hb hr r hr2
  obtain ⟨rC, hC⟩ := rf.stC
  obtain ⟨rL, hLs⟩ := hs.stL
  have nS := rSC_ne r
  have nLS := rLS_ne r
  have o3 : oR ≠ 3 := fun e => hoR (by simp [e])
  have hJΛ := hb.J
  have hgL : d.L.getD d.J 0 = d.L[d.J] := List.getD_eq_getElem _ _ hLJ
  rw [hgL] at hcap ⊢
  have split : [Tok.mul, Tok.const (d.L[d.J] : ℤ)] ++ linToks o (d.Cr r) ++ [Tok.mul, Tok.sub] =
      [Tok.mul] ++ ([Tok.const (d.L[d.J] : ℤ)] ++ (linToks o (d.Cr r) ++ ([Tok.mul] ++ [Tok.sub]))) := by simp
  rw [split] at hcap ⊢
  have c1 := TCap.left cap F hcap
  have r1 := TCap.right cap (Y 0) F hcap
  have c2 := TCap.left cap F r1
  have r2 := TCap.right cap (Y 0) F r1
  have c3 := TCap.left cap F r2
  have r3 := TCap.right cap (Y 0) F r2
  have c4 := TCap.left cap F r3
  have c5 := TCap.right cap (Y 0) F r3
  have s1 := litC_spec cap (Y 0) F .mul σ hs.rest (TCap.lit cap F c1).1 (TCap.lit cap F c1).2
  set σ1 := emitT (Y 0) F σ [Tok.mul]
  have hs1 := hs.emitT Y X F [Tok.mul]
  have hFS : Y 5 ≠ Y 0 := hY (by decide)
  have s2 := rateC_spec cap (Y 0) F (Y 5) hFS (X 6) (X 1) (fun i => hFX i 6) (fun i => hFX i 1) (hXX (by decide))
    d.L rL d.J (σ.val (X 6)) Λ hLJ σ1 hs1.rest (by rw [emitT_st_ne (Y 0) F _ hFS]; exact hLs)
    (by rw [emitT_sh_ne (Y 0) F _ hFS]; exact hs.sh 5 (by decide)) hs1.vJ
    (emitT_val_ne (Y 0) F _ (hFX 7 6).symm (hFX 16 6).symm σ _) (le_trans (encN_take_le _ _) hs.vLF)
    (hr 6 (by decide)) hJΛ hb.zL
    (by unfold TCap at c2; simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at c2
        rw [tokWord_const_nat] at c2; simp only [List.length_append] at c2 ⊢; omega)
    (by unfold TCap at hcap; have := hr 6 (by decide); omega)
    (fun x hx => by have := hb.zL x hx; unfold TCap at hcap; omega)
    (by unfold TCap at c2; simp at c2; omega)
  set σ2 := emitT (Y 0) F σ1 [Tok.const (d.L[d.J] : ℤ)]
  have hs2 := hs1.emitT Y X F [Tok.const (d.L[d.J] : ℤ)]
  have hSC : Y 0 ≠ Y (rSC r) := hY (Ne.symm nS.1)
  have hvX : ∀ i, σ2.val (X i) = σ.val (X i) := fun i => by
    simp only [σ2, σ1]
    rw [emitT_val_ne (Y 0) F _ (hFX 7 i).symm (hFX 16 i).symm, emitT_val_ne (Y 0) F _ (hFX 7 i).symm (hFX 16 i).symm]
  have s3 := stP_run cap (Y 0) F (Y (rSC r)) hSC (X (rG r)) (X oR) (X (rLS r)) (X 3) (fun i => hFX i _)
    (fun i => hFX i _) (fun i => hFX i _) (fun i => hFX i _) (d.Gr r) 0 o (σ.val (X (rLS r))) Λ [d.Cr r]
    (by simp [rf.bC]) (by simp) rC σ2 hs2.rest
    (by simp only [σ2, σ1]; rw [emitT_st_ne (Y 0) F _ hSC.symm, emitT_st_ne (Y 0) F _ hSC.symm, hC]; simp)
    (by simp only [σ2, σ1]; rw [emitT_sh_ne (Y 0) F _ hSC.symm, emitT_sh_ne (Y 0) F _ hSC.symm]; exact rf.shC)
    (by rw [hvX]; exact rf.vG) (by rw [hvX]; exact hov) (hvX _) (by rw [hvX]; exact hs.zero 3 (by decide))
    (by simpa using rf.vS) (by omega) hoG rf.rLS (by simpa using rf.zC) (by simpa using c3)
  simp only [List.getElem_cons_zero] at s3
  have hs3 := hs2.emitT Y X F (linToks o (d.Cr r))
  have s4 := litC_spec cap (Y 0) F .mul _ hs3.rest (TCap.lit cap F c4).1 (TCap.lit cap F c4).2
  have hs4 := hs3.emitT Y X F [Tok.mul]
  have s5 := litC_spec cap (Y 0) F .sub _ hs4.rest (TCap.lit cap F c5).1 (TCap.lit cap F c5).2
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 s5)))) ?_ ?_
  · simp only [σ2, σ1, emitT_append, List.append_assoc]
  · have h2 : (Λ + 1) ^ 2 ≤ (Λ + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    have h3 : 1 ≤ (Λ + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    rw [tokWord_mul_length, tokWord_sub_length]
    omega

/-- The `Φ`-moment printer of role `r`. -/
def momPP (r : ℕ) : WM ns nr :=
  .seq (phiA Y X F r 15) (.seq (phiB Y X F r 15) (.seq (phiA Y X F r (rG r)) (.seq (phiB Y X F r (rG r))
    (.seq (litC (Y 0) F .sub) (powC (Y 0) F (X 22))))))

theorem rG_not (r : ℕ) : rG r ∉ ([1, 2, 3, 6] : List (Fin 24)) := by unfold rG; split <;> decide

theorem momPP_spec (d : FData) (Λ : ℕ) (σ : WState ns nr) (hs : FState Y X F σ d) (hb : FBound d Λ)
    (hr : FBoundR X σ Λ) (r : ℕ) (hr2 : r < 2) (hJ1 : 1 ≤ d.J) (hLJ : d.J < d.L.length) (h2G : 2 * d.Gr r ≤ Λ)
    (hcap : TCap cap F σ (mpToks d r) Λ) :
    WExec cap (momPP Y X F r) σ (emitT (Y 0) F σ (mpToks d r)) (30000 * (Λ + 1) ^ 3) := by
  have hFX := hs.disj
  have rf := roleFacts_of Y X F hs hb hr r hr2
  unfold mpToks phToks at hcap ⊢
  set A0 := [Tok.const (d.L.getD (d.J - 1) 0 : ℤ)] ++ linToks 0 ((d.Br r).getD (d.J - 1) [])
  set B0 := [Tok.mul, Tok.const (d.L.getD d.J 0 : ℤ)] ++ linToks 0 (d.Cr r) ++ [Tok.mul, Tok.sub]
  set A1 := [Tok.const (d.L.getD (d.J - 1) 0 : ℤ)] ++ linToks (d.Gr r) ((d.Br r).getD (d.J - 1) [])
  set B1 := [Tok.mul, Tok.const (d.L.getD d.J 0 : ℤ)] ++ linToks (d.Gr r) (d.Cr r) ++ [Tok.mul, Tok.sub]
  have split : [Tok.const (d.L.getD (d.J - 1) 0 : ℤ)] ++ linToks 0 ((d.Br r).getD (d.J - 1) []) ++
      [Tok.mul, Tok.const (d.L.getD d.J 0 : ℤ)] ++ linToks 0 (d.Cr r) ++ [Tok.mul, Tok.sub] ++
      ([Tok.const (d.L.getD (d.J - 1) 0 : ℤ)] ++ linToks (d.Gr r) ((d.Br r).getD (d.J - 1) []) ++
      [Tok.mul, Tok.const (d.L.getD d.J 0 : ℤ)] ++ linToks (d.Gr r) (d.Cr r) ++ [Tok.mul, Tok.sub]) ++
      [Tok.sub, Tok.pow (2 * d.k)] = A0 ++ (B0 ++ (A1 ++ (B1 ++ ([Tok.sub] ++ [Tok.pow (2 * d.k)])))) := by
    simp [A0, B0, A1, B1, List.append_assoc]
  rw [split] at hcap ⊢
  have c1 := TCap.left cap F hcap
  have r1 := TCap.right cap (Y 0) F hcap
  have c2 := TCap.left cap F r1
  have r2 := TCap.right cap (Y 0) F r1
  have c3 := TCap.left cap F r2
  have r3 := TCap.right cap (Y 0) F r2
  have c4 := TCap.left cap F r3
  have r4 := TCap.right cap (Y 0) F r3
  have c5 := TCap.left cap F r4
  have c6 := TCap.right cap (Y 0) F r4
  have hoR := rG_not r
  have hFB : ∀ {τ : WState ns nr} (ts : List Tok), FBoundR X τ Λ → FBoundR X (emitT (Y 0) F τ ts) Λ :=
    fun ts h => h.emitT X F hFX (Y 0) ts
  have s1 := phiA_spec cap Y X F d Λ σ hs hb hr r hr2 15 (by decide) 0 hs.vo0 (by omega) hJ1 hLJ c1
  have hs1 := hs.emitT Y X F A0
  have s2 := phiB_spec cap Y X F d Λ _ hs1 hb (hFB A0 hr) r hr2 15 (by decide) 0 hs1.vo0 (by omega) hLJ c2
  have hs2 := hs1.emitT Y X F B0
  have vG2 : (emitT (Y 0) F (emitT (Y 0) F σ A0) B0).val (X (rG r)) = d.Gr r := by
    rw [emitT_val_ne (Y 0) F _ (hFX 7 _).symm (hFX 16 _).symm, emitT_val_ne (Y 0) F _ (hFX 7 _).symm (hFX 16 _).symm]
    exact rf.vG
  have s3 := phiA_spec cap Y X F d Λ _ hs2 hb (hFB B0 (hFB A0 hr)) r hr2 (rG r) hoR (d.Gr r) vG2 (by omega) hJ1 hLJ c3
  have hs3 := hs2.emitT Y X F A1
  have s4 := phiB_spec cap Y X F d Λ _ hs3 hb (hFB A1 (hFB B0 (hFB A0 hr))) r hr2 (rG r) hoR (d.Gr r)
    (by rw [emitT_val_ne (Y 0) F _ (hFX 7 _).symm (hFX 16 _).symm]; exact vG2) (by omega) hLJ c4
  have hs4 := hs3.emitT Y X F B1
  have s5 := litC_spec cap (Y 0) F .sub _ hs4.rest (TCap.lit cap F c5).1 (TCap.lit cap F c5).2
  have hs5 := hs4.emitT Y X F [Tok.sub]
  have s6 := powC_spec cap (Y 0) F (X 22) (fun i => hFX i 22) _ hs5.rest
    (by rw [hs5.vK, show (natWord 6).length = 7 by decide]; unfold TCap at c6; have := hb.k; omega)
    (TCap.lit cap F c6).2
  rw [hs5.vK] at s6
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 s6))))) ?_ ?_
  · simp only [emitT_append, List.append_assoc]
  · have hp := printCost_le (2 * d.k) Λ hb.k
    have h2 : (Λ + 1) ^ 2 ≤ (Λ + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    have h1 : 1 ≤ (Λ + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    rw [show (natWord 6).length = 7 by decide, tokWord_sub_length]
    omega

end Mom

end NearCubicGates.Close.CounterMachine
