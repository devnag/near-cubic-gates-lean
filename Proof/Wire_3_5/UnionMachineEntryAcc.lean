import Proof.Wire_3_5.UnionMachineEntryRead

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.Entry
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.UnionMachine.Round

local notation "rCC" => (0 : Fin 15)
local notation "rSG" => (1 : Fin 15)
local notation "rK1" => (2 : Fin 15)
local notation "rK0" => (3 : Fin 15)
local notation "rMP" => (6 : Fin 15)
local notation "rMN" => (7 : Fin 15)
local notation "rT1" => (14 : Fin 15)

variable (cap : ℕ)

/-- The accumulators of the three tests: `V` in `(8, 9)`, `Q` in `(10, 11)`, `μ` in `(12, 13)`. -/
def accPos (k : Fin 3) : Fin 15 := ⟨8 + 2 * k.val, by omega⟩
def accNeg (k : Fin 3) : Fin 15 := ⟨9 + 2 * k.val, by omega⟩

/-- A test's accumulated integer. -/
def accVal (σ : ES) (k : Fin 3) : ℤ := (σ.val (accPos k) : ℤ) - σ.val (accNeg k)

/-- `B += A; C += A; A := 0`. -/
def move2E (A B C : Fin 15) : WM 1 15 := .whr A (.seq (.dec A) (.seq (.inc B) (.inc C)))

theorem move2E_spec (A B C : Fin 15) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) (σ : ES)
    (hB : σ.val B + σ.val A ≤ cap) (hC : σ.val C + σ.val A ≤ cap) :
    WExec cap (move2E A B C) σ (((σ.setv A 0).setv B (σ.val B + σ.val A)).setv C (σ.val C + σ.val A))
      (σ.val A * (9 + 4) + 1) := by
  set n := σ.val A with hn
  let S : ℕ → ES := fun k => ((σ.setv A (n - k)).setv B (σ.val B + k)).setv C (σ.val C + k)
  have hS0 : S 0 = σ := by
    simp only [S]
    refine WState.eq rfl rfl ?_ rfl
    funext x
    simp only [WState.setv_val, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  have hSn : S n = ((σ.setv A 0).setv B (σ.val B + n)).setv C (σ.val C + n) := by simp [S]
  have h := wloop cap A (.seq (.inc B) (.inc C)) 9 n S
    (fun k _ => by simp [S, Function.update_apply, hAB, hAC, hBC, hAB.symm, hAC.symm, hBC.symm]) (by omega)
    (fun k hk => by
      have h1 := WExec.inc (cap := cap) B ((S k).setv A (n - k - 1))
        (by simp [S, Function.update_apply, hAB, hAC, hBC, hAB.symm, hAC.symm, hBC.symm]; omega)
      have h2 := WExec.inc (cap := cap) C (((S k).setv A (n - k - 1)).setv B
          (((S k).setv A (n - k - 1)).val B + 1))
        (by simp [S, Function.update_apply, hAB, hAC, hBC, hAB.symm, hAC.symm, hBC.symm]; omega)
      refine WExec.cast cap (WExec.seq h1 h2) ?_ (by omega)
      simp only [S]
      refine WState.eq rfl rfl ?_ rfl
      funext x
      simp only [WState.setv_val, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all <;> omega)
  rw [hS0, hSn] at h
  exact h

/-- `X += A` (`A` restored through `T1 = 0`). -/
def addTo (A X : Fin 15) : WM 1 15 := .seq (WM.move A rT1) (move2E rT1 A X)

theorem addTo_spec (A X : Fin 15) (hAX : A ≠ X) (hAT : A ≠ rT1) (hXT : X ≠ rT1) (σ : ES) (hT : σ.val rT1 = 0)
    (hX : σ.val X + σ.val A ≤ cap) (hA : σ.val A ≤ cap) :
    WExec cap (addTo A X) σ (σ.setv X (σ.val X + σ.val A)) (20 * σ.val A + 3) := by
  have h1 := wmove_spec cap A rT1 hAT (σ.val A) σ rfl hA (by omega)
  have h2 := move2E_spec cap rT1 A X hAT.symm hXT.symm hAX ((σ.setv A 0).setv rT1 (σ.val rT1 + σ.val A))
    (by simp [Function.update_apply, hAT]; omega) (by simp [Function.update_apply, hXT, hAX.symm]; omega)
  refine WExec.cast cap (WExec.seq h1 h2) ?_ (by simp [Function.update_apply, hT]; omega)
  refine WState.eq rfl rfl ?_ rfl
  funext x
  simp only [WState.setv_val, Function.update_apply]
  split_ifs <;> subst_vars <;> simp_all

/-- `X += CC·MP; Y += CC·MN; CC := 0`. -/
def mulAdd (X Y : Fin 15) : WM 1 15 := .whr rCC (.seq (.dec rCC) (.seq (addTo rMP X) (addTo rMN Y)))

theorem mulAdd_spec (X Y : Fin 15) (hXY : X ≠ Y) (hX : X.val ≥ 8) (hX' : X.val ≤ 13) (hY : Y.val ≥ 8)
    (hY' : Y.val ≤ 13) (σ : ES) (hT : σ.val rT1 = 0)
    (hcX : σ.val X + σ.val rCC * σ.val rMP ≤ cap) (hcY : σ.val Y + σ.val rCC * σ.val rMN ≤ cap)
    (hcC : σ.val rCC ≤ cap) (hMP : σ.val rMP ≤ cap) (hMN : σ.val rMN ≤ cap) :
    WExec cap (mulAdd X Y) σ
      (((σ.setv rCC 0).setv X (σ.val X + σ.val rCC * σ.val rMP)).setv Y (σ.val Y + σ.val rCC * σ.val rMN))
      (σ.val rCC * (20 * (σ.val rMP + σ.val rMN) + 7 + 4) + 1) := by
  have nXC : X ≠ rCC := fun h => by rw [h] at hX; simp at hX
  have nYC : Y ≠ rCC := fun h => by rw [h] at hY; simp at hY
  have nXP : X ≠ rMP := fun h => by rw [h] at hX; simp at hX
  have nYP : Y ≠ rMP := fun h => by rw [h] at hY; simp at hY
  have nXN : X ≠ rMN := fun h => by rw [h] at hX; simp at hX
  have nYN : Y ≠ rMN := fun h => by rw [h] at hY; simp at hY
  have nXT : X ≠ rT1 := fun h => by rw [h] at hX'; simp at hX'
  have nYT : Y ≠ rT1 := fun h => by rw [h] at hY'; simp at hY'
  obtain ⟨c, hc⟩ : ∃ c, c = σ.val rCC := ⟨_, rfl⟩
  obtain ⟨mp, hmp⟩ : ∃ m, m = σ.val rMP := ⟨_, rfl⟩
  obtain ⟨mn, hmn⟩ : ∃ m, m = σ.val rMN := ⟨_, rfl⟩
  rw [← hc, ← hmp] at hcX
  rw [← hc, ← hmn] at hcY
  rw [← hc, ← hmp, ← hmn]
  rw [← hc] at hcC
  rw [← hmp] at hMP
  rw [← hmn] at hMN
  let S : ℕ → ES := fun k => ((σ.setv rCC (c - k)).setv X (σ.val X + k * mp)).setv Y (σ.val Y + k * mn)
  have hS0 : S 0 = σ := by
    simp only [S]
    refine WState.eq rfl rfl ?_ rfl
    funext x
    simp only [WState.setv_val, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  have h := wloop cap rCC (.seq (addTo rMP X) (addTo rMN Y)) (20 * (mp + mn) + 7) c S
    (fun k _ => by simp [S, Function.update_apply, nXC.symm, nYC.symm]) hcC
    (fun k hk => by
      have hk1 : k * mp + mp ≤ c * mp := by nlinarith
      have hk2 : k * mn + mn ≤ c * mn := by nlinarith
      have v1 : ((S k).setv rCC (c - k - 1)).val rT1 = 0 := by
        simp [S, Function.update_apply, nXT.symm, nYT.symm, hT]
      have v2 : ((S k).setv rCC (c - k - 1)).val X = σ.val X + k * mp := by
        simp [S, Function.update_apply, nXC, hXY]
      have v3 : ((S k).setv rCC (c - k - 1)).val rMP = mp := by
        simp [S, Function.update_apply, nXP.symm, nYP.symm, hmp]
      have a1 := addTo_spec cap rMP X nXP.symm (by decide) nXT ((S k).setv rCC (c - k - 1)) v1
        (by rw [v2, v3]; omega) (by rw [v3]; omega)
      rw [v3, v2] at a1
      set τ1 := ((S k).setv rCC (c - k - 1)).setv X (σ.val X + k * mp + mp) with hτ1
      have w1 : τ1.val rT1 = 0 := by simp [τ1, S, Function.update_apply, nXT.symm, nYT.symm, hT]
      have w2 : τ1.val Y = σ.val Y + k * mn := by simp [τ1, S, Function.update_apply, nYC, hXY.symm]
      have w3 : τ1.val rMN = mn := by simp [τ1, S, Function.update_apply, nXN.symm, nYN.symm, hmn]
      have a2 := addTo_spec cap rMN Y nYN.symm (by decide) nYT τ1 w1 (by rw [w2, w3]; omega) (by rw [w3]; omega)
      rw [w3, w2] at a2
      refine WExec.cast cap (a1.seq a2) ?_ (by omega)
      simp only [τ1, S]
      refine WState.eq rfl rfl ?_ rfl
      funext x
      simp only [WState.setv_val, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all <;> ring_nf <;> omega)
  rw [hS0] at h
  refine WExec.cast cap h ?_ le_rfl
  simp only [S]
  refine WState.eq rfl rfl ?_ rfl
  funext x
  simp only [WState.setv_val, Function.update_apply]
  split_ifs <;> simp_all

/-- Add `±|c|·(MP − MN)` to one test's pair: `(P, N) += (|c|·MP, |c|·MN)`, swapped when negative. -/
def addPair (X Y : Fin 15) : WM 1 15 := .ifr rSG (mulAdd Y X) (mulAdd X Y)

/-- **The accumulation program**: dispatch on the kind flags. -/
def accP : WM 1 15 :=
  .ifr rK1 (addPair (accPos 2) (accNeg 2)) (.ifr rK0 (addPair (accPos 1) (accNeg 1)) (addPair (accPos 0) (accNeg 0)))

/-- The accumulation's effect on one register. -/
def accAdd (k : Fin 3) (neg : Bool) (c mp mn : ℕ) (r : Fin 15) : ℕ :=
  if r = accPos k then c * (if neg then mn else mp) else if r = accNeg k then c * (if neg then mp else mn) else 0

theorem acc_spec (k : Fin 3) (neg : Bool) (σ : ES) (hK1 : σ.val rK1 = (kindHi k).toNat)
    (hK0 : σ.val rK0 = (kindLo k).toNat) (hSG : σ.val rSG = neg.toNat) (hT : σ.val rT1 = 0)
    (hcap : ∀ i : Fin 6, σ.val ⟨8 + i.val, by omega⟩ + σ.val rCC * (σ.val rMP + σ.val rMN) ≤ cap)
    (hCC : σ.val rCC ≤ cap) (hMP : σ.val rMP ≤ cap) (hMN : σ.val rMN ≤ cap) :
    ∃ τ : ES, WExec cap accP σ τ (σ.val rCC * (20 * (σ.val rMP + σ.val rMN) + 7 + 4) + 1 + 3) ∧
      (∀ r, r ≠ rCC → τ.val r = σ.val r + accAdd k neg (σ.val rCC) (σ.val rMP) (σ.val rMN) r) ∧
      τ.val rCC = 0 ∧ τ.st = σ.st ∧ τ.sh = σ.sh ∧ τ.cell = σ.cell := by
  have hX : ∀ i : Fin 6, σ.val ⟨8 + i.val, by omega⟩ + σ.val rCC * σ.val rMP ≤ cap := fun i => by
    have := hcap i; nlinarith
  have hY : ∀ i : Fin 6, σ.val ⟨8 + i.val, by omega⟩ + σ.val rCC * σ.val rMN ≤ cap := fun i => by
    have := hcap i; nlinarith
  fin_cases k <;> cases neg
  · have m := mulAdd_spec cap (accPos 0) (accNeg 0) (by decide) (by decide) (by decide) (by decide) (by decide) σ hT
      (hX 0) (hY 1) hCC hMP hMN
    refine ⟨_, WExec.mono (WExec.ifrF (by simpa [kindHi] using hK1) (WExec.ifrF (by simpa [kindLo] using hK0) (WExec.ifrF (by simpa using hSG) m))) (by omega), fun r hr => ?_, by simp [accPos, accNeg], rfl, rfl, rfl⟩
    simp only [WState.setv_val, Function.update_apply, accAdd, accPos, accNeg]
    split_ifs <;> simp_all <;> omega
  · have m := mulAdd_spec cap (accNeg 0) (accPos 0) (by decide) (by decide) (by decide) (by decide) (by decide) σ hT
      (hX 1) (hY 0) hCC hMP hMN
    refine ⟨_, WExec.mono (WExec.ifrF (by simpa [kindHi] using hK1) (WExec.ifrF (by simpa [kindLo] using hK0) (WExec.ifrT (by simp at hSG; omega) m))) (by omega), fun r hr => ?_, by simp [accPos, accNeg], rfl, rfl, rfl⟩
    simp only [WState.setv_val, Function.update_apply, accAdd, accPos, accNeg]
    split_ifs <;> simp_all <;> omega
  · have m := mulAdd_spec cap (accPos 1) (accNeg 1) (by decide) (by decide) (by decide) (by decide) (by decide) σ hT
      (hX 2) (hY 3) hCC hMP hMN
    refine ⟨_, WExec.mono (WExec.ifrF (by simpa [kindHi] using hK1) (WExec.ifrT (by simp [kindLo] at hK0; omega) (WExec.ifrF (by simpa using hSG) m))) (by omega), fun r hr => ?_, by simp [accPos, accNeg], rfl, rfl, rfl⟩
    simp only [WState.setv_val, Function.update_apply, accAdd, accPos, accNeg]
    split_ifs <;> simp_all <;> omega
  · have m := mulAdd_spec cap (accNeg 1) (accPos 1) (by decide) (by decide) (by decide) (by decide) (by decide) σ hT
      (hX 3) (hY 2) hCC hMP hMN
    refine ⟨_, WExec.mono (WExec.ifrF (by simpa [kindHi] using hK1) (WExec.ifrT (by simp [kindLo] at hK0; omega) (WExec.ifrT (by simp at hSG; omega) m))) (by omega), fun r hr => ?_, by simp [accPos, accNeg], rfl, rfl, rfl⟩
    simp only [WState.setv_val, Function.update_apply, accAdd, accPos, accNeg]
    split_ifs <;> simp_all <;> omega
  · have m := mulAdd_spec cap (accPos 2) (accNeg 2) (by decide) (by decide) (by decide) (by decide) (by decide) σ hT
      (hX 4) (hY 5) hCC hMP hMN
    refine ⟨_, WExec.mono (WExec.ifrT (by simp [kindHi] at hK1; omega) (WExec.ifrF (by simpa using hSG) m)) (by omega), fun r hr => ?_, by simp [accPos, accNeg], rfl, rfl, rfl⟩
    simp only [WState.setv_val, Function.update_apply, accAdd, accPos, accNeg]
    split_ifs <;> simp_all <;> omega
  · have m := mulAdd_spec cap (accNeg 2) (accPos 2) (by decide) (by decide) (by decide) (by decide) (by decide) σ hT
      (hX 5) (hY 4) hCC hMP hMN
    refine ⟨_, WExec.mono (WExec.ifrT (by simp [kindHi] at hK1; omega) (WExec.ifrT (by simp at hSG; omega) m)) (by omega), fun r hr => ?_, by simp [accPos, accNeg], rfl, rfl, rfl⟩
    simp only [WState.setv_val, Function.update_apply, accAdd, accPos, accNeg]
    split_ifs <;> simp_all <;> omega

end NearCubicWires.WireExponent3_5.UnionMachine.Entry
