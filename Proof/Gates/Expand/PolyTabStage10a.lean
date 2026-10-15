import Proof.Gates.Expand.PolyTabStage9j

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.CounterMachine NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.TabMachine

variable {te qa : ℕ}

local notation "WX" => WMX (NSx te qa) NRk
local notation "WSt" => WState (NSx te qa) NRk

def initZ (K : Fin 64) : List (Fin 64) → WX
  | [] => WMX.skip
  | i :: l => .seq (initNum (sZ i) (rX K) (rX 51)) (initZ K l)

theorem initZ_spec (cap : ℕ) (K : Fin 64) (hK : K ≠ 51) (k : ℕ) (hcap : 2 * k ≤ cap) :
    ∀ (l : List (Fin 64)) (σ : WSt), l.Nodup → (∀ i ∈ l, σ.st (sZ i) = [] ∧ σ.sh (sZ i) = 0) →
      σ.val (rX K) = k → σ.val (rX 51) = 0 →
      ∃ τ, WXExec cap (initZ K l) σ τ (l.length * (initCost k + 1)) ∧ (∀ i ∈ l, NumOn τ (sZ i) k 0) ∧
        SameExcept σ τ (l.map sZ) []
  | [], σ, _, _, _, _ => ⟨σ, by simp only [initZ, List.length_nil, Nat.zero_mul]; exact WXExec.skip (cap := cap) σ,
      by simp, SameExcept.refl _ _ _⟩
  | i :: l, σ, hl, hb, hK', h51 => by
    have hl' := List.nodup_cons.mp hl
    have e1 := initNum_spec cap (X := sZ i) (K := rX K) (K2 := rX 51) (rX_ne hK) σ k
      (by rw [(hb i (by simp)).1]; simp) (hb i (by simp)).2 hK' h51 hcap
    set σ1 := σ.sets (sZ i) (frame (binary k 0)) with hσ1
    have hne : ∀ j ∈ l, sZ (te := te) (qa := qa) j ≠ sZ i := fun j hj e => hl'.1 (by rw [← sZ.injective e]; exact hj)
    obtain ⟨τ, e2, hn, hs⟩ := initZ_spec cap K hK k hcap l σ1 hl'.2 (fun j hj => by
        simp only [hσ1, WState.sets_st, WState.sets_sh, Function.update_of_ne (hne j hj)]
        exact hb j (by simp [hj])) (by simp [hσ1, hK']) (by simp [hσ1, h51])
    have hni : sZ (te := te) (qa := qa) i ∉ l.map sZ := fun hm => by
      obtain ⟨j, hj, e⟩ := List.mem_map.mp hm; exact hne j hj e
    refine ⟨τ, (WXExec.seq e1 e2).mono (by simp; ring_nf; omega), fun j hj => ?_, ?_⟩
    · rcases List.mem_cons.mp hj with rfl | hj
      · exact ⟨by rw [hs.st hni]; simp [hσ1], by rw [hs.sh hni]; simp [hσ1, (hb j (by simp)).2]⟩
      · exact hn j hj
    · refine SameExcept.trans (sameExcept_sets σ (List.mem_cons_self) _) (hs.weaken (fun x hx => ?_) (fun _ h => h))
      exact List.mem_cons_of_mem _ hx

/-- `sZ i := sZ i + n` (`sZ j` a width-`W` number, scratch). -/
def incZ (i j : Fin 64) : ℕ → WX
  | 0 => WMX.skip
  | n + 1 => .seq (BinW.inc (sZ i) (sZ j) (rX 3) (rX 4)) (incZ i j n)

theorem incZ_spec (cap W : ℕ) (i j : Fin 64) (hij : i ≠ j) (hcap : 2 * W + 1 ≤ cap) :
    ∀ (n a b : ℕ) (σ : WSt), NumOn σ (sZ i) W a → NumOn σ (sZ j) W b → σ.val (rX 3) = 0 → σ.val (rX 4) = 0 →
      a + n < 2 ^ W →
      WXExec cap (incZ i j n) σ (σ.sets (sZ i) (if n = 0 then σ.st (sZ i) else frame (binary W (a + n))))
        (n * (41 * W + 8))
  | 0, a, b, σ, _, _, _, _, _ => by
    simp only [incZ, if_pos rfl, Nat.zero_mul, if_true, BinW.sets_same rfl]; exact WXExec.skip (cap := cap) σ
  | n + 1, a, b, σ, hA, hB, h3, h4, hlt => by
    have e1 := BinW.inc_spec cap W (A := sZ i) (B := sZ j) (F := rX 3) (R := rX 4) (fun e => hij (sZ.injective e))
      (by polyTabNe) σ a b hA hB h3 h4 (by omega) hcap
    set σ1 := σ.sets (sZ i) (frame (binary W (a + 1))) with hσ1
    have hne : sZ (te := te) (qa := qa) j ≠ sZ i := fun e => hij (sZ.injective e).symm
    have e2 := incZ_spec cap W i j hij hcap n (a + 1) b σ1 ⟨by simp [hσ1], by simp [hσ1, hA.2]⟩
      ⟨by simp [hσ1, Function.update_of_ne hne, hB.1], by simp [hσ1, hB.2]⟩ (by simp [hσ1, h3]) (by simp [hσ1, h4])
      (by omega)
    refine (WXExec.seq e1 e2).cast cap ?_ (by ring_nf; omega)
    by_cases hn : n = 0
    · subst hn; simp [hσ1, BinW.sets_sets]
    · simp [hσ1, hn, show a + 1 + n = a + (n + 1) by ring, BinW.sets_sets]

/-- `sZ 26 := 2·sZ 26`, `c = rX K` times (`rX K` back at `0`; `sZ 44` scratch). -/
def powZ (K : Fin 64) : WX := .whr (rX K) (.seq (WMX.dec (rX K)) (BinW.shl (sZ 26) (sZ 44) (rX 3) (rX 4)))

theorem powZ_spec (cap W : ℕ) (K : Fin 64) (hK : K.val ∉ [3, 4]) (hcap : 2 * W + 1 ≤ cap) (c a b : ℕ) (σ : WSt)
    (hA : NumOn σ (sZ 26) W a) (hB : NumOn σ (sZ 44) W b) (h3 : σ.val (rX 3) = 0) (h4 : σ.val (rX 4) = 0)
    (hc : σ.val (rX K) = c) (hcc : c ≤ cap) :
    Runs cap (powZ K) σ (c * (41 * W + 8 + 4) + 1) (fun τ => NumOn τ (sZ 26) W (2 ^ c * a) ∧
      τ.val (rX K) = 0 ∧ SameExcept σ τ [sZ 26] [rX K]) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hK
  have k3 : rX K ≠ rX 3 := rX_ne (fun e => hK.1 (by rw [e]; rfl))
  have k4 : rX K ≠ rX 4 := rX_ne (fun e => hK.2 (by rw [e]; rfl))
  let Inv : ℕ → WSt → Prop := fun k τ => NumOn τ (sZ 26) W (2 ^ k * a) ∧ SameExcept σ τ [sZ 26] [rX K]
  obtain ⟨ρ, eρ, ⟨hρ, hfr⟩, hK0⟩ := Runs.count (cap := cap) (K := rX K)
    (body := BinW.shl (sZ 26) (sZ 44) (rX 3) (rX 4)) (41 * W + 8) c Inv hcc (fun k hk μ ⟨hμ, hfμ⟩ hμK => by
      have nZ : sZ (te := te) (qa := qa) 44 ∉ [sZ 26] := nm1 (by polyTabNe)
      have hB' : NumOn (μ.setv (rX K) (c - k - 1)) (sZ 44) W b :=
        ⟨by simp [hfμ.st nZ, hB.1], by simp [hfμ.sh nZ, hB.2]⟩
      have e := BinW.shl_spec cap W (A := sZ 26) (B := sZ 44) (F := rX 3) (R := rX 4) (by polyTabNe) (by polyTabNe)
        (μ.setv (rX K) (c - k - 1)) (2 ^ k * a) b ⟨by simp [hμ.1], by simp [hμ.2]⟩ hB'
        (by simp [Function.update_of_ne k3.symm, hfμ.val (nm1 k3.symm), h3])
        (by simp [Function.update_of_ne k4.symm, hfμ.val (nm1 k4.symm), h4]) hcap
      refine ⟨_, e, ⟨⟨by simp [pow_succ]; ring_nf, by simp [hμ.2]⟩, ?_⟩, by simp⟩
      exact (hfμ.trans (sameExcept_setv _ (List.mem_singleton_self _) _)).trans
        (sameExcept_sets _ (List.mem_singleton_self _) _))
    σ ⟨by simpa using hA, SameExcept.refl _ _ _⟩ hc
  exact ⟨ρ, eρ, hρ, hK0, hfr⟩

end NearCubicGates.Close.Expand.PolyTab
