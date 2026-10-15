import Proof.Gates.Cells.Prelude

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter
open NearCubicGates.Close.CounterMachine
open NearCubicWires.RepairRepresentation (natWord)

variable {C : Ctx}

def mainOf (cP gP sP : St VV MM) : St VV MM := .seq (preludeP cP) (cellLoop gP sP)

/-- The run bound of `mainOf`. -/
noncomputable def totCost (tc tg : Ctx → Call → Params → ℕ → ℕ) (ts : SolveMachine → Ctx → Call → Params → ℕ → ℕ)
    (S : SolveMachine) (C : Ctx) (c : Call) (p : Params) (wt : Wit c.n) (Big : ℕ) : ℕ :=
  preCost c p wt Big + 1 + tc C c p Big +
    (2 ^ cellBits wt.I * (cellCostU c p wt (tg C c p Big) (ts S C c p Big) + 4) + 4) + 1

open Classical in
theorem loop_sums {cT : ℕ} (c : Call) (p : Params) (wt : Wit c.n) (hs : Spec cT (header c) p)
    (hk : wt.I.card = p.k) :
    (∑ j ∈ Finset.range (2 ^ cellBits wt.I),
      (if CellTests c p wt (cellOf wt.I j) then cellCount c p wt (cellOf wt.I j) else 0)) = certainSum c p wt ∧
    (∑ j ∈ Finset.range (2 ^ cellBits wt.I), (if CellTests c p wt (cellOf wt.I j) then 0 else 1)) =
      uncCount c p wt := by
  have hiff : ∀ y : Cells wt.I, Certain c p wt y ↔ CellTests c p wt y := fun y => certain_iff_tests c p wt y hs hk
  constructor
  · unfold certainSum
    rw [Finset.sum_filter, sum_cells wt.I]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : CellTests c p wt (cellOf wt.I j)
    · rw [if_pos h, if_pos ((hiff _).2 h)]
    · rw [if_neg h, if_neg (fun h' => h ((hiff _).1 h'))]
  · unfold uncCount
    rw [Finset.card_filter, sum_cells wt.I]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : CellTests c p wt (cellOf wt.I j)
    · rw [if_pos h, if_neg (fun h' => h' ((hiff _).2 h))]
    · rw [if_neg h, if_pos (fun h' => h ((hiff _).1 h'))]

open Classical in

theorem mainOf_goal (S : SolveMachine) (cP gP sP : St VV MM) (tc tg : Ctx → Call → Params → ℕ → ℕ)
    (ts : SolveMachine → Ctx → Call → Params → ℕ → ℕ)
    (hC : ConstGoal cP tc) (hG : GatherGoal gP tg) (hS : SysGoal sP ts) (K e : ℕ)
    (hcost : ∀ (C : Ctx) {B1 B2 cT : ℕ} (r : CellReq B1 B2 cT) (Big : ℕ),
      (∀ x ∈ cellN r.c r.p r.wt, natBitLength x ≤ Big) → wdNeed r.c r.p r.wt Big ≤ C.Wd →
      totCost tc tg ts S C r.c r.p r.wt Big ≤ loopCost K e C r.c r.p Big) :
    LoopGoal (mainOf cP gP sP) S K e := by
  intro C B1 B2 cT r Big hK hinp hBig hWd hLB
  obtain ⟨w, hw⟩ := r.hw
  have hadm := r.adm
  have hs := selectParams_spec cT (header r.c) r.p r.hp
  have hk := decodeWitness_card r.c r.p w r.wt hw
  have hinp' : C.inp = (cellN r.c r.p r.wt).flatMap natWord ++ cellWord r.c r.p r.wt := by
    rw [hinp, cellN_word]; rfl
  have hpre := prelude_spec (C := C) r.c r.p r.wt hadm hs w hw cP tc hC Big hBig hWd hinp'
  have hrun : Hs C (mainOf cP gP sP) (a0 : DS VV MM) (totCost tc tg ts S C r.c r.p r.wt Big) (fun b =>
      Iface r.c r.p r.wt b ∧ Sto r.c r.p r.wt b ∧
      (b.env vCnt : ℚ) = ∑ j ∈ Finset.range (2 ^ cellBits r.wt.I),
        (if CellTests r.c r.p r.wt (cellOf r.wt.I j) then cellCount r.c r.p r.wt (cellOf r.wt.I j) else 0) ∧
      b.env vUnc = ∑ j ∈ Finset.range (2 ^ cellBits r.wt.I),
        (if CellTests r.c r.p r.wt (cellOf r.wt.I j) then 0 else 1)) := by
    unfold totCost
    refine Hs.seq hpre (fun b ⟨b1, b2, b3, b4, b5⟩ => ?_)
    exact cellLoop_spec (C := C) r.c r.p r.wt hadm hs w hw S gP sP tg ts hG hS hK Big hBig hWd hLB _ hinp' b b1 b2
      b3 b4 b5
  obtain ⟨b, n, hex, hn, hI, hSt, hv, hu⟩ := hrun
  obtain ⟨hs1, hs2⟩ := loop_sums r.c r.p r.wt hs hk
  exact ⟨b, n, hex, hn.trans (hcost C r Big hBig hWd), by rw [hv, hs1], by rw [hu, hs2], hSt.out, hI.cst⟩

end NearCubicGates.Close.Cells
