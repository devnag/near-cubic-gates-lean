import Proof.Wire_3_5.FinalPassFiltEval
import Proof.Wire_3_5.FinalPassPopList

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Filt
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.Pop
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.SupplierWalk
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Block

/-! ## Stage 7 alone -/

/-- **The stage-7 machine** (one for every table, threshold and point). -/
def stage7Machine : Machine (2 + 9) main7.toProg.size := main7.toProg.compile

/-- The evaluator's own tapes: the table word, the threshold, 7 blank registers. -/
def stage7Data (tbl : List (List (List Bool))) (thr c : ℕ) : Fin 9 → List Bool := fun i =>
  if i.val = 0 then tableWord tbl
  else if i.val = 1 then ListEval.unary thr
  else List.replicate (c + 1) false

theorem stage7_step (tbl : List (List (List Bool))) (thr c L : ℕ) (hlen : ∀ vs ∈ tbl, ∀ cs ∈ vs, cs.length ≤ L)
    (hc : capOf7 L tbl thr ≤ c) (Z : List Bool) (b : Bool) (hZ : Z.length = L) :
    Step stage7Machine (cost7 (tableWord tbl).length thr) (fun _ => 0)
      (Fin.addCases (m := 2) (n := 9) ![frame Z, [b]] (stage7Data tbl thr c)) (fun _ => 0)
      (Fin.addCases (m := 2) (n := 9) ![frame Z, [tabEval thr tbl Z]] (stage7Data tbl thr c)) := by
  subst hZ
  have h := (RExec.exec _ _ (main7_spec c Z tbl thr b hlen hc)).step
  refine Step.congr (Step.congr_in h ?_ ?_) ?_ ?_
  · funext j; fin_cases j <;> rfl
  · funext j; fin_cases j <;> simp [enc, role, streams7, S7, regTape_zero] <;> rfl
  · funext j; fin_cases j <;> rfl
  · funext j; fin_cases j <;> simp [enc, role, streams7, S7, regTape_zero] <;> rfl

/-- **The regular filter at a point**: at the seed's table, the stage-7 cell is `filterBits P e Z` (`filt:gap`). -/
theorem stage7_filter (P : GapParams) (e : GapSeed P) (c L : ℕ)
    (hc : capOf7 L (filterTable P e L) (majorityThreshold P.walkLen) ≤ c) (Z : List Bool) (b : Bool)
    (hZ : Z.length = L) :
    Step stage7Machine (cost7 (tableWord (filterTable P e L)).length (majorityThreshold P.walkLen)) (fun _ => 0)
      (Fin.addCases (m := 2) (n := 9) ![frame Z, [b]] (stage7Data (filterTable P e L) (majorityThreshold P.walkLen) c))
      (fun _ => 0)
      (Fin.addCases (m := 2) (n := 9) ![frame Z, [filterBits P e Z]]
        (stage7Data (filterTable P e L) (majorityThreshold P.walkLen) c)) := by
  have h := stage7_step (filterTable P e L) (majorityThreshold P.walkLen) c L
    (fun vs hvs cs hcs => (filterTable_lengths P e L vs hvs cs hcs).le) hc Z b hZ
  rw [filterBits_eq_tab, hZ]
  exact h

/-! ## Stage 3 then stage 7 -/

/-- **The composite program**: stage 3, stage 7 on the scratch, blank the scratch. -/
def comp37 : WM 4 7 := .seq (pop 0 3 4 0) (.seq (main7.lift fs5) (blankOut 0 3 4 0))

/-- **The stage-3∘7 machine** (one for every table, threshold, sign and point). -/
def stage37Machine : Machine (2 + 11) comp37.toProg.size := comp37.toProg.compile

/-- The evaluator's own tapes: the table word, the threshold, the scratch, the sign cell, 7 registers. -/
def stage37Data (tbl : List (List (List Bool))) (thr : ℕ) (sgn : Bool) (c : ℕ) : Fin 11 → List Bool := fun i =>
  if i.val = 0 then tableWord tbl
  else if i.val = 1 then ListEval.unary thr
  else if i.val = 3 then [sgn]
  else List.replicate (c + 1) false

/-- One step bound for every point of `L` occurrences. -/
def stage37Cost (W thr L : ℕ) : ℕ := passCost L + 1 + (cost7 W thr + 1 + passCost L)

theorem stage37_step (tbl : List (List (List Bool))) (thr L : ℕ) (sgn : Bool) (c : ℕ)
    (hlen : ∀ vs ∈ tbl, ∀ cs ∈ vs, cs.length ≤ L) (hc : capOf7 L tbl thr ≤ c)
    (X : List Bool) (b : Bool) (hX : X.length = 4 * L) :
    Step stage37Machine (stage37Cost (tableWord tbl).length thr L) (fun _ => 0)
      (Fin.addCases (m := 2) (n := 11) ![frame X, [b]] (stage37Data tbl thr sgn c)) (fun _ => 0)
      (Fin.addCases (m := 2) (n := 11) ![frame X, [tabEval thr tbl (popBits sgn X)]] (stage37Data tbl thr sgn c)) := by
  have hcL : 2 * L + 40 ≤ c := by unfold capOf7 at hc; omega
  have hZl : (popBits sgn X).length = L := popBits_length sgn L X hX
  generalize hd : tabEval thr tbl (popBits sgn X) = d
  obtain ⟨σ0, hσ0⟩ : ∃ σ : WState 4 7, σ = ⟨fun _ => 0, st35 X (tableWord tbl) thr sgn c, fun _ => 0, b⟩ :=
    ⟨_, rfl⟩
  -- stage 3
  have e1 := pop_spec c 0 3 4 0 (by decide) (by decide) (by decide) sgn L X [] (List.replicate (c + 1) false) σ0 hX
    (by rw [hσ0]; simp [st35, frame_eq_frameP]) (by rw [hσ0]) (by rw [hσ0]; rfl) (by rw [hσ0]) (by simp; omega)
    (by rw [hσ0]; rfl) (by rw [hσ0]) (by omega)
  obtain ⟨σ1, hσ1⟩ : ∃ σ : WState 4 7,
      σ = σ0.sets 3 (frameP (popBits sgn X) ++ (List.replicate (c + 1) false).drop (2 * L)) := ⟨_, rfl⟩
  rw [← hσ1] at e1
  -- stage 7, lifted
  have m7 := main7_spec c (popBits sgn X) tbl thr b (fun vs hvs cs hcs => (hlen vs hvs cs hcs).trans hZl.symm.le)
    (by rw [hZl]; exact hc)
  rw [hd] at m7
  have hrel : LiftRel fs5 (streams7 (popBits sgn X) tbl thr) σ1 (S7 0 0 0 0 0 0 0 b) := by
    refine ⟨fun i => by rw [hσ1, hσ0]; fin_cases i <;> rfl, fun i p => ?_, by rw [hσ1, hσ0]; funext i; fin_cases i <;> rfl,
      by rw [hσ1, hσ0]; rfl⟩
    fin_cases i
    · rw [hσ1]
      simp only [WState.sets_st, fs5, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Function.update_self,
        List.drop_replicate, streams7]
      exact readTapeBit_frame_pad _ _ _
    · rw [hσ1, hσ0]; rfl
    · rw [hσ1, hσ0]; rfl
  obtain ⟨ω2, e2, r2, o2⟩ := RExec.lift _ _ c le_rfl fs5 fs5_inj m7 σ1 hrel
  have hω2 : ω2 = ⟨fun _ => 0, σ1.st, fun _ => 0, d⟩ := by
    refine WState.eq ?_ o2.1 (r2.val.trans (by funext i; fin_cases i <;> rfl)) r2.cell
    funext j
    fin_cases j
    · show ω2.sh 0 = 0
      rw [o2.2 0 (by decide), hσ1, hσ0]; rfl
    · exact r2.sh 1
    · exact r2.sh 2
    · exact r2.sh 0
    · show ω2.sh 4 = 0
      rw [o2.2 4 (by decide), hσ1, hσ0]; rfl
  subst hω2
  have hst3 : σ1.st 3 = frameP (popBits sgn X) ++ (List.replicate (c + 1) false).drop (2 * L) := by
    rw [hσ1]; simp
  -- blank the scratch
  have e3 := blank_spec c 0 3 4 0 (by decide) (by decide) (by decide) sgn L X [] _
    (⟨fun _ => 0, σ1.st, fun _ => 0, d⟩ : WState 4 7) hX
    (by show σ1.st 0 = _; rw [hσ1, hσ0]; simp [st35, frame_eq_frameP]) rfl hst3 rfl
    (by simp [hZl]) (by show readTapeBit (σ1.st 4) 0 = sgn; rw [hσ1, hσ0]; rfl) rfl (by omega)
  have hfin : (⟨fun _ => 0, σ1.st, fun _ => 0, d⟩ : WState 4 7).sets 3
      (List.replicate (2 * L) false ++ (frameP (popBits sgn X) ++ (List.replicate (c + 1) false).drop (2 * L)).drop
        (2 * L)) = ⟨fun _ => 0, st35 X (tableWord tbl) thr sgn c, fun _ => 0, d⟩ := by
    rw [blank_restore L (c + 1) _ (by simp [hZl]) (by omega)]
    refine WState.eq rfl ?_ rfl rfl
    funext j
    simp only [WState.sets_st, Function.update_apply]
    split_ifs with hj
    · subst hj; rfl
    · rw [hσ1, hσ0]; simp [Function.update_of_ne hj]
  rw [hfin] at e3
  have hs7 := (WExec.exec c (WExec.seq e1 (WExec.seq e2 e3))).step
  refine Step.congr (Step.congr_in hs7 ?_ ?_) ?_ ?_
  · funext j; rw [hσ0]; simp only [wenc]; split <;> rfl
  · funext j; rw [hσ0]; fin_cases j <;> simp [wenc, role, st35, regTape_zero] <;> rfl
  · funext j; simp only [wenc]; split <;> rfl
  · funext j; fin_cases j <;> simp [wenc, role, st35, regTape_zero] <;> rfl

theorem stage37_filter (P : GapParams) (e : GapSeed P) (L : ℕ) (sgn : Bool) (c : ℕ)
    (hc : capOf7 L (filterTable P e L) (majorityThreshold P.walkLen) ≤ c) (X : List Bool) (b : Bool)
    (hX : X.length = 4 * L) :
    Step stage37Machine
      (stage37Cost (tableWord (filterTable P e L)).length (majorityThreshold P.walkLen) L) (fun _ => 0)
      (Fin.addCases (m := 2) (n := 11) ![frame X, [b]]
        (stage37Data (filterTable P e L) (majorityThreshold P.walkLen) sgn c)) (fun _ => 0)
      (Fin.addCases (m := 2) (n := 11) ![frame X, [filterBits P e (popBits sgn X)]]
        (stage37Data (filterTable P e L) (majorityThreshold P.walkLen) sgn c)) := by
  have h := stage37_step (filterTable P e L) (majorityThreshold P.walkLen) L sgn c
    (fun vs hvs cs hcs => (filterTable_lengths P e L vs hvs cs hcs).le) hc X b hX
  rw [filterBits_eq_tab, popBits_length sgn L X hX]
  exact h

/-! ## Costs -/

/-- The description size of the filter evaluators: the table word, the threshold and the point. -/
def stage7Size (W thr L : ℕ) : ℕ := W + thr + L + 1

theorem cost7_le (W thr L : ℕ) : cost7 W thr ≤ 170 * stage7Size W thr L := by
  unfold cost7 stage7Size; omega

theorem stage37_cost_le (W thr L : ℕ) : stage37Cost W thr L ≤ 290 * stage7Size W thr L := by
  unfold stage37Cost cost7 passCost stage7Size; omega

/-- **The step bounds are linear**, so within every budget class at the description size. -/
theorem stage7_within {E : Envelope} {cls : BudgetClass} {k psi : ℕ} (W thr L : ℕ) (hd : 1 ≤ classDeg E cls) :
    Within E cls 170 (stage7Size W thr L) k psi (cost7 W thr) :=
  Within.of_poly (by unfold stage7Size; omega) (by simpa using cost7_le W thr L) hd

theorem stage37_within {E : Envelope} {cls : BudgetClass} {k psi : ℕ} (W thr L : ℕ) (hd : 1 ≤ classDeg E cls) :
    Within E cls 290 (stage7Size W thr L) k psi (stage37Cost W thr L) :=
  Within.of_poly (by unfold stage7Size; omega) (by simpa using stage37_cost_le W thr L) hd

end NearCubicWires.WireExponent3_5.FinalPass.Filt
