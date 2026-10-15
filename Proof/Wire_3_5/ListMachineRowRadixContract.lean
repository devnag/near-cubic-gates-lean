import Proof.Wire_3_5.ListMachineRowRadixInst

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.ListMachine.Ref Finset
open NearCubicWires.WireExponent3_5.ListMachine (Poly Expr listBound)
open NearCubicWires.WireExponent3_5.ListMachine.Rec (coefWord termWord)
open NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.RepairOrdinary (frame frame_length)
open NearCubicWires.ExtDecompositionBatch

section
variable (D : ListData) (digs : List Dig) (p b0 s : ℕ)

/-- The factor blocks, in store order. -/
def radBlocksC : List (List Bool) :=
  digs.flatMap fun dg => (List.range (D.M + 1)).map (fun t => blockC D dg.1 t true false dg.2) ++
    (List.range (D.M + 1)).map (fun t => blockC D dg.1 t false false dg.2)

/-- The factor stages' cost bounds, summed. -/
def radCostsC : ℕ :=
  (digs.flatMap fun dg => (List.range (D.M + 1)).flatMap fun t =>
    [costC D dg.1 t true false dg.2, costC D dg.1 t false false dg.2]).sum

/-- **The scrub capacity.** -/
def radRC : ℕ := 2 + radCostsC D digs

/-- The contribution fields. -/
def radCs : List ℕ := consFrom D.M p b0 0 digs.length

/-- The residue pattern. -/
def radT : List Bool := patT p s (2 * digs.length * p + 1)

/-- The store's prints. -/
def radFs : List Poly := storeFrom D.M (radPp D digs) (radPm D digs) 0 digs.length

/-- **The log capacity.** -/
def radCapC : ℕ :=
  (2 * digs.length * (D.M + 1) * (4 * radRC D digs + 9) + 1) + (resLoopCost (radCs D digs p b0) + 3) +
    mselCost (radFs D digs) + incCost D.M (2 * digs.length)

/-- The setup values. -/
def radEvC : Fin 8 → List Bool :=
  radEv D.M (2 * digs.length) (radCs D digs p b0) (radT digs p s) (radCapC D digs p b0)

/-- **The RADIX row record** (computable). -/
def radRowRecC : List Bool :=
  fieldsWord (setupFieldsG (19 + 1) (radRC D digs) (radRC D digs + 1) (radEvC D digs p b0 s)) ++
    ((radBlocksC D digs).flatMap (fun b => true :: b) ++ [false])

def radRefC : Expr := radixExpr digs.length D.M p b0 (radPp D digs) (radPm D digs) (s : ZMod p)

variable (hok : DigsOk digs)

theorem blockSpecs_block (dg : Dig) (sgn : Bool) (hl : 4 * dg.1 ≤ dg.2.length) :
    (blockSpecs D dg sgn hl).map FSpec.block = (List.range (D.M + 1)).map fun t => blockC D dg.1 t sgn false dg.2 := by
  unfold blockSpecs
  rw [List.map_map]
  apply List.map_congr_left
  intro t ht
  have ht' : t ≤ D.M := Nat.le_of_lt_succ (List.mem_range.mp ht)
  simp only [Function.comp_apply]
  rw [visitSpec_block, min_eq_left ht']

theorem radSpecs_block : ∀ (digs : List Dig) (h : DigsOk digs), (radSpecs D digs h).map FSpec.block = radBlocksC D digs
  | [], _ => rfl
  | dg :: rest, h => by
    simp only [radSpecs, List.map_append, blockSpecs_block, radBlocksC, List.flatMap_cons, List.append_assoc]
    rw [radSpecs_block rest (fun x hx => h x (by simp [hx]))]
    rfl

theorem storeRec_radSpecs : storeRec (radSpecs D digs hok) = (radBlocksC D digs).flatMap (fun b => true :: b) ++ [false] := by
  rw [← radSpecs_block D digs hok, List.flatMap_map]
  rfl

theorem radRowRecC_eq :
    radRowRec D.M (2 * digs.length) (radCs D digs p b0) (radT digs p s) (radRC D digs) (radRC D digs + 1)
      (radCapC D digs p b0) (radSpecs D digs hok) = radRowRecC D digs p b0 s := by
  unfold radRowRec radRowRecC radEvC
  rw [storeRec_radSpecs]
  rfl

theorem mem_radSpecs : ∀ (digs : List Dig) (h : DigsOk digs) (x : FSpec (negFam F35)), x ∈ radSpecs D digs h →
    ∃ dg ∈ digs, ∃ t ≤ D.M, ∃ sgn : Bool, ∃ hl : 4 * dg.1 ≤ dg.2.length,
      x = visitSpec D dg.1 (min t D.M) sgn (capC D dg.1) (min_le_right _ _) le_rfl false dg.2 hl
  | [], _, x, hx => by simp [radSpecs] at hx
  | dg :: rest, h, x, hx => by
    simp only [radSpecs, List.mem_append] at hx
    rcases hx with hx | hx | hx
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
      exact ⟨dg, by simp, t, Nat.le_of_lt_succ (List.mem_range.mp ht), true, _, rfl⟩
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
      exact ⟨dg, by simp, t, Nat.le_of_lt_succ (List.mem_range.mp ht), false, _, rfl⟩
    · obtain ⟨dg', hdg', t, ht, sgn, hl, rfl⟩ := mem_radSpecs rest (fun x hx => h x (by simp [hx])) x hx
      exact ⟨dg', by simp [hdg'], t, ht, sgn, hl, rfl⟩

theorem costC_le_radCostsC (dg : Dig) (hdg : dg ∈ digs) (t : ℕ) (ht : t ≤ D.M) (sgn : Bool) :
    costC D dg.1 t sgn false dg.2 ≤ radCostsC D digs := by
  unfold radCostsC
  apply List.le_sum_of_mem
  refine List.mem_flatMap.mpr ⟨dg, hdg, List.mem_flatMap.mpr ⟨t, List.mem_range.mpr (by omega), ?_⟩⟩
  cases sgn <;> simp

theorem radSpecs_cost (x : FSpec (negFam F35)) (hx : x ∈ radSpecs D digs hok) : x.cost + 1 ≤ radRC D digs := by
  obtain ⟨dg, hdg, t, ht, sgn, hl, rfl⟩ := mem_radSpecs D digs hok x hx
  have h1 := visitSpec_cost_le D dg.1 (min t D.M) sgn (min_le_right _ _) false dg.2 hl
  have e : costC D dg.1 (min t D.M) sgn false dg.2 = costC D dg.1 t sgn false dg.2 := by rw [min_eq_left ht]
  have h2 := costC_le_radCostsC D digs dg hdg t ht sgn
  unfold radRC
  omega

/-- The RADIX row machine (the stage-3∘5 negation family). -/
noncomputable abbrev radMachine := radRowM (negFam F35)

/-- The RADIX row's cost at its record. -/
noncomputable def radRowCostC : ℕ :=
  radRowCost D.M (2 * digs.length) (radCs D digs p b0) (radT digs p s) (radRC D digs) (radRC D digs + 1)
    (radCapC D digs p b0) (radSpecs D digs hok)

/-! ## The cost bound -/

theorem setupFieldsG_eq (u R L : ℕ) (ev : Fin 8 → List Bool) :
    setupFieldsG u R L ev = [List.replicate R true, List.replicate L false, ev 0, ev 1, ev 2, ev 3, ev 4, ev 5, ev 7] := by
  simp only [setupFieldsG, targetsQ, List.map_cons, List.map_nil, setupG_driver, setupG_log]
  rw [setupG_e _ _ _ _ 0 (by decide), setupG_e _ _ _ _ 1 (by decide), setupG_e _ _ _ _ 2 (by decide),
    setupG_e _ _ _ _ 3 (by decide), setupG_e _ _ _ _ 4 (by decide), setupG_e _ _ _ _ 5 (by decide),
    setupG_e _ _ _ _ 7 (by decide)]

theorem setupFieldsG_len (u R L : ℕ) (ev : Fin 8 → List Bool) :
    R ≤ (fieldsWord (setupFieldsG u R L ev)).length ∧ (ev 7).length ≤ (fieldsWord (setupFieldsG u R L ev)).length := by
  rw [setupFieldsG_eq]
  simp only [fieldsWord, List.flatMap_cons, List.flatMap_nil, List.length_append, frame_length, List.length_replicate,
    List.length_nil]
  omega

theorem storeRec_len (xs : List (FSpec (negFam F35))) : xs.length ≤ (storeRec xs).length := by
  unfold storeRec
  have h : ∀ l : List (FSpec (negFam F35)), l.length ≤ (l.flatMap fun x => true :: x.block).length := by
    intro l; induction l with
    | nil => simp
    | cons x l ih => simp only [List.flatMap_cons, List.length_append, List.length_cons]; omega
  have := h xs
  simp only [List.length_append]; omega

theorem termCostR_le (fs : List Poly) : termCostR fs ≤ 2 * mselCost fs + 18 := by
  simp [termCostR, putCost, coefWord, NearCubicWires.RepairOrdinary.frame]
  omega

/-- The RADIX row's cost, for any parameters meeting the capacity conditions. -/
theorem radRowCost_bound {F : EvalFam} (K P : ℕ) (cs : List ℕ) (T : List Bool) (R Lg cap : ℕ) (xs : List (FSpec F))
    (hst : storeCost xs R ≤ cap) (hc1 : resLoopCost cs + 3 ≤ cap) (hc2 : mselCost (xs.map FSpec.poly) ≤ cap)
    (hc3 : incCost K P ≤ cap) :
    radRowCost K P cs T R Lg cap xs ≤ (K + 1) ^ P * (128 * ((radRowRec K P cs T R Lg cap xs).length + 1) ^ 2) := by
  set S := (radRowRec K P cs T R Lg cap xs).length with hS
  set N := (K + 1) ^ P with hN
  obtain ⟨hRf, hcf⟩ := setupFieldsG_len F.t R Lg (radEv K P cs T cap)
  have hc7 : (radEv K P cs T cap 7).length = cap := by simp [radEv]
  have hlen : (fieldsWord (setupFieldsG F.t R Lg (radEv K P cs T cap))).length + (storeRec xs).length = S := by
    rw [hS, radRowRec, List.length_append]
  have hRS : R ≤ S := by omega
  have hcS : cap ≤ S := by omega
  have hld := loadCost_le (setupFieldsG F.t R Lg (radEv K P cs T cap))
  have hterm := termCostR_le (xs.map FSpec.poly)
  have hpass : radPass K P cs (xs.map FSpec.poly) ≤ 6 * cap + 28 := by
    unfold radPass; omega
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hrc : radCost K P cs (xs.map FSpec.poly) ≤ N * (6 * S + 30) + 1 := by
    unfold radCost
    rw [← hN]
    have := Nat.mul_le_mul_left N (show radPass K P cs (xs.map FSpec.poly) + 2 ≤ 6 * S + 30 by omega)
    omega
  unfold radRowCost radPopCost
  have hpoly : 16 * S + 40 ≤ N * (16 * S + 40) := by nlinarith
  have hfin : N * (6 * S + 30) + N * (16 * S + 40) ≤ N * (128 * (S + 1) ^ 2) := by
    rw [← Nat.mul_add]; apply Nat.mul_le_mul_left; nlinarith
  omega

/-- **The RADIX row's cost**: at most `(M+1)^{2τ₀} · 128 · (|record| + 1)^2`. -/
theorem radRowCost_le : radRowCostC D digs p b0 s hok ≤
    (D.M + 1) ^ (2 * digs.length) * (128 * ((radRowRecC D digs p b0 s).length + 1) ^ 2) := by
  have hxlen : (radSpecs D digs hok).length = 2 * digs.length * (D.M + 1) := radSpecs_length D digs hok
  have hmp : (radSpecs D digs hok).map FSpec.poly = radFs D digs := by
    rw [radSpecs_poly D digs hok []]; rfl
  have hcapv : radCapC D digs p b0 = (2 * digs.length * (D.M + 1) * (4 * radRC D digs + 9) + 1) +
      (resLoopCost (radCs D digs p b0) + 3) + mselCost (radFs D digs) + incCost D.M (2 * digs.length) := rfl
  have hst : storeCost (radSpecs D digs hok) (radRC D digs) ≤ radCapC D digs p b0 := by
    have := storeCost_le (radSpecs D digs hok) (radRC D digs) (radSpecs_cost D digs hok)
    rw [hxlen] at this
    omega
  have h := radRowCost_bound D.M (2 * digs.length) (radCs D digs p b0) (radT digs p s) (radRC D digs) (radRC D digs + 1)
    (radCapC D digs p b0) (radSpecs D digs hok) hst (by omega) (by rw [hmp]; omega) (by omega)
  rw [radRowRecC_eq] at h
  exact h

/-! ## The RADIX row, end to end -/

theorem radT_eq (hs : s < p) : radT digs p s = patT p ((s : ZMod p).val) (2 * digs.length * p + 1) := by
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hs]; rfl

theorem radRow_run (hnest : ∀ j i, D.inLevel (j + 1) i = true → D.inLevel j i = true) (hτ : 1 ≤ digs.length)
    (hp : 0 < p) (hs : s < p) (pre rest out B : List Bool) :
    (∃ q A', Step radMachine (radRowCostC D digs p b0 s hok)
      (Fin.addCases (qH (19 + 1) pre.length (popH (19 + 1) 0 ![0, 0, 0, 0, 0, 0, out.length, 0])) (fun _ : Fin 1 => 0))
      (Fin.addCases (qA (19 + 1) (pre ++ frame (radRowRecC D digs p b0 s) ++ rest) (entryA (19 + 1) out B))
        (fun _ : Fin 1 => []))
      (Fin.addCases (qH (19 + 1) (pre.length + (2 * (radRowRecC D digs p b0 s).length + 1))
        (popH (19 + 1) q ![0, 0, 0, 0, 0, 0, (out ++ Rec.exprWord (radRefC D digs p b0 s)).length, 0]))
        (fun _ : Fin 1 => 0)) A' ∧
      A' (Fin.castAdd 1 (inQ (19 + 1))) = pre ++ frame (radRowRecC D digs p b0 s) ++ rest ∧
      A' (Fin.castAdd 1 (pQ (19 + 1) (eI (19 + 1) 6))) =
        NearCubicWires.RepairOrdinary.StablePartition.Workspace.overlay (out ++ Rec.exprWord (radRefC D digs p b0 s)) B) ∧
    (∀ σ : ℕ → Bool, IntExpression.eval (radRefC D digs p b0 s) σ =
      bitInt (decide (Rows.tupleResidue p b0 (fun d : Fin digs.length => repAt D digs true σ d)
        (fun d : Fin digs.length => repAt D digs false σ d) = (s : ZMod p)))) ∧
    radRowCostC D digs p b0 s hok ≤ (D.M + 1) ^ (2 * digs.length) * (128 * ((radRowRecC D digs p b0 s).length + 1) ^ 2) := by
  haveI : NeZero p := ⟨by omega⟩
  have hxlen : (radSpecs D digs hok).length = 2 * digs.length * (D.M + 1) := radSpecs_length D digs hok
  have hmp : (radSpecs D digs hok).map FSpec.poly = radFs D digs := by
    rw [radSpecs_poly D digs hok []]; rfl
  have hcapv : radCapC D digs p b0 = (2 * digs.length * (D.M + 1) * (4 * radRC D digs + 9) + 1) +
      (resLoopCost (radCs D digs p b0) + 3) + mselCost (radFs D digs) + incCost D.M (2 * digs.length) := rfl
  have hst : storeCost (radSpecs D digs hok) (radRC D digs) ≤ radCapC D digs p b0 := by
    have := storeCost_le (radSpecs D digs hok) (radRC D digs) (radSpecs_cost D digs hok)
    rw [hxlen] at this
    omega
  obtain ⟨A', hrun, hin, hout⟩ := radRow_step (negFam F35) D.M (2 * digs.length) (radCs D digs p b0) (radT digs p s)
    (radSpecs D digs hok) (by omega) (by simp [radCs]) hxlen pre rest out B (radRC D digs) (radRC D digs + 1)
    (radCapC D digs p b0) (by unfold radRC; omega) (radSpecs_cost D digs hok) le_rfl hst (by omega)
    (by rw [hmp]; omega) (by omega)
  have ho : radOut D.M (2 * digs.length) (radCs D digs p b0) (radT digs p s) ((radSpecs D digs hok).map FSpec.poly) =
      Rec.exprWord (radRefC D digs p b0 s) := by
    rw [hmp, radT_eq digs p s hs]
    exact radOut_eq digs.length D.M p b0 (radPp D digs) (radPm D digs) (s : ZMod p)
  rw [ho, radRowRecC_eq] at hrun
  rw [radRowRecC_eq] at hin
  rw [ho] at hout
  exact ⟨⟨_, A', hrun, hin, hout⟩, fun σ => radExpr_value D hnest digs hok p b0 (s : ZMod p) σ,
    radRowCost_le D digs p b0 s hok⟩

end

end NearCubicWires.WireExponent3_5.ListMachine.Row
