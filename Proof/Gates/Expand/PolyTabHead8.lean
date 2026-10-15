import Proof.Gates.Expand.PolyTabHead7

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
open NearCubicWires.RepairRepresentation
open StablePartition.Workspace (overlay)

variable (E : ExpandMachine) (a : WilliamsAlgorithm)

local notation "WSE" => WState (NSx (te E) (Qa a)) NRk

/-- **The head**: everything before the cut machine. -/
noncomputable def headP : WMX (NSx (te E) (Qa a)) NRk := .seq (headABC E a) (.seq phD1 phD2)

noncomputable def headCost (r : TabReq) : ℕ :=
  headABCCost E r + 1 + (phD1Cost (Wk E r + 1) (Wdk E r + 1) + 1 + phD2Cost r.s r.k (Wdk E r))

/-- The head's register capacity (it also covers the tail's caps). -/
noncomputable def capH (r : TabReq) : ℕ :=
  capABC E r + 2 * (Wdk E r + 1) + 2 + 2 * r.s + r.k + Wdk E r + 10 + capk E r + 2 ^ (2 * (r.s + Wdk E r + 10)) +
    capSk E r + 2 * ((r.s + 1) * (Wk E r + 1)) + 1

theorem nUL_val (x : Fin (NSx (te E) (Qa a) + 1)) (h : x.val ≠ 47 ∧ x.val ≠ 57 ∧ x.val ≠ 58 ∧ x.val ≠ 0 ∧
    (x.val < 65 ∨ 71 < x.val) ∧ (x.val < 86 ∨ 103 < x.val) ∧ (x.val < 105 ∨ 106 + te E ≤ x.val)) : x ∉ UL E a :=
  fun hm => by have := mem_UL E a x hm; omega

theorem sZ_nUL (i : Fin 64) (hi : i.val ∉ [46, 56, 57]) : sZ i ∉ UL E a := by
  apply nUL_val; simp at hi ⊢; have := i.isLt; omega

theorem sZ_nconst (i : Fin 64) (hi : i ∉ constL) : sZ (te := te E) (qa := Qa a) i ∉ constL.map sZ := sZ_nm i _ hi

theorem head_spec (r : TabReq) (cap : ℕ) (hcap : capH E r ≤ cap) :
    Runs cap (headP E a) (σI E a r) (headCost E r) (TailPre E a r cap) := by
  unfold capH at hcap
  have hWW := Wk_le_Wdk E r
  have hW10 := Wk_ge E r
  have hWd := Wdk_succ E r
  have q0 := Nat.two_pow_pos (2 * (r.s + Wdk E r + 10))
  obtain ⟨τ4, e4, H⟩ := headABC_spec E a r cap (by omega)
  obtain ⟨τ5, e5, D1, r31, F5⟩ := phD1_spec cap (Wk E r + 1) (Wdk E r + 1) (by omega) (by omega) (by omega) τ4
    (fun i hi => H.bl _ (sZ_nUL E a i (by revert i; decide))) H.r42 H.r44 (H.z 51 (by decide)) (H.z 3 (by decide))
    (H.z 4 (by decide)) (H.z 7 (by decide)) (H.z 31 (by decide))
  have v5 : ∀ j : Fin 64, j ≠ 31 → τ5.val (rX j) = τ4.val (rX j) := fun j hj => F5.val (nm1 (rX_ne hj))
  have y5 : ∀ q, (∀ j, q ≠ rX j) → τ5.val q = 0 := fun q hq => by rw [F5.val (nm1 (hq 31))]; exact H.y0 q hq
  obtain ⟨τ6, e6, st6, c6, v6, y13, y32, y41, y66, y84, y89, y106, y105, y107, x36⟩ := phD2_spec cap r.s r.k (Wdk E r)
    τ5 (by rw [v5 12 (by decide), H.r12]) (by rw [v5 45 (by decide), H.r45]) (by rw [v5 11 (by decide), H.r11])
    (by rw [v5 41 (by decide), H.r41]) (by rw [v5 7 (by decide), H.z 7 (by decide)])
    (by rw [v5 36 (by decide), H.z 36 (by decide)]) (fun j _ => y5 _ (fun i e => by
      have := congrArg Fin.val e; simp at this; omega)) (by omega)
  -- facts at τ6
  have yY : ∀ j : Fin 112, j.val ∉ [13, 32, 41, 66, 84, 89, 106, 105, 107] → τ6.val (rY j) = 0 := fun j hj => by
    have hn : rY j ∉ (RD2 : List (Fin NRk)) := by
      simp only [RD2, List.mem_cons, List.not_mem_nil, or_false, not_or]
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro e <;> have := congrArg Fin.val e <;> simp at this <;>
        omega
    rw [v6 _ hn]; exact y5 _ (fun i e => by have := congrArg Fin.val e; simp at this; omega)
  have sb6 : ∀ x, x ∉ UL E a → x ∉ constL.map sZ → τ6.st x = [] ∧ τ6.sh x = 0 := fun x h1 h2 => by
    rw [(st6 x).1, (st6 x).2, F5.st h2, F5.sh h2]; exact H.bl x h1
  have zb : ∀ i : Fin 64, i.val ∉ [46, 56, 57] → i ∉ constL → τ6.st (sZ i) = [] ∧ τ6.sh (sZ i) = 0 := fun i h1 h2 =>
    sb6 _ (sZ_nUL E a i h1) (sZ_nconst E a i h2)
  have n6 : ∀ {i : Fin 64} {W v : ℕ}, NumOn τ5 (sZ i) W v → NumOn τ6 (sZ i) W v := fun h =>
    ⟨by rw [(st6 _).1]; exact h.1, by rw [(st6 _).2]; exact h.2⟩
  have hWd' : (r.s + 1) * (Wk E r + 1) = Wdk E r + 1 := hWd.symm
  have hb : ∀ x : Fin (NSx (te E) (Qa a) + 1), 106 + te E ≤ x.val → τ6.st x = [] ∧ τ6.sh x = 0 := fun x hx =>
    sb6 x (nUL_val E a x (by omega)) (fun hm => by
      obtain ⟨i, _, e⟩ := List.mem_map.mp hm; have := congrArg Fin.val e; simp at this; omega)
  refine ⟨τ6, WXExec.seq e4 (WXExec.seq e5 e6), ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ⟨[], ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, y105, y106, ?_, fun i => hb _ (by rw [sP_val]; unfold te; omega), fun j => hb _ ?_, hb _ (by rw [sOUT_val]; unfold te; omega),
    fun j => ?_,
    by omega, by omega, by omega⟩
  -- GRest
  · exact fun i hi => ⟨0, n6 (D1.w1 i hi)⟩
  · exact fun i hi => ⟨0, by rw [hWd']; exact n6 (D1.wc i hi)⟩
  · exact n6 D1.c20
  · exact n6 D1.c21
  · exact n6 D1.c53
  · rw [hWd']; exact n6 D1.c26
  · rw [hWd']; exact n6 D1.c44
  · rw [hWd']; exact n6 D1.c45
  · exact n6 D1.c55
  · intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ⟨(zb 3 (by decide) (by decide)).2, by rw [(zb 3 (by decide) (by decide)).1]; simp⟩
    · exact ⟨(zb 47 (by decide) (by decide)).2, by rw [(zb 47 (by decide) (by decide)).1]; simp⟩
  · intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ⟨(zb 24 (by decide) (by decide)).2, by rw [(zb 24 (by decide) (by decide)).1]; simp⟩
    · exact ⟨(zb 33 (by decide) (by decide)).2, by rw [(zb 33 (by decide) (by decide)).1]; simp⟩
  · intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl
    · exact (zb 0 (by decide) (by decide)).2
    · exact (zb 2 (by decide) (by decide)).2
    · exact (zb 30 (by decide) (by decide)).2
    · exact (zb 31 (by decide) (by decide)).2
    · exact (zb 32 (by decide) (by decide)).2
  · intro j hj; exact yY j (by revert j; decide)
  · exact y13
  · exact y32
  · exact y41
  · exact y66
  · exact y84
  · exact y89
  · omega
  -- CutRest
  · exact yY 98 (by decide)
  · exact yY 99 (by decide)
  · exact yY 44 (by decide)
  · exact yY 47 (by decide)
  · rw [(st6 _).1, F5.st (sZ_nconst E a 46 (by decide)), H.z46, List.append_nil]
  · rw [(st6 _).2, F5.sh (sZ_nconst E a 46 (by decide)), H.z46h]
  · exact (zb 43 (by decide) (by decide)).2
  · rw [(zb 43 (by decide) (by decide)).1]; simp
  · exact (zb 54 (by decide) (by decide)).2
  · rw [(zb 54 (by decide) (by decide)).1]; simp
  · exact ⟨by rw [(zb 34 (by decide) (by decide)).1]; simp [overlay], by rw [(zb 34 (by decide) (by decide)).2]; rfl,
      by rw [yY 56 (by decide)]; rfl⟩
  · exact yY 74 (by decide)
  · exact yY 77 (by decide)
  -- the rest of TailPre
  · rw [(st6 _).1, F5.st (sZ_nconst E a 56 (by decide)), H.z56]
  · rw [(st6 _).2, F5.sh (sZ_nconst E a 56 (by decide)), H.z56h]
  · rw [(st6 _).1, F5.st (sZ_nconst E a 57 (by decide)), H.z57]
  · rw [(st6 _).2, F5.sh (sZ_nconst E a 57 (by decide)), H.z57h]
  · exact yY 100 (by decide)
  · exact yY 101 (by decide)
  · exact yY 102 (by decide)
  · exact yY 103 (by decide)
  · exact yY 104 (by decide)
  · exact yY 108 (by decide)
  · exact yY 109 (by decide)
  · exact y107
  · rw [sQ_val]; unfold qv te; split_ifs <;> omega
  · have hn : rB j ∉ (RD2 : List (Fin NRk)) := by
      simp only [RD2, List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro e <;> have := congrArg Fin.val e <;> simp at this <;>
        omega
    rw [v6 _ hn]; exact y5 _ (fun i e => by have := congrArg Fin.val e; simp at this; omega)

end NearCubicGates.Close.Expand.PolyTab
