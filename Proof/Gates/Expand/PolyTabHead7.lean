import Proof.Gates.Expand.PolyTabHead6

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

variable (E : ExpandMachine) (a : WilliamsAlgorithm)

local notation "WSE" => WState (NSx (te E) (Qa a)) NRk

noncomputable def headABC : WMX (NSx (te E) (Qa a)) NRk :=
  .seq (phA1 E a) (.seq (phA2 E a) (.seq (phB E a) (phC E a)))

noncomputable def headABCCost (r : TabReq) : ℕ :=
  phA1Cost E r + 1 + (phA2Cost E r + 1 + (phBCost E r + 1 + phCCost E r))

def capABC (r : TabReq) : ℕ := capA1 r (E.expand ⟨r.V, r.F⟩) + capA2 E r + capB E r + capC E r

/-- Every stream the head writes before the constants. -/
noncomputable def UL : List (Fin (NSx (te E) (Qa a) + 1)) := sS 1 :: SA1 E a ++ SB E a ++ List.ofFn ubw ++ MSS

theorem mem_UL (x : Fin (NSx (te E) (Qa a) + 1)) (hx : x ∈ UL E a) :
    x.val = 47 ∨ x.val = 57 ∨ x.val = 58 ∨ x.val = 0 ∨ (65 ≤ x.val ∧ x.val ≤ 71) ∨ (86 ≤ x.val ∧ x.val ≤ 103) ∨
      (105 ≤ x.val ∧ x.val < 106 + te E) := by
  simp only [UL, List.cons_append, List.mem_cons, List.mem_append] at hx
  rcases hx with h | (((h | h) | h) | h)
  · subst h; simp
  · have := mem_SA1 E a x (List.mem_cons_of_mem _ h); omega
  · have := mem_SB E a x h; omega
  · obtain ⟨i, e⟩ := List.mem_ofFn.mp h; subst e; have := i.isLt; simp; omega
  · simp only [MSS, List.mem_append, List.mem_cons, List.mem_ofFn, List.not_mem_nil, or_false] at h
    rcases h with ((h | h | h | h | h) | ⟨i, h⟩) | ⟨i, h⟩
    all_goals first
      | (subst h; simp; done)
      | (subst h; simp; omega)
      | (subst h; have := i.isLt; simp; omega)

/-- The state after stage 9. -/
structure HC (r : TabReq) (τ : WSE) : Prop where
  z46 : τ.st (sZ 46) = recStream ((codeRecs (tsK E r)).map (binary (Wk E r + 1)))
  z46h : τ.sh (sZ 46) = 0
  z56 : τ.st (sZ 56) = recStream (coefRecs r.s (Wk E r) (tsK E r))
  z56h : τ.sh (sZ 56) = 0
  z57 : τ.st (sZ 57) = recStream ((hsK E r).map (binary (Wk E r + 1)))
  z57h : τ.sh (sZ 57) = 0
  bl : ∀ x, x ∉ UL E a → τ.st x = [] ∧ τ.sh x = 0
  y0 : ∀ q, (∀ j, q ≠ rX j) → τ.val q = 0
  r42 : τ.val (rX 42) = Wk E r + 1
  r44 : τ.val (rX 44) = Wdk E r + 1
  r41 : τ.val (rX 41) = Wdk E r
  r12 : τ.val (rX 12) = r.s
  r45 : τ.val (rX 45) = r.s + 1
  r11 : τ.val (rX 11) = r.k
  z : ∀ j : Fin 64, j.val ∈ [3, 4, 7, 31, 36, 51] → τ.val (rX j) = 0

theorem headABC_spec (r : TabReq) (cap : ℕ) (hcap : capABC E r ≤ cap) :
    Runs cap (headABC E a) (σI E a r) (headABCCost E r) (HC E a r) := by
  unfold capABC at hcap
  obtain ⟨τ1, e1, A1⟩ := phA1_spec E a r cap (by omega)
  obtain ⟨τ2, e2, g, P2, R2⟩ := phA2_spec E a r cap (by omega) τ1 A1
  have BI := bIn_of E a r τ1 τ2 A1 g _ P2 R2
  obtain ⟨τ3, e3, BE⟩ := phB_spec E a r cap (by omega) g τ2 BI
  obtain ⟨τ4, e4, σA, hA, S9⟩ := phC_spec E a r cap (by omega) g τ2 τ3 BI BE
  -- registers at τ4
  have rr : ∀ j : Fin 64, XR j → j.val ∉ [9, 2, 19, 26, 43, 20, 5, 32] → τ4.val (rX j) = g j := fun j hj hj' => by
    rw [S9.x j hj]
    have j32 : j ≠ 32 := fun e => hj' (by rw [e]; simp)
    rw [Function.update_of_ne j32]
    exact BE.rx j hj.1 (by simp at hj' ⊢; omega)
  -- streams at τ4
  have nU : ∀ x, x ∉ UL E a → x ∉ MSS ∧ x ∉ List.ofFn ubw ∧ x ∉ SB E a ∧ x ∉ sS 1 :: SA1 E a := fun x hx =>
    ⟨fun h => hx (by simp only [UL, List.cons_append, List.mem_cons, List.mem_append]; tauto),
      fun h => hx (by simp only [UL, List.cons_append, List.mem_cons, List.mem_append]; tauto),
      fun h => hx (by simp only [UL, List.cons_append, List.mem_cons, List.mem_append]; tauto),
      fun h => hx (by simp only [UL, List.cons_append, List.mem_cons, List.mem_append] at h ⊢; tauto)⟩
  have z57m : sZ 57 ∉ (MSS : List (Fin (NSx (te E) (Qa a) + 1))) := fun hm => by
    simp only [MSS, List.mem_append, List.mem_cons, List.mem_ofFn, List.not_mem_nil, or_false] at hm
    rcases hm with ((h | h | h | h | h) | ⟨i, h⟩) | ⟨i, h⟩ <;> (have := congrArg Fin.val h; simp at this; try omega)
  have z57w : sZ 57 ∉ List.ofFn (ubw (te := te E) (qa := Qa a)) := fun hm => by
    obtain ⟨i, e⟩ := List.mem_ofFn.mp hm; have := congrArg Fin.val e; simp at this; omega
  refine ⟨τ4, WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 e4)), ?_, S9.z46h, ?_, S9.z56h, ?_, ?_, fun x hx => ?_,
    fun q hq => ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_⟩
  · rw [S9.z46, rec46]
  · rw [S9.z56, rec56]
  · rw [S9.fr.st z57m, hA.st z57w, BE.z57]
  · rw [S9.fr.sh z57m, hA.sh z57w, BE.z57h]
  · obtain ⟨h1, h2, h3, h4⟩ := nU x hx
    rw [S9.fr.st h1, S9.fr.sh h1, hA.st h2, hA.sh h2, BE.fr.st h3, BE.fr.sh h3]; exact BI.bl x h4
  · have hq' : q ∉ (RXL : List (Fin NRk)) := fun hm => by
      simp only [RXL, List.mem_ofFn] at hm; obtain ⟨j, e⟩ := hm; exact hq j e.symm
    rw [S9.fr.val hq', hA.val (by simp), BE.fr.val hq']; exact BI.oth q hq
  · rw [rr 42 (by decide) (by decide), R2.h42]
  · rw [rr 44 (by decide) (by decide), R2.h44]
  · rw [rr 41 (by decide) (by decide), R2.h41]
  · rw [rr 12 (by decide) (by decide), R2.h12]
  · rw [rr 45 (by decide) (by decide), R2.h45]
  · rw [rr 11 (by decide) (by decide), R2.h11]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with h | h | h | h | h | h
    · have : j = 3 := Fin.ext h
      subst this; rw [rr 3 (by decide) (by decide), R2.z 3 (by decide)]
    · have : j = 4 := Fin.ext h
      subst this; rw [rr 4 (by decide) (by decide), R2.z 4 (by decide)]
    · have : j = 7 := Fin.ext h
      subst this; rw [rr 7 (by decide) (by decide), R2.z 7 (by decide)]
    · have : j = 31 := Fin.ext h
      subst this; rw [rr 31 (by decide) (by decide), R2.z 31 (by decide)]
    · have : j = 36 := Fin.ext h
      subst this; rw [rr 36 (by decide) (by decide), R2.z 36 (by decide)]
    · have : j = 51 := Fin.ext h
      subst this; rw [rr 51 (by decide) (by decide), R2.z 51 (by decide)]

end NearCubicGates.Close.Expand.PolyTab
