import Proof.Gates.Expand.PolyTabHead1
import Proof.Gates.Expand.PolyTabStage10c

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.CounterMachine NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.TabMachine
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairRepresentation

variable (E : ExpandMachine) (a : WilliamsAlgorithm)

noncomputable def phA2 : WMX (NSx (te E) (Qa a)) NRk := .seq (cmScan (sS 1)) (.seq st4 (.seq st6a (.seq st7a st8pre)))

structure A2Regs (r : TabReq) (g : Fin 64 → ℕ) : Prop where
  h10 : g 10 = r.n
  h11 : g 11 = r.k
  h12 : g 12 = r.s
  h13 : g 13 = r.B
  h14 : g 14 = r.G
  h18 : g 18 = r.V
  h19 : g 19 = 2 ^ r.k
  h33 : g 33 = Cm E r
  h40 : g 40 = Wk E r
  h41 : g 41 = Wdk E r
  h42 : g 42 = Wk E r + 1
  h44 : g 44 = Wdk E r + 1
  h45 : g 45 = r.s + 1
  h15 : g 15 = 2 * r.n + 3
  h9 : g 9 = (preN r).length
  h2 : g 2 = pN r + 1
  h25 : g 25 = pk r + 1
  h43 : g 43 = pV r + 1
  h26 : g 26 = r.V
  h27 : g 27 = r.k + r.s + 2
  z : ∀ j : Fin 64, j.val ∈ [0, 1, 3, 4, 5, 6, 7, 8, 16, 17, 20, 21, 22, 23, 24, 28, 29, 30, 31, 32, 34, 35, 36, 37,
    38, 39, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63] → g j = 0

theorem frame_termsN {V : ℕ} (P : Terms V) : frame (termsWord P) = encN (termsN P) ++ [false] := by
  rw [Codec.frame_eq_marks, termsWord_eq, encN_eq_marks]

theorem cmx_full (r : TabReq) : cmx (E.expand ⟨r.V, r.F⟩) (E.expand ⟨r.V, r.F⟩).length = Cm E r := by
  unfold cmx Cm; rw [List.take_length]

def capA2 (r : TabReq) : ℕ :=
  2 ^ ((termsWord (E.expand ⟨r.V, r.F⟩)).length + 1) + 8 * (r.V + (termsWord (E.expand ⟨r.V, r.F⟩)).length + 1) ^ 2 +
    4 * (Wdk E r + 2) ^ 2 + 2 ^ (Lt r + 1) + 20 * (Mh r + 1) ^ 2 + pk r + 2 * r.G + pN r + 2 ^ r.k + r.V + r.k + r.s + 20

noncomputable def phA2Cost (r : TabReq) : ℕ :=
  (Ctm (E.expand ⟨r.V, r.F⟩) + 1 + ((E.expand ⟨r.V, r.F⟩).length * (6 * (Ctm (E.expand ⟨r.V, r.F⟩) + 1) + 4) + 1)) +
    1 + ((36 * (C4 E r + 1) + 4) + 1 + ((20 * (Cst r + 1) + 1) + 1 + (11 * (Cst r + 1) + 1 + c8 r)))

theorem phA2_spec (r : TabReq) (cap : ℕ) (hcap : capA2 E r ≤ cap) (τ : WState (NSx (te E) (Qa a)) NRk)
    (h : A1End E a r τ) :
    Runs cap (phA2 E a) τ (phA2Cost E r) (fun ρ => ∃ g, PS τ (sS 1) [] (termsN (E.expand ⟨r.V, r.F⟩)) [false]
      (posT (E.expand ⟨r.V, r.F⟩) (E.expand ⟨r.V, r.F⟩).length) g ρ ∧ A2Regs E r g) := by
  unfold capA2 at hcap
  have q1 := Nat.two_pow_pos (termsWord (E.expand ⟨r.V, r.F⟩)).length
  have q2 := Nat.two_pow_pos (Lt r)
  have q3 := Nat.two_pow_pos r.k
  have p0 : PS τ (sS 1) [] (termsN (E.expand ⟨r.V, r.F⟩)) [false] 0 (f1 r) τ :=
    ⟨⟨by rw [h.s1, frame_termsN], by rw [h.s1h]; simp [encN]⟩, h.x, SameExcept.refl _ _ _⟩
  have hz : ScanZero (f1 r) := fun j hj => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
      (have : j = ⟨_, j.isLt⟩ := rfl; simp [f1, fB, Fin.ext_iff, h])
  obtain ⟨τ1, e1, p1⟩ := cmScan_spec cap (E.expand ⟨r.V, r.F⟩) τ (sS 1) [] [false] (f1 r) hz (by dsimp only; omega) τ p0
  rw [cmx_full] at p1
  have w4 : WeakWorker E r (Function.update (f1 r) 33 (Cm E r)) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [Function.update_apply, f1, fB]
  obtain ⟨τ2, e2, g2, p2, a40, a41, a42, a44, a45, ag⟩ := st4_spec cap E r w4 (by omega) p1
  have hH := hdr cap r (by omega)
  have q : ∀ j : Fin 64, j.val ∉ [40, 41, 42, 44, 45, 46, 47, 48, 49, 50] → j ≠ 33 → g2 j = f1 r j := fun j hj h33 => by
    rw [ag j hj, Function.update_of_ne h33]
  obtain ⟨τ3, e3, p3⟩ := st6a_spec cap r hH (by omega) (by rw [q 10 (by decide) (by decide)]; simp [f1, fB])
    (by rw [q 11 (by decide) (by decide)]; simp [f1, fB]) (by rw [q 12 (by decide) (by decide)]; simp [f1, fB])
    (by rw [q 14 (by decide) (by decide)]; simp [f1, fB]) (by rw [q 18 (by decide) (by decide)]; simp [f1, fB])
    (by rw [q 19 (by decide) (by decide)]; simp [f1, fB]) (by rw [q 15 (by decide) (by decide)]; simp [f1, fB])
    (by rw [q 16 (by decide) (by decide)]; simp [f1, fB]) (by rw [q 9 (by decide) (by decide)]; simp [f1, fB])
    (by rw [q 7 (by decide) (by decide)]; simp [f1, fB]) p2
  obtain ⟨τ4, e4, p4⟩ := st7a_spec cap r hH (by omega) (by simp [q 11 (by decide) (by decide), f1, fB])
    (by simp [q 12 (by decide) (by decide), f1, fB]) (by simp [q 14 (by decide) (by decide), f1, fB]) (by simp)
    (by simp [q 16 (by decide) (by decide), f1, fB]) (by simp [q 2 (by decide) (by decide), f1, fB])
    (by simp [q 7 (by decide) (by decide), f1, fB]) p3
  obtain ⟨τ5, e5, p5⟩ := st8pre_spec cap r p4 (by simp [q 14 (by decide) (by decide), f1, fB]) (by simp)
    (by simp [q 16 (by decide) (by decide), f1, fB]) (by simp [q 7 (by decide) (by decide), f1, fB])
    (by simp [q 25 (by decide) (by decide), f1, fB]) (by simp) (by simp [q 19 (by decide) (by decide), f1, fB])
    (by simp [q 18 (by decide) (by decide), f1, fB]) (by simp [q 11 (by decide) (by decide), f1, fB])
    (by simp [q 12 (by decide) (by decide), f1, fB]) (by simp [q 43 (by decide) (by decide), f1, fB])
    (by simp [q 26 (by decide) (by decide), f1, fB]) (by simp [q 27 (by decide) (by decide), f1, fB]) (by omega)
  refine ⟨τ5, WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 e5))), _, p5, ?_⟩
  have qq : ∀ j : Fin 64, j.val ∉ [40, 41, 42, 44, 45, 46, 47, 48, 49, 50, 33, 15, 9, 2, 25, 43, 26, 27] →
      f8 r (Function.update (Function.update (Function.update g2 15 (2 * r.n + 3)) 9 (preN r).length) 2 (pN r + 1)) j =
        f1 r j := fun j hj => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    have n : ∀ i : Fin 64, j.val ≠ i.val → j ≠ i := fun i h e => h (by rw [e])
    simp only [f8, Function.update_apply, if_neg (n 25 hj.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1),
      if_neg (n 43 hj.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), if_neg (n 26 hj.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1),
      if_neg (n 27 hj.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2), if_neg (n 2 hj.2.2.2.2.2.2.2.2.2.2.2.2.2.1),
      if_neg (n 9 hj.2.2.2.2.2.2.2.2.2.2.2.2.1), if_neg (n 15 hj.2.2.2.2.2.2.2.2.2.2.2.1)]
    exact q j (by simp; omega) (n 33 hj.2.2.2.2.2.2.2.2.2.2.1)
  have hzz : ∀ j : Fin 64, j.val ∈ [0, 1, 3, 4, 5, 6, 7, 8, 16, 17, 20, 21, 22, 23, 24, 28, 29, 30, 31, 32, 34, 35, 36,
      37, 38, 39, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63] →
      f8 r (Function.update (Function.update (Function.update g2 15 (2 * r.n + 3)) 9 (preN r).length) 2 (pN r + 1)) j =
        0 := by
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rw [qq j (by simp; omega)]
    rcases hj with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
      (have : j = ⟨_, j.isLt⟩ := rfl; simp [f1, fB, Fin.ext_iff, h])
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hzz⟩
  all_goals first
    | (rw [qq _ (by decide)]; simp [f1, fB]; done)
    | (simp only [f8, Function.update_apply]; simp; done)
    | (simp only [f8, Function.update_apply]; simp [a40, a41, a42, a44, a45, ag]; done)
    | (simp only [f8, Function.update_apply]; simp; rw [ag 33 (by decide)]; simp; done)

end NearCubicGates.Close.Expand.PolyTab
