import Proof.Gates.Expand.Main2

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.Expand.Layout

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Expand

def clearG : WMX NS NR := .seq (clrR (GR 0)) (.seq (clrR (GR 1)) (.seq (clrR (GR 2)) (clrR (GR 4))))

def stageB : WMX NS NR := .seq (initL (GR 2) (GR 5) nbList) (.seq constB clearG)

def stageBCost (r : FormulaReq) : ℕ :=
  53 * (initCost (Wb2 r) + 1) + 1 + (constBCost (Wb2 r) r.1 (Wt r) r.2.degree + 1 +
    ((Lw r * (1 + 2) + 1) + 1 + ((Wt r * (1 + 2) + 1) + 1 + ((Wb2 r * (1 + 2) + 1) + 1 + ((Lw r + 2) * (1 + 2) + 1)))))

theorem wB_lt (V W Wb : ℕ) (hTW : 2 * 2 ^ V * 2 ^ W ≤ 2 ^ Wb) (j : Fin 53) : wB V W j < 2 ^ Wb := by
  have hV : 1 ≤ 2 ^ V := Nat.one_le_two_pow
  have hW : 1 ≤ 2 ^ W := Nat.one_le_two_pow
  have h1 : 2 ^ V * 2 ^ W < 2 ^ Wb := by nlinarith
  have h2 : 2 ^ W ≤ 2 ^ V * 2 ^ W := Nat.le_mul_of_pos_left _ hV
  have h3 : 2 ^ V ≤ 2 ^ V * 2 ^ W := Nat.le_mul_of_pos_right _ hW
  have h4 : 2 ^ (W - 1) ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h5 : (2 ^ V - 1) * 2 ^ W ≤ 2 ^ V * 2 ^ W := Nat.mul_le_mul_right _ (by omega)
  unfold wB; split_ifs <;> omega

/-- The stage-B cap. -/
def CapB (r : FormulaReq) (cap : ℕ) : Prop := 4 * Wb2 r + 4 * Wt r + 4 * r.1 + 4 * r.2.degree + 4 * Lw r + 20 ≤ cap

theorem stageB_spec (r : FormulaReq) (cap : ℕ) (σ : WState NS NR) (h : AState r σ) (hcap : CapB r cap)
    (hTW : 2 * 2 ^ r.1 * 2 ^ Wt r ≤ 2 ^ Wb2 r) (hW12 : Wb1 r ≤ Wb2 r) :
    Runs cap stageB σ (stageBCost r) (Ready r (Wt r) (Wb2 r)) := by
  unfold CapB at hcap
  obtain ⟨⟨w0, m0⟩, inp0, oth0, hd0, regs0, g10, g20, g30, d0, v0, y00, g00, g40⟩ := h
  have rz : ∀ q, q ∉ KeepA → σ.val q = 0 := regs0
  -- 1. every number stream at width Wb2
  refine Runs.seq (initL_spec cap (grN (by decide)) (Wb2 r) (by omega) nbList σ (fun X hX => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hX
      exact ⟨by rw [(m0 j).1]; simp [frame_length]; omega, (m0 j).2⟩) g20 (rz _ (by unfold KeepA; lay_ne)))
    (fun τ1 ⟨i1, f1, s1⟩ => ?_)
  have mz := mv_init (Wb2 r) σ τ1 i1 s1 (fun j => (m0 j).2)
  have vv1 : ∀ q, τ1.val q = σ.val q := fun q => f1.val (by simp)
  -- 2. the constants
  refine Runs.seq (constB_spec (cap := cap) r.2.degree mz (by rw [vv1]; exact rz _ (by unfold KeepA F0; lay_ne))
    (by rw [vv1]; exact rz _ (by unfold KeepA R0; lay_ne)) (by rw [vv1]; exact rz _ (by unfold KeepA; lay_ne))
    (by rw [vv1]; exact g30) (by rw [vv1]; exact v0) (by rw [vv1]; exact g10) (by unfold Wt; omega) hTW
    (by omega) (by unfold Wt at *; omega)) (fun τ2 ⟨c2, g32⟩ => ?_)
  -- 3. clear the glue registers
  have u2 : ∀ q, q ≠ GR 3 → τ2.val q = σ.val q := fun q hq => by rw [c2.regs q hq, vv1]
  refine Runs.seq ((rClrR cap (GR 0) τ2 (by rw [u2 _ (grN (by decide)), g00]; omega)).cost
    (le_of_eq (by rw [u2 _ (grN (by decide)), g00]))) (fun τ3 ⟨f3, z3⟩ => ?_)
  refine Runs.seq ((rClrR cap (GR 1) τ3 (by rw [f3.val (by lay_ne), u2 _ (grN (by decide)), g10]; omega)).cost
    (le_of_eq (by rw [f3.val (by lay_ne), u2 _ (grN (by decide)), g10]))) (fun τ4 ⟨f4, z4⟩ => ?_)
  refine Runs.seq ((rClrR cap (GR 2) τ4
    (by rw [f4.val (by lay_ne), f3.val (by lay_ne), u2 _ (grN (by decide)), g20]; omega)).cost (le_of_eq (by rw [f4.val (by lay_ne), f3.val (by lay_ne), u2 _ (grN (by decide)), g20])))
    (fun τ5 ⟨f5, z5⟩ => ?_)
  refine ((rClrR cap (GR 4) τ5
    (by rw [f5.val (by lay_ne), f4.val (by lay_ne), f3.val (by lay_ne), u2 _ (grN (by decide)), g40]; omega)).cost (le_of_eq (by rw [f5.val (by lay_ne), f4.val (by lay_ne),
    f3.val (by lay_ne), u2 _ (grN (by decide)), g40]))).post (fun τ6 ⟨f6, z6⟩ => ?_)
  have hS6 : ∀ x, τ6.st x = τ2.st x ∧ τ6.sh x = τ2.sh x := fun x =>
    ⟨by rw [f6.st (by simp), f5.st (by simp), f4.st (by simp), f3.st (by simp)],
     by rw [f6.sh (by simp), f5.sh (by simp), f4.sh (by simp), f3.sh (by simp)]⟩
  have hmv : MV NB (Wb2 r) (wB r.1 (Wt r)) τ6 := fun j =>
    ⟨by rw [(hS6 _).1]; exact (c2.mv j).1, by rw [(hS6 _).2]; exact (c2.mv j).2⟩
  have hO : ∀ x, x ∉ nbList → τ6.st x = σ.st x ∧ τ6.sh x = σ.sh x := fun x hx =>
    ⟨by rw [(hS6 x).1, (c2.strs x hx).1, f1.st hx], by rw [(hS6 x).2, (c2.strs x hx).2, f1.sh hx]⟩
  have hv6 : ∀ q, q ∉ [GR 0, GR 1, GR 2, GR 3, GR 4] → τ6.val q = σ.val q := fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    rw [f6.val (by simp [hq.2.2.2.2]), f5.val (by simp [hq.2.2.1]), f4.val (by simp [hq.2.1]),
      f3.val (by simp [hq.1]), u2 q hq.2.2.2.1]
  have hTW' := hTW
  have wl := wB_lt r.1 (Wt r) (Wb2 r) hTW
  have hUF : ∀ k : Fin 12, k.val < 3 → UF k ∉ nbList := fun k hk hm => by
    obtain ⟨j, hj⟩ := List.mem_ofFn.mp hm; exact NB_ne_rec j k hk hj
  have hW2 : 2 ≤ Wt r := by unfold Wt; omega
  have hpW : 2 * 2 ^ Wt r ≤ 2 ^ Wb2 r := le_trans (by
    calc 2 * 2 ^ Wt r = 2 * 1 * 2 ^ Wt r := by ring
      _ ≤ 2 * 2 ^ r.1 * 2 ^ Wt r := by gcongr; exact Nat.one_le_two_pow) hTW
  have hW1 : 2 ^ (Wt r) / 2 = 2 ^ (Wt r - 1) := by
    rw [show Wt r = Wt r - 1 + 1 by omega, pow_succ]; simp
  refine ⟨⟨by rw [(hO _ (hUF 0 (by decide))).2, (oth0 _ (hUF 0 (by decide)) (by lay_ne)).2],
      by rw [(hO _ (hUF 1 (by decide))).2, (oth0 _ (hUF 1 (by decide)) (by lay_ne)).2],
      by rw [(hO _ (hUF 2 (by decide))).2, (oth0 _ (hUF 2 (by decide)) (by lay_ne)).2],
      by rw [← NB_UF 3 (by decide)]; exact (hmv _).2,
      by rw [← NB_UF 3 (by decide), (hmv _).1]; simp [frame_length],
      ⟨_, by rw [← NB_UF 4 (by decide)]; exact hmv _⟩, ⟨_, by rw [← NB_UF 5 (by decide)]; exact hmv _⟩,
      ⟨_, by rw [← NB_UF 6 (by decide)]; exact hmv _⟩,
      by rw [← NB_UF 7 (by decide)]; simpa [wB] using hmv ⟨13, by decide⟩,
      by rw [← NB_UF 8 (by decide)]; simpa [wB] using hmv ⟨14, by decide⟩,
      ⟨_, by rw [← NB_UF 9 (by decide)]; exact hmv _⟩,
      by rw [← NB_UF 10 (by decide)]; simpa [wB] using hmv ⟨16, by decide⟩,
      fun k hk => by rw [hv6 _ (by lay_ne)]; exact rz _ (by unfold KeepA; simp at hk; rcases hk with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> lay_ne),
      by rw [hv6 _ (by lay_ne)]; exact v0⟩,
    by rw [hv6 _ (by lay_ne)]; exact d0, ⟨0, ?_⟩, by rw [hv6 _ (by lay_ne)]; exact y00,
    ⟨fun i => wB r.1 (Wt r) ⟨i.val + 21, by omega⟩, fun i => by rw [← NB_MB i]; exact hmv _,
      ⟨fun i => wl _, by simp [wB]; rw [Nat.sub_add_cancel Nat.one_le_two_pow]; exact hpW, by simp [wB], by simp [wB]⟩,
      ⟨by simp [wB], by simp [wB], by simp [wB], by simp [wB], by simp [wB], by simp [wB], by simp [wB]⟩,
      by simp [wB]⟩,
    ⟨fun i => wB r.1 (Wt r) ⟨i.val + 39, by omega⟩, fun i => by rw [← NB_PB i]; exact hmv _,
      ⟨by simp [wB], by simp [wB], by simp [wB], by simp [wB, hW1], by simp [wB]⟩, fun i => wl _⟩,
    ?_, ?_, ?_⟩
  · have hR6 : ∀ j, τ6.val (R j) = 0 := fun j => by
      rw [hv6 _ (by have := j.isLt; lay_ne)]; exact rz _ (by have := j.isLt; unfold KeepA; lay_ne)
    have hU0 : U 0 ∉ nbList := fun hm => by obtain ⟨j, hj⟩ := List.mem_ofFn.mp hm; exact NB_ne_0 j hj
    have e := evAt_of_mv (Wb2 r) (wB r.1 (Wt r)) τ6 hmv (frame (formulaWord r)) (by rw [(hO _ hU0).1]; exact inp0)
      (by rw [(hO _ hU0).2]; exact hd0) hR6 (by simp [wB]) (by simp [wB])
    simpa [wB] using e
  · have hOn : O ∉ nbList := fun hm => by obtain ⟨j, hj⟩ := List.mem_ofFn.mp hm; exact NB_ne_O j hj
    rw [(hO _ hOn).1, (oth0 _ hOn (by lay_ne)).1]
  · intro i
    by_cases hi : i ∈ nbList
    · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hi; exact (hmv j).2
    · rw [(hO i hi).2]
      by_cases h0 : i = U 0
      · subst h0; exact hd0
      · exact (oth0 i hi h0).2
  · intro q hq
    obtain ⟨k8, k10, ky⟩ := hq
    by_cases e0 : q = GR 0
    · subst e0; rw [f6.val (by lay_ne), f5.val (by lay_ne), f4.val (by lay_ne), z3]
    · by_cases e1 : q = GR 1
      · subst e1; rw [f6.val (by lay_ne), f5.val (by lay_ne), z4]
      · by_cases e2 : q = GR 2
        · subst e2; rw [f6.val (by lay_ne), z5]
        · by_cases e4 : q = GR 4
          · subst e4; exact z6
          · by_cases e3 : q = GR 3
            · subst e3; rw [f6.val (by lay_ne), f5.val (by lay_ne), f4.val (by lay_ne), f3.val (by lay_ne), g32]
            · rw [hv6 q (by simp [e0, e1, e2, e3, e4])]
              exact rz q (by simp [KeepA, e0, e1, e2, e3, e4, k8, k10, ky])

end NearCubicGates.Close.Expand.Layout
