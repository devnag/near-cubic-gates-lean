import Proof.Wire_3_5.PrimTTabSym

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimT
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm

section Many
variable {ns nr : ℕ} (cap : ℕ) (c : Fin nr)

/-- The scans of several native words, one after another. -/
def scanSeqW : List (Fin 6 ↪ Fin (ns + 1)) → WM ns nr
  | [] => .skip
  | S :: Ss => .seq (scanBodyW S c) (scanSeqW Ss)

theorem tabSeg_flatMap {n : ℕ} (Gs : List (List (NormalizedThresholdGate n))) :
    tabSeg Gs.flatten = (Gs.map tabSeg).flatten := by
  induction Gs with
  | nil => rfl
  | cons G Gs ih => simp [tabSeg_append, ih]

theorem tabH_append {n : ℕ} (G G' : List (NormalizedThresholdGate n)) : tabH (G ++ G') = tabH G + tabH G' := by
  unfold tabH; rw [tabSeg_append, List.length_append]

/-- One native word to scan: its roles, the natural `x`, the framed word `y`, the gate list. -/
structure ScanItem (ns n : ℕ) where
  S : Fin 6 ↪ Fin (ns + 1)
  x : ℕ
  y : List Bool
  G : List (NormalizedThresholdGate n)

def scanCosts {n : ℕ} : List (ScanItem ns n) → ℕ
  | [] => 0
  | it :: its => scanCost it.x it.y (tabH it.G) + 1 + scanCosts its

/-- **The scans of several native words**: the regions are appended in order; the words are only read. -/
theorem scanSeq_spec {n : ℕ} (S0 : Fin 6 ↪ Fin (ns + 1)) : ∀ (its : List (ScanItem ns n)) (a : List Bool) (m k : ℕ)
    (σ : WState ns nr), ScanSt S0 σ a m k → σ.val c = 0 →
    (∀ it ∈ its, ∀ i : Fin 6, i ≠ 0 → it.S i = S0 i) →
    (∀ it ∈ its, σ.st (it.S 0) = natWord it.x ++ (frame it.y ++ tabSeg it.G) ∧ σ.sh (it.S 0) = 0 ∧
      natBitLength it.x ≤ cap) →
    (its.map fun it => it.S 0).Nodup → (∀ it ∈ its, ∀ i : Fin 6, i ≠ 0 → it.S 0 ≠ S0 i) →
    ∃ τ, WExec cap (scanSeqW c (its.map (·.S))) σ τ (scanCosts its) ∧
      ScanSt S0 τ (a ++ tabSeg (its.map (·.G)).flatten) (m + tabH (its.map (·.G)).flatten)
        (k + ((its.map (·.G)).flatten).length) ∧
      τ.val c = 0 ∧ τ.cell = σ.cell ∧ (∀ it ∈ its, τ.st (it.S 0) = σ.st (it.S 0)) ∧
      (∀ j, (∀ it ∈ its, j ≠ it.S 0) → j ≠ S0 1 → j ≠ S0 2 → j ≠ S0 3 → j ≠ S0 4 → Same σ τ j) ∧
      (∀ q, q ≠ c → τ.val q = σ.val q)
  | [], a, m, k, σ, hs, hc, _, _, _, _ => by
    refine ⟨σ, WExec.skip σ, by simpa [tabSeg, tabH] using hs, hc, rfl, fun _ h => by simp at h,
      fun _ _ _ _ _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl⟩
  | it :: its, a, m, k, σ, hs, hc, hS, hW, hnd, hsep => by
    have hS1 := hS it (by simp)
    have hSc : it.S = S0 ∨ True := Or.inr trivial
    obtain ⟨hw, hwh, hk⟩ := hW it (by simp)
    have hsit : ScanSt it.S σ a m k := by
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hs
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        first | (rw [hS1 1 (by decide)]; assumption) | (rw [hS1 2 (by decide)]; assumption) |
          (rw [hS1 3 (by decide)]; assumption) | (rw [hS1 4 (by decide)]; assumption)
    obtain ⟨τ1, s1, hs1, w1, c1, cl1, o1, v1⟩ := scanBody_spec cap it.S c it.x it.y it.G a m k σ hsit hw hwh hc hk
    have hs1' : ScanSt S0 τ1 (a ++ tabSeg it.G) (m + tabH it.G) (k + it.G.length) := by
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hs1
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        first | (rw [← hS1 1 (by decide)]; assumption) | (rw [← hS1 2 (by decide)]; assumption) |
          (rw [← hS1 3 (by decide)]; assumption) | (rw [← hS1 4 (by decide)]; assumption)
    have hnd' : (its.map fun it => it.S 0).Nodup := (List.nodup_cons.mp hnd).2
    have hfresh : ∀ it' ∈ its, it'.S 0 ≠ it.S 0 := by
      intro it' h' e
      exact (List.nodup_cons.mp hnd).1 (List.mem_map.mpr ⟨it', h', e⟩)
    have oth : ∀ it' ∈ its, Same σ τ1 (it'.S 0) := by
      intro it' h'
      refine o1 _ (hfresh it' h') ?_ ?_ ?_ ?_
      all_goals first
        | (rw [hS1 1 (by decide)]; exact hsep it' (by simp [h']) 1 (by decide))
        | (rw [hS1 2 (by decide)]; exact hsep it' (by simp [h']) 2 (by decide))
        | (rw [hS1 3 (by decide)]; exact hsep it' (by simp [h']) 3 (by decide))
        | (rw [hS1 4 (by decide)]; exact hsep it' (by simp [h']) 4 (by decide))
    obtain ⟨τ, s2, hs2, c2, cl2, w2, o2, v2⟩ := scanSeq_spec S0 its (a ++ tabSeg it.G) (m + tabH it.G)
      (k + it.G.length) τ1 hs1' c1 (fun it' h' => hS it' (by simp [h']))
      (fun it' h' => by
        obtain ⟨e1, e2, e3⟩ := hW it' (by simp [h'])
        exact ⟨by rw [(oth it' h').1, e1], by rw [(oth it' h').2, e2], e3⟩)
      hnd' (fun it' h' => hsep it' (by simp [h']))
    refine ⟨τ, WExec.mono (WExec.seq s1 s2) (by simp [scanCosts]), ?_, c2, by rw [cl2, cl1], ?_, ?_, ?_⟩
    · have e1 : a ++ tabSeg it.G ++ tabSeg (its.map (·.G)).flatten = a ++ tabSeg ((it :: its).map (·.G)).flatten := by
        simp [tabSeg_append]
      have e2 : m + tabH it.G + tabH (its.map (·.G)).flatten = m + tabH ((it :: its).map (·.G)).flatten := by
        simp [tabH_append]; omega
      have e3 : k + it.G.length + ((its.map (·.G)).flatten).length = k + (((it :: its).map (·.G)).flatten).length := by
        simp; omega
      rw [← e1, ← e2, ← e3]; exact hs2
    · intro it' h'
      rcases List.mem_cons.mp h' with rfl | h''
      · rw [← w1]
        exact (o2 (it'.S 0) (fun it'' h3 => (hfresh it'' h3).symm) (hsep it' (by simp) 1 (by decide))
          (hsep it' (by simp) 2 (by decide)) (hsep it' (by simp) 3 (by decide)) (hsep it' (by simp) 4 (by decide))).1
      · rw [w2 it' h'', (oth it' h'').1]
    · intro j hj h1 h2 h3 h4
      have e0 : j ≠ it.S 0 := hj it (by simp)
      refine (o1 j e0 (by rw [hS1 1 (by decide)]; exact h1) (by rw [hS1 2 (by decide)]; exact h2)
        (by rw [hS1 3 (by decide)]; exact h3) (by rw [hS1 4 (by decide)]; exact h4)).trans'
        (o2 j (fun it' h' => hj it' (by simp [h'])) h1 h2 h3 h4)
    · intro q hq; rw [v2 q hq, v1 q]

end Many

end NearCubicWires.WireExponent3_5.PrimT
