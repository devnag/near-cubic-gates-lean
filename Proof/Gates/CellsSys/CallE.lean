import Proof.Gates.CellsSys.CallD

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Cells.SystemsPhase

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

variable {C : Ctx}

def cptsIn : St VV MM := forS a1I n1 cptB
def cptsP : St VV MM := forS a0I n0 cptsIn

def cptsInT : List (Fin VV) := a1I :: cptT
def cptsPT : List (Fin VV) := a0I :: cptsInT

/-- Row sums of a two-index family. -/
def rowS (f : ℕ → ℕ → ℕ) (a k : ℕ) : ℕ := ((List.range k).map (f a)).sum
def preS (f : ℕ → ℕ → ℕ) (N1 a : ℕ) : ℕ := ((List.range a).map (fun a' => rowS f a' N1)).sum

theorem sum_range_le (f : ℕ → ℕ) (k M : ℕ) (h : ∀ i < k, f i ≤ M) : ((List.range k).map f).sum ≤ k * M := by
  have := List.sum_le_card_nsmul ((List.range k).map f) M (fun x hx => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx; exact h i (List.mem_range.mp hi))
  simpa using this

theorem cfn_le (L : List ℕ) (K OP PI X0 Y0 X1 Y1 T0 W0 T1 W1 : ℕ) (md : ℕ → ℕ → ℕ) (a b : ℕ) :
    cfn L K OP PI X0 Y0 X1 Y1 T0 W0 T1 W1 md a b ≤ md a b := by
  unfold cfn; split_ifs <;> omega

theorem cptsIn_spec {e st : DS VV MM} {R : List Bool} {K OP PI X0 Y0 X1 Y1 N0 N1 T0 W0 T1 W1 Mx Bw : ℕ}
    {md : ℕ → ℕ → ℕ} (hN : CallN e K OP PI X0 Y0 X1 Y1 N0 N1 T0 W0 T1 W1 Mx Bw md C) (a : ℕ) (ha : a < N0)
    (h : CS e ((List.range N1).flatMap (rdW md a) ++ R) st) (h0 : st.env a0I = a)
    (hV : st.env vCnt = e.env vCnt + preS (cfn (e.ram sN) K OP PI X0 Y0 X1 Y1 T0 W0 T1 W1 md) N1 a) :
    Hs C cptsIn st (N1 * (cptCost Bw (e.ram sN).length + 4) + 4) (fun s' => CS e R s' ∧
      s'.env vCnt = e.env vCnt + preS (cfn (e.ram sN) K OP PI X0 Y0 X1 Y1 T0 W0 T1 W1 md) N1 (a + 1) ∧
      Fr st s' cptsInT) := by
  set f := cfn (e.ram sN) K OP PI X0 Y0 X1 Y1 T0 W0 T1 W1 md with hf
  have hN1 : st.env n1 = N1 := by rw [h.fr n1 (by decide) (by decide), hN.hn1]
  have hfM : ∀ a' < N0, ∀ b < N1, f a' b ≤ Mx := fun a' ha' b hb => (cfn_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans
    (hN.mx a' ha' b hb)
  have hpre : preS f N1 a ≤ a * (N1 * Mx) := sum_range_le _ a _ (fun a' ha' =>
    sum_range_le _ N1 Mx (fun b hb => hfM a' (by omega) b hb))
  have hroom := hN.room
  let I : ℕ → DS VV MM → Prop := fun k s =>
    CS e (((List.range N1).drop k).flatMap (rdW md a) ++ R) s ∧ s.env a0I = a ∧
      s.env vCnt = e.env vCnt + preS f N1 a + rowS f a k ∧ Fr st s cptsInT
  refine Hs.mono (forS_spec' (C := C) a1I n1 (by decide) cptB st N1 hN.wn1 I _
    (fun k s v ⟨i1, i2, i3, i4⟩ => ⟨i1.set (by decide) v, by rw [DS.set_env_ne _ _ (by decide)]; exact i2,
      by rw [DS.set_env_ne _ _ (by decide)]; exact i3, Fr.trans i4 (Fr.set s v (by decide))⟩)
    ⟨by simp only [List.drop_zero]; exact h, h0, by rw [hV]; simp [rowS], Fr.refl _ _⟩ hN1 ?_) le_rfl ?_
  · intro k hk s ⟨i1, i2, i3, i4⟩ hsk hsN
    rw [drop_range_cons' _ _ hk, List.flatMap_cons, List.append_assoc] at i1
    have hrow : rowS f a k ≤ k * Mx := sum_range_le _ k Mx (fun b hb => hfM a ha b (by omega))
    have hmd := hN.mx a ha k hk
    have hcnt : a * (N1 * Mx) + k * Mx + Mx ≤ N0 * N1 * Mx := by
      have h1 : a * N1 + k + 1 ≤ N0 * N1 := by
        have : (a + 1) * N1 ≤ N0 * N1 := Nat.mul_le_mul_right _ ha
        nlinarith
      have := Nat.mul_le_mul_right Mx h1
      nlinarith
    refine Hs.mono (cptB_spec hN a k ha hk i1 i2 hsk _ i3 (by omega)) le_rfl ?_
    rintro s' ⟨g1, g2, g3⟩
    refine ⟨⟨g2, by rw [g3 a0I (by decide)]; exact i2, ?_, Fr.trans i4 (g3.weaken (by decide))⟩,
      by rw [g3 a1I (by decide)]; exact hsk, by rw [g3 n1 (by decide)]; exact hsN⟩
    rw [g1]; unfold rowS; rw [List.range_succ, List.map_append, List.sum_append]; simp [hf]; ring
  · rintro s ⟨⟨i1, i2, i3, i4⟩, _, _⟩
    rw [List.drop_eq_nil_of_le (by simp), List.flatMap_nil, List.nil_append] at i1
    refine ⟨i1, ?_, i4⟩
    rw [i3]; unfold preS; rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; ring

theorem cptsP_spec {e st : DS VV MM} {R : List Bool} {K OP PI X0 Y0 X1 Y1 N0 N1 T0 W0 T1 W1 Mx Bw : ℕ}
    {md : ℕ → ℕ → ℕ} (hN : CallN e K OP PI X0 Y0 X1 Y1 N0 N1 T0 W0 T1 W1 Mx Bw md C)
    (h : CS e ((List.range N0).flatMap (fun a => (List.range N1).flatMap (rdW md a)) ++ R) st)
    (hV : st.env vCnt = e.env vCnt) :
    Hs C cptsP st (N0 * ((N1 * (cptCost Bw (e.ram sN).length + 4) + 4) + 4) + 4) (fun s' => CS e R s' ∧
      s'.env vCnt = e.env vCnt + preS (cfn (e.ram sN) K OP PI X0 Y0 X1 Y1 T0 W0 T1 W1 md) N1 N0 ∧
      Fr st s' cptsPT) := by
  set f := cfn (e.ram sN) K OP PI X0 Y0 X1 Y1 T0 W0 T1 W1 md with hf
  have hN0 : st.env n0 = N0 := by rw [h.fr n0 (by decide) (by decide), hN.hn0]
  let I : ℕ → DS VV MM → Prop := fun j s =>
    CS e (((List.range N0).drop j).flatMap (fun a => (List.range N1).flatMap (rdW md a)) ++ R) s ∧
      s.env vCnt = e.env vCnt + preS f N1 j ∧ Fr st s cptsPT
  refine Hs.mono (forS_spec' (C := C) a0I n0 (by decide) cptsIn st N0 hN.wn0 I _
    (fun k s v ⟨i1, i3, i4⟩ => ⟨i1.set (by decide) v, by rw [DS.set_env_ne _ _ (by decide)]; exact i3,
      Fr.trans i4 (Fr.set s v (by decide))⟩)
    ⟨by simp only [List.drop_zero]; exact h, by rw [hV]; simp [preS], Fr.refl _ _⟩ hN0 ?_) le_rfl ?_
  · intro j hj s ⟨i1, i3, i4⟩ hsj hsN
    rw [drop_range_cons' _ _ hj, List.flatMap_cons, List.append_assoc] at i1
    refine Hs.mono (cptsIn_spec hN j hj i1 hsj i3) le_rfl ?_
    rintro s' ⟨g1, g2, g3⟩
    exact ⟨⟨g1, g2, Fr.trans i4 (g3.weaken (by decide))⟩, by rw [g3 a0I (by decide)]; exact hsj,
      by rw [g3 n0 (by decide)]; exact hsN⟩
  · rintro s ⟨⟨i1, i3, i4⟩, _, _⟩
    rw [List.drop_eq_nil_of_le (by simp), List.flatMap_nil, List.nil_append] at i1
    exact ⟨i1, i3, i4⟩

end NearCubicGates.Close.Cells.SystemsPhase
