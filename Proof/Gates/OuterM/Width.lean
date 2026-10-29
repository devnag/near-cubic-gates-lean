import Proof.Gates.OuterM.WidthW
import Proof.Gates.Expand.PolyTabPack

set_option autoImplicit false

namespace NearCubicGates.Close.OuterM

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.Succinct NearCubicGates.Close.WordPrograms

def widthK (k A : ℕ) : ℕ := 600 * (k + 3) * (A + 2)

/-- The front's cost and the answer are linear in `N`. -/
theorem front_bounds (k A N : ℕ) :
    frontCost k A N + 60 * Outer.widthOf k A (2 ^ Nat.log 2 N) + 10 ≤ 271 * ((k + 3) * (A + 2) * (N + 1)) ∧
      Outer.widthOf k A (2 ^ Nat.log 2 N) ≤ 2 * ((k + 3) * (A + 2) * (N + 1)) := by
  set T := (k + 3) * (A + 2) * (N + 1) with hT
  have hcN : hc N ≤ N := hc_le N
  have hν : hc N - 1 ≤ N := by omega
  have hm : hc (cOf k N + 1) ≤ cOf k N + 1 := hc_le _
  have hq := q_eq k A N
  have hA1 : 1 ≤ (A + 2) := by omega
  have hN1 : N + 1 ≤ (k + 3) * (N + 1) := by nlinarith
  have hkN : (k + 3) * (N + 1) ≤ T := by rw [hT]; nlinarith
  have h5 : N + 1 ≤ T := hN1.trans hkN
  have h2 : cOf k N + 1 ≤ T := by
    have : cOf k N ≤ N * (k + 2) := Nat.mul_le_mul_right _ hν
    unfold cOf at *; nlinarith
  have h1 : (hc N - 1) * (8 * (k + 2) + 5) ≤ 8 * T := by
    have : (hc N - 1) * (8 * (k + 2) + 5) ≤ N * (8 * (k + 3)) := Nat.mul_le_mul hν (by omega)
    nlinarith
  have hAc : (cOf k N + 1) * (A + 1) ≤ T := by
    have : (cOf k N + 1) * (A + 1) ≤ (k + 3) * (N + 1) * (A + 1) := by
      apply Nat.mul_le_mul_right
      have : cOf k N ≤ N * (k + 2) := Nat.mul_le_mul_right _ hν
      unfold cOf at *; nlinarith
    rw [hT]; nlinarith
  have h3 : hc (cOf k N + 1) * (4 * A + 4) ≤ 4 * T := by
    have : hc (cOf k N + 1) * (4 * A + 4) ≤ (cOf k N + 1) * (4 * A + 4) := Nat.mul_le_mul_right _ hm
    nlinarith
  have hmA : hc (cOf k N + 1) * A + (cOf k N + 1) ≤ (cOf k N + 1) * (A + 1) := by
    have : hc (cOf k N + 1) * A ≤ (cOf k N + 1) * A := Nat.mul_le_mul_right _ hm
    nlinarith
  have h4 : A ≤ T := by
    have : A + 2 ≤ T := by rw [hT]; nlinarith
    omega
  have h6 : Outer.widthOf k A (2 ^ Nat.log 2 N) ≤ 2 * T := by
    rw [hq]
    omega
  refine ⟨?_, h6⟩
  unfold frontCost
  omega

theorem bitsCost_le (k A N : ℕ) : 2 * bitsCost k A N + 2 ≤ widthK k A * (N + 1) ^ 1 := by
  have h := (front_bounds k A N).1
  have hb := bits_length_le (Outer.widthOf k A (2 ^ Nat.log 2 N))
  have hK : widthK k A * (N + 1) ^ 1 = 600 * ((k + 3) * (A + 2) * (N + 1)) := by unfold widthK; ring
  rw [hK]; unfold bitsCost; omega

theorem unaryCost_le (k A N : ℕ) : 2 * unaryCost k A N + 2 ≤ widthK k A * (N + 1) ^ 1 := by
  have h := (front_bounds k A N).1
  have hK : widthK k A * (N + 1) ^ 1 = 600 * ((k + 3) * (A + 2) * (N + 1)) := by unfold widthK; ring
  rw [hK]; unfold unaryCost; omega

/-- The register capacity of a run on `x`. -/
def widthCap (k A : ℕ) (r : Σ N, BitInput N) : ℕ := r.1 + 2 * Outer.widthOf k A (2 ^ Nat.log 2 r.1) + 4

theorem ideal_facts (r : Σ N, BitInput N) :
    (Expand.PolyTab.idealStart 1 9 (List.ofFn r.2) (fun _ => 0)).st 0 = RepairOrdinary.frame (List.ofFn r.2) ∧
      (∀ i, (Expand.PolyTab.idealStart 1 9 (List.ofFn r.2) (fun _ => 0)).sh i = 0) ∧
      (∀ q, (Expand.PolyTab.idealStart 1 9 (List.ofFn r.2) (fun _ => 0)).val q = 0) ∧
      (Expand.PolyTab.idealStart 1 9 (List.ofFn r.2) (fun _ => 0)).st 1 = [] := by
  refine ⟨?_, fun _ => rfl, fun _ => rfl, ?_⟩ <;> simp [Expand.PolyTab.idealStart]

/-- **`q` in binary** (`sec:gadget-machine`, the exact native width): `x ↦ frame q.bits`, `q = q(2^{⌊log₂ |x|⌋})`. -/
noncomputable def widthBitsFn (k A : ℕ) : OrdinaryWordFunction (Σ N, BitInput N) (fun r => List.ofFn r.2)
    (fun r => RepairOrdinary.frame (Outer.widthOf k A (2 ^ Nat.log 2 r.1)).bits)
    (fun r => widthK k A * (r.1 + 1) ^ 1) :=
  Expand.PolyTab.wordFunction_of_ideal (widthBitsP k A) 1 (by decide) (widthCap k A) (fun _ _ => 0)
    (fun r => bitsCost k A r.1) (fun r => bitsCost_le k A r.1) (fun r => by
      refine ⟨rfl, ?_⟩
      obtain ⟨h0, hsh, hval, h1⟩ := ideal_facts r
      have := widthBitsP_spec (widthCap k A r) k A _ (List.ofFn r.2) h0 hsh hval h1
        (by simp [widthCap, List.length_ofFn])
      simpa [List.length_ofFn] using this)

/-- **`q` in unary** (`sec:gadget-machine`, the exact native width): `x ↦ 1^q`, `q = q(2^{⌊log₂ |x|⌋})`. -/
noncomputable def widthUnaryFn (k A : ℕ) : OrdinaryWordFunction (Σ N, BitInput N) (fun r => List.ofFn r.2)
    (fun r => List.replicate (Outer.widthOf k A (2 ^ Nat.log 2 r.1)) true)
    (fun r => widthK k A * (r.1 + 1) ^ 1) :=
  Expand.PolyTab.wordFunction_of_ideal (widthUnaryP k A) 1 (by decide) (widthCap k A) (fun _ _ => 0)
    (fun r => unaryCost k A r.1) (fun r => unaryCost_le k A r.1) (fun r => by
      refine ⟨rfl, ?_⟩
      obtain ⟨h0, hsh, hval, h1⟩ := ideal_facts r
      have := widthUnaryP_spec (widthCap k A r) k A _ (List.ofFn r.2) h0 hsh hval h1
        (by simp [widthCap, List.length_ofFn])
      simpa [List.length_ofFn] using this)

section
variable (mw : Outer.MWSource) {k : ℕ} {H : OrdinaryHierarchy (fun n => n ^ (k + 2))} {G : ℕ}
  (SV : Outer.SuccinctVerifier H G)

noncomputable def widthDonor : WidthDonor mw SV where
  K := widthK k (Outer.apad mw SV)
  word := widthBitsFn k (Outer.apad mw SV)
  unary := widthUnaryFn k (Outer.apad mw SV)

end

end NearCubicGates.Close.OuterM
