import Proof.Gates.TermLoop.Gadget1

set_option autoImplicit false

namespace NearCubicGates.Close.TermLoop

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.CanonicalWitnessCodec
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP NearCubicGates.Close.Interfaces
open NearCubicGates.Close.Setup
open NearCubicGates.Close.Worker (width pcpp gadgets sysCount Opd model1 model2)
open NearCubicGates.Close.CheckedPCPP.LitDecode (litVar litNeg)

noncomputable section

variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams} (D : SetupData s P g)
variable {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ) (B : Outer.OuterGuess (width s g N))
  (jk : Fin (nsW D + 1) → List Bool)

/-- The register file after loading literal `k` into `R n, R n+1, R n+2`. -/
def loadL (v : Fin nrW → ℕ) (k : Fin 3) (n : Fin 40) (hn : n.val ≤ 3) : Fin nrW → ℕ :=
  Function.update (Function.update (Function.update v (regE n) (v (rS k))) (regE ⟨n.val + 1, by omega⟩) (v (rF k)))
    (regE ⟨n.val + 2, by omega⟩) (if v (rF k) ≠ 0 then v (rV k) else v (rD k))

/-- The register file after loading the helper into `R n`. -/
def loadH (v : Fin nrW → ℕ) (n : Fin 40) : Fin nrW → ℕ := Function.update v (regE n) (v rPB + v rA)

theorem regE_low_ne (j : Fin 40) (r : Fin nrW) (hj : j.val < 10) (hr : 10 ≤ r.val) : regE j ≠ r :=
  fin_ne (by rw [regE_val]; omega)

theorem litLoad_nodup (k : Fin 3) (n : Fin 40) (hn : n.val ≤ 3) (hn' : n = 0 ∨ n = 3) :
    [rS k, rF k, rV k, rD k, regE n, regE ⟨n.val + 1, by omega⟩, regE ⟨n.val + 2, by omega⟩, rLT].Nodup := by
  rcases hn' with rfl | rfl <;> fin_cases k <;> decide +revert

theorem litLoad_shape (cap : ℕ) (vi : List Bool) (wh : ℕ) (v : Fin nrW → ℕ) (k : Fin 3) (n : Fin 40) (hn : n.val ≤ 3)
    (hn' : n = 0 ∨ n = 3) (h0 : v (regE n) = 0) (h1 : v (regE ⟨n.val + 1, by omega⟩) = 0) (h2 : v (regE ⟨n.val + 2, by omega⟩) = 0)
    (hT : v rLT = 0) (hc : v (rS k) + v (rF k) + v (rV k) + v (rD k) ≤ cap) :
    WExec cap (litLoad D k n hn) (Shape D x bits pad B jk vi wh v) (Shape D x bits pad B jk vi wh (loadL v k n hn))
      (18 * v (rS k) + 3 + 1 + (18 * v (rF k) + 3 + 1 + (18 * (if v (rF k) ≠ 0 then v (rV k) else v (rD k)) + 4))) := by
  have hk := k.isLt
  have n9 : ∀ r : Fin nrW, 10 ≤ r.val → r ≠ regE 9 := fun r h => fin_ne (by rw [regE_val]; simp; omega)
  have m9 : ∀ j : Fin 40, j.val ≤ 5 → regE j ≠ regE 9 := fun j h => regE_ne9 j (by omega)
  have val : ∀ r : Fin nrW, r ≠ regE 9 → (Shape D x bits pad B jk vi wh v).val r = v r := fun r h => by
    simp only [shape_val]; rw [Function.update_of_ne h]
  have e := Worker.loadLit_spec (cap := cap) (rS k) (rF k) (rV k) (rD k) (regE n) (regE ⟨n.val + 1, by omega⟩)
    (regE ⟨n.val + 2, by omega⟩) rLT (litLoad_nodup k n hn hn')
    (Shape D x bits pad B jk vi wh v)
    (by rw [val _ (m9 n (by omega))]; exact h0) (by rw [val _ (m9 _ (by simp; omega))]; exact h1)
    (by rw [val _ (m9 _ (by simp; omega))]; exact h2) (by rw [val _ (n9 _ (by show 10 ≤ 74; omega))]; exact hT)
    (by rw [val _ (n9 _ (by rw [rS_val]; omega)), val _ (n9 _ (by rw [rF_val]; omega)),
      val _ (n9 _ (by rw [rV_val]; omega)), val _ (n9 _ (by rw [rD_val]; omega))]; exact hc)
  rw [val _ (n9 _ (by rw [rS_val]; omega)), val _ (n9 _ (by rw [rF_val]; omega)),
      val _ (n9 _ (by rw [rV_val]; omega)), val _ (n9 _ (by rw [rD_val]; omega))] at e
  rwa [shape_setv _ _ _ _ _ _ _ _ _ _ (m9 n (by omega)), shape_setv _ _ _ _ _ _ _ _ _ _ (m9 _ (by simp; omega)),
    shape_setv _ _ _ _ _ _ _ _ _ _ (m9 _ (by simp; omega))] at e

theorem helpLoad_shape (cap : ℕ) (vi : List Bool) (wh : ℕ) (v : Fin nrW → ℕ) (n : Fin 40) (hn : n = 2 ∨ n = 5)
    (h0 : v (regE n) = 0) (hT : v rLT = 0) (hc : v rPB + v rA ≤ cap) :
    WExec cap (helpLoad D n) (Shape D x bits pad B jk vi wh v) (Shape D x bits pad B jk vi wh (loadH v n))
      (18 * v rPB + 3 + 1 + (18 * v rA + 3)) := by
  have n9 : ∀ r : Fin nrW, 10 ≤ r.val → r ≠ regE 9 := fun r h => fin_ne (by rw [regE_val]; simp; omega)
  have m9 : regE n ≠ regE 9 := regE_ne9 n (by rcases hn with rfl | rfl <;> decide)
  have val : ∀ r : Fin nrW, r ≠ regE 9 → (Shape D x bits pad B jk vi wh v).val r = v r := fun r h => by
    simp only [shape_val]; rw [Function.update_of_ne h]
  have e := Worker.loadHelper_spec (cap := cap) rPB rA (regE n) rLT (by rcases hn with rfl | rfl <;> decide)
    (Shape D x bits pad B jk vi wh v) (by rw [val _ m9]; exact h0) (by rw [val _ (n9 _ (by show 10 ≤ 74; omega))]; exact hT)
    (by rw [val _ (n9 _ (by rw [rPB_val]; omega)), val _ (n9 _ (by rw [rA_val]; omega))]; exact hc)
  rw [val _ (n9 _ (by rw [rPB_val]; omega)), val _ (n9 _ (by rw [rA_val]; omega)),
    shape_setv _ _ _ _ _ _ _ _ _ _ m9] at e
  exact e

/-! ## The loaded descriptors -/

section Desc
variable (i : ℕ)

theorem vC_S (k : Fin 3) : vC D x bits pad B jk i (rS k) = litNeg (clauseOf s P g x B i k) := by
  fin_cases k <;> rfl
theorem vC_V (k : Fin 3) : vC D x bits pad B jk i (rV k) = litVar (clauseOf s P g x B i k) := by
  fin_cases k <;> rfl
theorem vC_D (k : Fin 3) : vC D x bits pad B jk i (rD k) = litVar (clauseOf s P g x B i k) - sysCount s P g x B := by
  fin_cases k <;> rfl
theorem vC_F (k : Fin 3) : vC D x bits pad B jk i (rF k) = sysCount s P g x B - litVar (clauseOf s P g x B i k) := by
  fin_cases k <;> rfl
theorem vC_PB : vC D x bits pad B jk i rPB = (pcpp s P g x B).proofBits := rfl
theorem vC_A : vC D x bits pad B jk i rA = i := rfl

theorem litNeg_le_one {a : ℕ} (l : Literal a) : litNeg l ≤ 1 := by cases l <;> simp [litNeg]

/-- The descriptor in `R n, R n+1, R n+2` after loading literal `k`. -/
theorem loadOpd_lit (v : Fin nrW → ℕ) (k : Fin 3) (n : Fin 40) (hn : n.val ≤ 3)
    (hS : v (rS k) = litNeg (clauseOf s P g x B i k)) (hV : v (rV k) = litVar (clauseOf s P g x B i k))
    (hD : v (rD k) = litVar (clauseOf s P g x B i k) - sysCount s P g x B)
    (hF : v (rF k) = sysCount s P g x B - litVar (clauseOf s P g x B i k)) :
    (⟨decide (loadL v k n hn (regE n) ≠ 0), decide (loadL v k n hn (regE ⟨n.val + 1, by omega⟩) ≠ 0),
      loadL v k n hn (regE ⟨n.val + 2, by omega⟩)⟩ : Opd) = litOpd s P g x B i k := by
  have a1 : regE n ≠ regE ⟨n.val + 1, by omega⟩ := regE_ne _ _ (fun e => by have := congrArg Fin.val e; simp at this)
  have a2 : regE n ≠ regE ⟨n.val + 2, by omega⟩ := regE_ne _ _ (fun e => by have := congrArg Fin.val e; simp at this)
  have a3 : regE ⟨n.val + 1, by omega⟩ ≠ regE ⟨n.val + 2, by omega⟩ :=
    regE_ne _ _ (fun e => by have := congrArg Fin.val e; simp at this)
  simp only [loadL, Function.update_self, Function.update_of_ne a2, Function.update_of_ne a1,
    Function.update_of_ne a3, hS, hV, hD, hF, litOpd]
  congr 1
  · simp only [decide_eq_decide]; omega
  · by_cases h : litVar (clauseOf s P g x B i k) < sysCount s P g x B
    · rw [if_pos (by omega), if_pos h]
    · rw [if_neg (by omega), if_neg h]

end Desc

end

end NearCubicGates.Close.TermLoop
