import Proof.Gates.TermLoop.Step
import Proof.Gates.TermLoop.Values

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
open NearCubicGates.Close.Worker.Format (readField)

noncomputable section

variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams} (D : SetupData s P g)
variable {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ) (B : Outer.OuterGuess (width s g N))
  (jk : Fin (nsW D + 1) → List Bool)
variable {B1 B2 : ℕ} (ctr : Counter B1 B2) (ω : ℚ)

theorem sysCount_eq : sysCount s P g x B = width s g N + P.code.length (width s g N) := rfl

/-! ## Register files -/

/-- The register file at the start of pass `i`. -/
def v0 (i : ℕ) : Fin nrW → ℕ :=
  Function.update (Function.update (LoopEntry D N x bits pad B jk).val rA i) rLC (gadgets s g N - i - 1)

/-- After the front end. -/
def vF (i : ℕ) : Fin nrW → ℕ :=
  let cl := clauseOf s P g x B i
  Function.update (Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (v0 D x bits pad B jk i)
    48 (litVar (cl 0))) 49 (litVar (cl 1))) 50 (litVar (cl 2)))
    51 (litNeg (cl 0))) 52 (litNeg (cl 1))) 53 (litNeg (cl 2)))
    54 (pcpp s P g x B).proofBits) 55 (pcpp s P g x B).randomBits

/-- After the classification. -/
def vC (i : ℕ) : Fin nrW → ℕ :=
  let V := fun k : Fin 3 => litVar (clauseOf s P g x B i k)
  let SC := sysCount s P g x B
  Function.update (Function.update (Function.update (Function.update (Function.update (Function.update
    (vF D x bits pad B jk i)
    66 (V 0 - SC)) 67 (SC - V 0)) 68 (V 1 - SC)) 69 (SC - V 1)) 70 (V 2 - SC)) 71 (SC - V 2)

/-- `LoopPre` is a shape. -/
theorem loopPre_eq (i : ℕ) :
    LoopPre D ctr ω x bits pad B jk i =
      Shape D x bits pad B jk (viOf s P g x bits pad B ctr ω i)
        (fieldPos (guessWord N bits pad) (fieldsStart s P g x bits pad B) (10 * i)) (v0 D x bits pad B jk i) := by
  unfold LoopPre
  rw [loopIter_eq, shape_setv D x bits pad B jk _ _ _ rLC (by decide), Function.update_idem]
  rfl

/-! ## Register lookups -/

@[simp] theorem rLC_val : (rLC : Fin nrW).val = 46 := rfl
@[simp] theorem rA_val : (rA : Fin nrW).val = 45 := rfl
@[simp] theorem rPB_val : (rPB : Fin nrW).val = 47 := rfl
@[simp] theorem rSC_val : (rSC : Fin nrW).val = 44 := rfl
@[simp] theorem regE_val (j : Fin 40) : (regE j).val = j.val := rfl

theorem v0_lt (i : ℕ) (r : Fin nrW) (h48 : 48 ≤ r.val) : v0 D x bits pad B jk i r = 0 := by
  have h1 : r ≠ rLC := fin_ne (by rw [rLC_val]; omega)
  have h2 : r ≠ rA := fin_ne (by rw [rA_val]; omega)
  simp only [v0, Function.update_of_ne h1, Function.update_of_ne h2, loopEntry_val]
  have : ¬ r.val = 6 ∧ ¬ r.val = 7 ∧ ¬ r.val = 8 ∧ ¬ r.val = 9 ∧ ¬ r.val = 40 ∧ ¬ r.val = 41 ∧ ¬ r.val = 42 ∧
    ¬ r.val = 43 ∧ ¬ r.val = 44 ∧ ¬ r.val = 46 ∧ ¬ r.val = 47 := by omega
  simp [this]

theorem v0_small (i : ℕ) (j : Fin 40) (h : 10 ≤ j.val) : v0 D x bits pad B jk i (regE j) = 0 := by
  have h1 : regE j ≠ rLC := fin_ne (by rw [rLC_val, regE_val]; omega)
  have h2 : regE j ≠ rA := fin_ne (by rw [rA_val, regE_val]; omega)
  simp only [v0, Function.update_of_ne h1, Function.update_of_ne h2, loopEntry_val]
  have hv : (regE j).val = j.val := rfl
  have : ¬ j.val = 6 ∧ ¬ j.val = 7 ∧ ¬ j.val = 8 ∧ ¬ j.val = 9 ∧ ¬ j.val = 40 ∧ ¬ j.val = 41 ∧ ¬ j.val = 42 ∧
    ¬ j.val = 43 ∧ ¬ j.val = 44 ∧ ¬ j.val = 46 ∧ ¬ j.val = 47 := by have := j.isLt; omega
  simp [hv, this]

theorem v0_ops (i : ℕ) (j : Fin 40) (h : j.val < 6) : v0 D x bits pad B jk i (regE j) = 0 := by
  have h1 : regE j ≠ rLC := fin_ne (by rw [rLC_val, regE_val]; omega)
  have h2 : regE j ≠ rA := fin_ne (by rw [rA_val, regE_val]; omega)
  simp only [v0, Function.update_of_ne h1, Function.update_of_ne h2, loopEntry_val]
  have hv : (regE j).val = j.val := rfl
  have : ¬ j.val = 6 ∧ ¬ j.val = 7 ∧ ¬ j.val = 8 ∧ ¬ j.val = 9 ∧ ¬ j.val = 40 ∧ ¬ j.val = 41 ∧ ¬ j.val = 42 ∧
    ¬ j.val = 43 ∧ ¬ j.val = 44 ∧ ¬ j.val = 46 ∧ ¬ j.val = 47 := by omega
  simp [hv, this]

/-! ## The front end on a shape -/

theorem frontR_eq (k : Fin 18) : (frontR k).val = if k.val = 0 then 45 else 47 + k.val := by
  fin_cases k <;> rfl

theorem shape_sh_J (vi : List Bool) (wh : ℕ) (v : Fin nrW → ℕ) :
    (Shape D x bits pad B jk vi wh v).sh (sJ D) = 0 := by
  have := sJ_range D
  exact shape_sh_other D x bits pad B jk _ _ _ _ (fin_ne (by rw [sWT_val]; omega)) (fin_ne (by rw [sVI_val]; omega))

theorem shape_st_J (vi : List Bool) (wh : ℕ) (v : Fin nrW → ℕ) :
    (Shape D x bits pad B jk vi wh v).st (sJ D) = (pcpp s P g x B).word := by
  have := sJ_range D
  rw [shape_st_other D x bits pad B jk _ _ _ _ (fin_ne (by rw [sVI_val]; omega)), loopEntry_st_J]

theorem v0_rA (i : ℕ) : v0 D x bits pad B jk i rA = i := by
  simp only [v0]; rw [Function.update_of_ne (by decide), Function.update_self]

/-- **The front end on a shape.** -/
theorem front_shape (cap : ℕ) (i : ℕ) (vi : List Bool) (wh : ℕ)
    (hcap : 16 * ((pcpp s P g x B).word.length + i + sysCount s P g x B + (pcpp s P g x B).proofBits + 2) ≤ cap) :
    WXExec cap (ClauseFront.frontW (sJ D) frontR) (Shape D x bits pad B jk vi wh (v0 D x bits pad B jk i))
      (Shape D x bits pad B jk vi wh (vF D x bits pad B jk i))
      (ClauseFront.frontCost ((pcpp s P g x B).word.length + i + sysCount s P g x B + (pcpp s P g x B).proofBits)) := by
  have n9 : ∀ k : Fin 18, frontR k ≠ regE 9 := fun k => fin_ne (by rw [frontR_eq, regE_val]; split_ifs <;> omega)
  have e := ClauseFront.front_exec (cap := cap) (sJ D) frontR (pcpp s P g x B) i
    (Shape D x bits pad B jk vi wh (v0 D x bits pad B jk i))
    (by rw [shape_st_J]; exact RdEq.refl _) (shape_sh_J D x bits pad B jk _ _ _)
    (by simp only [shape_val]; rw [Function.update_of_ne (n9 0)]; exact v0_rA D x bits pad B jk i)
    (by
      intro k hk
      simp only [shape_val]; rw [Function.update_of_ne (n9 k)]
      apply v0_lt
      rw [frontR_eq]; have : k.val ≠ 0 := fun h => hk (Fin.ext h); simp only [this, if_false]; omega)
    hcap
  refine WXExec.cast cap e ?_ le_rfl
  unfold ClauseFront.frontState
  simp only
  rw [shape_setv _ _ _ _ _ _ _ _ _ _ (n9 1), shape_setv _ _ _ _ _ _ _ _ _ _ (n9 2), shape_setv _ _ _ _ _ _ _ _ _ _ (n9 3),
    shape_setv _ _ _ _ _ _ _ _ _ _ (n9 4), shape_setv _ _ _ _ _ _ _ _ _ _ (n9 5), shape_setv _ _ _ _ _ _ _ _ _ _ (n9 6),
    shape_setv _ _ _ _ _ _ _ _ _ _ (n9 7), shape_setv _ _ _ _ _ _ _ _ _ _ (n9 8)]
  rfl

/-! ## The classification on a shape -/

theorem vF_V (i : ℕ) (k : Fin 3) : vF D x bits pad B jk i (rV k) = litVar (clauseOf s P g x B i k) := by
  fin_cases k <;> rfl

theorem vF_S (i : ℕ) (k : Fin 3) : vF D x bits pad B jk i (rS k) = litNeg (clauseOf s P g x B i k) := by
  fin_cases k <;> rfl

theorem vF_SC (i : ℕ) : vF D x bits pad B jk i rSC = sysCount s P g x B := rfl

theorem vF_ge (i : ℕ) (r : Fin nrW) (h : 56 ≤ r.val) : vF D x bits pad B jk i r = 0 := by
  simp only [vF, Function.update_apply]
  rw [if_neg (fin_ne (by show r.val ≠ 55; omega)), if_neg (fin_ne (by show r.val ≠ 54; omega)),
    if_neg (fin_ne (by show r.val ≠ 53; omega)), if_neg (fin_ne (by show r.val ≠ 52; omega)),
    if_neg (fin_ne (by show r.val ≠ 51; omega)), if_neg (fin_ne (by show r.val ≠ 50; omega)),
    if_neg (fin_ne (by show r.val ≠ 49; omega)), if_neg (fin_ne (by show r.val ≠ 48; omega))]
  exact v0_lt D x bits pad B jk i r (by omega)

theorem rD_val (k : Fin 3) : (rD k).val = 66 + 2 * k.val := rfl
theorem rF_val (k : Fin 3) : (rF k).val = 67 + 2 * k.val := rfl
theorem rV_val (k : Fin 3) : (rV k).val = 48 + k.val := rfl
theorem rS_val (k : Fin 3) : (rS k).val = 51 + k.val := rfl

/-- One classification on a shape. -/
theorem ltSub_shape (cap : ℕ) (vi : List Bool) (wh : ℕ) (v : Fin nrW → ℕ) (k : Fin 3)
    (hD : v (rD k) = 0) (hF : v (rF k) = 0) (hT : v rT1 = 0) (hX : v rT2 = 0) (hc : v (rV k) + v rSC ≤ cap) :
    WExec cap (Worker.ltSubW (rV k) rSC (rD k) (rF k) rT1 rT2) (Shape D x bits pad B jk vi wh v)
      (Shape D x bits pad B jk vi wh
        (Function.update (Function.update v (rD k) (v (rV k) - v rSC)) (rF k) (v rSC - v (rV k))))
      (18 * v (rV k) + 3 + 1 + (18 * v rSC + 3 + 1 + (8 * v rSC + 1))) := by
  have n9 : ∀ r : Fin nrW, 10 ≤ r.val → r ≠ regE 9 := fun r h => fin_ne (by rw [regE_val]; simp; omega)
  have hk := k.isLt
  have val : ∀ r : Fin nrW, 10 ≤ r.val → (Shape D x bits pad B jk vi wh v).val r = v r := fun r h => by
    simp only [shape_val]; rw [Function.update_of_ne (n9 r h)]
  have e := Worker.ltSubW_spec (cap := cap) (rV k) rSC (rD k) (rF k) rT1 rT2 (by fin_cases k <;> decide)
    (Shape D x bits pad B jk vi wh v)
    (by rw [val _ (by rw [rD_val]; omega)]; exact hD) (by rw [val _ (by rw [rF_val]; omega)]; exact hF)
    (by rw [val _ (by show 10 ≤ 72; omega)]; exact hT) (by rw [val _ (by show 10 ≤ 73; omega)]; exact hX)
    (by rw [val _ (by rw [rV_val]; omega), val _ (by show 10 ≤ 44; omega)]; exact hc)
  rw [val _ (by rw [rV_val]; omega), val _ (by show 10 ≤ 44; omega)] at e
  rwa [shape_setv _ _ _ _ _ _ _ _ _ _ (n9 _ (by rw [rD_val]; omega)),
    shape_setv _ _ _ _ _ _ _ _ _ _ (n9 _ (by rw [rF_val]; omega))] at e

/-- **The classification on a shape.** -/
theorem classify_shape (cap Z : ℕ) (i : ℕ) (vi : List Bool) (wh : ℕ)
    (hV : ∀ k, litVar (clauseOf s P g x B i k) ≤ Z) (hSC : sysCount s P g x B ≤ Z) (hcap : 2 * Z ≤ cap) :
    WExec cap (classifyW D) (Shape D x bits pad B jk vi wh (vF D x bits pad B jk i))
      (Shape D x bits pad B jk vi wh (vC D x bits pad B jk i)) (200 * (Z + 1)) := by
  have z : ∀ r : Fin nrW, 56 ≤ r.val → vF D x bits pad B jk i r = 0 := vF_ge D x bits pad B jk i
  have V := vF_V D x bits pad B jk i
  have SC := vF_SC D x bits pad B jk i
  have h0 := hV 0; have h1 := hV 1; have h2 := hV 2
  have e0 := ltSub_shape D x bits pad B jk cap vi wh (vF D x bits pad B jk i) 0 (z _ (by decide)) (z _ (by decide))
    (z _ (by decide)) (z _ (by decide)) (by rw [V, SC]; omega)
  rw [V, SC] at e0
  set v1 := Function.update (Function.update (vF D x bits pad B jk i) (rD 0)
    (litVar (clauseOf s P g x B i 0) - sysCount s P g x B)) (rF 0) (sysCount s P g x B - litVar (clauseOf s P g x B i 0))
    with hv1
  have l1 : ∀ r : Fin nrW, r ≠ rD 0 → r ≠ rF 0 → v1 r = vF D x bits pad B jk i r := fun r a b => by
    rw [hv1, Function.update_of_ne b, Function.update_of_ne a]
  have e1 := ltSub_shape D x bits pad B jk cap vi wh v1 1 (by rw [l1 _ (by decide) (by decide)]; exact z _ (by decide))
    (by rw [l1 _ (by decide) (by decide)]; exact z _ (by decide)) (by rw [l1 _ (by decide) (by decide)]; exact z _ (by decide))
    (by rw [l1 _ (by decide) (by decide)]; exact z _ (by decide))
    (by rw [l1 _ (by decide) (by decide), l1 _ (by decide) (by decide), V, SC]; omega)
  rw [l1 _ (by decide) (by decide), l1 _ (by decide) (by decide), V, SC] at e1
  set v2 := Function.update (Function.update v1 (rD 1)
    (litVar (clauseOf s P g x B i 1) - sysCount s P g x B)) (rF 1) (sysCount s P g x B - litVar (clauseOf s P g x B i 1))
    with hv2
  have l2 : ∀ r : Fin nrW, r ≠ rD 0 → r ≠ rF 0 → r ≠ rD 1 → r ≠ rF 1 → v2 r = vF D x bits pad B jk i r :=
    fun r a b c d => by rw [hv2, Function.update_of_ne d, Function.update_of_ne c, l1 r a b]
  have e2 := ltSub_shape D x bits pad B jk cap vi wh v2 2
    (by rw [l2 _ (by decide) (by decide) (by decide) (by decide)]; exact z _ (by decide))
    (by rw [l2 _ (by decide) (by decide) (by decide) (by decide)]; exact z _ (by decide))
    (by rw [l2 _ (by decide) (by decide) (by decide) (by decide)]; exact z _ (by decide))
    (by rw [l2 _ (by decide) (by decide) (by decide) (by decide)]; exact z _ (by decide))
    (by rw [l2 _ (by decide) (by decide) (by decide) (by decide), l2 _ (by decide) (by decide) (by decide) (by decide),
      V, SC]; omega)
  rw [l2 _ (by decide) (by decide) (by decide) (by decide), l2 _ (by decide) (by decide) (by decide) (by decide),
    V, SC] at e2
  refine WExec.mono (WExec.cast cap (WExec.seq e0 (WExec.seq e1 e2)) ?_ le_rfl) (by omega)
  rfl

end

end NearCubicGates.Close.TermLoop
