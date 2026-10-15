import Proof.Gates.TermLoop.Gadget3

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
open NearCubicGates.Close.WorkerArith (TermFit termW1 termW2 termCost bud1 bud2 entryWord)
open NearCubicGates.Close.CheckedPCPP.LitDecode (litVar litNeg)

noncomputable section

variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams} (D : SetupData s P g)
variable {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ) (B : Outer.OuterGuess (width s g N))
  (jk : Fin (nsW D + 1) → List Bool)
variable {B1 B2 : ℕ} (ctr : Counter B1 B2) (hct : ctr.program.program.tapeCount = D.tc) (ω : ℚ)

/-! ## Loaded register files -/

theorem loadL0 (v : Fin nrW → ℕ) (k : Fin 3) :
    loadL v k 0 (by decide) (regE 0) = v (rS k) ∧ loadL v k 0 (by decide) (regE 1) = v (rF k) ∧
      loadL v k 0 (by decide) (regE 2) = (if v (rF k) ≠ 0 then v (rV k) else v (rD k)) := ⟨rfl, rfl, rfl⟩

theorem loadL3 (v : Fin nrW → ℕ) (k : Fin 3) :
    loadL v k 3 (by decide) (regE 3) = v (rS k) ∧ loadL v k 3 (by decide) (regE 4) = v (rF k) ∧
      loadL v k 3 (by decide) (regE 5) = (if v (rF k) ≠ 0 then v (rV k) else v (rD k)) := ⟨rfl, rfl, rfl⟩

theorem loadL0_other (v : Fin nrW → ℕ) (k : Fin 3) (r : Fin nrW) (h0 : r ≠ regE 0) (h1 : r ≠ regE 1)
    (h2 : r ≠ regE 2) : loadL v k 0 (by decide) r = v r := by
  unfold loadL
  exact (Function.update_of_ne h2 _ _).trans ((Function.update_of_ne h1 _ _).trans (Function.update_of_ne h0 _ _))

theorem loadL3_other (v : Fin nrW → ℕ) (k : Fin 3) (r : Fin nrW) (h0 : r ≠ regE 3) (h1 : r ≠ regE 4)
    (h2 : r ≠ regE 5) : loadL v k 3 (by decide) r = v r := by
  unfold loadL
  exact (Function.update_of_ne h2 _ _).trans ((Function.update_of_ne h1 _ _).trans (Function.update_of_ne h0 _ _))

theorem loadH_at (v : Fin nrW → ℕ) (n : Fin 40) : loadH v n (regE n) = v rPB + v rA := by
  simp [loadH]

theorem loadH_other (v : Fin nrW → ℕ) (n : Fin 40) (r : Fin nrW) (h : r ≠ regE n) : loadH v n r = v r := by
  unfold loadH; rw [Function.update_of_ne h]

/-- Literal `k`'s value bounds. -/
theorem lit_bounds (i : ℕ) (k : Fin 3) :
    litVar (clauseOf s P g x B i k) < sysCount s P g x B + (pcpp s P g x B).proofBits ∧
      litNeg (clauseOf s P g x B i k) ≤ 1 ∧ (pcpp s P g x B).proofBits + gadgets s g N = auxN s P g x B :=
  ⟨ClauseFront.litVar_lt _, litNeg_le_one _, rfl⟩

theorem lit_idx (Z i : ℕ) (hidx : sysCount s P g x B + auxN s P g x B ≤ Z) (k : Fin 3) :
    (litOpd s P g x B i k).idx ≤ Z ∧
      ((litOpd s P g x B i k).sys = true → (litOpd s P g x B i k).idx < width s g N + P.code.length (width s g N)) ∧
      ((litOpd s P g x B i k).sys = false → (litOpd s P g x B i k).idx < auxN s P g x B) := by
  obtain ⟨h1, -, h3⟩ := lit_bounds (P := P) x B i k
  rw [← sysCount_eq (P := P) x B]
  unfold litOpd
  by_cases h : litVar (clauseOf s P g x B i k) < sysCount s P g x B
  · simp [h]; omega
  · simp [h]; omega

theorem hi_ne (r : Fin nrW) (h : 10 ≤ r.val) (j : Fin 40) (hj : j.val < 10) : r ≠ regE j :=
  fin_ne (by rw [regE_val]; omega)

theorem loadL0_hi (v : Fin nrW → ℕ) (k : Fin 3) (r : Fin nrW) (h : 10 ≤ r.val) : loadL v k 0 (by decide) r = v r :=
  loadL0_other v k r (hi_ne r h 0 (by decide)) (hi_ne r h 1 (by decide)) (hi_ne r h 2 (by decide))

theorem loadL3_hi (v : Fin nrW → ℕ) (k : Fin 3) (r : Fin nrW) (h : 10 ≤ r.val) : loadL v k 3 (by decide) r = v r :=
  loadL3_other v k r (hi_ne r h 3 (by decide)) (hi_ne r h 4 (by decide)) (hi_ne r h 5 (by decide))

theorem loadH_hi (v : Fin nrW → ℕ) (n : Fin 40) (hn : n.val < 10) (r : Fin nrW) (h : 10 ≤ r.val) : loadH v n r = v r :=
  loadH_other v n r (hi_ne r h n hn)

theorem rS_ge (k : Fin 3) : 10 ≤ (rS k).val := by rw [rS_val]; omega
theorem rV_ge (k : Fin 3) : 10 ≤ (rV k).val := by rw [rV_val]; omega
theorem rD_ge (k : Fin 3) : 10 ≤ (rD k).val := by rw [rD_val]; omega
theorem rF_ge (k : Fin 3) : 10 ≤ (rF k).val := by rw [rF_val]; omega

/-! ## The patterns -/

section Patterns
variable (cap Z Bc V : ℕ) (i : ℕ) (vi : List Bool) (wh : ℕ)
  (hwh : fieldEnd (guessWord N bits pad) wh ≤ (guessWord N bits pad).length)
  (hfit : TermFit cap (circs s g N bits pad) (auxN s P g x B) (suppRows P (width s g N))
    (P.code.length (width s g N)) ω (headField bits pad (N := N) wh) Z Bc V)
  (h7 : (Codec.cwPrefix (circs s g N bits pad) (auxN s P g x B)).length ≤ Z)
  (h8 : (Codec.rowPrefix (suppRows P (width s g N)) (P.code.length (width s g N))).length ≤ Z)
  (hidx : sysCount s P g x B + auxN s P g x B ≤ Z) (hi : i < gadgets s g N)
include hwh hfit h7 h8 hidx hi

/-- **Term pattern: one literal (terms 1–3).** -/
theorem stepLit1 (k : Fin 3)
    (hcap : vi.length + 1000 * (Z + 1) + 8 * bud1 ctr (circs s g N bits pad) ω (headField bits pad (N := N) wh)
      (litOpd s P g x B i k) ≤ cap) :
    ∃ τ, WXExec cap (.seq (.wm (litLoad D k 0 (by decide))) (.seq (termW1 (termEnv D) ctr (ctrMap D ctr hct) ω)
        (.wm (clearOps D)))) (Shape D x bits pad B jk vi wh (vC D x bits pad B jk i)) τ
        (termCost ctr.program.program.tapeCount Z Bc (bud1 ctr (circs s g N bits pad) ω
          (headField bits pad (N := N) wh) (litOpd s P g x B i k)) + 200 * (Z + 1)) ∧
      SimW (Shape D x bits pad B jk (vi ++ marks (entryWord (model1 ctr (circs s g N bits pad)
        (suppRows P (width s g N)) ω (headField bits pad (N := N) wh) (litOpd s P g x B i k))))
        (fieldEnd (guessWord N bits pad) wh) (vC D x bits pad B jk i)) τ := by
  set v := vC D x bits pad B jk i with hv
  have hZc : Z ≤ cap := by have := hfit.capV; omega
  obtain ⟨b1, b2, b3⟩ := lit_bounds (P := P) x B i k
  have hS : v (rS k) = litNeg (clauseOf s P g x B i k) := vC_S D x bits pad B jk i k
  have hV : v (rV k) = litVar (clauseOf s P g x B i k) := vC_V D x bits pad B jk i k
  have hD : v (rD k) = litVar (clauseOf s P g x B i k) - sysCount s P g x B := vC_D D x bits pad B jk i k
  have hF : v (rF k) = sysCount s P g x B - litVar (clauseOf s P g x B i k) := vC_F D x bits pad B jk i k
  have hops : opsSum (loadL v k 0 (by decide)) ≤ 2 * Z + 1 := by
    obtain ⟨l0, l1, l2⟩ := loadL0 v k
    unfold opsSum
    rw [l0, l1, l2, loadL0_other v k _ (by decide) (by decide) (by decide),
      loadL0_other v k _ (by decide) (by decide) (by decide), loadL0_other v k _ (by decide) (by decide) (by decide),
      show v (regE 3) = 0 from vC_ops D x bits pad B jk i 3 (by decide),
      show v (regE 4) = 0 from vC_ops D x bits pad B jk i 4 (by decide),
      show v (regE 5) = 0 from vC_ops D x bits pad B jk i 5 (by decide), hS, hF, hV, hD]
    split_ifs <;> omega
  have hld := litLoad_shape D x bits pad B jk cap vi wh v k 0 (by decide) (Or.inl rfl)
    (vC_ops D x bits pad B jk i 0 (by decide)) (vC_ops D x bits pad B jk i 1 (by decide))
    (vC_ops D x bits pad B jk i 2 (by decide)) (vC_LT D x bits pad B jk i)
    (by rw [hS, hV, hD, hF]; omega)
  obtain ⟨l0, l1, l2⟩ := loadL0 v k
  have hopd : (⟨decide (loadL v k 0 (by decide) (regE 0) ≠ 0), decide (loadL v k 0 (by decide) (regE 1) ≠ 0),
      loadL v k 0 (by decide) (regE 2)⟩ : Opd) = litOpd s P g x B i k :=
    loadOpd_lit (P := P) x B i v k 0 (by decide) hS hV hD hF
  obtain ⟨ix, isys, iaux⟩ := lit_idx (P := P) x B Z i hidx k
  rw [← hopd] at ix isys iaux
  obtain ⟨τ, e, sm⟩ := term1_shape D x bits pad B jk ctr hct ω cap Z Bc V vi wh (loadL v k 0 (by decide))
    (regOK_loadL x bits pad B v (regOK_vC D x bits pad B jk i) k 0 (by decide)) hwh hfit
    (fun h => isys (by simpa using h)) (fun h => iaux (by simpa using h)) h7 h8 ix (by rw [hopd]; exact hcap)
  rw [hopd] at e sm
  obtain ⟨τ', e', sm'⟩ := step_ideal D x bits pad B jk cap _ _ vi wh _ v (loadL v k 0 (by decide)) _ _ _ hld ⟨τ, e, sm⟩
    (by rw [zeroOps_loadL, zeroOps_self _ (vC_ops D x bits pad B jk i)]) (by omega)
  refine ⟨τ', WXExec.mono e' ?_, sm'⟩
  rw [hS, hF]
  split_ifs <;> simp only [hV, hD] <;> omega

/-- **Term pattern: the helper (term 0).** -/
theorem stepHelp1
    (hcap : vi.length + 1000 * (Z + 1) + 8 * bud1 ctr (circs s g N bits pad) ω (headField bits pad (N := N) wh)
      (helpOpd s P g x B i) ≤ cap) :
    ∃ τ, WXExec cap (.seq (.wm (helpLoad D 2)) (.seq (termW1 (termEnv D) ctr (ctrMap D ctr hct) ω)
        (.wm (clearOps D)))) (Shape D x bits pad B jk vi wh (vC D x bits pad B jk i)) τ
        (termCost ctr.program.program.tapeCount Z Bc (bud1 ctr (circs s g N bits pad) ω
          (headField bits pad (N := N) wh) (helpOpd s P g x B i)) + 200 * (Z + 1)) ∧
      SimW (Shape D x bits pad B jk (vi ++ marks (entryWord (model1 ctr (circs s g N bits pad)
        (suppRows P (width s g N)) ω (headField bits pad (N := N) wh) (helpOpd s P g x B i))))
        (fieldEnd (guessWord N bits pad) wh) (vC D x bits pad B jk i)) τ := by
  set v := vC D x bits pad B jk i with hv
  have hZc : Z ≤ cap := by have := hfit.capV; omega
  have hPB : v rPB = (pcpp s P g x B).proofBits := vC_PB D x bits pad B jk i
  have hA : v rA = i := vC_A D x bits pad B jk i
  have hb : (pcpp s P g x B).proofBits + gadgets s g N = auxN s P g x B := rfl
  have z : ∀ j : Fin 40, j.val < 6 → v (regE j) = 0 := vC_ops D x bits pad B jk i
  have hld := helpLoad_shape D x bits pad B jk cap vi wh v 2 (Or.inl rfl) (z 2 (by decide))
    (vC_LT D x bits pad B jk i) (by rw [hPB, hA]; omega)
  have e0 : loadH v 2 (regE 0) = 0 := by rw [loadH_other v 2 _ (by decide)]; exact z 0 (by decide)
  have e1 : loadH v 2 (regE 1) = 0 := by rw [loadH_other v 2 _ (by decide)]; exact z 1 (by decide)
  have e2 : loadH v 2 (regE 2) = (pcpp s P g x B).proofBits + i := by rw [loadH_at, hPB, hA]
  have hopd : (⟨decide (loadH v 2 (regE 0) ≠ 0), decide (loadH v 2 (regE 1) ≠ 0), loadH v 2 (regE 2)⟩ : Opd) =
      helpOpd s P g x B i := by
    rw [e0, e1, e2]; rfl
  obtain ⟨τ, e, sm⟩ := term1_shape D x bits pad B jk ctr hct ω cap Z Bc V vi wh (loadH v 2)
    (regOK_loadH x bits pad B v (regOK_vC D x bits pad B jk i) 2 (by decide)) hwh hfit
    (fun h => absurd e1 h) (fun _ => by rw [e2]; omega) h7 h8 (by rw [e2]; omega) (by rw [hopd]; exact hcap)
  rw [hopd] at e sm
  have hops : opsSum (loadH v 2) ≤ Z := by
    unfold opsSum
    rw [e0, e1, e2, loadH_other v 2 _ (by decide), loadH_other v 2 _ (by decide), loadH_other v 2 _ (by decide),
      z 3 (by decide), z 4 (by decide), z 5 (by decide)]
    omega
  obtain ⟨τ', e', sm'⟩ := step_ideal D x bits pad B jk cap _ _ vi wh _ v (loadH v 2) _ _ _ hld ⟨τ, e, sm⟩
    (by rw [zeroOps_loadH _ _ (by decide), zeroOps_self _ z]) (by omega)
  refine ⟨τ', WXExec.mono e' ?_, sm'⟩
  rw [hPB, hA]; omega

/-- **Term pattern: two literals (terms 4–6).** -/
theorem stepLit2 (k k' : Fin 3)
    (hcap : vi.length + 1000 * (Z + 1) + 8 * bud2 ctr (circs s g N bits pad) (suppRows P (width s g N)) ω
      (headField bits pad (N := N) wh) (litOpd s P g x B i k) (litOpd s P g x B i k') ≤ cap) :
    ∃ τ, WXExec cap (.seq (.wm (.seq (litLoad D k 0 (by decide)) (litLoad D k' 3 (by decide))))
        (.seq (termW2 (termEnv D) ctr (ctrMap D ctr hct) ω) (.wm (clearOps D))))
        (Shape D x bits pad B jk vi wh (vC D x bits pad B jk i)) τ
        (termCost ctr.program.program.tapeCount Z Bc (bud2 ctr (circs s g N bits pad) (suppRows P (width s g N)) ω
          (headField bits pad (N := N) wh) (litOpd s P g x B i k) (litOpd s P g x B i k')) + 200 * (Z + 1)) ∧
      SimW (Shape D x bits pad B jk (vi ++ marks (entryWord (model2 ctr (circs s g N bits pad)
        (suppRows P (width s g N)) ω (headField bits pad (N := N) wh) (litOpd s P g x B i k) (litOpd s P g x B i k'))))
        (fieldEnd (guessWord N bits pad) wh) (vC D x bits pad B jk i)) τ := by
  set v := vC D x bits pad B jk i with hv
  have hZc : Z ≤ cap := by have := hfit.capV; omega
  have z : ∀ j : Fin 40, j.val < 6 → v (regE j) = 0 := vC_ops D x bits pad B jk i
  obtain ⟨b1, b2, b3⟩ := lit_bounds (P := P) x B i k
  obtain ⟨b1', b2', -⟩ := lit_bounds (P := P) x B i k'
  have hS : v (rS k) = litNeg (clauseOf s P g x B i k) := vC_S D x bits pad B jk i k
  have hV : v (rV k) = litVar (clauseOf s P g x B i k) := vC_V D x bits pad B jk i k
  have hD : v (rD k) = litVar (clauseOf s P g x B i k) - sysCount s P g x B := vC_D D x bits pad B jk i k
  have hF : v (rF k) = sysCount s P g x B - litVar (clauseOf s P g x B i k) := vC_F D x bits pad B jk i k
  set v1 := loadL v k 0 (by decide) with hv1
  have hS' : v1 (rS k') = litNeg (clauseOf s P g x B i k') := by
    rw [hv1, loadL0_hi v k _ (rS_ge k')]; exact vC_S D x bits pad B jk i k'
  have hV' : v1 (rV k') = litVar (clauseOf s P g x B i k') := by
    rw [hv1, loadL0_hi v k _ (rV_ge k')]; exact vC_V D x bits pad B jk i k'
  have hD' : v1 (rD k') = litVar (clauseOf s P g x B i k') - sysCount s P g x B := by
    rw [hv1, loadL0_hi v k _ (rD_ge k')]; exact vC_D D x bits pad B jk i k'
  have hF' : v1 (rF k') = sysCount s P g x B - litVar (clauseOf s P g x B i k') := by
    rw [hv1, loadL0_hi v k _ (rF_ge k')]; exact vC_F D x bits pad B jk i k'
  have z1 : ∀ j : Fin 40, 3 ≤ j.val → j.val < 6 → v1 (regE j) = 0 := fun j h3 h6 => by
    rw [hv1, loadL0_other v k _ (regE_ne _ _ (fun e => by rw [e] at h3; simp at h3))
      (regE_ne _ _ (fun e => by rw [e] at h3; simp at h3)) (regE_ne _ _ (fun e => by rw [e] at h3; simp at h3))]
    exact z j h6
  have hld1 := litLoad_shape D x bits pad B jk cap vi wh v k 0 (by decide) (Or.inl rfl) (z 0 (by decide))
    (z 1 (by decide)) (z 2 (by decide)) (vC_LT D x bits pad B jk i) (by rw [hS, hV, hD, hF]; omega)
  have hld2 := litLoad_shape D x bits pad B jk cap vi wh v1 k' 3 (by decide) (Or.inr rfl) (z1 3 (by decide) (by decide))
    (z1 4 (by decide) (by decide)) (z1 5 (by decide) (by decide))
    (by rw [hv1, loadL0_hi v k _ (by show 10 ≤ 74; omega)]; exact vC_LT D x bits pad B jk i)
    (by rw [hS', hV', hD', hF']; omega)
  set v2 := loadL v1 k' 3 (by decide) with hv2
  have r012 : ∀ j : Fin 40, j.val < 3 → v2 (regE j) = v1 (regE j) := fun j h => by
    rw [hv2, loadL3_other v1 k' _ (regE_ne _ _ (fun e => by rw [e] at h; simp at h))
      (regE_ne _ _ (fun e => by rw [e] at h; simp at h)) (regE_ne _ _ (fun e => by rw [e] at h; simp at h))]
  have hopd1 : (⟨decide (v2 (regE 0) ≠ 0), decide (v2 (regE 1) ≠ 0), v2 (regE 2)⟩ : Opd) = litOpd s P g x B i k := by
    rw [r012 0 (by decide), r012 1 (by decide), r012 2 (by decide)]
    exact loadOpd_lit (P := P) x B i v k 0 (by decide) hS hV hD hF
  have hopd2 : (⟨decide (v2 (regE 3) ≠ 0), decide (v2 (regE 4) ≠ 0), v2 (regE 5)⟩ : Opd) = litOpd s P g x B i k' :=
    loadOpd_lit (P := P) x B i v1 k' 3 (by decide) hS' hV' hD' hF'
  obtain ⟨ix, isys, iaux⟩ := lit_idx (P := P) x B Z i hidx k
  obtain ⟨ix', isys', iaux'⟩ := lit_idx (P := P) x B Z i hidx k'
  rw [← hopd1] at ix isys iaux
  rw [← hopd2] at ix' isys' iaux'
  obtain ⟨τ, e, sm⟩ := term2_shape D x bits pad B jk ctr hct ω cap Z Bc V vi wh v2
    (regOK_loadL x bits pad B v1 (regOK_loadL x bits pad B v (regOK_vC D x bits pad B jk i) k 0 (by decide)) k' 3
      (by decide)) hwh hfit
    (fun h => isys (by simpa using h)) (fun h => iaux (by simpa using h))
    (fun h => isys' (by simpa using h)) (fun h => iaux' (by simpa using h)) h7 h8 ix ix'
    (by rw [hopd1, hopd2]; exact hcap)
  rw [hopd1, hopd2] at e sm
  have hops : opsSum v2 ≤ 4 * Z + 2 := by
    obtain ⟨l0, l1, l2⟩ := loadL0 v k
    obtain ⟨l3, l4, l5⟩ := loadL3 v1 k'
    unfold opsSum
    rw [r012 0 (by decide), r012 1 (by decide), r012 2 (by decide), hv2, l3, l4, l5, hv1, l0, l1, l2]
    rw [← hv1, hS, hF, hS', hF']
    split_ifs <;> simp only [hV, hD, hV', hD'] <;> omega
  obtain ⟨τ', e', sm'⟩ := step_ideal D x bits pad B jk cap _ _ vi wh _ v v2 _ _ _ (WExec.seq hld1 hld2) ⟨τ, e, sm⟩
    (by rw [hv2, zeroOps_loadL, hv1, zeroOps_loadL, zeroOps_self _ z]) (by omega)
  refine ⟨τ', WXExec.mono e' ?_, sm'⟩
  rw [hS, hF, hS', hF']
  split_ifs <;> simp only [hV, hD, hV', hD'] <;> omega

/-- **Term pattern: a literal and the helper (terms 7–9).** -/
theorem stepLitHelp (k : Fin 3)
    (hcap : vi.length + 1000 * (Z + 1) + 8 * bud2 ctr (circs s g N bits pad) (suppRows P (width s g N)) ω
      (headField bits pad (N := N) wh) (litOpd s P g x B i k) (helpOpd s P g x B i) ≤ cap) :
    ∃ τ, WXExec cap (.seq (.wm (.seq (litLoad D k 0 (by decide)) (helpLoad D 5)))
        (.seq (termW2 (termEnv D) ctr (ctrMap D ctr hct) ω) (.wm (clearOps D))))
        (Shape D x bits pad B jk vi wh (vC D x bits pad B jk i)) τ
        (termCost ctr.program.program.tapeCount Z Bc (bud2 ctr (circs s g N bits pad) (suppRows P (width s g N)) ω
          (headField bits pad (N := N) wh) (litOpd s P g x B i k) (helpOpd s P g x B i)) + 200 * (Z + 1)) ∧
      SimW (Shape D x bits pad B jk (vi ++ marks (entryWord (model2 ctr (circs s g N bits pad)
        (suppRows P (width s g N)) ω (headField bits pad (N := N) wh) (litOpd s P g x B i k) (helpOpd s P g x B i))))
        (fieldEnd (guessWord N bits pad) wh) (vC D x bits pad B jk i)) τ := by
  set v := vC D x bits pad B jk i with hv
  have hZc : Z ≤ cap := by have := hfit.capV; omega
  have z : ∀ j : Fin 40, j.val < 6 → v (regE j) = 0 := vC_ops D x bits pad B jk i
  obtain ⟨b1, b2, b3⟩ := lit_bounds (P := P) x B i k
  have hS : v (rS k) = litNeg (clauseOf s P g x B i k) := vC_S D x bits pad B jk i k
  have hV : v (rV k) = litVar (clauseOf s P g x B i k) := vC_V D x bits pad B jk i k
  have hD : v (rD k) = litVar (clauseOf s P g x B i k) - sysCount s P g x B := vC_D D x bits pad B jk i k
  have hF : v (rF k) = sysCount s P g x B - litVar (clauseOf s P g x B i k) := vC_F D x bits pad B jk i k
  have hPB : v rPB = (pcpp s P g x B).proofBits := vC_PB D x bits pad B jk i
  have hA : v rA = i := vC_A D x bits pad B jk i
  set v1 := loadL v k 0 (by decide) with hv1
  have z1 : ∀ j : Fin 40, 3 ≤ j.val → j.val < 6 → v1 (regE j) = 0 := fun j h3 h6 => by
    rw [hv1, loadL0_other v k _ (regE_ne _ _ (fun e => by rw [e] at h3; simp at h3))
      (regE_ne _ _ (fun e => by rw [e] at h3; simp at h3)) (regE_ne _ _ (fun e => by rw [e] at h3; simp at h3))]
    exact z j h6
  have hPB1 : v1 rPB = (pcpp s P g x B).proofBits := by rw [hv1, loadL0_hi v k _ (by rw [rPB_val]; omega)]; exact hPB
  have hA1 : v1 rA = i := by rw [hv1, loadL0_hi v k _ (by rw [rA_val]; omega)]; exact hA
  have hld1 := litLoad_shape D x bits pad B jk cap vi wh v k 0 (by decide) (Or.inl rfl) (z 0 (by decide))
    (z 1 (by decide)) (z 2 (by decide)) (vC_LT D x bits pad B jk i) (by rw [hS, hV, hD, hF]; omega)
  have hld2 := helpLoad_shape D x bits pad B jk cap vi wh v1 5 (Or.inr rfl) (z1 5 (by decide) (by decide))
    (by rw [hv1, loadL0_hi v k _ (by show 10 ≤ 74; omega)]; exact vC_LT D x bits pad B jk i)
    (by rw [hPB1, hA1]; omega)
  set v2 := loadH v1 5 with hv2
  have r012 : ∀ j : Fin 40, j.val < 3 → v2 (regE j) = v1 (regE j) := fun j h => by
    rw [hv2, loadH_other v1 5 _ (regE_ne _ _ (fun e => by rw [e] at h; simp at h))]
  have e3 : v2 (regE 3) = 0 := by rw [hv2, loadH_other v1 5 _ (by decide)]; exact z1 3 (by decide) (by decide)
  have e4 : v2 (regE 4) = 0 := by rw [hv2, loadH_other v1 5 _ (by decide)]; exact z1 4 (by decide) (by decide)
  have e5 : v2 (regE 5) = (pcpp s P g x B).proofBits + i := by rw [hv2, loadH_at, hPB1, hA1]
  have hopd1 : (⟨decide (v2 (regE 0) ≠ 0), decide (v2 (regE 1) ≠ 0), v2 (regE 2)⟩ : Opd) = litOpd s P g x B i k := by
    rw [r012 0 (by decide), r012 1 (by decide), r012 2 (by decide)]
    exact loadOpd_lit (P := P) x B i v k 0 (by decide) hS hV hD hF
  have hopd2 : (⟨decide (v2 (regE 3) ≠ 0), decide (v2 (regE 4) ≠ 0), v2 (regE 5)⟩ : Opd) = helpOpd s P g x B i := by
    rw [e3, e4, e5]; rfl
  obtain ⟨ix, isys, iaux⟩ := lit_idx (P := P) x B Z i hidx k
  rw [← hopd1] at ix isys iaux
  obtain ⟨τ, e, sm⟩ := term2_shape D x bits pad B jk ctr hct ω cap Z Bc V vi wh v2
    (regOK_loadH x bits pad B v1 (regOK_loadL x bits pad B v (regOK_vC D x bits pad B jk i) k 0 (by decide)) 5
      (by decide)) hwh hfit
    (fun h => isys (by simpa using h)) (fun h => iaux (by simpa using h))
    (fun h => absurd e4 h) (fun _ => by rw [e5]; omega) h7 h8 ix (by rw [e5]; omega)
    (by rw [hopd1, hopd2]; exact hcap)
  rw [hopd1, hopd2] at e sm
  have hops : opsSum v2 ≤ 3 * Z + 2 := by
    obtain ⟨l0, l1, l2⟩ := loadL0 v k
    unfold opsSum
    rw [r012 0 (by decide), r012 1 (by decide), r012 2 (by decide), e3, e4, e5, hv1, l0, l1, l2, hS, hF]
    split_ifs <;> simp only [hV, hD] <;> omega
  obtain ⟨τ', e', sm'⟩ := step_ideal D x bits pad B jk cap _ _ vi wh _ v v2 _ _ _ (WExec.seq hld1 hld2) ⟨τ, e, sm⟩
    (by rw [hv2, zeroOps_loadH _ _ (by decide), hv1, zeroOps_loadL, zeroOps_self _ z]) (by omega)
  refine ⟨τ', WXExec.mono e' ?_, sm'⟩
  rw [hS, hF, hPB1, hA1]
  split_ifs <;> simp only [hV, hD] <;> omega

end Patterns

end

end NearCubicGates.Close.TermLoop
