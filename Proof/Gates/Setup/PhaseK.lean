import Proof.Gates.Setup.PhaseR
import Proof.Gates.Succinct.Check
import Proof.Gates.CheckedPCPP.EncSetup

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.Setup

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.RepairOrdinary.Streaming NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.CanonicalWitnessCodec NearCubicWires.ExecutableInterfaces
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicWires.Bindings.CLW20Lemma311
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearCubicGates.Close.Worker (width pcpp gadgets oracleOK nu PairOK)
open NearCubicWires.WireExponent3_5.PrimAsm.DockW (updS)

noncomputable section

/-! ## CHECK's register file (`60 … 104`) -/

theorem vreg_card : Fintype.card Succinct.VReg = 45 := by decide

/-- CHECK's registers: `VReg` onto `60 … 104`. -/
noncomputable def EK (v : Succinct.VReg) : Fin nrW :=
  ⟨60 + (Fintype.equivFin Succinct.VReg v).val, by
    have := lt_of_lt_of_eq (Fintype.equivFin Succinct.VReg v).isLt vreg_card; show _ < 128; omega⟩

theorem EK_val (v : Succinct.VReg) : 60 ≤ (EK v).val ∧ (EK v).val < 105 := by
  have := lt_of_lt_of_eq (Fintype.equivFin Succinct.VReg v).isLt vreg_card; unfold EK; simp only; omega

theorem EK_inj : Function.Injective EK := by
  intro a b h
  have := congrArg Fin.val h
  unfold EK at this; simp only at this
  exact (Fintype.equivFin Succinct.VReg).injective (Fin.ext (by omega))

theorem EK_ne (v : Succinct.VReg) (r : Fin nrW) (h : r.val < 60 ∨ 105 ≤ r.val) : EK v ≠ r := by
  intro e; have := EK_val v; rw [e] at this; omega

/-! ## Register programs -/

section Regs
variable {ns : ℕ} {cap : ℕ}

def sizeNuW (C : Fin nrW) : WMX ns nrW :=
  .seq (.wm (Codec.dupR rNu pT1 dS)) (Recovery.HTParts.sizeW pT1 pH pB C)

theorem sizeNuW_exec (C : Fin nrW) (hC : ∀ r ∈ ([rNu, pT1, pH, pB, dS] : List (Fin nrW)), C ≠ r) (ν : ℕ)
    (σ : WState ns nrW) (hν : σ.val rNu = ν) (hz : ∀ r ∈ ([pT1, pH, pB, dS] : List (Fin nrW)), σ.val r = 0)
    (hC0 : σ.val C = 0) (hcap : 2 * ν + 2 ≤ cap) :
    WXExec cap (sizeNuW C) σ (σ.setv C ν.size) (60 * (ν + 1) ^ 2) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hz hC
  obtain ⟨z1, zH, zB, zd⟩ := hz
  obtain ⟨c1, c2, c3, c4, c5⟩ := hC
  have hs : ν.size ≤ ν := by rw [Nat.size_le]; exact Nat.lt_two_pow_self
  have e1 := Codec.dupR_spec cap rNu pT1 dS (by decide) (by decide) (by decide) σ zd (by rw [hν, z1]; omega)
  rw [z1, hν, Nat.zero_add] at e1
  have e2 := Recovery.HTParts.sizeW_exec (cap := cap) (X := pT1) (H := pH) (B := pB) (C := C)
    (by simp [List.nodup_cons]; refine ⟨⟨by decide, by decide, Ne.symm c2⟩, ⟨by decide, Ne.symm c3⟩, Ne.symm c4⟩)
    ν (by omega) ν (σ.setv pT1 ν) le_rfl (by simp) (by rw [upd_ne _ _ (by decide)]; exact zH)
    (by rw [upd_ne _ _ (by decide)]; exact zB) (by rw [upd_ne _ _ c2, hC0]; omega)
  have hσ : (σ.setv pT1 ν).setv pT1 0 = σ := by rw [LitDecode.setv_setv, ← z1, wsetv_same]
  have hC1 : (σ.setv pT1 ν).val C = 0 := by rw [upd_ne _ _ c2]; exact hC0
  refine WXExec.cast cap (WXExec.seq (WXExec.wm e1) e2) ?_ ?_
  · rw [hσ, hC1, Nat.zero_add]
  · have : ν.size * (12 * ν + 30) ≤ ν * (12 * ν + 30) := Nat.mul_le_mul_right _ hs
    nlinarith

def powNuW (k : ℕ) (Y : Fin nrW) : WMX ns nrW :=
  .seq (WMX.inc Y) (.seq (.wm (Codec.dupR rNu pX1 dS)) (.seq (EncSetup.powW pX1 Y pX3 pH pB k) (.wm (WM.clear pX1))))

theorem powNuW_exec (k : ℕ) (Y : Fin nrW) (hY : ∀ r ∈ ([rNu, pX1, pX3, pH, pB, dS] : List (Fin nrW)), Y ≠ r)
    (ν : ℕ) (hν1 : 1 ≤ ν) (σ : WState ns nrW) (hν : σ.val rNu = ν)
    (hz : ∀ r ∈ ([pX1, pX3, pH, pB, dS] : List (Fin nrW)), σ.val r = 0) (hY0 : σ.val Y = 0)
    (hcap : 2 * ν ^ k + ν ^ k * ν ^ k + ν + 2 ≤ cap) :
    WXExec cap (powNuW k Y) σ (σ.setv Y (ν ^ k)) (100 * (k + 1) * (ν ^ k + ν + 1) ^ 2) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hz hY
  obtain ⟨z1, z3, zH, zB, zd⟩ := hz
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hY
  have hp1 : 1 ≤ ν ^ k := Nat.one_le_pow _ _ hν1
  have e1 := WXExec.inc (cap := cap) Y σ (by rw [hY0]; omega)
  rw [hY0, Nat.zero_add] at e1
  have e2 := Codec.dupR_spec cap rNu pX1 dS (by decide) (by decide) (by decide) (σ.setv Y 1)
    (by rw [upd_ne _ _ (Ne.symm c6)]; exact zd) (by rw [upd_ne _ _ (Ne.symm c1), upd_ne _ _ (Ne.symm c2), hν, z1]; omega)
  rw [show (σ.setv Y 1).setv pX1 ((σ.setv Y 1).val pX1 + (σ.setv Y 1).val rNu) = (σ.setv Y 1).setv pX1 ν by
    rw [upd_ne _ _ (Ne.symm c1), upd_ne _ _ (Ne.symm c2), hν, z1, Nat.zero_add]] at e2
  have e3 := EncSetup.powW_spec (cap := cap) (X := pX1) (Y := Y) (Z := pX3) (A2 := pH) (T := pB)
    (by simp [List.nodup_cons]; exact ⟨⟨c4, c2, c3, c5⟩, ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩,
      by decide⟩) (ν ^ k) k ((σ.setv Y 1).setv pX1 ν)
    (by rw [upd_ne _ _ (by decide), upd_ne _ _ (Ne.symm c3)]; exact z3)
    (by rw [upd_ne _ _ (by decide), upd_ne _ _ (Ne.symm c4)]; exact zH)
    (by rw [upd_ne _ _ (by decide), upd_ne _ _ (Ne.symm c5)]; exact zB)
    (by rw [upd_ne _ _ c2]; simp) (by simp; omega) (by omega)
  rw [show ((σ.setv Y 1).setv pX1 ν).setv Y (((σ.setv Y 1).setv pX1 ν).val Y * ((σ.setv Y 1).setv pX1 ν).val pX1 ^ k) =
      ((σ.setv Y 1).setv pX1 ν).setv Y (ν ^ k) by rw [upd_ne _ _ c2]; simp] at e3
  have e4 := wclear_spec (cap := cap) pX1 ν (((σ.setv Y 1).setv pX1 ν).setv Y (ν ^ k))
    (by rw [upd_ne _ _ (Ne.symm c2)]; simp) (by rw [upd_ne _ _ (Ne.symm c2)]; simp; omega)
  refine WXExec.cast cap (WXExec.seq e1 (WXExec.seq (WXExec.wm e2) (WXExec.seq e3 (WXExec.wm e4)))) ?_ ?_
  · apply WState.eq <;> try rfl
    funext r
    simp only [WState.setv_val]
    by_cases h1 : r = pX1
    · subst h1
      rw [Function.update_self, Function.update_of_ne (Ne.symm c2), z1]
    · rw [Function.update_of_ne h1]
      by_cases h2 : r = Y
      · subst h2; rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne h2, Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h2]
  · have hl : (σ.setv Y 1).val rNu = ν := by rw [upd_ne _ _ (Ne.symm c1)]; exact hν
    rw [hl]
    unfold EncSetup.powCost
    have h1 : ν ≤ ν ^ k + ν + 1 := by omega
    have h2 : ν ^ k ≤ ν ^ k + ν + 1 := by omega
    obtain ⟨M, hM⟩ : ∃ M, M = ν ^ k + ν + 1 := ⟨_, rfl⟩
    rw [← hM] at h1 h2 ⊢
    have h3 : k * (40 * ν ^ k * ν ^ k + 40 * ν ^ k + 20) ≤ k * (40 * M * M + 40 * M + 20) := by
      apply Nat.mul_le_mul_left; nlinarith
    have hM1 : 1 ≤ M := by omega
    have hMM : M ≤ M * M := Nat.le_mul_self M
    have h4 : k * M ≤ k * (M * M) := Nat.mul_le_mul_left _ hMM
    have h5 : k ≤ k * (M * M) := Nat.le_mul_of_pos_right _ (by nlinarith)
    have e : 100 * (k + 1) * M ^ 2 = 100 * (k * (M * M)) + 100 * (M * M) := by ring
    have e2 : k * (40 * M * M + 40 * M + 20) = 40 * (k * (M * M)) + 40 * (k * M) + 20 * k := by ring
    rw [e]
    have hνM : ν ≤ M * M := h1.trans hMM
    omega

end Regs

/-! ## Phase K -/

variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams}

/-- The evaluator's guards: `L_ν = ν^{lenExp+2}`, `lb = size (L_ν + 4)`, `lp = size ν`; the base `b = ν^{lenRoot+1}`. -/
def lenL (g : GateParams) (ν : ℕ) : ℕ := ν ^ (g.lenExp + 2)
def lbOf (g : GateParams) (ν : ℕ) : ℕ := (lenL g ν + 4).size
def lpOf (ν : ℕ) : ℕ := ν.size
def baseOf (g : GateParams) (ν : ℕ) : ℕ := ν ^ (g.lenRoot + 1)

theorem lenL_eq (g : GateParams) (ν : ℕ) : lenL g ν = Outer.instLength g.lenExp ν := rfl

section Prog
variable (D : SetupData s P g) (W : OuterM.WidthDonor s.mw (g.sv s))

/-- **Phase K**: the guards, the base, CHECK, `FL := [CheckAt]`, then the guards and `ν` cleared. -/
def phK : WMX (nsW D) nrW :=
  .seq (.wm (Codec.dupR rN (EK .nN) dS))
  (.seq (sizeNuW (EK (.e .lp)))
  (.seq (powNuW (g.lenExp + 2) pX2)
  (.seq (.wm (NodeEmit.incN pX2 4))
  (.seq (Recovery.HTParts.sizeW pX2 pH pB (EK (.e .lb)))
  (.seq (powNuW (g.lenRoot + 1) rBs)
  (.seq (.wm (Succinct.checkW (sD1 D W) (sPT D) (sVV D) (sTT D) (sX D) EK))
  (.seq (.ifr (EK .f) WMX.skip (WMX.wr (sFL D) false))
  (.wm (.seq (WM.clear (EK .f)) (.seq (WM.clear (EK (.e .lb))) (.seq (WM.clear (EK (.e .lp)))
    (.seq (WM.clear (EK .nN)) (WM.clear rNu)))))))))))))

end Prog

/-- The register capacity phase K needs. -/
def capK (g : GateParams) (N : ℕ) : ℕ :=
  let ν := nu N
  4 * N + 4 * lenL g ν * lenL g ν + 4 * baseOf g ν * baseOf g ν + 10 * lenL g ν + 8 * (lbOf g ν + lpOf ν) +
    16 * 2 ^ (lbOf g ν + lpOf ν + 1) + 10 * ν + 300

/-- The cost of phase K (`dl` the length of `B_src`'s description). -/
def costK (g : GateParams) (N dl : ℕ) : ℕ :=
  let ν := nu N
  18 * N + 3 + 60 * (ν + 1) ^ 2 + 100 * (g.lenExp + 3) * (lenL g ν + ν + 1) ^ 2 + 16 +
    (lbOf g ν * (12 * (lenL g ν + 4) + 30) + 1) + 100 * (g.lenRoot + 2) * (baseOf g ν + ν + 1) ^ 2 +
    Succinct.checkCost dl (lbOf g ν) (lpOf ν) N + 3 * (lbOf g ν + lpOf ν + N + ν) + 40

open Classical in

structure AfterK (D : SetupData s P g) (W : OuterM.WidthDonor s.mw (g.sv s)) (R : OuterM.ARun s.mw (g.sv s))
    {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ) (B : Outer.OuterGuess (width s g N))
    (ι : WState (nsW D) nrW) : Prop where
  sx : ι.st (sX D) = RepairOrdinary.frame (List.ofFn x)
  bw : ι.st (sBW D) = RepairOrdinary.frame bits
  wt : ι.st (sWT D) = guessWord N bits pad
  fl : ι.st (sFL D) = [decide (Outer.CheckAt (nu N) x B.src)]
  d2 : ι.st (sD2 D W) = PCPPNative.descriptor B.pf
  mw : ι.st (sMW D W R) = mwWord s g N B.src
  blank : ∀ i : Fin (nsW D + 1), i.val ≠ 0 → i.val ≠ 1 → i.val ≠ 2 → (16 ≤ i.val → 21 ≤ i.val) →
    (i.val < 21 ∨ 16 + D.tA ≤ i.val) → ι.st i = []
  sh : ι.sh = fun i => if i = sWT D then pairEnd (guessWord N bits pad) else 0
  val : ι.val = fun r => if r = regE 6 then width s g N else if r = rN then N
    else if r = rBs then baseOf g (nu N) else 0
  cell : ι.cell = false

theorem nodes_le_descriptor {n : ℕ} (B : BooleanCircuit n) : B.nodes.length ≤ (PCPPNative.descriptor B).length := by
  rw [PCPPNative.descriptor_eq]
  simp only [List.length_append]
  have : ∀ l : List (BooleanNode n), l.length ≤ (l.flatMap PCPPRequestNodeSchema.native).length := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.length_cons, List.flatMap_cons, List.length_append]
      have : 1 ≤ (PCPPRequestNodeSchema.native a).length := by
        unfold PCPPRequestNodeSchema.native; simp <;> omega
      omega
  have := this B.nodes
  omega

theorem size_le_self (v : ℕ) : v.size ≤ v := by rw [Nat.size_le]; exact Nat.lt_two_pow_self

theorem EK_ne6 (v : Succinct.VReg) : EK v ≠ regE 6 := EK_ne v _ (by left; decide)

theorem phK_exec (D : SetupData s P g) (W : OuterM.WidthDonor s.mw (g.sv s)) (R : OuterM.ARun s.mw (g.sv s))
    (hL : Lay D W R) {N : ℕ} (x : BitInput N) (bits : List Bool) (pad cap : ℕ) (B : Outer.OuterGuess (width s g N))
    (hpow : N = 2 ^ nu N) (hN4 : 4 ≤ N) (hfit : Outer.SrcFits g.lenExp (nu N) B.src) (hcap : capK g N ≤ cap)
    (ι : WState (nsW D) nrW) (hι : AfterR D W R x bits pad B ι)
    (hFL : ι.st (sFL D) = [true]) :
    ∃ τ, WXExec cap (phK D W) ι τ (costK g N (PCPPNative.descriptor B.src).length) ∧ AfterK D W R x bits pad B τ := by
  classical
  have hcap' := hcap
  unfold capK lbOf lpOf at hcap'
  simp only at hcap'
  set ν := nu N with hνdef
  set L := lenL g ν with hLdef
  set b := baseOf g ν with hbdef
  have hLL : 4 * L * L = 4 * (L * L) := by ring
  have hbb : 4 * b * b = 4 * (b * b) := by ring
  have hbb2 : b ≤ b * b := Nat.le_mul_self b
  have hLL2 : L ≤ L * L := Nat.le_mul_self L
  have hν1 : 1 ≤ ν := by
    have : 2 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by norm_num) (by omega)
    show 1 ≤ Nat.log 2 N; omega
  have hval : ∀ r, r ≠ regE 6 → r ≠ rN → r ≠ rNu → ι.val r = 0 := fun r h1 h2 h3 => by
    rw [hι.val]; simp [h1, h2, h3]
  have hnu : ι.val rNu = ν := by
    rw [hι.val]; simp only; rw [if_neg (by decide), if_neg (by decide)]; simp [hνdef]
  have hNv : ι.val rN = N := by rw [hι.val]; simp only; rw [if_neg (by decide)]; simp
  have hEK0 : ∀ v, ι.val (EK v) = 0 := fun v =>
    hval _ (EK_ne6 v) (EK_ne v _ (by left; decide)) (EK_ne v _ (by right; decide))
  -- 1. `nN := N`
  have e1 := Codec.dupR_spec cap rN (EK .nN) dS (EK_ne _ _ (by left; decide)).symm (by decide)
    (EK_ne _ _ (by left; decide)) ι (hval _ (by decide) (by decide) (by decide)) (by rw [hNv, hEK0]; omega)
  rw [hEK0, hNv, Nat.zero_add] at e1
  set σ1 := ι.setv (EK .nN) N with hσ1
  -- 2. `lp := size ν`
  have hlp_ne : ∀ r ∈ ([rNu, pT1, pH, pB, dS] : List (Fin nrW)), EK (.e .lp) ≠ r := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact EK_ne _ _ (by first | (left; decide) | (right; decide))
  have e2 := sizeNuW_exec (cap := cap) (EK (.e .lp)) hlp_ne ν σ1
    (by rw [hσ1, upd_ne _ _ (EK_ne _ _ (by right; decide)).symm]; exact hnu)
    (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;>
          (rw [hσ1, upd_ne _ _ (EK_ne _ _ (by first | (left; decide) | (right; decide))).symm]
           exact hval _ (by decide) (by decide) (by decide)))
    (by rw [hσ1, upd_ne _ _ (EK_inj.ne (by decide)), hEK0]) (by omega)
  set σ2 := σ1.setv (EK (.e .lp)) ν.size with hσ2
  -- registers outside CHECK's file are those of `ι`
  have c2 : ∀ r : Fin nrW, (r.val < 60 ∨ 105 ≤ r.val) → σ2.val r = ι.val r := fun r hr => by
    rw [hσ2, upd_ne _ _ (EK_ne _ _ hr).symm, hσ1, upd_ne _ _ (EK_ne _ _ hr).symm]
  -- 3. `pX2 := L`, 4. `+ 4`
  have hY : ∀ r ∈ ([rNu, pX1, pX3, pH, pB, dS] : List (Fin nrW)), pX2 ≠ r := by decide
  have e3 := powNuW_exec (cap := cap) (g.lenExp + 2) pX2 hY ν hν1 σ2 (by rw [c2 _ (by right; decide)]; exact hnu)
    (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;>
          (rw [c2 _ (by first | (left; decide) | (right; decide))]; exact hval _ (by decide) (by decide) (by decide)))
    (by rw [c2 _ (by right; decide)]; exact hval _ (by decide) (by decide) (by decide)) (by
      show 2 * L + L * L + ν + 2 ≤ cap; omega)
  set σ3 := σ2.setv pX2 L with hσ3
  have e4 := NodeEmit.incN_spec (cap := cap) pX2 4 σ3 (by simp [hσ3]; omega)
  rw [show σ3.setv pX2 (σ3.val pX2 + 4) = σ2.setv pX2 (L + 4) by simp [hσ3, LitDecode.setv_setv]] at e4
  set σ4 := σ2.setv pX2 (L + 4) with hσ4
  -- 5. `lb := size (L + 4)`
  have hnd : ([pX2, pH, pB, EK (.e .lb)] : List (Fin nrW)).Nodup := by
    have h1 : pX2 ≠ EK (.e .lb) := (EK_ne _ _ (by right; decide)).symm
    have h2 : pH ≠ EK (.e .lb) := (EK_ne _ _ (by right; decide)).symm
    have h3 : pB ≠ EK (.e .lb) := (EK_ne _ _ (by right; decide)).symm
    have d1 : pX2 ≠ pH := by decide
    have d2 : pX2 ≠ pB := by decide
    have d3 : pH ≠ pB := by decide
    simp [List.nodup_cons, h1, h2, h3, d1, d2, d3]
  have e5 := Recovery.HTParts.sizeW_exec (cap := cap) (X := pX2) (H := pH) (B := pB) (C := EK (.e .lb))
    hnd
    (L + 4) (by omega) (L + 4) σ4 le_rfl (by simp [hσ4])
    (by rw [hσ4, upd_ne _ _ (by decide), c2 _ (by right; decide)]; exact hval _ (by decide) (by decide) (by decide))
    (by rw [hσ4, upd_ne _ _ (by decide), c2 _ (by right; decide)]; exact hval _ (by decide) (by decide) (by decide))
    (by
      rw [hσ4, upd_ne _ _ (EK_ne _ _ (by right; decide)), hσ2, upd_ne _ _ (EK_inj.ne (by decide)), hσ1,
        upd_ne _ _ (EK_inj.ne (by decide)), hEK0, Nat.zero_add]
      have := size_le_self (L + 4); omega)
  have hlb0 : σ4.val (EK (.e .lb)) = 0 := by
    rw [hσ4, upd_ne _ _ (EK_ne _ _ (by right; decide)), hσ2, upd_ne _ _ (EK_inj.ne (by decide)), hσ1,
      upd_ne _ _ (EK_inj.ne (by decide)), hEK0]
  rw [hlb0, Nat.zero_add] at e5
  set σ5 := (σ4.setv pX2 0).setv (EK (.e .lb)) (L + 4).size with hσ5
  -- 6. `rBs := b`
  have c5 : ∀ r : Fin nrW, (r.val < 60 ∨ 105 ≤ r.val) → r ≠ pX2 → σ5.val r = ι.val r := fun r hr h2 => by
    rw [hσ5, upd_ne _ _ (EK_ne _ _ hr).symm, upd_ne _ _ h2, hσ4, upd_ne _ _ h2, c2 r hr]
  have hY' : ∀ r ∈ ([rNu, pX1, pX3, pH, pB, dS] : List (Fin nrW)), rBs ≠ r := by decide
  have e6 := powNuW_exec (cap := cap) (g.lenRoot + 1) rBs hY' ν hν1 σ5 (by rw [c5 _ (by right; decide) (by decide)]; exact hnu)
    (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;>
          (rw [c5 _ (by first | (left; decide) | (right; decide)) (by decide)]
           exact hval _ (by decide) (by decide) (by decide)))
    (by rw [c5 _ (by right; decide) (by decide)]; exact hval _ (by decide) (by decide) (by decide))
    (by show 2 * b + b * b + ν + 2 ≤ cap; omega)
  set σ6 := σ5.setv rBs b with hσ6
  -- the state before CHECK
  have st6 : σ6.st = ι.st := by simp only [hσ6, hσ5, hσ4, hσ2, hσ1, WState.setv_st]
  have sh6 : σ6.sh = ι.sh := by simp only [hσ6, hσ5, hσ4, hσ2, hσ1, WState.setv_sh]
  have cell6 : σ6.cell = ι.cell := by simp only [hσ6, hσ5, hσ4, hσ2, hσ1, WState.setv_cell]
  have nB : ∀ v, EK v ≠ rBs := fun v => EK_ne v _ (by right; decide)
  have nX : ∀ v, EK v ≠ pX2 := fun v => EK_ne v _ (by right; decide)
  have z6 : ∀ v, v ≠ .nN → v ≠ .e .lb → v ≠ .e .lp → σ6.val (EK v) = 0 := fun v h1 h2 h3 => by
    rw [hσ6, upd_ne _ _ (nB v), hσ5, upd_ne _ _ (EK_inj.ne h2), upd_ne _ _ (nX v), hσ4, upd_ne _ _ (nX v), hσ2,
      upd_ne _ _ (EK_inj.ne h3), hσ1, upd_ne _ _ (EK_inj.ne h1), hEK0]
  have vN : σ6.val (EK .nN) = N := by
    rw [hσ6, upd_ne _ _ (nB _), hσ5, upd_ne _ _ (EK_inj.ne (by decide)), upd_ne _ _ (nX _), hσ4, upd_ne _ _ (nX _),
      hσ2, upd_ne _ _ (EK_inj.ne (by decide)), hσ1]; simp
  have vlp : σ6.val (EK (.e .lp)) = ν.size := by
    rw [hσ6, upd_ne _ _ (nB _), hσ5, upd_ne _ _ (EK_inj.ne (by decide)), upd_ne _ _ (nX _), hσ4, upd_ne _ _ (nX _),
      hσ2]; simp
  have vlb : σ6.val (EK (.e .lb)) = (L + 4).size := by
    rw [hσ6, upd_ne _ _ (nB _), hσ5]; simp
  have vb : σ6.val rBs = b := by rw [hσ6]; simp
  have c6 : ∀ r : Fin nrW, (r.val < 60 ∨ 105 ≤ r.val) → r ≠ pX2 → r ≠ rBs → σ6.val r = ι.val r :=
    fun r hr h2 h3 => by rw [hσ6, upd_ne _ _ h3, c5 r hr h2]
  -- 7. CHECK
  have vD1 := sD1_val hL
  have hblank : ∀ i : Fin (nsW D + 1), i.val ≠ 0 → i.val ≠ 1 → i.val ≠ 2 → i.val ≠ 16 → i.val ≠ 17 →
      (i.val < 21 ∨ 16 + D.tA ≤ i.val) → σ6.st i = [] := fun i h0 h1 h2 h16 h17 hr => by
    rw [st6]; exact hι.blank i h0 h1 h2 h16 h17 hr
  have hshW : ∀ i, i ≠ sWT D → σ6.sh i = 0 := fun i hi => by rw [sh6, hι.sh]; simp [hi]
  have vPT := sPT_val hL
  have vVV := sVV_val hL
  have vTT := sTT_val hL
  have hrd : Succinct.EvalReady (sD1 D W) (sPT D) (sVV D) EK (PCPPNative.descriptor B.src ++ []) (L + 4).size ν.size
      σ6 :=
    { st := by rw [st6, hι.d1, List.append_nil]
      sh := hshW _ (fin_ne_of_val (by simp [sWT, fixS]; omega))
      vv := ⟨0, by rw [hblank _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; rfl⟩
      vvh := hshW _ (fin_ne_of_val (by simp [sWT, fixS]; omega))
      ph := hshW _ (fin_ne_of_val (by simp [sWT, fixS]; omega))
      lb := vlb
      lp := vlp
      z := fun r hr => z6 _ (by simp) (by intro h; injection h with h; subst h; simp [Succinct.scratchE] at hr)
        (by intro h; injection h with h; subst h; simp [Succinct.scratchE] at hr)
      s := z6 _ (by simp) (by simp) (by simp)
      j := z6 _ (by simp) (by simp) (by simp)
      cd := z6 _ (by simp) (by simp) (by simp) }
  have hnd5 : ([sD1 D W, sPT D, sVV D, sTT D, sX D] : List (Fin (nsW D + 1))).Nodup := by
    have a1 : sD1 D W ≠ sPT D := fin_ne_of_val (by omega)
    have a2 : sD1 D W ≠ sVV D := fin_ne_of_val (by omega)
    have a3 : sD1 D W ≠ sTT D := fin_ne_of_val (by omega)
    have a4 : sD1 D W ≠ sX D := fin_ne_of_val (by show (sD1 D W).val ≠ 0; omega)
    have a5 : sPT D ≠ sVV D := fin_ne_of_val (by omega)
    have a6 : sPT D ≠ sTT D := fin_ne_of_val (by omega)
    have a7 : sPT D ≠ sX D := fin_ne_of_val (by show (sPT D).val ≠ 0; omega)
    have a8 : sVV D ≠ sTT D := fin_ne_of_val (by omega)
    have a9 : sVV D ≠ sX D := fin_ne_of_val (by show (sVV D).val ≠ 0; omega)
    have a10 : sTT D ≠ sX D := fin_ne_of_val (by show (sTT D).val ≠ 0; omega)
    simp [List.nodup_cons, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10]
  have hdl : (PCPPNative.descriptor B.src).length ≤ L := hfit
  have hs : B.src.nodes.length + 5 ≤ 2 ^ (L + 4).size := by
    have := Nat.lt_size_self (L + 4); have := nodes_le_descriptor B.src; omega
  obtain ⟨τ7, e7, hf1, hf2, hTT7, hse7, hP7, hV7⟩ := Succinct.checkW_check cap (sD1 D W) (sPT D) (sVV D) (sTT D) (sX D)
    hnd5 EK EK_inj σ6 B.src [] ν (L + 4).size ν.size x hrd
    (hblank _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
    (hblank _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
    (hshW _ (fin_ne_of_val (by simp [sWT, fixS]; omega))) vN
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact z6 _ (by simp) (by simp) (by simp))
    (by rw [st6]; exact hι.x) (hshW _ (fin_ne_of_val (by simp [sX, sWT, fixS])))
    (by rw [hpow]) hs (Nat.lt_size_self ν) (by
      simp only [List.append_nil]
      have := size_le_self (L + 4)
      omega)
  -- facts on the state after CHECK
  have nPT : ∀ i, i ∉ [sPT D, sVV D, sTT D] → τ7.st i = ι.st i ∧ τ7.sh i = ι.sh i := fun i hi => by
    rw [(hse7.1 i hi).1, (hse7.1 i hi).2, st6, sh6]; exact ⟨rfl, rfl⟩
  have mem3 : ∀ i : Fin (nsW D + 1), i.val < 18 ∨ 21 ≤ i.val → i ∉ [sPT D, sVV D, sTT D] := fun i hi h => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> omega
  have v7 : ∀ r, r ≠ EK .f → τ7.val r = σ6.val r := fun r hr => hse7.2.1 r (by simpa using hr)
  have FL7 : τ7.st (sFL D) = [true] := by
    rw [(nPT _ (mem3 _ (by have := sFL_val hL; omega))).1]; exact hFL
  have FLh7 : τ7.sh (sFL D) = 0 := by
    have hne : sFL D ≠ sWT D := fin_ne_of_val (by have := sFL_val hL; show (sFL D).val ≠ 2; omega)
    rw [(nPT _ (mem3 _ (by have := sFL_val hL; omega))).2, hι.sh]; simp only; rw [if_neg hne]
  -- 8. the flag
  set fv := τ7.val (EK .f) with hfv
  have e8 : WXExec cap (.ifr (EK .f) WMX.skip (WMX.wr (sFL D) false)) τ7
      (τ7.sets (sFL D) [decide (Outer.CheckAt ν x B.src)]) 2 := by
    by_cases hc : Outer.CheckAt ν x B.src
    · have h1 : fv = 1 := hf2.2 hc
      refine WXExec.cast cap (WXExec.ifrT (by rw [← hfv, h1]; omega) (WXExec.skip cap τ7)) ?_ (by omega)
      apply WState.eq <;> try rfl
      funext i; by_cases hi : i = sFL D
      · subst hi; simp [FL7, hc]
      · simp [Function.update_of_ne hi]
    · have h0 : fv = 0 := by have := mt hf2.1 hc; omega
      refine WXExec.cast cap (WXExec.ifrF (by rw [← hfv, h0]) (WXExec.wr (cap := cap) (sFL D) false τ7)) ?_ (by omega)
      rw [FL7, FLh7]; simp [hc]; rfl
  set τ8 := τ7.sets (sFL D) [decide (Outer.CheckAt ν x B.src)] with hτ8
  -- 9. the clears
  have v8 : ∀ r, r ≠ EK .f → τ8.val r = σ6.val r := fun r hr => by rw [hτ8, WState.sets_val]; exact v7 r hr
  have nf : ∀ v, v ≠ .f → EK v ≠ EK .f := fun v h => EK_inj.ne h
  have w9a : τ8.val (EK .f) = fv := by rw [hτ8, WState.sets_val]
  have e9a := wclear_spec (cap := cap) (EK .f) fv τ8 w9a (by rw [w9a]; omega)
  have w9b : (τ8.setv (EK .f) 0).val (EK (.e .lb)) = (L + 4).size := by
    rw [upd_ne _ _ (nf _ (by simp)), v8 _ (nf _ (by simp)), vlb]
  have e9b := wclear_spec (cap := cap) (EK (.e .lb)) (L + 4).size (τ8.setv (EK .f) 0) w9b
    (by rw [w9b]; have := size_le_self (L + 4); omega)
  have w9c : ((τ8.setv (EK .f) 0).setv (EK (.e .lb)) 0).val (EK (.e .lp)) = ν.size := by
    rw [upd_ne _ _ (EK_inj.ne (by decide)), upd_ne _ _ (nf _ (by simp)), v8 _ (nf _ (by simp)), vlp]
  have e9c := wclear_spec (cap := cap) (EK (.e .lp)) ν.size ((τ8.setv (EK .f) 0).setv (EK (.e .lb)) 0) w9c
    (by rw [w9c]; have := size_le_self ν; omega)
  have w9d : (((τ8.setv (EK .f) 0).setv (EK (.e .lb)) 0).setv (EK (.e .lp)) 0).val (EK .nN) = N := by
    rw [upd_ne _ _ (EK_inj.ne (by decide)), upd_ne _ _ (EK_inj.ne (by decide)), upd_ne _ _ (nf _ (by simp)),
      v8 _ (nf _ (by simp)), vN]
  have e9d := wclear_spec (cap := cap) (EK .nN) N (((τ8.setv (EK .f) 0).setv (EK (.e .lb)) 0).setv (EK (.e .lp)) 0)
    w9d (by rw [w9d]; omega)
  have hnuK : ∀ v, rNu ≠ EK v := fun v => (EK_ne v _ (by right; decide)).symm
  have w9e : ((((τ8.setv (EK .f) 0).setv (EK (.e .lb)) 0).setv (EK (.e .lp)) 0).setv (EK .nN) 0).val rNu = ν := by
    rw [upd_ne _ _ (hnuK _), upd_ne _ _ (hnuK _), upd_ne _ _ (hnuK _), upd_ne _ _ (hnuK _),
      v8 _ (hnuK _), c6 _ (by right; decide) (by decide) (by decide)]; exact hnu
  have e9e := wclear_spec (cap := cap) rNu ν
    ((((τ8.setv (EK .f) 0).setv (EK (.e .lb)) 0).setv (EK (.e .lp)) 0).setv (EK .nN) 0) w9e (by rw [w9e]; omega)
  set τ9 := ((((τ8.setv (EK .f) 0).setv (EK (.e .lb)) 0).setv (EK (.e .lp)) 0).setv (EK .nN) 0).setv rNu 0 with hτ9
  have hpL : ν ^ (g.lenExp + 2) = L := rfl
  have hpb : ν ^ (g.lenRoot + 1) = b := rfl
  rw [hpL] at e3
  rw [hpb] at e6
  refine ⟨τ9, ?_, ?_⟩
  · refine WXExec.mono (WXExec.seq (WXExec.wm e1) (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq (WXExec.wm e4)
      (WXExec.seq e5 (WXExec.seq e6 (WXExec.seq (WXExec.wm e7) (WXExec.seq e8
      (WXExec.wm (WExec.seq e9a (WExec.seq e9b (WExec.seq e9c (WExec.seq e9d e9e))))))))))))) ?_
    unfold costK lbOf lpOf
    simp only [List.append_nil, ← hνdef, ← hLdef, ← hbdef]
    have : fv ≤ 1 := hf1
    rw [show g.lenExp + 2 + 1 = g.lenExp + 3 from rfl, show g.lenRoot + 1 + 1 = g.lenRoot + 2 from rfl]
    omega
  · have hFLv := sFL_val hL
    have s98 : ∀ i, τ9.st i = τ8.st i := fun i => by simp only [hτ9, WState.setv_st]
    have s87 : ∀ i, i ≠ sFL D → τ8.st i = τ7.st i := fun i hi => by simp [hτ8, Function.update_of_ne hi]
    have far : ∀ i : Fin (nsW D + 1), i.val ≠ 16 → (i.val < 18 ∨ 21 ≤ i.val) → τ9.st i = ι.st i := fun i h16 hr => by
      rw [s98, s87 i (fin_ne_of_val (by omega)), (nPT i (mem3 i hr)).1]
    have hEKs : ∀ v, EK v ≠ regE 6 ∧ EK v ≠ rN ∧ EK v ≠ rNu ∧ EK v ≠ rBs ∧ EK v ≠ pX2 := fun v =>
      ⟨EK_ne6 v, EK_ne v _ (by left; decide), EK_ne v _ (by right; decide), EK_ne v _ (by right; decide),
        EK_ne v _ (by right; decide)⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [far _ (by simp [sX, fixS]) (by left; simp [sX, fixS])]; exact hι.x
    · rw [far _ (by simp [sBW, fixS]) (by left; simp [sBW, fixS])]; exact hι.bw
    · rw [far _ (by simp [sWT, fixS]) (by left; simp [sWT, fixS])]; exact hι.wt
    · rw [s98]; simp [hτ8, hνdef]
    · rw [far _ (by have := sD2_val hL; omega) (by right; have := sD2_val hL; omega)]; exact hι.d2
    · rw [far _ (by have := sMW_val hL; omega) (by right; have := sMW_val hL; omega)]; exact hι.mw
    · intro i h0 h1 h2 h16 hr
      have h16' : i.val ≠ 16 := fun h => by have := h16 (by omega); omega
      have h1720 : i.val < 17 ∨ 21 ≤ i.val := by by_cases h : 16 ≤ i.val <;> [right; left] <;> [exact h16 h; omega]
      rw [far i h16' (by omega)]
      exact hι.blank i h0 h1 h2 h16' (by omega) hr
    · rw [hτ9]
      simp only [WState.setv_sh, hτ8, WState.sets_sh]
      funext i
      by_cases hi : i ∈ [sPT D, sVV D, sTT D]
      · have hW : i ≠ sWT D := by
          intro h; subst h; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with h | h | h <;> have := congrArg Fin.val h <;> simp [sWT, fixS] at this <;> omega
        rw [if_neg hW]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl
        · exact hP7
        · exact hV7
        · exact hTT7
      · rw [(nPT i hi).2, hι.sh]
    · funext r
      obtain ⟨e6', eN, eNu, eB, eX⟩ := hEKs .nN
      simp only [hτ9, WState.setv_val, Function.update_apply]
      by_cases r1 : r = rNu
      · subst r1; rw [if_pos rfl, if_neg (by decide), if_neg (by decide), if_neg (by decide)]
      by_cases r2 : r = EK .nN
      · subst r2; simp [e6', eN, eB]
      by_cases r3 : r = EK (.e .lp)
      · subst r3; simp [(hEKs _).1, (hEKs _).2.1, (hEKs _).2.2.2.1]
      by_cases r4 : r = EK (.e .lb)
      · subst r4; simp [(hEKs _).1, (hEKs _).2.1, (hEKs _).2.2.2.1]
      by_cases r5 : r = EK .f
      · subst r5; simp [(hEKs _).1, (hEKs _).2.1, (hEKs _).2.2.2.1]
      rw [if_neg r1, if_neg r2, if_neg r3, if_neg r4, if_neg r5, v8 r r5]
      by_cases r6 : r = rBs
      · subst r6; rw [vb, if_neg (by decide), if_neg (by decide), if_pos rfl]
      by_cases r7 : r = pX2
      · subst r7
        rw [show σ6.val pX2 = 0 by
          rw [hσ6, upd_ne _ _ (by decide), hσ5, upd_ne _ _ (EK_ne _ _ (by right; decide)).symm]; simp]
        rw [if_neg (by decide), if_neg (by decide), if_neg (by decide)]
      by_cases hEK : r.val < 60 ∨ 105 ≤ r.val
      · rw [c6 r hEK r7 r6, hι.val]
        simp only [r6, r1, if_false]
      · have hz : σ6.val r = ι.val r := by
          rw [hσ6, upd_ne _ _ r6, hσ5, upd_ne _ _ r4, upd_ne _ _ r7, hσ4, upd_ne _ _ r7, hσ2, upd_ne _ _ r3, hσ1,
            upd_ne _ _ r2]
        have h6 : r ≠ regE 6 := fun h => hEK (by left; rw [h]; decide)
        have hrN : r ≠ rN := fun h => hEK (by left; rw [h]; decide)
        rw [hz, hι.val]
        simp only [h6, hrN, r1, r6, if_false]
    · simp only [hτ9, WState.setv_cell, hτ8, WState.sets_cell]
      rw [hse7.2.2, cell6]; exact hι.cell

end

end NearCubicGates.Close.Setup
