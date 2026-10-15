import Proof.Gates.Succinct.SubstitutionSizes

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Succinct.SubstMachine

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Succinct
open RepairRepresentation (natWord)

theorem marks_app (u v : List Bool) : marks (u ++ v) = marks u ++ marks v := by simp [marks, List.flatMap_append]

theorem marks_length' (u : List Bool) : (marks u).length = 2 * u.length := by
  induction u with
  | nil => rfl
  | cons b u ih => simp [marks, List.flatMap_cons] at ih ⊢; omega

@[simp] theorem WR_apply (i : Fin 8) : WR i = regH (.w i) := rfl

/-- The output stream holds `marks out`, head and position register at its end. -/
def OutOK (τ : WState 4 nrH) (out : List Bool) : Prop :=
  τ.st sO = marks out ∧ τ.sh sO = 2 * out.length ∧ τ.val (regH (.w 7)) = 2 * out.length

/-- The writer's scratch is clean. -/
def WClean (τ : WState 4 nrH) : Prop := (∀ i : Fin 8, i ≠ 7 → τ.val (regH (.w i)) = 0) ∧ τ.val (regH .wt) = 0

/-- A template reads only named registers other than the writer's. -/
def TOK (f : CheckedPCPP.NodeEmit.Field nrH) : Prop := ∀ x ∈ f.1, ∃ u, x = regH u ∧ (∀ i, u ≠ .w i) ∧ u ≠ .wt

theorem fieldOK_of (f : CheckedPCPP.NodeEmit.Field nrH) (h : TOK f) : CheckedPCPP.NodeEmit.FieldOK WR (regH .wt) f := by
  intro x hx
  obtain ⟨u, rfl, h1, h2⟩ := h x hx
  refine ⟨fun i e => ?_, fun e => h2 (regH_inj e)⟩
  exact h1 i (regH_inj e)

theorem appendO_outOK (σ : WState 4 nrH) (out u : List Bool) (h : OutOK σ out) :
    OutOK (appendO σ sO (regH (.w 7)) (marks u)) (out ++ u) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · simp [h1, marks_app]
  · simp [h2, marks_length']; ring
  · simp [h3, marks_length']; ring

theorem appendO_wclean (σ : WState 4 nrH) (u : List Bool) (h : WClean σ) : WClean (appendO σ sO (regH (.w 7)) u) := by
  refine ⟨fun i hi => ?_, ?_⟩
  · have : regH (.w i) ≠ regH (.w 7) := by simpa using hi
    simp [Function.update_apply, this, h.1 i hi]
  · simp [Function.update_apply, h.2]

theorem appendO_val_ne (σ : WState 4 nrH) (u : List Bool) (v : HReg) (hv : v ≠ .w 7) :
    (appendO σ sO (regH (.w 7)) u).val (regH v) = σ.val (regH v) := by
  simp [Function.update_apply, hv]

theorem appendO_st_ne (σ : WState 4 nrH) (r : Fin nrH) (u : List Bool) (i : Fin (4 + 1)) (hi : i ≠ sO) :
    (appendO σ sO r u).st i = σ.st i ∧ (appendO σ sO r u).sh i = σ.sh i := by
  simp [Function.update_apply, hi]

/-- **One node of `D_B`** (paper §11.4; `NodeEmit.nodeW_spec`). -/
theorem emitN_spec (cap : ℕ) (σ : WState 4 nrH) (a b c : CheckedPCPP.NodeEmit.Field nrH) {n : ℕ} (nd : BooleanNode n)
    (out : List Bool) (hout : OutOK σ out) (hcl : WClean σ) (hok : TOK a ∧ TOK b ∧ TOK c)
    (hlen : a.1.length ≤ 3 ∧ b.1.length ≤ 3 ∧ c.1.length ≤ 3)
    (hd : CheckedPCPP.NodeEmit.fieldVal σ a = PCPPRequestNodeSchema.fields nd 0 ∧
      CheckedPCPP.NodeEmit.fieldVal σ b = PCPPRequestNodeSchema.fields nd 1 ∧
      CheckedPCPP.NodeEmit.fieldVal σ c = PCPPRequestNodeSchema.fields nd 2)
    (V : ℕ) (hV : ∀ i, PCPPRequestNodeSchema.fields nd i ≤ V)
    (hcap : 2 * out.length + 2 * (PCPPRequestNodeSchema.native nd).length + 7 * V + 12 ≤ cap) :
    WExec cap (emit a b c) σ (appendO σ sO (regH (.w 7)) (marks (PCPPRequestNodeSchema.native nd)))
      (CheckedPCPP.NodeEmit.nodeCost V) := by
  have hTR : ∀ i : Fin 8, regH .wt ≠ WR i := fun i e => by simp [WR] at e
  have h := CheckedPCPP.NodeEmit.nodeW_spec cap sO WR (regH .wt) hTR (tm a b c)
    (fun i => by fin_cases i <;> simp [tm] <;> first | exact fieldOK_of _ hok.1 | exact fieldOK_of _ hok.2.1 |
      exact fieldOK_of _ hok.2.2) nd σ
    (fun i => by fin_cases i <;> simp [tm] <;> first | exact hd.1 | exact hd.2.1 | exact hd.2.2)
    (fun i => by fin_cases i <;> simp [tm] <;> omega) V hV ⟨fun i hi => hcl.1 i hi, hcl.2⟩
    (by rw [hout.1, hout.2.1, marks_length']) (by rw [WR_apply, hout.2.2]; omega)
  rw [WR_apply] at h
  exact h

/-- **One field of `D_B`'s header** (paper §11.4; `NodeEmit.fieldW_spec`). -/
theorem fieldN_spec (cap : ℕ) (σ : WState 4 nrH) (u : HReg) (hu : (∀ i, u ≠ .w i) ∧ u ≠ .wt) (out : List Bool)
    (hout : OutOK σ out) (hcl : WClean σ)
    (hcap : σ.val (regH u) + 2 * out.length + 6 * natBitLength (σ.val (regH u)) + 6 ≤ cap) :
    WExec cap (CheckedPCPP.NodeEmit.fieldW sO WR (regH .wt) ([regH u], 0)) σ
      (appendO σ sO (regH (.w 7)) (marks (natWord (σ.val (regH u)))))
      (CheckedPCPP.NodeEmit.fieldCost (σ.val (regH u)) 1) := by
  have hTR : ∀ i : Fin 8, regH .wt ≠ WR i := fun i e => by simp [WR] at e
  have h := CheckedPCPP.NodeEmit.fieldW_spec cap sO WR (regH .wt) hTR ([regH u], 0)
    (fieldOK_of _ (fun x hx => ⟨u, by simpa using hx, hu.1, hu.2⟩)) σ ⟨fun i hi => hcl.1 i hi, hcl.2⟩
    (by rw [hout.1, hout.2.1, marks_length'])
    (by simp only [CheckedPCPP.NodeEmit.fieldVal, CheckedPCPP.NodeEmit.regSum, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero]
        rw [WR_apply, hout.2.2]; omega)
  simp only [CheckedPCPP.NodeEmit.fieldVal, CheckedPCPP.NodeEmit.regSum, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero, WR_apply] at h
  exact h

end NearCubicGates.Close.Succinct.SubstMachine
