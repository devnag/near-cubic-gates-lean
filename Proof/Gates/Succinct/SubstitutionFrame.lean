import Proof.Gates.Succinct.SubstitutionEmit

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

/-- A frame: only the streams `S` and the registers `R` change. -/
abbrev Fr (σ τ : WState 4 nrH) (S : List (Fin (4 + 1))) (R : List HReg) : Prop := SameExcept σ τ S (R.map regH)

theorem Fr.v {σ τ : WState 4 nrH} {S : List (Fin (4 + 1))} {R : List HReg} (h : Fr σ τ S R) {u : HReg} (hu : u ∉ R) :
    τ.val (regH u) = σ.val (regH u) := h.val (by simpa using hu)

theorem Fr.s {σ τ : WState 4 nrH} {S : List (Fin (4 + 1))} {R : List HReg} (h : Fr σ τ S R) {i : Fin (4 + 1)}
    (hi : i ∉ S) : τ.st i = σ.st i ∧ τ.sh i = σ.sh i := ⟨h.st hi, h.sh hi⟩

theorem Fr.trans' {σ τ ρ : WState 4 nrH} {S S' : List (Fin (4 + 1))} {R R' : List HReg} (h1 : Fr σ τ S R)
    (h2 : Fr τ ρ S' R') : Fr σ ρ (S ++ S') (R ++ R') := by
  have := SameExcept.comp' h1 h2
  show SameExcept σ ρ (S ++ S') ((R ++ R').map regH)
  rw [List.map_append]; exact this

theorem Fr.mono {σ τ : WState 4 nrH} {S S' : List (Fin (4 + 1))} {R R' : List HReg} (h : Fr σ τ S R)
    (hS : ∀ x ∈ S, x ∈ S') (hR : ∀ u ∈ R, u ∈ R') : Fr σ τ S' R' :=
  SameExcept.weaken h hS (fun r hr => by
    simp only [List.mem_map] at hr ⊢; obtain ⟨u, hu, rfl⟩ := hr; exact ⟨u, hR u hu, rfl⟩)

/-- Frames of the basic updates. -/
theorem fr_setv (σ : WState 4 nrH) (u : HReg) (v : ℕ) : Fr σ (σ.setv (regH u) v) [] [u] :=
  ⟨fun y _ => ⟨rfl, rfl⟩, fun r hr => by
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp [Function.update_apply, hr], rfl⟩

theorem fr_seth (σ : WState 4 nrH) (i : Fin (4 + 1)) (n : ℕ) : Fr σ (σ.seth i n) [i] [] :=
  ⟨fun y hy => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    simp [Function.update_apply, hy], fun r _ => rfl, rfl⟩

theorem fr_sets (σ : WState 4 nrH) (i : Fin (4 + 1)) (l : List Bool) : Fr σ (σ.sets i l) [i] [] :=
  ⟨fun y hy => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    simp [Function.update_apply, hy], fun r _ => rfl, rfl⟩

theorem fr_refl (σ : WState 4 nrH) (S : List (Fin (4 + 1))) (R : List HReg) : Fr σ σ S R := SameExcept.refl _ _ _

theorem fr_appendO (σ : WState 4 nrH) (u : List Bool) : Fr σ (appendO σ sO (regH (.w 7)) u) [sO] [.w 7] := by
  refine ⟨fun y hy => ?_, fun r hr => ?_, by simp⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; simp [Function.update_apply, hy]
  · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp [Function.update_apply, hr]

/-! ## Reads -/

/-- **An exact read**, framed. -/
theorem rd_fr (cap : ℕ) (i : Fin (4 + 1)) (cd tgt : HReg) (h1 : ∀ r, cd ≠ .f r) (h2 : ∀ r, tgt ≠ .f r)
    (h3 : tgt ≠ cd) (h4 : tgt ≠ .pk) (h5 : tgt ≠ .pt) (h6 : cd ≠ .pk) (h7 : cd ≠ .pt)
    (σ : WState 4 nrH) (pre rest : List Bool) (x : ℕ) (hst : σ.st i = pre ++ natWord x ++ rest)
    (hsh : σ.sh i = pre.length) (hf : ∀ r, σ.val (regH (.f r)) = 0) (hpk : σ.val (regH .pk) = 0)
    (hpt : σ.val (regH .pt) = 0) (ht : σ.val (regH tgt) = 0) (hcap : σ.val (regH cd) + 8 * x + 16 ≤ cap) :
    ∃ τ, WExec cap (rd i (fam cd) tgt) σ τ (readCost x) ∧ τ.sh i = pre.length + (natWord x).length ∧
      τ.val (regH cd) = σ.val (regH cd) + (natWord x).length ∧ τ.val (regH tgt) = x ∧ Fr σ τ [i] [cd, tgt] ∧
      τ.st i = σ.st i := by
  have e := readEx_spec cap i (fam cd) (regH .pk) (regH .pt) (regH tgt) (rdRegs cd tgt h1 h2 h3 h4 h5 h6 h7) σ pre rest x
    hst hsh (famZero _ _ hf) hpk hpt ht (by rw [fam_cd]; omega)
  refine ⟨_, e, by simp, by simp [Function.update_apply, Ne.symm h3], by simp, ?_, by simp⟩
  refine ⟨fun y hy => ?_, fun r hr => ?_, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; simp [Function.update_apply, hy]
  · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [Function.update_apply, hr.1, hr.2]

/-- **A skipped field**, framed. -/
theorem sk1_fr (cap : ℕ) (i : Fin (4 + 1)) (cd : HReg) (h1 : ∀ r, cd ≠ .f r) (h6 : cd ≠ .z) (h7 : cd ≠ .jk)
    (σ : WState 4 nrH) (pre rest : List Bool) (x : ℕ) (hst : σ.st i = pre ++ natWord x ++ rest)
    (hsh : σ.sh i = pre.length) (hf : ∀ r, σ.val (regH (.f r)) = 0) (hz : σ.val (regH .z) = 0)
    (hj : σ.val (regH .jk) = 0) (hcap : σ.val (regH cd) + 2 * natBitLength x + 12 ≤ cap) :
    ∃ τ, WExec cap (sk1 i (fam cd)) σ τ (skipCost x) ∧ τ.sh i = pre.length + (natWord x).length ∧
      τ.val (regH cd) = σ.val (regH cd) + (natWord x).length ∧ Fr σ τ [i] [cd] ∧ τ.st i = σ.st i := by
  have e := skipF_spec cap i (fam cd) (fam_inj _ h1) (regH .z) (regH .jk) (famNe _ _ (by simp) (Ne.symm h6))
    (famNe _ _ (by simp) (Ne.symm h7)) σ pre rest x hst hsh (famZero _ _ hf) hz hj (by rw [fam_cd]; omega)
  refine ⟨_, e, by simp, by simp, ?_, by simp⟩
  refine ⟨fun y hy => ?_, fun r hr => ?_, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; simp [Function.update_apply, hy]
  · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp [Function.update_apply, hr]

/-- **A cleared register**, framed. -/
theorem clr_fr (cap : ℕ) (u : HReg) (σ : WState 4 nrH) (hcap : σ.val (regH u) ≤ cap) :
    ∃ τ, WExec cap (WM.clear (regH u)) σ τ (3 * σ.val (regH u) + 1) ∧ τ.val (regH u) = 0 ∧ Fr σ τ [] [u] :=
  ⟨_, wclear_spec cap (regH u) _ σ rfl hcap, by simp, fr_setv σ u 0⟩

/-- **An addition**, framed. -/
theorem add_fr (cap : ℕ) (src dst : HReg) (h1 : src ≠ dst) (h2 : src ≠ .t) (h3 : dst ≠ .t) (σ : WState 4 nrH)
    (ht : σ.val (regH .t) = 0) (hcap : σ.val (regH dst) + σ.val (regH src) ≤ cap) :
    ∃ τ, WExec cap (add src dst) σ τ (18 * σ.val (regH src) + 3) ∧
      τ.val (regH dst) = σ.val (regH dst) + σ.val (regH src) ∧ Fr σ τ [] [dst] :=
  ⟨_, addTo_spec cap (regH src) (regH dst) (regH .t) (by simpa using h1) (by simpa using h2) (by simpa using h3) σ ht
    (by omega) hcap, by simp, fr_setv σ dst _⟩

/-- **An image**, framed. -/
theorem pos_fr (cap : ℕ) (X P : HReg) (hX : X ∉ [HReg.sc, .sb, .nB1, .oB, .t, P]) (hP : P ∉ [HReg.sc, .sb, .nB1, .oB, .t])
    (σ : WState 4 nrH) (fl : List Bool) (hOF : σ.st sF = fl) (hOFh : σ.sh sF = 0) (hp : σ.val (regH P) = 0)
    (hsc : σ.val (regH .sc) = 0) (hsb : σ.val (regH .sb) = 0) (ht : σ.val (regH .t) = 0)
    (hcap : posF fl (σ.val (regH X)) (σ.val (regH .nB1)) (σ.val (regH .oB)) + σ.val (regH X) * σ.val (regH .nB1) +
      σ.val (regH .nB1) + 2 * σ.val (regH X) + 2 ≤ cap) :
    ∃ τ, WExec cap (pos X P) σ τ (posCost (σ.val (regH X)) (σ.val (regH .nB1)) (σ.val (regH .oB))) ∧
      τ.val (regH P) = posF fl (σ.val (regH X)) (σ.val (regH .nB1)) (σ.val (regH .oB)) ∧ Fr σ τ [] [P] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hX hP
  have e := posW_spec cap sF (regH X) (regH P) (regH .sc) (regH .sb) (regH .nB1) (regH .oB) (regH .t)
    (by simp [hX.1, hX.2.1, hX.2.2.1, hX.2.2.2.1, hX.2.2.2.2.1, hX.2.2.2.2.2, hP.1, hP.2.1, hP.2.2.1, hP.2.2.2.1,
      hP.2.2.2.2, Ne.symm hX.1, Ne.symm hX.2.1]) σ fl hOF hOFh hp hsc hsb ht hcap
  exact ⟨_, e, by simp, fr_setv σ P _⟩

/-- **A comparison**, framed. -/
theorem less_fr (cap : ℕ) (A B : HReg) (hR : [A, B, HReg.ga, .gb, .gz, .lt, .t].Nodup) (σ : WState 4 nrH)
    (hz : ∀ u ∈ [HReg.ga, .gb, .gz, .lt, .t], σ.val (regH u) = 0) (hcap : σ.val (regH A) + σ.val (regH B) + 3 ≤ cap) :
    ∃ τ, WExec cap (lessW A B) σ τ (30 * (σ.val (regH A) + σ.val (regH B)) + 40) ∧
      τ.val (regH .lt) = (if σ.val (regH A) < σ.val (regH B) then 1 else 0) ∧ Fr σ τ [] [.lt] := by
  have hR' : [regH A, regH B, regH .ga, regH .gb, regH .gz, regH .lt, regH .t].Nodup := by
    have := hR.map regH_inj
    simpa using this
  have e := ltWM_spec cap (regH A) (regH B) (regH .ga) (regH .gb) (regH .gz) (regH .lt) (regH .t) hR' σ
    (hz _ (by simp)) (hz _ (by simp)) (hz _ (by simp)) (hz _ (by simp)) (hz _ (by simp)) hcap
  exact ⟨_, e, by simp, fr_setv σ .lt _⟩

end NearCubicGates.Close.Succinct.SubstMachine
