import Proof.Gates.Succinct.SubstitutionProg

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Succinct.SubstMachine

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.Bindings.MW20
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Succinct
open RepairRepresentation (natWord)

variable {q : ℕ}

/-! ## The inputs -/

/-- The fields of `B`'s nodes, in order. -/
def bfl (B : BooleanCircuit q) : List ℕ :=
  B.nodes.flatMap fun nd => [PCPPRequestNodeSchema.fields nd 0, PCPPRequestNodeSchema.fields nd 1,
    PCPPRequestNodeSchema.fields nd 2]

theorem native_bfl (B : BooleanCircuit q) :
    B.nodes.flatMap PCPPRequestNodeSchema.native = (bfl B).flatMap natWord := by
  unfold bfl
  rw [List.flatMap_assoc]
  congr 1
  funext nd
  simp [PCPPRequestNodeSchema.native]

theorem bfl_length (B : BooleanCircuit q) : (bfl B).length = 3 * B.nodes.length := by
  unfold bfl
  induction B.nodes with
  | nil => simp
  | cons nd l ih => simp [List.flatMap_cons, ih]; ring

theorem fields_le {n : ℕ} (nd : BooleanNode n) (t : ℕ) (hw : nd.WellFormedAt t) (i : Fin 3) :
    PCPPRequestNodeSchema.fields nd i ≤ t + n + 5 := by
  cases nd with
  | const b => fin_cases i <;> simp [PCPPRequestNodeSchema.fields] <;> cases b <;> simp
  | input j => fin_cases i <;> simp [PCPPRequestNodeSchema.fields] <;> omega
  | not c => fin_cases i <;> simp [PCPPRequestNodeSchema.fields, BooleanNode.WellFormedAt] at hw ⊢ <;> omega
  | and l r => fin_cases i <;> simp [PCPPRequestNodeSchema.fields, BooleanNode.WellFormedAt] at hw ⊢ <;> omega
  | or l r => fin_cases i <;> simp [PCPPRequestNodeSchema.fields, BooleanNode.WellFormedAt] at hw ⊢ <;> omega

theorem bfl_le (B : BooleanCircuit q) : ∀ x ∈ bfl B, x ≤ B.nodes.length + q + 5 := by
  intro x hx
  unfold bfl at hx
  rw [List.mem_flatMap] at hx
  obtain ⟨nd, hnd, hx⟩ := hx
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hnd
  have hw := B.wellFormed ⟨t, ht⟩
  simp only [List.get_eq_getElem] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · have := fields_le _ t hw 0; omega
  · have := fields_le _ t hw 1; omega
  · have := fields_le _ t hw 2; omega

theorem natWord_len3 (v : ℕ) : 3 ≤ (natWord v).length := by
  rw [natWord_length]; have : 1 ≤ natBitLength v := by unfold natBitLength; omega
  omega

theorem flatMap_natWord_len (l : List ℕ) : 3 * l.length ≤ (l.flatMap natWord).length := by
  induction l with
  | nil => simp
  | cons v l ih => simp only [List.flatMap_cons, List.length_append, List.length_cons]; have := natWord_len3 v; omega

/-- The register values after the header. -/
def V1 (o : OracleOutput) (B : BooleanCircuit q) : HReg → ℕ
  | .nC => o.circuit.nodes.length
  | .q => q
  | .nB => B.nodes.length
  | .bq => hc q + 1
  | .nB1 => B.nodes.length - 1
  | .oB => B.output.val
  | .cdW => (natWord o.circuit.nodes.length).length
  | _ => 0

/-- The state after the header. -/
structure HeadPost (o : OracleOutput) (B : BooleanCircuit q) (τ : WState 4 nrH) : Prop where
  stW : τ.st sW = o.word
  stD : τ.st sD = PCPPNative.descriptor B
  stL : τ.st sL = natWord o.ell
  stO : τ.st sO = []
  stF : τ.st sF = []
  shW : τ.sh sW = (natWord o.ell).length + (natWord o.circuit.nodes.length).length
  shD : τ.sh sD = (natWord q).length + (natWord B.nodes.length).length
  shO : τ.sh sO = 0
  shF : τ.sh sF = 0
  shL : τ.sh sL = 0
  val : ∀ u, τ.val (regH u) = V1 o B u
  cell : τ.cell = false

/-- The start: the two port words, everything else blank. -/
def start (w d : List Bool) : WState 4 nrH :=
  ⟨fun _ => 0, fun i => if i = sW then w else if i = sD then d else [], fun _ => 0, false⟩

theorem ofFn_prefix (w rest : List Bool) :
    List.ofFn (fun j : Fin w.length => readTapeBit (w ++ rest) (0 + j.val)) = w := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp [readTapeBit, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using h1),
    List.getElem?_eq_getElem h2]

theorem oracleNodeWord_len3 {n a : ℕ} (nd : OracleNode n a) : 3 ≤ (oracleNodeWord nd).length := by
  have h0 := natWord_len3 0; have h1 := natWord_len3 1; have h2 := natWord_len3 2; have h3 := natWord_len3 3
  have h4 := natWord_len3 4; have h5 := natWord_len3 5
  cases nd <;> simp only [oracleNodeWord, List.length_append] <;> omega

theorem cw_len {n a : ℕ} (l : List (OracleNode n a)) : l.length ≤ (l.flatMap oracleNodeWord).length := by
  induction l with
  | nil => simp
  | cons v l ih => simp only [List.flatMap_cons, List.length_append, List.length_cons]; have := oracleNodeWord_len3 v; omega

theorem word_eq (o : OracleOutput) : o.word = natWord o.ell ++ natWord o.circuit.nodes.length ++
    o.circuit.nodes.flatMap oracleNodeWord ++ natWord o.circuit.output.val := rfl

theorem desc_eq (B : BooleanCircuit q) : PCPPNative.descriptor B = natWord q ++ natWord B.nodes.length ++
    (bfl B).flatMap natWord ++ natWord B.output.val := by
  rw [PCPPNative.descriptor_eq, native_bfl]

/-- The size parameter of one substitution: both port words and the width. -/
def sizeS (o : OracleOutput) (B : BooleanCircuit q) : ℕ := o.word.length + (PCPPNative.descriptor B).length + q + 1

theorem sizes_le (o : OracleOutput) (B : BooleanCircuit q) :
    o.circuit.nodes.length + 1 ≤ sizeS o B ∧ B.nodes.length + 1 ≤ sizeS o B ∧ q + 1 ≤ sizeS o B ∧
      (natWord o.ell).length + (natWord o.circuit.nodes.length).length ≤ o.word.length ∧
      natBitLength o.ell ≤ o.word.length ∧
      (natWord q).length + (natWord B.nodes.length).length + ((bfl B).flatMap natWord).length +
        (natWord B.output.val).length = (PCPPNative.descriptor B).length ∧
      (natWord o.circuit.nodes.length).length ≤ o.word.length := by
  have h1 := cw_len o.circuit.nodes
  have h2 := flatMap_natWord_len (bfl B)
  have h3 := bfl_length B
  have hw : o.word.length = (natWord o.ell).length + (natWord o.circuit.nodes.length).length +
      (o.circuit.nodes.flatMap oracleNodeWord).length + (natWord o.circuit.output.val).length := by
    rw [word_eq]; simp only [List.length_append]
  have hd : (PCPPNative.descriptor B).length = (natWord q).length + (natWord B.nodes.length).length +
      ((bfl B).flatMap natWord).length + (natWord B.output.val).length := by
    rw [desc_eq]; simp only [List.length_append]
  have hl := natWord_length o.ell
  unfold sizeS
  refine ⟨by omega, by omega, by omega, by omega, by omega, hd.symm, by omega⟩

/-- The five streams' contents and heads. -/
def StrAt (τ : WState 4 nrH) (w d o f l : List Bool) (hw hd ho hf hl : ℕ) : Prop :=
  τ.st sW = w ∧ τ.st sD = d ∧ τ.st sO = o ∧ τ.st sF = f ∧ τ.st sL = l ∧
  τ.sh sW = hw ∧ τ.sh sD = hd ∧ τ.sh sO = ho ∧ τ.sh sF = hf ∧ τ.sh sL = hl

/-- The register file read through the register names. -/
def RV (τ : WState 4 nrH) (V : HReg → ℕ) : Prop := ∀ u, τ.val (regH u) = V u

theorem RV.zero_of (τ : WState 4 nrH) (h : ∀ r, τ.val r = 0) : RV τ (fun _ => 0) := fun _ => h _

/-- **Header A**: `ℓ`'s field copied to `sL`. -/
theorem headerA_spec (cap : ℕ) (σ : WState 4 nrH) (W Dd rest : List Bool) (ℓ : ℕ) (hW : W = natWord ℓ ++ rest)
    (hs : StrAt σ W Dd [] [] [] 0 0 0 0 0) (hv : RV σ (fun _ => 0)) (hcap : 4 * W.length + 10 ≤ cap) :
    ∃ τ, WExec cap headerA σ τ (100 * W.length + 100) ∧
      StrAt τ W Dd [] [] (natWord ℓ) (natWord ℓ).length 0 0 0 0 ∧ RV τ (fun _ => 0) ∧ τ.cell = σ.cell := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := hs
  have hlw : (natWord ℓ).length ≤ W.length := by rw [hW]; simp
  have hnl : (natWord ℓ).length = 2 * natBitLength ℓ + 1 := natWord_length ℓ
  have hones : ones (σ.st sW) (σ.sh sW) = natBitLength ℓ := by
    rw [a1, a6, hW]; simpa using ones_natWord [] rest ℓ
  have v0 : ∀ u, σ.val (regH u) = 0 := hv
  have e1 := peekW_spec cap sW (regH .pk) (regH .pt) (by simp) σ (v0 _) (by rw [hones, v0]; omega)
  rw [hones, v0, Nat.zero_add] at e1
  set L0 := natBitLength ℓ with hL0
  set σ1 := σ.setv (regH .pk) L0 with hσ1
  have e2 := addTo_spec cap (regH .pk) (regH .sk) (regH .t) (by simp) (by simp) (by simp) σ1 (by simp [σ1, v0])
    (by simp [σ1]; omega) (by simp [σ1, v0]; omega)
  rw [show σ1.val (regH .sk) + σ1.val (regH .pk) = L0 by simp [σ1, v0]] at e2
  set σ2 := σ1.setv (regH .sk) L0 with hσ2
  have e3 := addTo_spec cap (regH .pk) (regH .sk) (regH .t) (by simp) (by simp) (by simp) σ2 (by simp [σ2, σ1, v0])
    (by simp [σ2, σ1]; omega) (by simp [σ2, σ1]; omega)
  rw [show σ2.val (regH .sk) + σ2.val (regH .pk) = 2 * L0 by simp [σ2, σ1]; ring] at e3
  set σ3 := σ2.setv (regH .sk) (2 * L0) with hσ3
  have e4 := WExec.inc (cap := cap) (regH .sk) σ3 (by simp [σ3]; omega)
  rw [show σ3.val (regH .sk) + 1 = (natWord ℓ).length by simp [σ3]; omega] at e4
  set σ4 := σ3.setv (regH .sk) (natWord ℓ).length with hσ4
  have e5 := copyCells_spec cap sW sL (by simp) (regH .sk) σ4 (natWord ℓ).length (by simp [σ4]) (by simp [σ4, σ3, σ2, σ1, a5, a10])
    (by omega)
  have hcopy : List.ofFn (fun j : Fin (natWord ℓ).length => readTapeBit (σ4.st sW) (σ4.sh sW + j.val)) =
      natWord ℓ := by
    simp only [σ4, σ3, σ2, σ1, WState.setv_st, WState.setv_sh, a1, a6, hW]
    exact ofFn_prefix _ _
  rw [hcopy] at e5
  set σ5 := (((σ4.seth sW (σ4.sh sW + (natWord ℓ).length)).sets sL (σ4.st sL ++ natWord ℓ)).seth sL
    (σ4.sh sL + (natWord ℓ).length)).setv (regH .sk) 0 with hσ5
  have e6 := addTo_spec cap (regH .pk) (regH .sk) (regH .t) (by simp) (by simp) (by simp) σ5
    (by simp [σ5, σ4, σ3, σ2, σ1, v0]) (by simp [σ5, σ4, σ3, σ2, σ1]; omega) (by simp [σ5, σ4, σ3, σ2, σ1]; omega)
  rw [show σ5.val (regH .sk) + σ5.val (regH .pk) = L0 by simp [σ5, σ4, σ3, σ2, σ1]] at e6
  set σ6 := σ5.setv (regH .sk) L0 with hσ6
  have e7 := addTo_spec cap (regH .pk) (regH .sk) (regH .t) (by simp) (by simp) (by simp) σ6
    (by simp [σ6, σ5, σ4, σ3, σ2, σ1, v0]) (by simp [σ6, σ5, σ4, σ3, σ2, σ1]; omega)
    (by simp [σ6, σ5, σ4, σ3, σ2, σ1]; omega)
  rw [show σ6.val (regH .sk) + σ6.val (regH .pk) = 2 * L0 by simp [σ6, σ5, σ4, σ3, σ2, σ1]; ring] at e7
  set σ7 := σ6.setv (regH .sk) (2 * L0) with hσ7
  have e8 := WExec.inc (cap := cap) (regH .sk) σ7 (by simp [σ7]; omega)
  rw [show σ7.val (regH .sk) + 1 = (natWord ℓ).length by simp [σ7]; omega] at e8
  set σ8 := σ7.setv (regH .sk) (natWord ℓ).length with hσ8
  have e9 := wrewind_spec cap sL (regH .sk) (natWord ℓ).length σ8 (by simp [σ8]) (by simp [σ8]; omega)
  set σ9 := (σ8.setv (regH .sk) 0).seth sL (σ8.sh sL - (natWord ℓ).length) with hσ9
  have e10 := wclear_spec cap (regH .pk) L0 σ9 (by simp [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1]) (by
    simp [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1]; omega)
  refine ⟨σ9.setv (regH .pk) 0, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5
    (WExec.seq e6 (WExec.seq e7 (WExec.seq e8 (WExec.seq e9 e10))))))))) ?_, ?_, ?_, ?_⟩
  · have c1 : σ1.val (regH .pk) = L0 := by simp [σ1]
    have c2 : σ2.val (regH .pk) = L0 := by simp [σ2, σ1]
    have c5 : σ5.val (regH .pk) = L0 := by simp [σ5, σ4, σ3, σ2, σ1]
    have c6 : σ6.val (regH .pk) = L0 := by simp [σ6, σ5, σ4, σ3, σ2, σ1]
    omega
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10]
  · intro u; simp [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, v0]
    intros; simp_all
  · simp [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1]

/-- **Header B**: `n_C`, `q`, `n_B`. -/
theorem headerB_spec (cap : ℕ) (σ : WState 4 nrH) (W Dd rW rD : List Bool) (ℓ nC nB : ℕ)
    (hW : W = natWord ℓ ++ natWord nC ++ rW) (hD : Dd = natWord q ++ natWord nB ++ rD)
    (hs : StrAt σ W Dd [] [] (natWord ℓ) (natWord ℓ).length 0 0 0 0) (hv : RV σ (fun _ => 0))
    (hcap : 8 * (nC + q + nB) + 4 * (W.length + Dd.length) + 100 ≤ cap) :
    ∃ τ, WExec cap headerB σ τ (readCost nC + readCost q + readCost nB + 3 * Dd.length + 10) ∧
      StrAt τ W Dd [] [] (natWord ℓ) ((natWord ℓ).length + (natWord nC).length)
        ((natWord q).length + (natWord nB).length) 0 0 0 ∧
      RV τ (fun u => if u = .nC then nC else if u = .cdW then (natWord nC).length else if u = .q then q else
        if u = .nB then nB else 0) ∧ τ.cell = σ.cell := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := hs
  have v0 : ∀ u, σ.val (regH u) = 0 := hv
  have hDl : (natWord q).length + (natWord nB).length ≤ Dd.length := by rw [hD]; simp
  have hq1 := natWord_length q
  have hn1 := natWord_length nB
  have hc1 := natWord_length nC
  have e1 := readEx_spec cap sW RW (regH .pk) (regH .pt) (regH .nC) (rdRegs .cdW .nC (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp)) σ (natWord ℓ) rW nC (by rw [a1, hW]) a6
    (famZero _ _ (fun r => v0 _)) (v0 _) (v0 _) (v0 _) (by simp [v0] <;> omega)
  set σ1 := ((σ.seth sW ((natWord ℓ).length + (natWord nC).length)).setv (RW .cd)
    (σ.val (RW .cd) + (natWord nC).length)).setv (regH .nC) nC with hσ1
  have v1 : ∀ u, σ1.val (regH u) = if u = .nC then nC else if u = .cdW then (natWord nC).length else 0 := by
    intro u; simp [σ1, Function.update_apply, v0]; try (intros; simp_all)
  have e2 := readEx_spec cap sD RB (regH .pk) (regH .pt) (regH .q) (rdRegs .cdB .q (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp)) σ1 [] (natWord nB ++ rD) q
    (by simp [σ1, a2, hD, List.append_assoc]) (by simp [σ1, a7]) (famZero _ _ (fun r => by rw [v1]; simp))
    (by rw [v1]; simp) (by rw [v1]; simp) (by rw [v1]; simp) (by simp [v1] <;> omega)
  set σ2 := ((σ1.seth sD ([].length + (natWord q).length)).setv (RB .cd)
    (σ1.val (RB .cd) + (natWord q).length)).setv (regH .q) q with hσ2
  have v2 : ∀ u, σ2.val (regH u) = if u = .q then q else if u = .cdB then (natWord q).length else
      if u = .nC then nC else if u = .cdW then (natWord nC).length else 0 := by
    intro u; simp [σ2, Function.update_apply, v1]; try (intros; simp_all)
  have e3 := readEx_spec cap sD RB (regH .pk) (regH .pt) (regH .nB) (rdRegs .cdB .nB (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp)) σ2 (natWord q) rD nB
    (by simp [σ2, σ1, a2, hD]) (by simp [σ2]) (famZero _ _ (fun r => by rw [v2]; simp))
    (by rw [v2]; simp) (by rw [v2]; simp) (by rw [v2]; simp) (by simp [v2] <;> omega)
  set σ3 := ((σ2.seth sD ((natWord q).length + (natWord nB).length)).setv (RB .cd)
    (σ2.val (RB .cd) + (natWord nB).length)).setv (regH .nB) nB with hσ3
  have e4 := wclear_spec cap (regH .cdB) ((natWord q).length + (natWord nB).length) σ3
    (by simp [σ3, Function.update_apply, v2]) (by simp [σ3, Function.update_apply, v2] <;> omega)
  refine ⟨σ3.setv (regH .cdB) 0, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) (by omega), ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [σ3, σ2, σ1, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10]
  · intro u; simp [σ3, Function.update_apply, v2]; split_ifs <;> simp_all
  · simp [σ3, σ2, σ1]

/-- **Header C**: the guard `hc q + 1`, `n_B − 1`, `3 n_B`. -/
theorem headerC_spec (cap : ℕ) (σ : WState 4 nrH) (V : HReg → ℕ) (hv : RV σ V)
    (hz : V .x = 0 ∧ V .t = 0 ∧ V .h = 0 ∧ V .bq = 0 ∧ V .nB1 = 0 ∧ V .sk = 0)
    (hcap : 4 * (V .q + V .nB) + 10 ≤ cap) :
    ∃ τ, WExec cap headerC σ τ (100 * (V .q + V .nB) + 100) ∧ τ.st = σ.st ∧ τ.sh = σ.sh ∧
      RV τ (fun u => if u = .bq then hc (V .q) + 1 else if u = .nB1 then V .nB - 1 else
        if u = .sk then 3 * V .nB else V u) ∧ τ.cell = σ.cell := by
  obtain ⟨zx, zt, zh, zbq, znb1, zsk⟩ := hz
  have hv' : ∀ u, σ.val (regH u) = V u := hv
  have hcq := hc_le (V .q)
  have e1 := addTo_spec cap (regH .q) (regH .x) (regH .t) (by simp) (by simp) (by simp) σ (by rw [hv']; exact zt)
    (by rw [hv'] <;> omega) (by rw [hv', hv'] <;> omega)
  rw [show σ.val (regH .x) + σ.val (regH .q) = (V .q) by rw [hv', hv', zx, Nat.zero_add]] at e1
  set σ1 := σ.setv (regH .x) (V .q) with hσ1
  have e2 := hcW_spec cap (regH .x) (regH .bq) (regH .h) (by simp) (by simp) (by simp) (V .q) σ1 (by simp [σ1])
    (by simp [σ1, Function.update_apply, hv', zh]) (by simp [σ1, Function.update_apply, hv', zbq] <;> omega) (by omega)
  rw [show σ1.val (regH .bq) + hc (V .q) = hc (V .q) by simp [σ1, Function.update_apply, hv', zbq]] at e2
  set σ2 := (σ1.setv (regH .x) 0).setv (regH .bq) (hc (V .q)) with hσ2
  have e3 := WExec.inc (cap := cap) (regH .bq) σ2 (by simp [σ2] <;> omega)
  set σ3 := σ2.setv (regH .bq) (σ2.val (regH .bq) + 1) with hσ3
  have e4 := addTo_spec cap (regH .nB) (regH .nB1) (regH .t) (by simp) (by simp) (by simp) σ3
    (by simp [σ3, σ2, σ1, Function.update_apply, hv', zt]) (by simp [σ3, σ2, σ1, Function.update_apply, hv'] <;> omega)
    (by simp [σ3, σ2, σ1, Function.update_apply, hv', znb1] <;> omega)
  rw [show σ3.val (regH .nB1) + σ3.val (regH .nB) = (V .nB) by simp [σ3, σ2, σ1, Function.update_apply, hv', znb1]] at e4
  set σ4 := σ3.setv (regH .nB1) (V .nB) with hσ4
  have e5 := WExec.dec (cap := cap) (regH .nB1) σ4 (by simp [σ4] <;> omega)
  set σ5 := σ4.setv (regH .nB1) (σ4.val (regH .nB1) - 1) with hσ5
  have e6 := addTo_spec cap (regH .nB) (regH .sk) (regH .t) (by simp) (by simp) (by simp) σ5
    (by simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply, hv', zt])
    (by simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply, hv'] <;> omega)
    (by simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply, hv', zsk] <;> omega)
  rw [show σ5.val (regH .sk) + σ5.val (regH .nB) = (V .nB) by simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply, hv', zsk]] at e6
  set σ6 := σ5.setv (regH .sk) (V .nB) with hσ6
  have e7 := addTo_spec cap (regH .nB) (regH .sk) (regH .t) (by simp) (by simp) (by simp) σ6
    (by simp [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hv', zt])
    (by simp [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hv'] <;> omega)
    (by simp [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hv'] <;> omega)
  rw [show σ6.val (regH .sk) + σ6.val (regH .nB) = 2 * (V .nB) by
    simp [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hv']; ring] at e7
  set σ7 := σ6.setv (regH .sk) (2 * (V .nB)) with hσ7
  have e8 := addTo_spec cap (regH .nB) (regH .sk) (regH .t) (by simp) (by simp) (by simp) σ7
    (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hv', zt])
    (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hv'] <;> omega)
    (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hv'] <;> omega)
  rw [show σ7.val (regH .sk) + σ7.val (regH .nB) = 3 * (V .nB) by
    simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hv']; ring] at e8
  have c1 : σ.val (regH .q) = (V .q) := hv' _
  have c4 : σ3.val (regH .nB) = (V .nB) := by simp [σ3, σ2, σ1, Function.update_apply, hv']
  have c6 : σ5.val (regH .nB) = (V .nB) := by simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply, hv']
  have c7 : σ6.val (regH .nB) = (V .nB) := by simp [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hv']
  have c8 : σ7.val (regH .nB) = (V .nB) := by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hv']
  have c5 : σ4.val (regH .nB1) = (V .nB) := by simp [σ4]
  refine ⟨σ7.setv (regH .sk) (3 * (V .nB)), WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4
    (WExec.seq e5 (WExec.seq e6 (WExec.seq e7 e8))))))) ?_, ?_, ?_, ?_, ?_⟩
  · rw [c1, c4, c6, c7, c8]; omega
  · simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1]
  · simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1]
  · intro u; simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hv']
    by_cases h1 : u = .sk
    · subst h1; simp
    · by_cases h2 : u = .nB1
      · subst h2; simp
      · by_cases h3 : u = .bq
        · subst h3; simp
        · by_cases h4 : u = .x
          · subst h4; simp [zx]
          · simp [h1, h2, h3, h4]
  · simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1]

/-- **Header D**: `o_B`; the head of `sD` back at `B`'s nodes. -/
theorem headerD_spec (cap : ℕ) (B : BooleanCircuit q) (σ : WState 4 nrH) (V : HReg → ℕ) (hv : RV σ V)
    (W Lw : List Bool) (hw : ℕ)
    (hs : StrAt σ W (PCPPNative.descriptor B) [] [] Lw hw ((natWord q).length + (natWord B.nodes.length).length) 0 0 0)
    (hz : (∀ r, V (.f r) = 0) ∧ V .sk = 3 * B.nodes.length ∧ V .z = 0 ∧ V .jk = 0 ∧ V .cdB = 0 ∧ V .pk = 0 ∧
      V .pt = 0 ∧ V .oB = 0)
    (hcap : 20 * ((PCPPNative.descriptor B).length + q) + 100 ≤ cap) :
    ∃ τ, WExec cap headerD σ τ (100000 * ((PCPPNative.descriptor B).length + q + 2) ^ 2) ∧
      StrAt τ W (PCPPNative.descriptor B) [] [] Lw hw ((natWord q).length + (natWord B.nodes.length).length) 0 0 0 ∧
      RV τ (fun u => if u = .oB then B.output.val else if u = .sk then 0 else V u) ∧ τ.cell = σ.cell := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := hs
  obtain ⟨zf, zsk, zz, zjk, zcd, zpk, zpt, zoB⟩ := hz
  have hv' : ∀ u, σ.val (regH u) = V u := hv
  have hD := desc_eq B
  have hbl := bfl_length B
  have hwBl := flatMap_natWord_len (bfl B)
  have hDl : (natWord q).length + (natWord B.nodes.length).length + ((bfl B).flatMap natWord).length + (natWord B.output.val).length =
      (PCPPNative.descriptor B).length := by rw [hD]; simp only [List.length_append]
  have hoB := B.output.isLt
  have e1 := skipN_spec cap sD RB (fam_inj _ (by simp)) (regH .z) (regH .jk) (regH .sk) (famNe _ _ (by simp) (by simp))
    (famNe _ _ (by simp) (by simp)) (famNe _ _ (by simp) (by simp)) (by simp) (by simp) σ
    (natWord q ++ natWord B.nodes.length) (natWord B.output.val) (bfl B) (B.nodes.length + q + 6)
    (fun x hx => (nbl_le x).trans (by have := bfl_le B x hx; omega))
    (by rw [a2, hD]) (by rw [a7]; simp) (famZero _ _ (fun r => by rw [hv']; exact zf r)) (by rw [hv']; exact zz)
    (by rw [hv']; exact zjk) (by rw [hv', zsk, hbl]) (by simp only [RB, fam_cd, hv', zcd]; omega) (by omega)
  set σ1 := ((σ.seth sD ((natWord q ++ natWord B.nodes.length).length + ((bfl B).flatMap natWord).length)).setv (RB .cd)
    (σ.val (RB .cd) + ((bfl B).flatMap natWord).length)).setv (regH .sk) 0 with hσ1
  have v1 : ∀ u, σ1.val (regH u) = if u = .sk then 0 else if u = .cdB then ((bfl B).flatMap natWord).length else V u := by
    intro u; simp [σ1, Function.update_apply, hv', zcd]; try (split_ifs <;> simp_all)
  have e2 := readEx_spec cap sD RB (regH .pk) (regH .pt) (regH .oB) (rdRegs .cdB .oB (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp)) σ1 (natWord q ++ natWord B.nodes.length ++ ((bfl B).flatMap natWord)) [] B.output.val
    (by simp [σ1, a2, hD]) (by simp [σ1, Nat.add_assoc]) (famZero _ _ (fun r => by rw [v1]; simp [zf]))
    (by rw [v1]; simp [zpk]) (by rw [v1]; simp [zpt]) (by rw [v1]; simp [zoB])
    (by have : σ1.val (RB .cd) = ((bfl B).flatMap natWord).length := by simp [RB, v1]
        rw [this]; omega)
  set σ2 := ((σ1.seth sD ((natWord q ++ natWord B.nodes.length ++ ((bfl B).flatMap natWord)).length + (natWord B.output.val).length)).setv (RB .cd)
    (σ1.val (RB .cd) + (natWord B.output.val).length)).setv (regH .oB) B.output.val with hσ2
  have e3 := wrewind_spec cap sD (regH .cdB) (((bfl B).flatMap natWord).length + (natWord B.output.val).length) σ2
    (by simp [σ2, Function.update_apply, v1]) (by
      have : σ2.val (regH .cdB) = ((bfl B).flatMap natWord).length + (natWord B.output.val).length := by
        simp [σ2, Function.update_apply, v1]
      rw [this]; omega)
  refine ⟨(σ2.setv (regH .cdB) 0).seth sD (σ2.sh sD - (((bfl B).flatMap natWord).length + (natWord B.output.val).length)),
    WExec.mono (WExec.seq e1 (WExec.seq e2 e3)) ?_, ?_, ?_, ?_⟩
  · have hrc := readCost B.output.val
    unfold readCost
    have : B.output.val ≤ (PCPPNative.descriptor B).length := by omega
    have : 3 * B.nodes.length ≤ (PCPPNative.descriptor B).length := by omega
    nlinarith
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [σ2, σ1, WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh, Function.update_apply,
        sD_ne_sW, sW_ne_sD, sO_ne_sD, sF_ne_sD, sL_ne_sD, if_true, if_false, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
        List.length_append] <;> omega
  · intro u; simp [σ2, Function.update_apply, v1]; split_ifs <;> simp_all
  · simp [σ2, σ1]

/-- The cost class of the header. -/
def headCost (S : ℕ) : ℕ := 1000000 * (S + 2) ^ 2

theorem header_spec (o : OracleOutput) (B : BooleanCircuit q) (cap : ℕ) (hcap : 100 * sizeS o B ≤ cap) :
    ∃ τ, WExec cap header (start o.word (PCPPNative.descriptor B)) τ (headCost (sizeS o B)) ∧ HeadPost o B τ := by
  obtain ⟨hzC, hzB, hzq, hwh, hlb, hdl, hnCw⟩ := sizes_le o B
  have hS : sizeS o B = o.word.length + (PCPPNative.descriptor B).length + q + 1 := rfl
  have hW := word_eq o
  have hD := desc_eq B
  have hpre : StrAt (start o.word (PCPPNative.descriptor B)) o.word (PCPPNative.descriptor B) [] [] [] 0 0 0 0 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [start]
  obtain ⟨τ1, e1, s1, v1, c1⟩ := headerA_spec cap _ o.word (PCPPNative.descriptor B)
    (natWord o.circuit.nodes.length ++ o.circuit.nodes.flatMap oracleNodeWord ++ natWord o.circuit.output.val) o.ell
    (by rw [hW]; simp only [List.append_assoc]) hpre (RV.zero_of _ (fun _ => rfl)) (by omega)
  obtain ⟨τ2, e2, s2, v2, c2⟩ := headerB_spec (q := q) cap τ1 o.word (PCPPNative.descriptor B)
    (o.circuit.nodes.flatMap oracleNodeWord ++ natWord o.circuit.output.val)
    ((bfl B).flatMap natWord ++ natWord B.output.val) o.ell
    o.circuit.nodes.length B.nodes.length (by rw [hW]; simp only [List.append_assoc])
    (by rw [hD]; simp only [List.append_assoc]) s1 v1 (by omega)
  obtain ⟨τ3, e3, s3st, s3sh, v3, c3⟩ := headerC_spec cap τ2 _ v2 (by simp) (by simp; omega)
  have s3 : StrAt τ3 o.word (PCPPNative.descriptor B) [] [] (natWord o.ell)
      ((natWord o.ell).length + (natWord o.circuit.nodes.length).length)
      ((natWord q).length + (natWord B.nodes.length).length) 0 0 0 := by
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := s2
    exact ⟨by rw [s3st]; exact a1, by rw [s3st]; exact a2, by rw [s3st]; exact a3, by rw [s3st]; exact a4,
      by rw [s3st]; exact a5, by rw [s3sh]; exact a6, by rw [s3sh]; exact a7, by rw [s3sh]; exact a8,
      by rw [s3sh]; exact a9, by rw [s3sh]; exact a10⟩
  obtain ⟨τ4, e4, s4, v4, c4⟩ := headerD_spec cap B τ3 _ v3 _ _ _ s3 (by simp) (by omega)
  refine ⟨τ4, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) ?_, ?_⟩
  · have r1 : readCost o.circuit.nodes.length ≤ 10000 * (sizeS o B + 2) ^ 2 := by
      unfold readCost; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
    have r2 : readCost q ≤ 10000 * (sizeS o B + 2) ^ 2 := by
      unfold readCost; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
    have r3 : readCost B.nodes.length ≤ 10000 * (sizeS o B + 2) ^ 2 := by
      unfold readCost; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
    have r4 : 100000 * ((PCPPNative.descriptor B).length + q + 2) ^ 2 ≤ 100000 * (sizeS o B + 2) ^ 2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
    have r5 : sizeS o B + 2 ≤ (sizeS o B + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
    simp only [ite_true, if_neg (show HReg.q ≠ HReg.nC by decide), if_neg (show HReg.q ≠ HReg.cdW by decide),
      if_neg (show HReg.nB ≠ HReg.nC by decide), if_neg (show HReg.nB ≠ HReg.cdW by decide),
      if_neg (show HReg.nB ≠ HReg.q by decide)]
    unfold headCost
    omega
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := s4
    refine ⟨a1, a2, a5, a3, a4, a6, a7, a8, a9, a10, fun u => ?_, by rw [c4, c3, c2, c1]; rfl⟩
    rw [v4 u]
    cases u <;> simp [V1]

end NearCubicGates.Close.Succinct.SubstMachine
