import Proof.Wire_3_5.PrimTTabConv

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.PrimT
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.Corner

section Write
variable {ns nr : ℕ} (cap : ℕ)

/-! ## Moves seen from outside -/

theorem Mv.other {I O R : Fin (ns + 1)} {c f : Fin nr} {σ τ : WState ns nr} {pI pR cv fv : ℕ} {w : List Bool}
    (m : Mv I O R c f σ τ pI w pR cv fv) (j : Fin (ns + 1)) (h1 : j ≠ I) (h2 : j ≠ O) (h3 : j ≠ R) :
    τ.st j = σ.st j ∧ τ.sh j = σ.sh j :=
  m.fr.1 j (by rintro (h | h | h) <;> contradiction)

theorem Mv.otherv {I O R : Fin (ns + 1)} {c f : Fin nr} {σ τ : WState ns nr} {pI pR cv fv : ℕ} {w : List Bool}
    (m : Mv I O R c f σ τ pI w pR cv fv) (q : Fin nr) (h1 : q ≠ c) (h2 : q ≠ f) : τ.val q = σ.val q :=
  m.fr.2.1 q (by rintro (h | h) <;> contradiction)

/-- A move that writes nothing and returns the ruler and the carry changes only the input and the count. -/
theorem Mv.narrow {I O R : Fin (ns + 1)} {c f : Fin nr} {σ τ : WState ns nr} {pI cv : ℕ}
    (m : Mv I O R c f σ τ pI [] (σ.sh R) cv (σ.val f)) (hO : σ.sh O = (σ.st O).length) :
    WFrame (fun i => i = I) (fun q => q = c) σ τ := by
  refine ⟨fun j hj => ?_, fun q hq => ?_, m.fr.2.2⟩
  · by_cases hjO : j = O
    · subst hjO; exact ⟨by rw [m.sO]; simp, by rw [m.hO, m.sO, hO]; simp⟩
    · by_cases hjR : j = R
      · subst hjR; exact ⟨m.sR, m.hR⟩
      · exact m.other j hj hjO hjR
  · by_cases hqf : q = f
    · subst hqf; exact m.vf
    · exact m.otherv q hq hqf

variable (Sm : Fin 5 ↪ Fin (ns + 1)) (Rg : Fin 3 ↪ Fin nr)

/-! ## The programs -/

/-- Head `A` skips the weights, counted on the unary `1^n`. -/
def skipWsW : WM ns nr := .whs (Sm 2) (.seq (skipIntW (Sm 0) (Rg 0)) (.seq (.fwd (Sm 2)) (.inc (Rg 2))))

/-- Head `B` writes the weights' pairs, counted on the unary `1^n`. -/
def convWsW : WM ns nr :=
  .whs (Sm 2) (.seq (convIntW (Sm 1) (Sm 4) (Sm 3) (Rg 0) (Rg 1)) (.seq (.fwd (Sm 2)) (.inc (Rg 2))))

/-- One gate, first half: the marker, then head `A` writes the pair of `−θ`. -/
def gateAW : WM ns nr :=
  .seq (emitW (Sm 4) true) (.seq (skipNatW (Sm 0) (Rg 0)) (.seq (skipWsW Sm Rg) (.seq (WM.rewind (Sm 2) (Rg 2))
    (.seq (convThrW (Sm 0) (Sm 4) (Sm 3) (Rg 0) (Rg 1)) (.fwd (Sm 0))))))

/-- One gate, second half: head `B` writes the weights' pairs. -/
def gateBW : WM ns nr :=
  .seq (skipNatW (Sm 1) (Rg 0)) (.seq (convWsW Sm Rg) (.seq (WM.rewind (Sm 2) (Rg 2))
    (.seq (skipIntW (Sm 1) (Rg 0)) (.fwd (Sm 1)))))

/-- One gate of the table. -/
def gateBodyW : WM ns nr := .seq (gateAW Sm Rg) (gateBW Sm Rg)

/-- **The table writer.** -/
def tableW : WM ns nr := .seq (.whs (Sm 0) (gateBodyW Sm Rg)) (emitW (Sm 4) false)

/-- The bounds one gate needs: every count fits the registers, every magnitude the width. -/
def GateOk (h : ℕ) {n : ℕ} (g : NormalizedThresholdGate n) : Prop :=
  (∀ i, natBitLength (g.weight i).natAbs ≤ h ∧ natBitLength (g.weight i).natAbs ≤ cap) ∧
    natBitLength (g.threshold - 1).natAbs + 1 ≤ h ∧ natBitLength (g.threshold - 1).natAbs ≤ cap ∧
    natBitLength n ≤ h ∧ natBitLength n ≤ cap ∧ n ≤ cap ∧ 2 ≤ cap

/-! ## Distinct roles -/

theorem sm_ne (i j : Fin 5) (h : i ≠ j) : Sm i ≠ Sm j := Sm.injective.ne h
theorem rg_ne (i j : Fin 3) (h : i ≠ j) : Rg i ≠ Rg j := Rg.injective.ne h

/-! ## Skipping the weights -/

theorem flatMap_intWord_cons (w : ℤ) (ws : List ℤ) :
    frameP ((w :: ws).flatMap intWord) = frameP (intWord w) ++ frameP (ws.flatMap intWord) := by
  simp [frameP_append']

theorem skipWs_spec (h : ℕ) (rest : List Bool) : ∀ (ws : List ℤ) (pre : List Bool) (j : ℕ) (σ : WState ns nr),
    σ.st (Sm 0) = pre ++ (frameP (ws.flatMap intWord) ++ rest) → σ.sh (Sm 0) = pre.length →
    σ.st (Sm 2) = List.replicate (j + ws.length) true → σ.sh (Sm 2) = j → σ.val (Rg 2) = j →
    j + ws.length ≤ cap → σ.val (Rg 0) = 0 →
    (∀ w ∈ ws, natBitLength w.natAbs ≤ h ∧ natBitLength w.natAbs ≤ cap) → σ.sh (Sm 4) = (σ.st (Sm 4)).length →
    ∃ τ, WExec cap (skipWsW Sm Rg) σ τ (ws.length * (16 * h + 20) + 1) ∧
      τ.sh (Sm 0) = pre.length + 2 * (ws.flatMap intWord).length ∧ τ.sh (Sm 2) = j + ws.length ∧
      τ.val (Rg 2) = j + ws.length ∧ τ.val (Rg 0) = 0 ∧
      WFrame (fun i => i = Sm 0 ∨ i = Sm 2) (fun q => q = Rg 0 ∨ q = Rg 2) σ τ ∧
      τ.st (Sm 0) = σ.st (Sm 0) ∧ τ.st (Sm 2) = σ.st (Sm 2)
  | [], pre, j, σ, _, hAh, hN, hNh, hr, _, hc, _, _ => by
    have hz : wbit σ (Sm 2) = false := by simp [wbit, hN, hNh, readTapeBit]
    refine ⟨σ, WExec.mono (WExec.whsF hz) (by simp), by simp [hAh], by simp [hNh], by simp [hr], hc,
      WFrame.refl _ _ σ, rfl, rfl⟩
  | w :: ws, pre, j, σ, hA, hAh, hN, hNh, hr, hcap, hc, hws, hO => by
    have d03 := sm_ne Sm 0 3 (by decide); have d04 := sm_ne Sm 0 4 (by decide)
    have d20 := sm_ne Sm 2 0 (by decide)
    have d24 := sm_ne Sm 2 4 (by decide); have d23 := sm_ne Sm 2 3 (by decide)
    have r01 := rg_ne Rg 0 1 (by decide); have r20 := rg_ne Rg 2 0 (by decide); have r21 := rg_ne Rg 2 1 (by decide)
    obtain ⟨hw1, hw2⟩ := hws w (by simp)
    obtain ⟨τ1, s1, m1⟩ := skipIntW_spec cap (Sm 0) (Sm 4) (Sm 3) (Rg 0) (Rg 1) d04 d03 (sm_ne Sm 4 3 (by decide)) r01
      pre (frameP (ws.flatMap intWord) ++ rest) w σ (by rw [hA, flatMap_intWord_cons]; simp) hAh hc hw2 hO
    have hN1 := m1.other (Sm 2) d20 d24 d23
    have hr1 := m1.otherv (Rg 2) r20 r21
    have hlen : (w :: ws).length = ws.length + 1 := rfl
    have s2 := WExec.fwd (cap := cap) (Sm 2) τ1
    have s3 := WExec.inc (cap := cap) (Rg 2) (τ1.seth (Sm 2) (τ1.sh (Sm 2) + 1)) (by simp [hr1, hr]; omega)
    set τ3 := (τ1.seth (Sm 2) (τ1.sh (Sm 2) + 1)).setv (Rg 2) ((τ1.seth (Sm 2) (τ1.sh (Sm 2) + 1)).val (Rg 2) + 1)
      with hτ3
    have t3st : ∀ i, τ3.st i = τ1.st i := fun i => by rw [hτ3]; rfl
    have t3sh : τ3.sh (Sm 2) = τ1.sh (Sm 2) + 1 := by rw [hτ3]; simp
    have t3sh0 : τ3.sh (Sm 0) = τ1.sh (Sm 0) := by rw [hτ3]; simp [Function.update_of_ne d20.symm]
    have t3sh4 : τ3.sh (Sm 4) = τ1.sh (Sm 4) := by rw [hτ3]; simp [Function.update_of_ne d24.symm]
    have t3r : τ3.val (Rg 2) = τ1.val (Rg 2) + 1 := by rw [hτ3]; simp
    have t3c : τ3.val (Rg 0) = τ1.val (Rg 0) := by rw [hτ3]; simp [Function.update_of_ne r20.symm]
    obtain ⟨τ, s4, e0, e2, er, ec, fr, sA, sN⟩ := skipWs_spec h rest ws (pre ++ frameP (intWord w)) (j + 1) τ3
      (by rw [t3st, m1.sI, hA, flatMap_intWord_cons]; simp)
      (by rw [t3sh0, m1.hI]; simp)
      (by rw [t3st, hN1.1, hN, hlen, show j + (ws.length + 1) = j + 1 + ws.length by omega])
      (by rw [t3sh, hN1.2, hNh]) (by rw [t3r, hr1, hr])
      (by rw [hlen] at hcap; omega) (by rw [t3c, m1.vc])
      (fun w' hw' => hws w' (by simp [hw'])) (by rw [t3sh4, t3st, m1.hO])
    have hwb : wbit σ (Sm 2) = true := by
      simp only [wbit, hN, hNh, readTapeBit]; rw [List.getD_eq_getElem _ _ (by simp)]; simp
    refine ⟨τ, WExec.mono (WExec.whsT hwb (WExec.seq s1 (WExec.seq s2 s3)) s4) ?_, ?_, ?_, ?_, ec, ?_, ?_, ?_⟩
    · have := Nat.mul_le_mul_left (16 : ℕ) hw1
      have e : (ws.length + 1) * (16 * h + 20) = ws.length * (16 * h + 20) + (16 * h + 20) := by ring
      rw [hlen, e]; omega
    · rw [e0]; simp [intWord, List.flatMap_cons]; omega
    · rw [e2, hlen]; omega
    · rw [er, hlen]; omega
    · exact ((m1.narrow hO).mono (fun i hi => Or.inl hi) (fun q hq => Or.inl hq)).trans
        (((frame_seth _ _ τ1 (Sm 2) _ (Or.inr rfl)).trans (frame_setv _ _ _ (Rg 2) _ (Or.inr rfl))).trans fr)
    · rw [sA, t3st, m1.sI]
    · rw [sN, t3st, hN1.1]

/-! ## Writing the weights' pairs -/

theorem convWs_spec (h : ℕ) (rest : List Bool) (hcap : 1 ≤ cap) : ∀ (ws : List ℤ) (pre : List Bool) (j : ℕ)
    (σ : WState ns nr),
    σ.st (Sm 1) = pre ++ (frameP (ws.flatMap intWord) ++ rest) → σ.sh (Sm 1) = pre.length →
    σ.st (Sm 2) = List.replicate (j + ws.length) true → σ.sh (Sm 2) = j → σ.val (Rg 2) = j →
    j + ws.length ≤ cap → σ.val (Rg 0) = 0 → σ.val (Rg 1) = 0 →
    (∀ w ∈ ws, natBitLength w.natAbs ≤ h ∧ natBitLength w.natAbs ≤ cap) → σ.sh (Sm 4) = (σ.st (Sm 4)).length →
    σ.st (Sm 3) = false :: List.replicate h true → σ.sh (Sm 3) = 0 →
    ∃ τ, WExec cap (convWsW Sm Rg) σ τ (ws.length * (70 * h + 70) + 1) ∧
      τ.st (Sm 4) = σ.st (Sm 4) ++ ws.flatMap (pairW h) ∧ τ.sh (Sm 4) = (τ.st (Sm 4)).length ∧
      τ.sh (Sm 1) = pre.length + 2 * (ws.flatMap intWord).length ∧ τ.sh (Sm 2) = j + ws.length ∧
      τ.val (Rg 2) = j + ws.length ∧ τ.val (Rg 0) = 0 ∧ τ.val (Rg 1) = 0 ∧ τ.sh (Sm 3) = 0 ∧
      WFrame (fun i => i = Sm 1 ∨ i = Sm 2 ∨ i = Sm 4 ∨ i = Sm 3) (fun _ => True) σ τ ∧
      τ.st (Sm 1) = σ.st (Sm 1) ∧ τ.st (Sm 2) = σ.st (Sm 2) ∧ τ.st (Sm 3) = σ.st (Sm 3)
  | [], pre, j, σ, _, hBh, hN, hNh, hr, _, hc, hf, _, hO, _, hRh => by
    have hz : wbit σ (Sm 2) = false := by simp [wbit, hN, hNh, readTapeBit]
    refine ⟨σ, WExec.mono (WExec.whsF hz) (by simp), by simp, hO, by simp [hBh], by simp [hNh], by simp [hr], hc, hf,
      hRh, WFrame.refl _ _ σ, rfl, rfl, rfl⟩
  | w :: ws, pre, j, σ, hB, hBh, hN, hNh, hr, hcap', hc, hf, hws, hO, hR, hRh => by
    have d14 := sm_ne Sm 1 4 (by decide); have d13 := sm_ne Sm 1 3 (by decide)
    have d43 := sm_ne Sm 4 3 (by decide); have d21 := sm_ne Sm 2 1 (by decide)
    have d24 := sm_ne Sm 2 4 (by decide); have d23 := sm_ne Sm 2 3 (by decide)
    have r01 := rg_ne Rg 0 1 (by decide); have r20 := rg_ne Rg 2 0 (by decide); have r21 := rg_ne Rg 2 1 (by decide)
    obtain ⟨hw1, hw2⟩ := hws w (by simp)
    have hlen : (w :: ws).length = ws.length + 1 := rfl
    obtain ⟨τ1, s1, m1⟩ := convIntW_spec cap (Sm 1) (Sm 4) (Sm 3) (Rg 0) (Rg 1) d14 d13 d43 r01 hcap pre
      (frameP (ws.flatMap intWord) ++ rest) w h σ (by rw [hB, flatMap_intWord_cons]; simp) hBh hc hf hw1 hw2 hO hR hRh
    have hN1 := m1.other (Sm 2) d21 d24 d23
    have hr1 := m1.otherv (Rg 2) r20 r21
    have s2 := WExec.fwd (cap := cap) (Sm 2) τ1
    have s3 := WExec.inc (cap := cap) (Rg 2) (τ1.seth (Sm 2) (τ1.sh (Sm 2) + 1)) (by simp [hr1, hr]; omega)
    set τ3 := (τ1.seth (Sm 2) (τ1.sh (Sm 2) + 1)).setv (Rg 2) ((τ1.seth (Sm 2) (τ1.sh (Sm 2) + 1)).val (Rg 2) + 1)
      with hτ3
    have t3st : ∀ i, τ3.st i = τ1.st i := fun i => by rw [hτ3]; rfl
    have t3sh : τ3.sh (Sm 2) = τ1.sh (Sm 2) + 1 := by rw [hτ3]; simp
    have t3sh1 : τ3.sh (Sm 1) = τ1.sh (Sm 1) := by rw [hτ3]; simp [Function.update_of_ne d21.symm]
    have t3sh3 : τ3.sh (Sm 3) = τ1.sh (Sm 3) := by rw [hτ3]; simp [Function.update_of_ne d23.symm]
    have t3sh4 : τ3.sh (Sm 4) = τ1.sh (Sm 4) := by rw [hτ3]; simp [Function.update_of_ne d24.symm]
    have t3r : τ3.val (Rg 2) = τ1.val (Rg 2) + 1 := by rw [hτ3]; simp
    have t3c : τ3.val (Rg 0) = τ1.val (Rg 0) := by rw [hτ3]; simp [Function.update_of_ne r20.symm]
    have t3f : τ3.val (Rg 1) = τ1.val (Rg 1) := by rw [hτ3]; simp [Function.update_of_ne r21.symm]
    obtain ⟨τ, s4, eO, eOh, eB, eN, er, ec, ef, eR, fr, sB, sN, sR⟩ := convWs_spec h rest hcap ws
      (pre ++ frameP (intWord w)) (j + 1) τ3
      (by rw [t3st, m1.sI, hB, flatMap_intWord_cons]; simp) (by rw [t3sh1, m1.hI]; simp)
      (by rw [t3st, hN1.1, hN, hlen, show j + (ws.length + 1) = j + 1 + ws.length by omega])
      (by rw [t3sh, hN1.2, hNh]) (by rw [t3r, hr1, hr]) (by rw [hlen] at hcap'; omega) (by rw [t3c, m1.vc])
      (by rw [t3f, m1.vf]) (fun w' hw' => hws w' (by simp [hw'])) (by rw [t3sh4, t3st, m1.hO])
      (by rw [t3st, m1.sR, hR]) (by rw [t3sh3, m1.hR])
    have hwb : wbit σ (Sm 2) = true := by
      simp only [wbit, hN, hNh, readTapeBit]; rw [List.getD_eq_getElem _ _ (by simp)]; simp
    refine ⟨τ, WExec.mono (WExec.whsT hwb (WExec.seq s1 (WExec.seq s2 s3)) s4) ?_, ?_, eOh, ?_, ?_, ?_, ec, ef, eR, ?_,
      ?_, ?_, ?_⟩
    · have := Nat.mul_le_mul_left (9 : ℕ) hw1
      have e : (ws.length + 1) * (70 * h + 70) = ws.length * (70 * h + 70) + (70 * h + 70) := by ring
      rw [hlen, e]; unfold convIntCost countCost wordCost; omega
    · rw [eO, t3st, m1.sO]; simp
    · rw [eB]; simp [intWord, List.flatMap_cons]; omega
    · rw [eN, hlen]; omega
    · rw [er, hlen]; omega
    · exact (m1.fr.mono (fun i hi => by rcases hi with h | h | h <;> simp [h]) (fun _ _ => trivial)).trans
        (((frame_seth _ _ τ1 (Sm 2) _ (by simp)).trans (frame_setv _ _ _ (Rg 2) _ trivial)).trans fr)
    · rw [sB, t3st, m1.sI]
    · rw [sN, t3st, hN1.1]
    · rw [sR, t3st, m1.sR]

/-! ## One gate -/

/-- The standing state between the steps of a gate: the unary `1^n` and the ruler at their starts, the table head at
its end, the registers `0`. -/
def Std (σ : WState ns nr) (h n : ℕ) : Prop :=
  σ.st (Sm 2) = List.replicate n true ∧ σ.sh (Sm 2) = 0 ∧ σ.st (Sm 3) = false :: List.replicate h true ∧
    σ.sh (Sm 3) = 0 ∧ σ.sh (Sm 4) = (σ.st (Sm 4)).length ∧ σ.val (Rg 0) = 0 ∧ σ.val (Rg 1) = 0 ∧ σ.val (Rg 2) = 0

theorem std_mv {I : Fin (ns + 1)} {σ τ : WState ns nr} {h n pI pR cv fv : ℕ} {w : List Bool}
    (hs : Std Sm Rg σ h n) (m : Mv I (Sm 4) (Sm 3) (Rg 0) (Rg 1) σ τ pI w pR cv fv) (hI : I ≠ Sm 2) (hpR : pR = 0)
    (hcv : cv = 0) (hfv : fv = 0) : Std Sm Rg τ h n := by
  obtain ⟨h1, h2, h3, _, _, _, _, h8⟩ := hs
  have d24 := sm_ne Sm 2 4 (by decide); have d23 := sm_ne Sm 2 3 (by decide)
  have r20 := rg_ne Rg 2 0 (by decide); have r21 := rg_ne Rg 2 1 (by decide)
  have hN := m.other (Sm 2) hI.symm d24 d23
  exact ⟨hN.1.trans h1, hN.2.trans h2, m.sR.trans h3, m.hR.trans hpR, m.hO, m.vc.trans hcv, m.vf.trans hfv,
    (m.otherv (Rg 2) r20 r21).trans h8⟩

theorem frame_tabGW {n : ℕ} (g : NormalizedThresholdGate n) :
    frame (tabGW g) = frameP (natWord n) ++ (frameP ((List.ofFn g.weight).flatMap intWord) ++
      (frameP (intWord (g.threshold - 1)) ++ [false])) := by
  rw [frame_eq_frameP, tabGW_eq, frameP_append', frameP_append']; simp

theorem frame_tabGW_length {n : ℕ} (g : NormalizedThresholdGate n) :
    (frame (tabGW g)).length = 2 * (natWord n).length + 2 * ((List.ofFn g.weight).flatMap intWord).length +
      2 * (intWord (g.threshold - 1)).length + 1 := by
  rw [frame_tabGW]; simp; omega

def gateACost (n h : ℕ) : ℕ := 16 * n * h + 25 * n + 85 * h + 80

/-- **One gate, first half**: the marker and the pair of `−θ`; head `A` ends at the next gate. -/
theorem gateA_spec {n : ℕ} (g : NormalizedThresholdGate n) (h : ℕ) (preA restA : List Bool) (σ : WState ns nr)
    (hs : Std Sm Rg σ h n) (hA : σ.st (Sm 0) = preA ++ (frame (tabGW g) ++ restA)) (hAh : σ.sh (Sm 0) = preA.length)
    (hok : GateOk cap h g) :
    ∃ τ, WExec cap (gateAW Sm Rg) σ τ (gateACost n h) ∧ Std Sm Rg τ h n ∧
      τ.st (Sm 4) = σ.st (Sm 4) ++ (true :: pairW h (-g.threshold)) ∧
      τ.sh (Sm 0) = preA.length + (frame (tabGW g)).length ∧ τ.st (Sm 0) = σ.st (Sm 0) ∧
      WFrame (fun i => i = Sm 0 ∨ i = Sm 2 ∨ i = Sm 3 ∨ i = Sm 4) (fun _ => True) σ τ := by
  obtain ⟨hwok, hth1, hth2, hn1, hn2, hn3, hcap2⟩ := hok
  obtain ⟨hN, hNh, hR, hRh, hO, hc, hf, hr⟩ := hs
  have d04 := sm_ne Sm 0 4 (by decide); have d03 := sm_ne Sm 0 3 (by decide); have d43 := sm_ne Sm 4 3 (by decide)
  have d02 := sm_ne Sm 0 2 (by decide); have d24 := sm_ne Sm 2 4 (by decide); have d23 := sm_ne Sm 2 3 (by decide)
  have r01 := rg_ne Rg 0 1 (by decide); have r20 := rg_ne Rg 2 0 (by decide); have r21 := rg_ne Rg 2 1 (by decide)
  set ws := List.ofFn g.weight with hws
  set t := g.threshold - 1 with ht
  have hwsl : ws.length = n := by simp [hws]
  -- 1: the marker
  have s1 := emitW_spec cap (Sm 4) true σ hO
  set σ1 := (σ.sets (Sm 4) (σ.st (Sm 4) ++ [true])).seth (Sm 4) ((σ.st (Sm 4)).length + 1) with hσ1
  have hs1 : Std Sm Rg σ1 h n :=
    ⟨by simp [hσ1, Function.update_of_ne d24, hN], by simp [hσ1, Function.update_of_ne d24, hNh],
      by simp [hσ1, Function.update_of_ne d43.symm, hR], by simp [hσ1, Function.update_of_ne d43.symm, hRh],
      by simp [hσ1], by simp [hσ1, hc], by simp [hσ1, hf], by simp [hσ1, hr]⟩
  have hA1 : σ1.st (Sm 0) = preA ++ (frameP (natWord n) ++ (frameP (ws.flatMap intWord) ++
      (frameP (intWord t) ++ ([false] ++ restA)))) := by
    simp only [hσ1, WState.seth_st, WState.sets_st, Function.update_of_ne d04, hA, frame_tabGW]; simp [hws, ht]
  have hAh1 : σ1.sh (Sm 0) = preA.length := by simp [hσ1, Function.update_of_ne d04, hAh]
  -- 2: skip `natWord n`
  obtain ⟨τ2, s2, m2⟩ := skipNatW_spec cap (Sm 0) (Sm 4) (Sm 3) (Rg 0) (Rg 1) d04 d03 d43 r01 preA _ n σ1 hA1 hAh1
    hs1.2.2.2.2.2.1 hn2 hs1.2.2.2.2.1
  have hs2 := std_mv Sm Rg hs1 m2 d02 hs1.2.2.2.1 rfl hs1.2.2.2.2.2.2.1
  -- 3: skip the weights
  obtain ⟨τ3, s3, e3A, e3N, e3r, e3c, fr3, s3A, s3N⟩ := skipWs_spec cap Sm Rg h
    (frameP (intWord t) ++ ([false] ++ restA)) ws (preA ++ frameP (natWord n)) 0 τ2
    (by rw [m2.sI, hA1]; simp) (by rw [m2.hI]; simp)
    (by rw [hs2.1, Nat.zero_add, hwsl]) hs2.2.1 hs2.2.2.2.2.2.2.2 (by rw [hwsl]; omega) hs2.2.2.2.2.2.1
    (fun w hw => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw
      exact hwok i) hs2.2.2.2.2.1
  have o3 := fr3.1 (Sm 3) (by rintro (e | e) <;> [exact d03 e.symm; exact d23 e.symm])
  have o4 := fr3.1 (Sm 4) (by rintro (e | e) <;> [exact d04 e.symm; exact d24 e.symm])
  have v1 := fr3.2.1 (Rg 1) (by rintro (e | e) <;> [exact r01 e.symm; exact r21 e.symm])
  -- 4: return the unary counter
  have s4 := wrewind_spec cap (Sm 2) (Rg 2) n τ3 (by rw [e3r, Nat.zero_add, hwsl]) (by rw [e3r]; omega)
  set τ4 := (τ3.setv (Rg 2) 0).seth (Sm 2) (τ3.sh (Sm 2) - n) with hτ4
  have hs4 : Std Sm Rg τ4 h n :=
    ⟨by simp [hτ4, s3N, hs2.1], by simp [hτ4, e3N, hwsl],
      by simp [hτ4, o3.1, hs2.2.2.1], by simp [hτ4, Function.update_of_ne d23.symm, o3.2, hs2.2.2.2.1],
      by simp [hτ4, Function.update_of_ne d24.symm, o4.1, o4.2, hs2.2.2.2.2.1],
      by simp [hτ4, Function.update_of_ne r20.symm, e3c], by simp [hτ4, Function.update_of_ne r21.symm, v1,
        hs2.2.2.2.2.2.2.1], by simp [hτ4]⟩
  have hA4 : τ4.st (Sm 0) = (preA ++ frameP (natWord n) ++ frameP (ws.flatMap intWord)) ++
      (frameP (intWord t) ++ ([false] ++ restA)) := by
    simp only [hτ4, WState.seth_st, WState.setv_st]; rw [s3A, m2.sI, hA1]; simp
  have hAh4 : τ4.sh (Sm 0) = (preA ++ frameP (natWord n) ++ frameP (ws.flatMap intWord)).length := by
    simp only [hτ4, WState.seth_sh, WState.setv_sh]; rw [Function.update_of_ne d02, e3A]; simp; omega
  -- 5: the pair of `−θ`
  obtain ⟨τ5, s5, m5⟩ := convThrW_spec cap (Sm 0) (Sm 4) (Sm 3) (Rg 0) (Rg 1) d04 d03 d43 r01 hcap2
    (preA ++ frameP (natWord n) ++ frameP (ws.flatMap intWord)) ([false] ++ restA) t h τ4 hA4 hAh4
    hs4.2.2.2.2.2.1 hs4.2.2.2.2.2.2.1 hth1 hth2 hs4.2.2.2.2.1 hs4.2.2.1 hs4.2.2.2.1
  have hs5 := std_mv Sm Rg hs4 m5 d02 rfl rfl rfl
  -- 6: past the frame's end
  have s6 := WExec.fwd (cap := cap) (Sm 0) τ5
  set τ6 := τ5.seth (Sm 0) (τ5.sh (Sm 0) + 1) with hτ6
  refine ⟨τ6, WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 s6))))) ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · have hk1 := Nat.mul_le_mul_left (16 : ℕ) hn1
    have hk2 := Nat.mul_le_mul_left (9 : ℕ) (show natBitLength t.natAbs ≤ h by omega)
    have hm : n * (16 * h + 20) = 16 * n * h + 20 * n := by ring
    rw [hwsl, hm]; unfold gateACost convIntCost countCost wordCost; omega
  · exact ⟨by simp [hτ6, Function.update_of_ne d02, hs5.1], by simp [hτ6, Function.update_of_ne d02.symm, hs5.2.1],
      by simp [hτ6, hs5.2.2.1], by simp [hτ6, Function.update_of_ne d03.symm, hs5.2.2.2.1],
      by simp [hτ6, Function.update_of_ne d04.symm, hs5.2.2.2.2.1], by simp [hτ6, hs5.2.2.2.2.2.1],
      by simp [hτ6, hs5.2.2.2.2.2.2.1], by simp [hτ6, hs5.2.2.2.2.2.2.2]⟩
  · simp only [hτ6, WState.seth_st]
    rw [m5.sO, hτ4]; simp only [WState.seth_st, WState.setv_st]; rw [o4.1, m2.sO, hσ1]
    simp [neg_threshold_eq g, ← ht]
  · simp only [hτ6, WState.seth_sh, Function.update_self]
    rw [m5.hI, frame_tabGW_length]; simp [hws, ht]; omega
  · simp only [hτ6, WState.seth_st]; rw [m5.sI, hA4, hA]; simp [frame_tabGW, hws, ht]
  · have f1 : WFrame (fun i => i = Sm 0 ∨ i = Sm 2 ∨ i = Sm 3 ∨ i = Sm 4) (fun _ => True) σ σ1 :=
      (frame_sets _ _ σ _ _ (by simp)).trans (frame_seth _ _ _ _ _ (by simp))
    have f2 := m2.fr.mono (S' := fun i => i = Sm 0 ∨ i = Sm 2 ∨ i = Sm 3 ∨ i = Sm 4) (Rg' := fun _ => True)
      (fun i hi => by rcases hi with e | e | e <;> simp [e]) (fun _ _ => trivial)
    have f3 := fr3.mono (S' := fun i => i = Sm 0 ∨ i = Sm 2 ∨ i = Sm 3 ∨ i = Sm 4) (Rg' := fun _ => True)
      (fun i hi => by rcases hi with e | e <;> simp [e]) (fun _ _ => trivial)
    have f4 : WFrame (fun i => i = Sm 0 ∨ i = Sm 2 ∨ i = Sm 3 ∨ i = Sm 4) (fun _ => True) τ3 τ4 :=
      (frame_setv _ _ τ3 _ _ trivial).trans (frame_seth _ _ _ _ _ (by simp))
    have f5 := m5.fr.mono (S' := fun i => i = Sm 0 ∨ i = Sm 2 ∨ i = Sm 3 ∨ i = Sm 4) (Rg' := fun _ => True)
      (fun i hi => by rcases hi with e | e | e <;> simp [e]) (fun _ _ => trivial)
    exact f1.trans (f2.trans (f3.trans (f4.trans (f5.trans (frame_seth _ _ τ5 _ _ (by simp))))))

def gateBCost (n h : ℕ) : ℕ := 70 * n * h + 75 * n + 32 * h + 30

/-- **One gate, second half**: the weights' pairs; head `B` ends at the next gate. -/
theorem gateB_spec {n : ℕ} (g : NormalizedThresholdGate n) (h : ℕ) (preB restB : List Bool) (σ : WState ns nr)
    (hs : Std Sm Rg σ h n) (hB : σ.st (Sm 1) = preB ++ (frame (tabGW g) ++ restB)) (hBh : σ.sh (Sm 1) = preB.length)
    (hok : GateOk cap h g) :
    ∃ τ, WExec cap (gateBW Sm Rg) σ τ (gateBCost n h) ∧ Std Sm Rg τ h n ∧
      τ.st (Sm 4) = σ.st (Sm 4) ++ (List.ofFn g.weight).flatMap (pairW h) ∧
      τ.sh (Sm 1) = preB.length + (frame (tabGW g)).length ∧ τ.st (Sm 1) = σ.st (Sm 1) ∧
      WFrame (fun i => i = Sm 1 ∨ i = Sm 2 ∨ i = Sm 3 ∨ i = Sm 4) (fun _ => True) σ τ := by
  obtain ⟨hwok, hth1, hth2, hn1, hn2, hn3, hcap2⟩ := hok
  have hs0 := hs
  obtain ⟨hN, hNh, hR, hRh, hO, hc, hf, hr⟩ := hs
  have d14 := sm_ne Sm 1 4 (by decide); have d13 := sm_ne Sm 1 3 (by decide); have d43 := sm_ne Sm 4 3 (by decide)
  have d12 := sm_ne Sm 1 2 (by decide); have d24 := sm_ne Sm 2 4 (by decide); have d23 := sm_ne Sm 2 3 (by decide)
  have r01 := rg_ne Rg 0 1 (by decide); have r20 := rg_ne Rg 2 0 (by decide); have r21 := rg_ne Rg 2 1 (by decide)
  set ws := List.ofFn g.weight with hws
  set t := g.threshold - 1 with ht
  have hwsl : ws.length = n := by simp [hws]
  have hB0 : σ.st (Sm 1) = preB ++ (frameP (natWord n) ++ (frameP (ws.flatMap intWord) ++
      (frameP (intWord t) ++ ([false] ++ restB)))) := by rw [hB, frame_tabGW]; simp [hws, ht]
  -- 1: skip `natWord n`
  obtain ⟨τ1, s1, m1⟩ := skipNatW_spec cap (Sm 1) (Sm 4) (Sm 3) (Rg 0) (Rg 1) d14 d13 d43 r01 preB _ n σ hB0 hBh
    hc hn2 hO
  have hs1 := std_mv Sm Rg hs0 m1 d12 hRh rfl hf
  -- 2: the weights' pairs
  obtain ⟨τ2, s2, e2O, e2Oh, e2B, e2N, e2r, e2c, e2f, e2R, fr2, s2B, s2N, s2R⟩ := convWs_spec cap Sm Rg h
    (frameP (intWord t) ++ ([false] ++ restB)) (by omega) ws (preB ++ frameP (natWord n)) 0 τ1
    (by rw [m1.sI, hB0]; simp) (by rw [m1.hI]; simp)
    (by rw [hs1.1, Nat.zero_add, hwsl]) hs1.2.1 hs1.2.2.2.2.2.2.2 (by rw [hwsl]; omega) hs1.2.2.2.2.2.1
    hs1.2.2.2.2.2.2.1
    (fun w hw => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw
      exact hwok i) hs1.2.2.2.2.1 hs1.2.2.1 hs1.2.2.2.1
  -- 3: return the unary counter
  have s3 := wrewind_spec cap (Sm 2) (Rg 2) n τ2 (by rw [e2r, Nat.zero_add, hwsl]) (by rw [e2r]; omega)
  set τ3 := (τ2.setv (Rg 2) 0).seth (Sm 2) (τ2.sh (Sm 2) - n) with hτ3
  have hs3 : Std Sm Rg τ3 h n :=
    ⟨by simp [hτ3, s2N, hs1.1], by simp [hτ3, e2N, hwsl],
      by simp [hτ3, s2R, hs1.2.2.1], by simp [hτ3, Function.update_of_ne d23.symm, e2R],
      by simp [hτ3, Function.update_of_ne d24.symm, e2Oh],
      by simp [hτ3, Function.update_of_ne r20.symm, e2c], by simp [hτ3, Function.update_of_ne r21.symm, e2f],
      by simp [hτ3]⟩
  have hB3 : τ3.st (Sm 1) = (preB ++ frameP (natWord n) ++ frameP (ws.flatMap intWord)) ++
      (frameP (intWord t) ++ ([false] ++ restB)) := by
    simp only [hτ3, WState.seth_st, WState.setv_st]; rw [s2B, m1.sI, hB0]; simp
  have hBh3 : τ3.sh (Sm 1) = (preB ++ frameP (natWord n) ++ frameP (ws.flatMap intWord)).length := by
    simp only [hτ3, WState.seth_sh, WState.setv_sh]; rw [Function.update_of_ne d12, e2B]; simp; omega
  -- 4: skip `θ − 1`
  obtain ⟨τ4, s4, m4⟩ := skipIntW_spec cap (Sm 1) (Sm 4) (Sm 3) (Rg 0) (Rg 1) d14 d13 d43 r01
    (preB ++ frameP (natWord n) ++ frameP (ws.flatMap intWord)) ([false] ++ restB) t τ3 hB3 hBh3
    hs3.2.2.2.2.2.1 hth2 hs3.2.2.2.2.1
  have hs4 := std_mv Sm Rg hs3 m4 d12 hs3.2.2.2.1 rfl hs3.2.2.2.2.2.2.1
  -- 5: past the frame's end
  have s5 := WExec.fwd (cap := cap) (Sm 1) τ4
  set τ5 := τ4.seth (Sm 1) (τ4.sh (Sm 1) + 1) with hτ5
  refine ⟨τ5, WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 s5)))) ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hk1 := Nat.mul_le_mul_left (16 : ℕ) hn1
    have hk2 := Nat.mul_le_mul_left (16 : ℕ) (show natBitLength t.natAbs ≤ h by omega)
    have hm : n * (70 * h + 70) = 70 * n * h + 70 * n := by ring
    rw [hwsl, hm]; unfold gateBCost; omega
  · exact ⟨by simp [hτ5, hs4.1], by simp [hτ5, Function.update_of_ne d12.symm, hs4.2.1],
      by simp [hτ5, hs4.2.2.1], by simp [hτ5, Function.update_of_ne d13.symm, hs4.2.2.2.1],
      by simp [hτ5, Function.update_of_ne d14.symm, hs4.2.2.2.2.1], by simp [hτ5, hs4.2.2.2.2.2.1],
      by simp [hτ5, hs4.2.2.2.2.2.2.1], by simp [hτ5, hs4.2.2.2.2.2.2.2]⟩
  · simp only [hτ5, WState.seth_st]
    rw [m4.sO, hτ3]; simp only [WState.seth_st, WState.setv_st]; rw [e2O, m1.sO]; simp [hws]
  · simp only [hτ5, WState.seth_sh, Function.update_self]
    rw [m4.hI, frame_tabGW_length]; simp [hws, ht]; omega
  · simp only [hτ5, WState.seth_st]; rw [m4.sI, hB3, hB]; simp [frame_tabGW, hws, ht]
  · have f1 := m1.fr.mono (S' := fun i => i = Sm 1 ∨ i = Sm 2 ∨ i = Sm 3 ∨ i = Sm 4) (Rg' := fun _ => True)
      (fun i hi => by rcases hi with e | e | e <;> simp [e]) (fun _ _ => trivial)
    have f2 := fr2.mono (S' := fun i => i = Sm 1 ∨ i = Sm 2 ∨ i = Sm 3 ∨ i = Sm 4) (Rg' := fun _ => True)
      (fun i hi => by rcases hi with e | e | e | e <;> simp [e]) (fun _ _ => trivial)
    have f3 : WFrame (fun i => i = Sm 1 ∨ i = Sm 2 ∨ i = Sm 3 ∨ i = Sm 4) (fun _ => True) τ2 τ3 :=
      (frame_setv _ _ τ2 _ _ trivial).trans (frame_seth _ _ _ _ _ (by simp))
    have f4 := m4.fr.mono (S' := fun i => i = Sm 1 ∨ i = Sm 2 ∨ i = Sm 3 ∨ i = Sm 4) (Rg' := fun _ => True)
      (fun i hi => by rcases hi with e | e | e <;> simp [e]) (fun _ _ => trivial)
    exact f1.trans (f2.trans (f3.trans (f4.trans (frame_seth _ _ τ4 _ _ (by simp)))))

def gateCost (n h : ℕ) : ℕ := gateACost n h + 1 + gateBCost n h

/-- **One gate of the table**: `gateW h g` appended; both heads at the next gate. -/
theorem gate_spec {n : ℕ} (g : NormalizedThresholdGate n) (h : ℕ) (preA restA preB restB : List Bool)
    (σ : WState ns nr) (hs : Std Sm Rg σ h n) (hA : σ.st (Sm 0) = preA ++ (frame (tabGW g) ++ restA))
    (hAh : σ.sh (Sm 0) = preA.length) (hB : σ.st (Sm 1) = preB ++ (frame (tabGW g) ++ restB))
    (hBh : σ.sh (Sm 1) = preB.length) (hok : GateOk cap h g) :
    ∃ τ, WExec cap (gateBodyW Sm Rg) σ τ (gateCost n h) ∧ Std Sm Rg τ h n ∧
      τ.st (Sm 4) = σ.st (Sm 4) ++ gateW h g ∧
      τ.sh (Sm 0) = preA.length + (frame (tabGW g)).length ∧ τ.sh (Sm 1) = preB.length + (frame (tabGW g)).length ∧
      τ.st (Sm 0) = σ.st (Sm 0) ∧ τ.st (Sm 1) = σ.st (Sm 1) ∧
      WFrame (fun i => i = Sm 0 ∨ i = Sm 1 ∨ i = Sm 2 ∨ i = Sm 3 ∨ i = Sm 4) (fun _ => True) σ τ := by
  have d10 := sm_ne Sm 1 0 (by decide); have d12 := sm_ne Sm 1 2 (by decide)
  have d13 := sm_ne Sm 1 3 (by decide); have d14 := sm_ne Sm 1 4 (by decide)
  obtain ⟨τ1, s1, hs1, eO1, eA1, sA1, fr1⟩ := gateA_spec cap Sm Rg g h preA restA σ hs hA hAh hok
  have oB := fr1.1 (Sm 1) (by rintro (e | e | e | e) <;> [exact d10 e; exact d12 e; exact d13 e; exact d14 e])
  obtain ⟨τ, s2, hs2, eO2, eB2, sB2, fr2⟩ := gateB_spec cap Sm Rg g h preB restB τ1 hs1 (by rw [oB.1, hB])
    (by rw [oB.2, hBh]) hok
  have oA := fr2.1 (Sm 0) (by rintro (e | e | e | e) <;> [exact d10 e.symm; exact (sm_ne Sm 0 2 (by decide)) e;
    exact (sm_ne Sm 0 3 (by decide)) e; exact (sm_ne Sm 0 4 (by decide)) e])
  refine ⟨τ, WExec.seq s1 s2, hs2, ?_, by rw [oA.2, eA1], eB2, by rw [oA.1, sA1], by rw [sB2, oB.1], ?_⟩
  · rw [eO2, eO1]; simp [gateW]
  · exact (fr1.mono (fun i hi => by rcases hi with e | e | e | e <;> simp [e]) (fun _ _ => trivial)).trans
      (fr2.mono (fun i hi => by rcases hi with e | e | e | e <;> simp [e]) (fun _ _ => trivial))

/-! ## The table -/

theorem tabGW_head {n : ℕ} (g : NormalizedThresholdGate n) (rest : List Bool) :
    readTapeBit (frame (tabGW g) ++ rest) 0 = true := by
  rw [tabGW_eq, CompilerMachine.Pool.natWord_eq]
  obtain ⟨k, hk⟩ : ∃ k, natBitLength n = k + 1 := ⟨natBitLength n - 1, by have := one_le_nbl n; omega⟩
  rw [hk]; simp [List.replicate_succ, frame, readTapeBit]

theorem tableLoop_spec (h n : ℕ) : ∀ (G : List (NormalizedThresholdGate n)) (preA preB : List Bool)
    (σ : WState ns nr), Std Sm Rg σ h n → σ.st (Sm 0) = preA ++ tabSeg G → σ.sh (Sm 0) = preA.length →
    σ.st (Sm 1) = preB ++ tabSeg G → σ.sh (Sm 1) = preB.length → (∀ g ∈ G, GateOk cap h g) →
    ∃ τ, WExec cap (.whs (Sm 0) (gateBodyW Sm Rg)) σ τ (G.length * (gateCost n h + 2) + 1) ∧ Std Sm Rg τ h n ∧
      τ.st (Sm 4) = σ.st (Sm 4) ++ G.flatMap (gateW h) ∧ τ.st (Sm 0) = σ.st (Sm 0) ∧ τ.st (Sm 1) = σ.st (Sm 1) ∧
      WFrame (fun i => i = Sm 0 ∨ i = Sm 1 ∨ i = Sm 2 ∨ i = Sm 3 ∨ i = Sm 4) (fun _ => True) σ τ
  | [], preA, preB, σ, hs, hA, hAh, _, _, _ => by
    have hz : wbit σ (Sm 0) = false := by simp [wbit, hA, hAh, tabSeg, readTapeBit]
    exact ⟨σ, WExec.mono (WExec.whsF hz) (by simp), hs, by simp, rfl, rfl, WFrame.refl _ _ σ⟩
  | g :: G, preA, preB, σ, hs, hA, hAh, hB, hBh, hok => by
    obtain ⟨τ1, s1, hs1, eO1, eA1, eB1, sA1, sB1, fr1⟩ := gate_spec cap Sm Rg g h preA (tabSeg G) preB (tabSeg G) σ hs
      (by rw [hA, tabSeg_cons]) hAh (by rw [hB, tabSeg_cons]) hBh (hok g (by simp))
    obtain ⟨τ, s2, hs2, eO2, sA2, sB2, fr2⟩ := tableLoop_spec h n G (preA ++ frame (tabGW g)) (preB ++ frame (tabGW g))
      τ1 hs1 (by rw [sA1, hA, tabSeg_cons]; simp) (by rw [eA1]; simp) (by rw [sB1, hB, tabSeg_cons]; simp)
      (by rw [eB1]; simp) (fun g' hg' => hok g' (by simp [hg']))
    have hw : wbit σ (Sm 0) = true := by
      simp only [wbit, hA, hAh, tabSeg_cons, readTapeBit]
      have := tabGW_head g (tabSeg G)
      unfold readTapeBit at this
      rw [List.getD_append_right _ _ _ _ (le_refl _)]; simpa using this
    refine ⟨τ, WExec.mono (WExec.whsT hw s1 s2) ?_, hs2, ?_, by rw [sA2, sA1], by rw [sB2, sB1], fr1.trans fr2⟩
    · simp only [List.length_cons]; rw [Nat.succ_mul]; omega
    · rw [eO2, eO1]; simp

/-- **The gate table** (the consumer's `gatesW h G`, C5's `Corner.cw_spec`): from two copies of the framed bottom
region at their starts, the unary `1^n`, the ruler `false :: 1^h`, zero registers, every gate within the bounds, the
table gains `gatesW h G`. -/
theorem tableW_spec (h n : ℕ) (G : List (NormalizedThresholdGate n)) (σ : WState ns nr) (hs : Std Sm Rg σ h n)
    (hA : σ.st (Sm 0) = tabSeg G) (hAh : σ.sh (Sm 0) = 0) (hB : σ.st (Sm 1) = tabSeg G) (hBh : σ.sh (Sm 1) = 0)
    (hok : ∀ g ∈ G, GateOk cap h g) :
    ∃ τ, WExec cap (tableW Sm Rg) σ τ (G.length * (gateCost n h + 2) + 5) ∧
      τ.st (Sm 4) = σ.st (Sm 4) ++ gatesW h G ∧ τ.st (Sm 0) = σ.st (Sm 0) ∧ τ.st (Sm 1) = σ.st (Sm 1) ∧
      τ.st (Sm 2) = σ.st (Sm 2) ∧ τ.st (Sm 3) = σ.st (Sm 3) ∧ τ.val (Rg 0) = 0 ∧ τ.val (Rg 1) = 0 ∧
      τ.val (Rg 2) = 0 ∧ WFrame (fun i => i = Sm 0 ∨ i = Sm 1 ∨ i = Sm 2 ∨ i = Sm 3 ∨ i = Sm 4) (fun _ => True) σ τ := by
  obtain ⟨τ1, s1, hs1, eO1, sA1, sB1, fr1⟩ := tableLoop_spec cap Sm Rg h n G [] [] σ hs (by simpa using hA)
    (by simpa using hAh) (by simpa using hB) (by simpa using hBh) hok
  have s2 := emitW_spec cap (Sm 4) false τ1 hs1.2.2.2.2.1
  have d40 := sm_ne Sm 4 0 (by decide); have d41 := sm_ne Sm 4 1 (by decide)
  have d42 := sm_ne Sm 4 2 (by decide); have d43 := sm_ne Sm 4 3 (by decide)
  refine ⟨_, WExec.mono (WExec.seq s1 s2) (by omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [eO1, gatesW]
  · simp [Function.update_of_ne d40.symm, sA1]
  · simp [Function.update_of_ne d41.symm, sB1]
  · simp [Function.update_of_ne d42.symm, hs1.1, hs.1]
  · simp [Function.update_of_ne d43.symm, hs1.2.2.1, hs.2.2.1]
  · simp [hs1.2.2.2.2.2.1]
  · simp [hs1.2.2.2.2.2.2.1]
  · simp [hs1.2.2.2.2.2.2.2]
  · exact fr1.trans ((frame_sets _ _ τ1 _ _ (by simp)).trans (frame_seth _ _ _ _ _ (by simp)))

end Write

end NearCubicWires.WireExponent3_5.PrimT
