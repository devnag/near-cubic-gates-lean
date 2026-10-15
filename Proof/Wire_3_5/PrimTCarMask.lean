import Proof.Wire_3_5.PrimTTabWrite
import Proof.Wire_3_5.FinalPassMaskRef

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.PrimT.CarMask
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.Corner
open NearCubicWires.WireExponent3_5.PrimT

section Neg
variable {ns nr : ℕ} (cap : ℕ)

section Cell
variable (I O R : Fin (ns + 1)) (c f : Fin nr)

/-- **A negated weight's pair** from its framed `intWord`: `convIntW` with its sign branches swapped. -/
def convNegW : WM ns nr :=
  .seq (.fwd I) (.ifs I (.seq (.fwd I) (.seq (convNatW I O R c f cpyOut cpyNxt) (zeroW I O R c f)))
    (.seq (.fwd I) (.seq (zeroW I O R c f) (convNatW I O R c f cpyOut cpyNxt))))

variable (hIO : I ≠ O) (hIR : I ≠ R) (hOR : O ≠ R) (hcf : c ≠ f)
include hIO hIR hOR hcf

/-- **A negated weight's pair**: from the framed `intWord z`, the P/N pair `pairW h (−z)`. -/
theorem convNegW_spec (hcap : 1 ≤ cap) (pre rest : List Bool) (z : ℤ) (h : ℕ) (σ : WState ns nr)
    (hI : σ.st I = pre ++ (frameP (intWord z) ++ rest)) (hIh : σ.sh I = pre.length) (hc : σ.val c = 0)
    (hf : σ.val f = 0) (hkh : natBitLength z.natAbs ≤ h) (hkc : natBitLength z.natAbs ≤ cap)
    (hO : σ.sh O = (σ.st O).length) (hR : σ.st R = false :: List.replicate h true) (hRh : σ.sh R = 0) :
    ∃ τ, WExec cap (convNegW I O R c f) σ τ (convIntCost (natBitLength z.natAbs) h) ∧
      Mv I O R c f σ τ (pre.length + 2 * (intWord z).length) (pairW h (-z)) 0 0 0 := by
  obtain ⟨s1, m1⟩ := fwdI_mv cap I O R c f hIO hIR hOR hcf σ hO
  set σ1 := σ.seth I (σ.sh I + 1) with hσ1
  obtain ⟨s2, m2⟩ := fwdI_mv cap I O R c f hIO hIR hOR hcf σ1 m1.hO
  set σ2 := σ1.seth I (σ1.sh I + 1) with hσ2
  have hsign : wbit σ1 I = decide (z < 0) := by
    simp only [wbit, m1.sI, m1.hI, hI, hIh]
    have := rd_bit pre (intWord z) rest 0 (by simp [intWord])
    simpa [intWord] using this
  have hI2 : σ2.st I = (pre ++ [true, decide (z < 0)]) ++ (frameP (natWord z.natAbs) ++ rest) := by
    rw [m2.sI, m1.sI, hI, frameP_intWord]; simp
  have hIh2 : σ2.sh I = (pre ++ [true, decide (z < 0)]).length := by rw [m2.hI, m1.hI, hIh]; simp
  have hlen : (intWord z).length = (natWord z.natAbs).length + 1 := by simp [intWord]
  by_cases hz : z < 0
  · obtain ⟨σ3, s3, m3⟩ := convNatW_spec cap I O R c f hIO hIR hOR hcf hcap cpyOut cpyNxt (pre ++ [true, decide (z < 0)])
      rest z.natAbs h false σ2 hI2 hIh2 (by rw [m2.vc, m1.vc, hc]) (by rw [m2.vf, m1.vf, hf]; rfl) hkh hkc m2.hO
      (by rw [m2.sR, m1.sR, hR]) (by rw [m2.hR, m1.hR, hRh])
    obtain ⟨τ, s4, m4⟩ := wordZ_spec cap I O R c f hIO hIR hOR hcf hcap h σ3 m3.vc m3.vf m3.hO
      (by rw [m3.sR, m2.sR, m1.sR, hR]) m3.hR
    have run : WExec cap (convNegW I O R c f) σ τ _ :=
      WExec.seq s1 (WExec.ifsT (by rw [hsign]; simpa using hz) (WExec.seq s2 (WExec.seq s3 s4)))
    refine ⟨τ, WExec.mono run (by unfold convIntCost; omega), ?_⟩
    refine ((m1.trans m2).trans m3).trans_eq m4 ?_ ?_ rfl rfl rfl
    · rw [m3.hI, hlen]; simp; omega
    · rw [pairW_of_int, if_neg (by omega), cmap_cpy, Int.natAbs_neg]; simp
  · obtain ⟨σ3, s3, m3⟩ := wordZ_spec cap I O R c f hIO hIR hOR hcf hcap h σ2 (by rw [m2.vc, m1.vc, hc])
      (by rw [m2.vf, m1.vf, hf]) m2.hO (by rw [m2.sR, m1.sR, hR]) (by rw [m2.hR, m1.hR, hRh])
    obtain ⟨τ, s4, m4⟩ := convNatW_spec cap I O R c f hIO hIR hOR hcf hcap cpyOut cpyNxt (pre ++ [true, decide (z < 0)])
      rest z.natAbs h false σ3 (by rw [m3.sI, hI2]) (by rw [m3.hI, hIh2]) m3.vc (by rw [m3.vf]; rfl) hkh hkc m3.hO
      (by rw [m3.sR, m2.sR, m1.sR, hR]) m3.hR
    have run : WExec cap (convNegW I O R c f) σ τ _ :=
      WExec.seq s1 (WExec.ifsF (by rw [hsign]; simpa using hz) (WExec.seq s2 (WExec.seq s3 s4)))
    refine ⟨τ, WExec.mono run (by unfold convIntCost; omega), ?_⟩
    refine ((m1.trans m2).trans m3).trans_eq m4 ?_ ?_ rfl rfl rfl
    · rw [hlen]; simp; omega
    · rw [pairW_of_int, cmap_cpy]
      by_cases hz' : -z < 0
      · rw [if_pos hz', Int.natAbs_neg]; simp
      · have hz0 : z = 0 := by omega
        subst hz0; simp

end Cell

variable (Sm : Fin 5 ↪ Fin (ns + 1)) (Rg : Fin 3 ↪ Fin nr)

/-! ## The negation's gate -/

/-- Head `B` writes the negated weights' pairs, counted on the unary `1^n`. -/
def convNegWsW : WM ns nr :=
  .whs (Sm 2) (.seq (convNegW (Sm 1) (Sm 4) (Sm 3) (Rg 0) (Rg 1)) (.seq (.fwd (Sm 2)) (.inc (Rg 2))))

/-- The negation's gate, first half: the marker, then head `A` writes the pair of `θ − 1 = −(1 − θ)`. -/
def negAW : WM ns nr :=
  .seq (emitW (Sm 4) true) (.seq (skipNatW (Sm 0) (Rg 0)) (.seq (skipWsW Sm Rg) (.seq (WM.rewind (Sm 2) (Rg 2))
    (.seq (convIntW (Sm 0) (Sm 4) (Sm 3) (Rg 0) (Rg 1)) (.fwd (Sm 0))))))

/-- The negation's gate, second half: head `B` writes the negated weights' pairs. -/
def negBW : WM ns nr :=
  .seq (skipNatW (Sm 1) (Rg 0)) (.seq (convNegWsW Sm Rg) (.seq (WM.rewind (Sm 2) (Rg 2))
    (.seq (skipIntW (Sm 1) (Rg 0)) (.fwd (Sm 1)))))

theorem convNegWs_spec (h : ℕ) (rest : List Bool) (hcap : 1 ≤ cap) : ∀ (ws : List ℤ) (pre : List Bool) (j : ℕ)
    (σ : WState ns nr),
    σ.st (Sm 1) = pre ++ (frameP (ws.flatMap intWord) ++ rest) → σ.sh (Sm 1) = pre.length →
    σ.st (Sm 2) = List.replicate (j + ws.length) true → σ.sh (Sm 2) = j → σ.val (Rg 2) = j →
    j + ws.length ≤ cap → σ.val (Rg 0) = 0 → σ.val (Rg 1) = 0 →
    (∀ w ∈ ws, natBitLength w.natAbs ≤ h ∧ natBitLength w.natAbs ≤ cap) → σ.sh (Sm 4) = (σ.st (Sm 4)).length →
    σ.st (Sm 3) = false :: List.replicate h true → σ.sh (Sm 3) = 0 →
    ∃ τ, WExec cap (convNegWsW Sm Rg) σ τ (ws.length * (70 * h + 70) + 1) ∧
      τ.st (Sm 4) = σ.st (Sm 4) ++ ws.flatMap (fun z => pairW h (-z)) ∧ τ.sh (Sm 4) = (τ.st (Sm 4)).length ∧
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
    obtain ⟨τ1, s1, m1⟩ := convNegW_spec cap (Sm 1) (Sm 4) (Sm 3) (Rg 0) (Rg 1) d14 d13 d43 r01 hcap pre
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
    obtain ⟨τ, s4, eO, eOh, eB, eN, er, ec, ef, eR, fr, sB, sN, sR⟩ := convNegWs_spec h rest hcap ws
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

/-- **The negation's gate, first half**: the marker and the pair of `θ − 1`; head `A` ends at the next gate. -/
theorem negA_spec {n : ℕ} (g : NormalizedThresholdGate n) (h : ℕ) (preA restA : List Bool) (σ : WState ns nr)
    (hs : Std Sm Rg σ h n) (hA : σ.st (Sm 0) = preA ++ (frame (tabGW g) ++ restA)) (hAh : σ.sh (Sm 0) = preA.length)
    (hok : GateOk cap h g) :
    ∃ τ, WExec cap (negAW Sm Rg) σ τ (gateACost n h) ∧ Std Sm Rg τ h n ∧
      τ.st (Sm 4) = σ.st (Sm 4) ++ (true :: pairW h (g.threshold - 1)) ∧
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
  -- 5: the pair of `θ − 1`
  obtain ⟨τ5, s5, m5⟩ := convIntW_spec cap (Sm 0) (Sm 4) (Sm 3) (Rg 0) (Rg 1) d04 d03 d43 r01 (by omega)
    (preA ++ frameP (natWord n) ++ frameP (ws.flatMap intWord)) ([false] ++ restA) t h τ4 hA4 hAh4
    hs4.2.2.2.2.2.1 hs4.2.2.2.2.2.2.1 (by omega) hth2 hs4.2.2.2.2.1 hs4.2.2.1 hs4.2.2.2.1
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
    simp [← ht]
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

/-- **The negation's gate, second half**: the negated weights' pairs; head `B` ends at the next gate. -/
theorem negB_spec {n : ℕ} (g : NormalizedThresholdGate n) (h : ℕ) (preB restB : List Bool) (σ : WState ns nr)
    (hs : Std Sm Rg σ h n) (hB : σ.st (Sm 1) = preB ++ (frame (tabGW g) ++ restB)) (hBh : σ.sh (Sm 1) = preB.length)
    (hok : GateOk cap h g) :
    ∃ τ, WExec cap (negBW Sm Rg) σ τ (gateBCost n h) ∧ Std Sm Rg τ h n ∧
      τ.st (Sm 4) = σ.st (Sm 4) ++ (List.ofFn g.weight).flatMap (fun z => pairW h (-z)) ∧
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
  -- 2: the negated weights' pairs
  obtain ⟨τ2, s2, e2O, e2Oh, e2B, e2N, e2r, e2c, e2f, e2R, fr2, s2B, s2N, s2R⟩ := convNegWs_spec cap Sm Rg h
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

/-- The table word of an atom's negation, from the atom's fields. -/
theorem gateW_negGate (h : ℕ) {n : ℕ} (g : NormalizedThresholdGate n) :
    gateW h (negGate g) = true :: (pairW h (g.threshold - 1) ++ (List.ofFn g.weight).flatMap (fun z => pairW h (-z))) := by
  unfold gateW negGate
  have e : -(1 - g.threshold) = g.threshold - 1 := by ring
  simp only [e, List.ofFn_eq_map, List.flatMap_map]

end Neg

/-- The table of the doubled atom list is the atoms' and negations' gates in turn. -/
theorem gatesW_maskGates (h : ℕ) {n : ℕ} (X : List (NormalizedThresholdGate n)) :
    gatesW h (maskGates X) = X.flatMap (fun g => gateW h g ++ gateW h (negGate g)) ++ [false] := by
  unfold gatesW maskGates
  rw [List.flatMap_assoc]
  simp

/-! ## One atom and its negation -/

section Mask
variable {ns nr : ℕ} (cap : ℕ) (Sm Sn : Fin 5 ↪ Fin (ns + 1)) (Rg : Fin 3 ↪ Fin nr)

def maskBodyW : WM ns nr := .seq (gateBodyW Sm Rg) (.seq (negAW Sn Rg) (negBW Sn Rg))

/-- **The mask table writer.** -/
def maskTableW : WM ns nr := .seq (.whs (Sm 0) (maskBodyW Sm Sn Rg)) (emitW (Sm 4) false)

def maskCost (n h : ℕ) : ℕ := gateCost n h + 1 + (gateACost n h + 1 + gateBCost n h)

/-- The four copies and the shared streams: the positions a mask step may move. -/
def MaskS (i : Fin (ns + 1)) : Prop := i = Sm 0 ∨ i = Sm 1 ∨ i = Sn 0 ∨ i = Sn 1 ∨ i = Sm 2 ∨ i = Sm 3 ∨ i = Sm 4

variable (e2 : Sn 2 = Sm 2) (e3 : Sn 3 = Sm 3) (e4 : Sn 4 = Sm 4)
  (dC0 : Sn 0 ≠ Sm 0) (dC1 : Sn 0 ≠ Sm 1) (dD0 : Sn 1 ≠ Sm 0) (dD1 : Sn 1 ≠ Sm 1)
include e2 e3 e4 dC0 dC1 dD0 dD1

theorem std_swap (σ : WState ns nr) (h n : ℕ) : Std Sn Rg σ h n ↔ Std Sm Rg σ h n := by
  unfold Std; rw [e2, e3, e4]

/-- **One atom and its negation**: `gateW h g ++ gateW h (negGate g)` appended; all four heads at the next atom. -/
theorem mask_spec {n : ℕ} (g : NormalizedThresholdGate n) (h : ℕ)
    (preA restA preB restB preC restC preD restD : List Bool) (σ : WState ns nr) (hs : Std Sm Rg σ h n)
    (hA : σ.st (Sm 0) = preA ++ (frame (tabGW g) ++ restA)) (hAh : σ.sh (Sm 0) = preA.length)
    (hB : σ.st (Sm 1) = preB ++ (frame (tabGW g) ++ restB)) (hBh : σ.sh (Sm 1) = preB.length)
    (hC : σ.st (Sn 0) = preC ++ (frame (tabGW g) ++ restC)) (hCh : σ.sh (Sn 0) = preC.length)
    (hD : σ.st (Sn 1) = preD ++ (frame (tabGW g) ++ restD)) (hDh : σ.sh (Sn 1) = preD.length)
    (hok : GateOk cap h g) :
    ∃ τ, WExec cap (maskBodyW Sm Sn Rg) σ τ (maskCost n h) ∧ Std Sm Rg τ h n ∧
      τ.st (Sm 4) = σ.st (Sm 4) ++ (gateW h g ++ gateW h (negGate g)) ∧
      τ.sh (Sm 0) = preA.length + (frame (tabGW g)).length ∧ τ.sh (Sm 1) = preB.length + (frame (tabGW g)).length ∧
      τ.sh (Sn 0) = preC.length + (frame (tabGW g)).length ∧ τ.sh (Sn 1) = preD.length + (frame (tabGW g)).length ∧
      τ.st (Sm 0) = σ.st (Sm 0) ∧ τ.st (Sm 1) = σ.st (Sm 1) ∧ τ.st (Sn 0) = σ.st (Sn 0) ∧
      τ.st (Sn 1) = σ.st (Sn 1) ∧ WFrame (MaskS Sm Sn) (fun _ => True) σ τ := by
  have n0 : ∀ j : Fin 5, j ≠ 0 → Sn 0 ≠ Sn j := fun j hj => Sn.injective.ne (Ne.symm hj)
  have n1 : ∀ j : Fin 5, j ≠ 1 → Sn 1 ≠ Sn j := fun j hj => Sn.injective.ne (Ne.symm hj)
  have m0 : ∀ j : Fin 5, j ≠ 0 → Sm 0 ≠ Sm j := fun j hj => Sm.injective.ne (Ne.symm hj)
  have m1 : ∀ j : Fin 5, j ≠ 1 → Sm 1 ≠ Sm j := fun j hj => Sm.injective.ne (Ne.symm hj)
  have c2 : Sn 0 ≠ Sm 2 := e2 ▸ n0 2 (by decide)
  have c3 : Sn 0 ≠ Sm 3 := e3 ▸ n0 3 (by decide)
  have c4 : Sn 0 ≠ Sm 4 := e4 ▸ n0 4 (by decide)
  have d2 : Sn 1 ≠ Sm 2 := e2 ▸ n1 2 (by decide)
  have d3 : Sn 1 ≠ Sm 3 := e3 ▸ n1 3 (by decide)
  have d4 : Sn 1 ≠ Sm 4 := e4 ▸ n1 4 (by decide)
  have a2 : Sm 0 ≠ Sn 2 := e2 ▸ m0 2 (by decide)
  have a3 : Sm 0 ≠ Sn 3 := e3 ▸ m0 3 (by decide)
  have a4 : Sm 0 ≠ Sn 4 := e4 ▸ m0 4 (by decide)
  have b2 : Sm 1 ≠ Sn 2 := e2 ▸ m1 2 (by decide)
  have b3 : Sm 1 ≠ Sn 3 := e3 ▸ m1 3 (by decide)
  have b4 : Sm 1 ≠ Sn 4 := e4 ▸ m1 4 (by decide)
  have cd : Sn 0 ≠ Sn 1 := n0 1 (by decide)
  -- the atom
  obtain ⟨τ1, s1, hs1, eO1, eA1, eB1, sA1, sB1, fr1⟩ := gate_spec cap Sm Rg g h preA restA preB restB σ hs hA hAh
    hB hBh hok
  have oC1 := fr1.1 (Sn 0) (by rintro (e | e | e | e | e); exacts [dC0 e, dC1 e, c2 e, c3 e, c4 e])
  have oD1 := fr1.1 (Sn 1) (by rintro (e | e | e | e | e); exacts [dD0 e, dD1 e, d2 e, d3 e, d4 e])
  -- the negation, first half
  obtain ⟨τ2, s2, hs2, eO2, eC2, sC2, fr2⟩ := negA_spec cap Sn Rg g h preC restC τ1
    ((std_swap Sm Sn Rg e2 e3 e4 dC0 dC1 dD0 dD1 τ1 h n).mpr hs1) (by rw [oC1.1, hC]) (by rw [oC1.2, hCh]) hok
  have oA2 := fr2.1 (Sm 0) (by rintro (e | e | e | e); exacts [dC0 e.symm, a2 e, a3 e, a4 e])
  have oB2 := fr2.1 (Sm 1) (by rintro (e | e | e | e); exacts [dC1 e.symm, b2 e, b3 e, b4 e])
  have oD2 := fr2.1 (Sn 1) (by
    rintro (e | e | e | e); exacts [cd e.symm, n1 2 (by decide) e, n1 3 (by decide) e, n1 4 (by decide) e])
  -- the negation, second half
  obtain ⟨τ, s3, hs3, eO3, eD3, sD3, fr3⟩ := negB_spec cap Sn Rg g h preD restD τ2 hs2
    (by rw [oD2.1, oD1.1, hD]) (by rw [oD2.2, oD1.2, hDh]) hok
  have oA3 := fr3.1 (Sm 0) (by rintro (e | e | e | e); exacts [dD0 e.symm, a2 e, a3 e, a4 e])
  have oB3 := fr3.1 (Sm 1) (by rintro (e | e | e | e); exacts [dD1 e.symm, b2 e, b3 e, b4 e])
  have oC3 := fr3.1 (Sn 0) (by
    rintro (e | e | e | e); exacts [cd e, n0 2 (by decide) e, n0 3 (by decide) e, n0 4 (by decide) e])
  refine ⟨τ, WExec.seq s1 (WExec.seq s2 s3), (std_swap Sm Sn Rg e2 e3 e4 dC0 dC1 dD0 dD1 τ h n).mp hs3, ?_,
    by rw [oA3.2, oA2.2, eA1], by rw [oB3.2, oB2.2, eB1], by rw [oC3.2, eC2], eD3,
    by rw [oA3.1, oA2.1, sA1], by rw [oB3.1, oB2.1, sB1], by rw [oC3.1, sC2, oC1.1], by rw [sD3, oD2.1, oD1.1], ?_⟩
  · rw [← e4, eO3, eO2, e4, eO1, gateW_negGate]; simp
  · have hm : ∀ i, (i = Sn 0 ∨ i = Sn 2 ∨ i = Sn 3 ∨ i = Sn 4) → MaskS Sm Sn i := by
      intro i hi; rcases hi with e | e | e | e
      · exact Or.inr (Or.inr (Or.inl e))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (e.trans e2)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (e.trans e3))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (e.trans e4))))))
    have hm' : ∀ i, (i = Sn 1 ∨ i = Sn 2 ∨ i = Sn 3 ∨ i = Sn 4) → MaskS Sm Sn i := by
      intro i hi; rcases hi with e | e | e | e
      · exact Or.inr (Or.inr (Or.inr (Or.inl e)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (e.trans e2)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (e.trans e3))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (e.trans e4))))))
    have hg : ∀ i, (i = Sm 0 ∨ i = Sm 1 ∨ i = Sm 2 ∨ i = Sm 3 ∨ i = Sm 4) → MaskS Sm Sn i := by
      intro i hi; rcases hi with e | e | e | e | e
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr e)))))
    exact (fr1.mono hg (fun _ _ => trivial)).trans ((fr2.mono hm (fun _ _ => trivial)).trans
      (fr3.mono hm' (fun _ _ => trivial)))

/-! ## The mask table -/

theorem maskLoop_spec (h n : ℕ) : ∀ (G : List (NormalizedThresholdGate n)) (preA preB preC preD : List Bool)
    (σ : WState ns nr), Std Sm Rg σ h n → σ.st (Sm 0) = preA ++ tabSeg G → σ.sh (Sm 0) = preA.length →
    σ.st (Sm 1) = preB ++ tabSeg G → σ.sh (Sm 1) = preB.length → σ.st (Sn 0) = preC ++ tabSeg G →
    σ.sh (Sn 0) = preC.length → σ.st (Sn 1) = preD ++ tabSeg G → σ.sh (Sn 1) = preD.length →
    (∀ g ∈ G, GateOk cap h g) →
    ∃ τ, WExec cap (.whs (Sm 0) (maskBodyW Sm Sn Rg)) σ τ (G.length * (maskCost n h + 2) + 1) ∧
      Std Sm Rg τ h n ∧ τ.st (Sm 4) = σ.st (Sm 4) ++ G.flatMap (fun g => gateW h g ++ gateW h (negGate g)) ∧
      τ.st (Sm 0) = σ.st (Sm 0) ∧ τ.st (Sm 1) = σ.st (Sm 1) ∧ τ.st (Sn 0) = σ.st (Sn 0) ∧
      τ.st (Sn 1) = σ.st (Sn 1) ∧ WFrame (MaskS Sm Sn) (fun _ => True) σ τ
  | [], preA, preB, preC, preD, σ, hs, hA, hAh, _, _, _, _, _, _, _ => by
    have hz : wbit σ (Sm 0) = false := by simp [wbit, hA, hAh, tabSeg, readTapeBit]
    exact ⟨σ, WExec.mono (WExec.whsF hz) (by simp), hs, by simp, rfl, rfl, rfl, rfl, WFrame.refl _ _ σ⟩
  | g :: G, preA, preB, preC, preD, σ, hs, hA, hAh, hB, hBh, hC, hCh, hD, hDh, hok => by
    obtain ⟨τ1, s1, hs1, eO1, eA1, eB1, eC1, eD1, sA1, sB1, sC1, sD1, fr1⟩ := mask_spec cap Sm Sn Rg e2 e3 e4 dC0 dC1
      dD0 dD1 g h preA (tabSeg G) preB (tabSeg G) preC (tabSeg G) preD (tabSeg G) σ hs
      (by rw [hA, tabSeg_cons]) hAh (by rw [hB, tabSeg_cons]) hBh (by rw [hC, tabSeg_cons]) hCh
      (by rw [hD, tabSeg_cons]) hDh (hok g (by simp))
    obtain ⟨τ, s2, hs2, eO2, sA2, sB2, sC2, sD2, fr2⟩ := maskLoop_spec h n G (preA ++ frame (tabGW g))
      (preB ++ frame (tabGW g)) (preC ++ frame (tabGW g)) (preD ++ frame (tabGW g)) τ1 hs1
      (by rw [sA1, hA, tabSeg_cons]; simp) (by rw [eA1]; simp) (by rw [sB1, hB, tabSeg_cons]; simp)
      (by rw [eB1]; simp) (by rw [sC1, hC, tabSeg_cons]; simp) (by rw [eC1]; simp)
      (by rw [sD1, hD, tabSeg_cons]; simp) (by rw [eD1]; simp) (fun g' hg' => hok g' (by simp [hg']))
    have hw : wbit σ (Sm 0) = true := by
      simp only [wbit, hA, hAh, tabSeg_cons, readTapeBit]
      have := tabGW_head g (tabSeg G)
      unfold readTapeBit at this
      rw [List.getD_append_right _ _ _ _ (le_refl _)]; simpa using this
    refine ⟨τ, WExec.mono (WExec.whsT hw s1 s2) ?_, hs2, ?_, by rw [sA2, sA1], by rw [sB2, sB1], by rw [sC2, sC1],
      by rw [sD2, sD1], fr1.trans fr2⟩
    · simp only [List.length_cons]; rw [Nat.succ_mul]; omega
    · rw [eO2, eO1]; simp

/-- **The mask table** (the consumer's `gatesW h (maskGates X)`, C5's `Corner.cw_spec` on PA's carrier slice): from
four copies of `tabSeg X` at their starts, the unary `1^n`, the ruler `false :: 1^h`, zero registers, every atom within
the bounds, the table gains `gatesW h (maskGates X)`. -/
theorem maskTableW_spec (h n : ℕ) (X : List (NormalizedThresholdGate n)) (σ : WState ns nr) (hs : Std Sm Rg σ h n)
    (hA : σ.st (Sm 0) = tabSeg X) (hAh : σ.sh (Sm 0) = 0) (hB : σ.st (Sm 1) = tabSeg X) (hBh : σ.sh (Sm 1) = 0)
    (hC : σ.st (Sn 0) = tabSeg X) (hCh : σ.sh (Sn 0) = 0) (hD : σ.st (Sn 1) = tabSeg X) (hDh : σ.sh (Sn 1) = 0)
    (hok : ∀ g ∈ X, GateOk cap h g) :
    ∃ τ, WExec cap (maskTableW Sm Sn Rg) σ τ (X.length * (maskCost n h + 2) + 5) ∧
      τ.st (Sm 4) = σ.st (Sm 4) ++ gatesW h (maskGates X) ∧ τ.st (Sm 0) = σ.st (Sm 0) ∧
      τ.st (Sm 1) = σ.st (Sm 1) ∧ τ.st (Sn 0) = σ.st (Sn 0) ∧ τ.st (Sn 1) = σ.st (Sn 1) ∧
      τ.st (Sm 2) = σ.st (Sm 2) ∧ τ.st (Sm 3) = σ.st (Sm 3) ∧ τ.val (Rg 0) = 0 ∧ τ.val (Rg 1) = 0 ∧
      τ.val (Rg 2) = 0 ∧ WFrame (MaskS Sm Sn) (fun _ => True) σ τ := by
  obtain ⟨τ1, s1, hs1, eO1, sA1, sB1, sC1, sD1, fr1⟩ := maskLoop_spec cap Sm Sn Rg e2 e3 e4 dC0 dC1 dD0 dD1 h n X
    [] [] [] [] σ hs (by simpa using hA) (by simpa using hAh) (by simpa using hB) (by simpa using hBh)
    (by simpa using hC) (by simpa using hCh) (by simpa using hD) (by simpa using hDh) hok
  have s2 := emitW_spec cap (Sm 4) false τ1 hs1.2.2.2.2.1
  have d40 := sm_ne Sm 4 0 (by decide); have d41 := sm_ne Sm 4 1 (by decide)
  have d42 := sm_ne Sm 4 2 (by decide); have d43 := sm_ne Sm 4 3 (by decide)
  have c4 : Sn 0 ≠ Sm 4 := e4 ▸ Sn.injective.ne (show (0 : Fin 5) ≠ 4 by decide)
  have dd4 : Sn 1 ≠ Sm 4 := e4 ▸ Sn.injective.ne (show (1 : Fin 5) ≠ 4 by decide)
  refine ⟨_, WExec.mono (WExec.seq s1 s2) (by omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [gatesW_maskGates]; simp [eO1]
  · simp [Function.update_of_ne d40.symm, sA1]
  · simp [Function.update_of_ne d41.symm, sB1]
  · simp [Function.update_of_ne c4, sC1]
  · simp [Function.update_of_ne dd4, sD1]
  · simp [Function.update_of_ne d42.symm, hs1.1, hs.1]
  · simp [Function.update_of_ne d43.symm, hs1.2.2.1, hs.2.2.1]
  · simp [hs1.2.2.2.2.2.1]
  · simp [hs1.2.2.2.2.2.2.1]
  · simp [hs1.2.2.2.2.2.2.2]
  · exact fr1.trans ((frame_sets _ _ τ1 _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))).trans
      (frame_seth _ _ _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))))

end Mask

/-! ## The width -/

/-- **`hov` of `cw_spec` for a carrier's doubled atom list** at the table width `tabH X`. -/
theorem mask_hov {n : ℕ} (X : List (NormalizedThresholdGate n)) :
    ∀ g ∈ maskGates X, (-g.threshold).toNat + ((List.ofFn g.weight).map Int.natAbs).sum < 2 ^ tabH X ∧
      (-(-g.threshold)).toNat + ((List.ofFn g.weight).map Int.natAbs).sum < 2 ^ tabH X := by
  intro g' hg'
  unfold maskGates at hg'
  obtain ⟨g, hg, hmem⟩ := List.mem_flatMap.mp hg'
  have hle := tabGW_le_tabH X g hg
  have hpos : 1 ≤ (tabGW g).length := by rw [tabGW_eq]; simp [intWord]; omega
  have hp : 2 * 2 ^ (tabGW g).length ≤ 2 ^ tabH X := by
    rw [← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨h1, h2⟩ := gate_mag_lt g
  rcases List.mem_cons.mp hmem with h0 | hmem'
  · rw [h0]
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show (tabGW g).length ≤ tabH X by omega)
    omega
  · rw [List.mem_singleton] at hmem'
    rw [hmem']
    have hs : ((List.ofFn (negGate g).weight).map Int.natAbs).sum = ((List.ofFn g.weight).map Int.natAbs).sum := by
      simp [negGate, List.map_ofFn, Function.comp_def]
    rw [hs]
    have ht1 : (-(negGate g).threshold).toNat ≤ (-(-g.threshold)).toNat := by simp only [negGate]; omega
    have ht2 : (-(-(negGate g).threshold)).toNat ≤ (-g.threshold).toNat + 1 := by simp only [negGate]; omega
    have hone : 1 ≤ 2 ^ (tabGW g).length := Nat.one_le_two_pow
    omega

end NearCubicWires.WireExponent3_5.PrimT.CarMask
