import Proof.Wire_3_5.PrimTTabScan

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.PrimT.CarWM
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.Corner
open NearCubicWires.WireExponent3_5.PrimT

section Words
variable {ns nr : ℕ} (cap : ℕ)

/-! ## Copying one framed word -/

/-- One framed cell pair copied from `N` to the end of `O`. -/
def copyBodyW (N O : Fin (ns + 1)) : WM ns nr :=
  .seq (.fwd N) (.seq (emitW O true) (.seq (.ifs N (emitW O true) (emitW O false)) (.fwd N)))

/-- **Copy one framed word** from `N` (at its head) to the end of `O`. -/
def copyFrameW (N O : Fin (ns + 1)) : WM ns nr := .seq (.whs N (copyBodyW N O)) (emitW O false)

theorem rd_at (pre l : List Bool) : readTapeBit (pre ++ l) pre.length = l.getD 0 false := by
  unfold readTapeBit; rw [List.getD_append_right _ _ _ _ (le_refl _)]; simp

theorem rd_at1 (pre l : List Bool) : readTapeBit (pre ++ l) (pre.length + 1) = l.getD 1 false := by
  unfold readTapeBit; rw [List.getD_append_right _ _ _ _ (by omega)]; simp

theorem copyLoop_spec (N O : Fin (ns + 1)) (hNO : N ≠ O) (rest : List Bool) :
    ∀ (y pre : List Bool) (σ : WState ns nr), σ.st N = pre ++ (frame y ++ rest) → σ.sh N = pre.length →
      σ.sh O = (σ.st O).length →
      ∃ τ, WExec cap (.whs N (copyBodyW N O)) σ τ (14 * y.length + 1) ∧ τ.st O = σ.st O ++ frameP y ∧
        τ.sh O = (τ.st O).length ∧ τ.st N = σ.st N ∧ τ.sh N = pre.length + 2 * y.length ∧
        (∀ j, j ≠ N → j ≠ O → Same σ τ j) ∧ τ.val = σ.val ∧ τ.cell = σ.cell
  | [], pre, σ, hN, hNh, hO => by
    have hz : wbit σ N = false := by simp only [wbit, hN, hNh, rd_at]; rfl
    exact ⟨σ, WExec.mono (WExec.whsF hz) (by omega), by simp [frameP], hO, rfl, by simp [hNh],
      fun _ _ _ => ⟨rfl, rfl⟩, rfl, rfl⟩
  | b :: bs, pre, σ, hN, hNh, hO => by
    have hON : O ≠ N := fun e => hNO e.symm
    obtain ⟨σ1, s1, n1, n1h, o1, v1, c1⟩ := fwd_facts cap N σ
    have O1 := o1 O hON
    obtain ⟨σ2, s2, e2, e2h, o2, v2, c2⟩ := emit_facts cap O true σ1 (by rw [O1.1, O1.2, hO])
    have N2 := o2 N hNO
    have hb : wbit σ2 N = b := by
      simp only [wbit, N2.1, N2.2, n1, n1h, hN, hNh, rd_at1]; rfl
    obtain ⟨σ3, s3, e3, e3h, o3, v3, c3⟩ := emit_facts cap O b σ2 e2h
    have s3' : WExec cap (.ifs N (emitW O true) (emitW O false)) σ2 σ3 4 := by
      cases b
      · exact WExec.ifsF hb s3
      · exact WExec.ifsT hb s3
    have N3 := o3 N hNO
    obtain ⟨σ4, s4, n4, n4h, o4, v4, c4⟩ := fwd_facts cap N σ3
    have O4 := o4 O hON
    obtain ⟨τ, s5, eO, eOh, eN, eNh, oth, v5, c5⟩ := copyLoop_spec N O hNO rest bs (pre ++ [true, b]) σ4
      (by rw [n4, N3.1, N2.1, n1, hN]; simp [frame]) (by rw [n4h, N3.2, N2.2, n1h, hNh]; simp)
      (by rw [O4.1, O4.2, e3h])
    have hw : wbit σ N = true := by simp only [wbit, hN, hNh, rd_at]; rfl
    refine ⟨τ, WExec.mono (WExec.whsT hw (WExec.seq s1 (WExec.seq s2 (WExec.seq s3' s4))) s5) (by simp; omega),
      ?_, eOh, ?_, ?_, ?_, ?_, ?_⟩
    · rw [eO, O4.1, e3, e2, O1.1]; simp [frameP]
    · rw [eN, n4, N3.1, N2.1, n1]
    · rw [eNh]; simp; omega
    · intro j h1 h2
      exact ((((o1 j h1).trans' (o2 j h2)).trans' (o3 j h2)).trans' (o4 j h1)).trans' (oth j h1 h2)
    · rw [v5, v4, v3, v2, v1]
    · rw [c5, c4, c3, c2, c1]

/-- **One framed word copied** to the end of `O`. -/
theorem copyFrame_spec (N O : Fin (ns + 1)) (hNO : N ≠ O) (pre y rest : List Bool) (σ : WState ns nr)
    (hN : σ.st N = pre ++ (frame y ++ rest)) (hNh : σ.sh N = pre.length) (hO : σ.sh O = (σ.st O).length) :
    ∃ τ, WExec cap (copyFrameW N O) σ τ (14 * y.length + 5) ∧ τ.st O = σ.st O ++ frame y ∧
      τ.sh O = (τ.st O).length ∧ τ.st N = σ.st N ∧ τ.sh N = pre.length + 2 * y.length ∧
      (∀ j, j ≠ N → j ≠ O → Same σ τ j) ∧ τ.val = σ.val ∧ τ.cell = σ.cell := by
  obtain ⟨τ1, s1, e1, e1h, n1, n1h, o1, v1, c1⟩ := copyLoop_spec cap N O hNO rest y pre σ hN hNh hO
  obtain ⟨τ, s2, e2, e2h, o2, v2, c2⟩ := emit_facts cap O false τ1 e1h
  have N2 := o2 N hNO
  refine ⟨τ, WExec.mono (WExec.seq s1 s2) (by omega), by rw [e2, e1, frame_eq_frameP]; simp, e2h,
    by rw [N2.1, n1], by rw [N2.2, n1h], fun j h1 h2 => (o1 j h1 h2).trans' (o2 j h2), by rw [v2, v1],
    by rw [c2, c1]⟩

/-! ## Skipping the accumulated native words -/

theorem skipTabs_spec {n : ℕ} (A : Fin (ns + 1)) : ∀ (G : List (NormalizedThresholdGate n)) (pre : List Bool)
    (σ : WState ns nr), σ.st A = pre ++ tabSeg G → σ.sh A = pre.length →
    WExec cap (.whs A (skipFrameW A)) σ (σ.seth A (pre.length + (tabSeg G).length)) (4 * (tabSeg G).length + 1)
  | [], pre, σ, hA, hAh => by
    have hz : wbit σ A = false := by simp only [wbit, hA, hAh, rd_at]; rfl
    have e : σ.seth A (pre.length + (tabSeg ([] : List (NormalizedThresholdGate n))).length) = σ := by
      rw [show (tabSeg ([] : List (NormalizedThresholdGate n))).length = 0 from rfl, Nat.add_zero, ← hAh, wseth_same]
    rw [e]; exact WExec.mono (WExec.whsF hz) (by omega)
  | g :: G, pre, σ, hA, hAh => by
    have s1 := skipFrame_spec cap A pre (tabSeg G) (tabGW g) σ (by rw [hA, tabSeg_cons]) hAh
    have ih := skipTabs_spec A G (pre ++ frame (tabGW g)) (σ.seth A (pre.length + (frame (tabGW g)).length))
      (by simp [hA, tabSeg_cons]) (by simp)
    rw [wseth_seth] at ih
    have hw : wbit σ A = true := by
      simp only [wbit, hA, hAh, rd_at, tabSeg_cons]
      have := tabGW_head g (tabSeg G); simpa [readTapeBit] using this
    have hpos : 1 ≤ (tabGW g).length := by rw [tabGW_eq]; simp [intWord]; omega
    have hl : (tabSeg (g :: G)).length = (frame (tabGW g)).length + (tabSeg G).length := by
      rw [tabSeg_cons, List.length_append]
    rw [hl, frame_length] at *
    have e : (pre ++ frame (tabGW g)).length + (tabSeg G).length = pre.length + (2 * (tabGW g).length + 1 +
        (tabSeg G).length) := by simp [frame_length]; omega
    rw [e] at ih
    exact WExec.mono (WExec.whsT hw s1 ih) (by omega)

/-! ## Skipping `i` atoms along the round counter -/

theorem flatMap_split (ys : List (List Bool)) (k : ℕ) (hk : k < ys.length) :
    ys.flatMap frame = (ys.take k).flatMap frame ++ (frame ys[k] ++ (ys.drop (k + 1)).flatMap frame) := by
  have e : ys = ys.take k ++ ys[k] :: ys.drop (k + 1) := by rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
  exact (congrArg (List.flatMap frame) e).trans (by simp only [List.flatMap_append, List.flatMap_cons])

theorem take_succ_len (ys : List (List Bool)) (k : ℕ) (hk : k < ys.length) :
    ((ys.take (k + 1)).flatMap frame).length = ((ys.take k).flatMap frame).length + (frame ys[k]).length := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.flatMap_append, List.length_append]
  simp

theorem skipAtoms_spec (S K : Fin (ns + 1)) (hSK : S ≠ K) (W : ℕ) (ys : List (List Bool))
    (hys : ∀ y ∈ ys, y.length = W) (tail : List Bool) (i : ℕ) (hi : i ≤ ys.length) (rest : List Bool) :
    ∀ (d k : ℕ) (σ : WState ns nr), k + d = i → σ.st S = ys.flatMap frame ++ tail →
      σ.sh S = ((ys.take k).flatMap frame).length → σ.st K = List.replicate i true ++ (false :: rest) →
      σ.sh K = k →
      ∃ τ, WExec cap (.whs K (.seq (skipFrameW S) (.fwd K))) σ τ (d * (5 * W + 8) + 1) ∧ τ.st = σ.st ∧
        τ.sh S = ((ys.take i).flatMap frame).length ∧ τ.sh K = i ∧ (∀ j, j ≠ S → j ≠ K → τ.sh j = σ.sh j) ∧
        τ.val = σ.val ∧ τ.cell = σ.cell
  | 0, k, σ, hkd, hS, hSh, hK, hKh => by
    have hk : k = i := by omega
    subst hk
    have hz : wbit σ K = false := by
      simp only [wbit, hK, hKh]
      have := rd_at (List.replicate k true) (false :: rest); simpa using this
    exact ⟨σ, WExec.mono (WExec.whsF hz) (by omega), rfl, hSh, hKh, fun _ _ _ => rfl, rfl, rfl⟩
  | d + 1, k, σ, hkd, hS, hSh, hK, hKh => by
    have hk : k < ys.length := by omega
    have hKS : K ≠ S := fun e => hSK e.symm
    have s1 := skipFrame_spec cap S ((ys.take k).flatMap frame) ((ys.drop (k + 1)).flatMap frame ++ tail) ys[k] σ
      (by rw [hS, flatMap_split ys k hk]; simp) hSh
    set σ1 := σ.seth S (((ys.take k).flatMap frame).length + (frame ys[k]).length) with hσ1
    have s2 := WExec.fwd (cap := cap) K σ1
    set σ2 := σ1.seth K (σ1.sh K + 1) with hσ2
    have hlen : ys[k].length = W := hys _ (List.getElem_mem hk)
    obtain ⟨τ, s3, est, eS, eK, oth, ev, ec⟩ := skipAtoms_spec S K hSK W ys hys tail i hi rest d (k + 1) σ2
      (by omega) (by simp [hσ2, hσ1, hS])
      (by simp only [hσ2, hσ1, WState.seth_sh]; rw [Function.update_of_ne hSK, Function.update_self, take_succ_len ys k hk])
      (by simp [hσ2, hσ1, hK])
      (by simp only [hσ2, hσ1, WState.seth_sh]; rw [Function.update_self, Function.update_of_ne hKS, hKh])
    have hki : k < i := by omega
    have hw : wbit σ K = true := by
      simp only [wbit, hK, hKh]
      unfold readTapeBit; rw [List.getD_append _ _ _ _ (by simp; omega)]; simp [hki]
    refine ⟨τ, WExec.mono (WExec.whsT hw (WExec.seq s1 s2) s3) ?_, by rw [est]; simp [hσ2, hσ1], eS, eK, ?_,
      by rw [ev]; simp [hσ2, hσ1], by rw [ec]; simp [hσ2, hσ1]⟩
    · rw [hlen]; have : (d + 1) * (5 * W + 8) = d * (5 * W + 8) + (5 * W + 8) := by ring
      omega
    · intro j h1 h2; rw [oth j h1 h2]; simp [hσ2, hσ1, Function.update_of_ne h1, Function.update_of_ne h2]

/-- Writing `true` at the counter's first `false`. -/
theorem write_counter (i : ℕ) (rest : List Bool) :
    writeTapeBit (List.replicate i true ++ (false :: rest)) i true = List.replicate (i + 1) true ++ rest := by
  induction i with
  | zero => rfl
  | succ i ih => simp [List.replicate_succ, writeTapeBit, ih]

end Words

/-! ## The round's programs -/

/-- **The crop** (streams `0` atoms, `1` counter, `2` worker input): skip `i` atoms, copy atom `i`, advance. -/
def cropW : WM 2 0 := .seq (.whs 1 (.seq (skipFrameW 0) (.fwd 1))) (.seq (copyFrameW 0 2) (.wr 1 true))

/-- **The append** (streams `0` native output, `1` accumulator): skip the header and the words, append the new word. -/
def appendW : WM 1 0 :=
  .seq (.fwd 1) (.seq (.fwd 1) (.seq (.fwd 1) (.seq (.fwd 1) (.seq (.whs 1 (skipFrameW 1)) (copyFrameW 0 1)))))

/-- The accumulator's header, the scan's native-word shape `natWord 0 ++ frame []`. -/
def accHdr : List Bool := [true, false, false, false]

theorem hdr_eq : accHdr = natWord 0 ++ frame [] := by decide

/-- **The accumulator's header** written on an empty stream. -/
def initW : WM 0 0 := .seq (emitW 0 true) (.seq (emitW 0 false) (.seq (emitW 0 false) (emitW 0 false)))

def cropCost (i W : ℕ) : ℕ := i * (5 * W + 8) + 14 * W + 10

theorem cropW_spec (cap W : ℕ) (ys : List (List Bool)) (hys : ∀ y ∈ ys, y.length = W) (tail : List Bool) (i : ℕ)
    (hi : i < ys.length) (rest : List Bool) (σ : WState 2 0) (h0 : ∀ j, σ.sh j = 0)
    (hS : σ.st 0 = ys.flatMap frame ++ tail) (hK : σ.st 1 = List.replicate i true ++ (false :: rest))
    (hC : σ.st 2 = []) :
    ∃ τ, WExec cap cropW σ τ (cropCost i W) ∧ τ.st 0 = σ.st 0 ∧ τ.st 1 = List.replicate (i + 1) true ++ rest ∧
      τ.st 2 = frame ys[i] ∧ τ.cell = σ.cell := by
  obtain ⟨τ1, s1, est, eS, eK, oth, ev, ec⟩ := skipAtoms_spec cap (0 : Fin 3) 1 (by decide) W ys hys tail i hi.le
    rest i 0 σ (by omega) hS (by simp [h0]) hK (h0 1)
  obtain ⟨τ2, s2, e2, e2h, n2, -, o2, v2, c2⟩ := copyFrame_spec cap (0 : Fin 3) 2 (by decide)
    ((ys.take i).flatMap frame) ys[i] ((ys.drop (i + 1)).flatMap frame ++ tail) τ1
    (by rw [est, hS, flatMap_split ys i hi]; simp) eS (by rw [est, hC, oth 2 (by decide) (by decide), h0]; rfl)
  have K2 := o2 1 (by decide) (by decide)
  have s3 := WExec.wr (cap := cap) (1 : Fin 3) true τ2
  refine ⟨_, WExec.mono (WExec.seq s1 (WExec.seq s2 s3)) ?_, ?_, ?_, ?_, ?_⟩
  · have hl : ys[i].length = W := hys _ (List.getElem_mem hi)
    rw [hl]; unfold cropCost; omega
  · simp; rw [n2, est]
  · simp; rw [K2.1, K2.2, est, hK, eK, write_counter]
  · simp; rw [e2, est, hC]; rfl
  · simp; rw [c2, ec]

def appendCost {n : ℕ} (G : List (NormalizedThresholdGate n)) (y : List Bool) : ℕ :=
  4 * (tabSeg G).length + 14 * y.length + 20

theorem appendW_spec (cap : ℕ) {n : ℕ} (G : List (NormalizedThresholdGate n)) (y rest : List Bool)
    (σ : WState 1 0) (h0 : ∀ j, σ.sh j = 0) (hN : σ.st 0 = frame y ++ rest) (hA : σ.st 1 = accHdr ++ tabSeg G) :
    ∃ τ, WExec cap appendW σ τ (appendCost G y) ∧ τ.st 0 = σ.st 0 ∧ τ.st 1 = accHdr ++ tabSeg G ++ frame y ∧
      τ.cell = σ.cell := by
  have f1 := WExec.fwd (cap := cap) (1 : Fin 2) σ
  have f2 := WExec.fwd (cap := cap) (1 : Fin 2) (σ.seth 1 (σ.sh 1 + 1))
  rw [wseth_seth] at f2; simp only [WState.seth_sh, Function.update_self] at f2
  have f3 := WExec.fwd (cap := cap) (1 : Fin 2) (σ.seth 1 (σ.sh 1 + 1 + 1))
  rw [wseth_seth] at f3; simp only [WState.seth_sh, Function.update_self] at f3
  have f4 := WExec.fwd (cap := cap) (1 : Fin 2) (σ.seth 1 (σ.sh 1 + 1 + 1 + 1))
  rw [wseth_seth] at f4; simp only [WState.seth_sh, Function.update_self] at f4
  set σ4 := σ.seth 1 (σ.sh 1 + 1 + 1 + 1 + 1) with hσ4
  have s5 := skipTabs_spec cap (1 : Fin 2) G accHdr σ4 (by simp [hσ4, hA]) (by simp [hσ4, h0]; rfl)
  set σ5 := σ4.seth 1 (accHdr.length + (tabSeg G).length) with hσ5
  obtain ⟨τ, s6, e6, -, n6, -, -, -, c6⟩ := copyFrame_spec cap (0 : Fin 2) 1 (by decide) [] y rest σ5
    (by simp [hσ5, hσ4, hN]) (by simp [hσ5, hσ4, h0]) (by simp [hσ5, hσ4, hA])
  refine ⟨τ, WExec.mono (WExec.seq f1 (WExec.seq f2 (WExec.seq f3 (WExec.seq f4 (WExec.seq s5 s6))))) ?_, ?_, ?_, ?_⟩
  · unfold appendCost; omega
  · rw [n6]; simp [hσ5, hσ4]
  · rw [e6]; simp [hσ5, hσ4, hA]
  · rw [c6]; simp [hσ5, hσ4]

theorem initW_spec (cap : ℕ) (σ : WState 0 0) (h0 : σ.sh 0 = 0) (hA : σ.st 0 = []) :
    ∃ τ, WExec cap initW σ τ 15 ∧ τ.st 0 = accHdr ∧ τ.cell = σ.cell := by
  obtain ⟨σ1, s1, e1, e1h, -, -, c1⟩ := emit_facts cap (0 : Fin 1) true σ (by rw [h0, hA]; rfl)
  obtain ⟨σ2, s2, e2, e2h, -, -, c2⟩ := emit_facts cap (0 : Fin 1) false σ1 e1h
  obtain ⟨σ3, s3, e3, e3h, -, -, c3⟩ := emit_facts cap (0 : Fin 1) false σ2 e2h
  obtain ⟨τ, s4, e4, -, -, -, c4⟩ := emit_facts cap (0 : Fin 1) false σ3 e3h
  refine ⟨τ, WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) (by omega), ?_, by rw [c4, c3, c2, c1]⟩
  rw [e4, e3, e2, e1, hA]; rfl

end NearCubicWires.WireExponent3_5.PrimT.CarWM
