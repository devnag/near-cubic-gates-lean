import Proof.Gates.CheckedPCPP.MsgWrite

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CheckedPCPP

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.WordPrograms NearCubicGates.PublishedSources.PCPP

variable {ns nr : ℕ} {cap : ℕ}

theorem pairs_read_even : ∀ (w : List Bool) (j : ℕ), readTapeBit (FramedSim.pairs w) (2 * j) = decide (j < w.length)
  | [], j => by simp [readTapeBit]
  | b :: w, 0 => by simp [readTapeBit]
  | b :: w, j + 1 => by
    have := pairs_read_even w j
    simp only [FramedSim.pairs_cons, readTapeBit, List.length_cons] at this ⊢
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, List.getD_cons_succ, List.getD_cons_succ, this]
    simp

theorem pairs_read_odd : ∀ (w : List Bool) (j : ℕ), readTapeBit (FramedSim.pairs w) (2 * j + 1) = w.getD j false
  | [], j => by simp [readTapeBit]
  | b :: w, 0 => by simp [readTapeBit]
  | b :: w, j + 1 => by
    have := pairs_read_odd w j
    simp only [FramedSim.pairs_cons, readTapeBit] at this ⊢
    rw [show 2 * (j + 1) + 1 = 2 * j + 1 + 1 + 1 by ring, List.getD_cons_succ, List.getD_cons_succ, this]
    simp

/-- Move the head of `X` right `R` times (`R` kept; `C`, `T` scratch `0`). -/
def fwdBy (X : Fin (ns + 1)) (R C T : Fin nr) : WMX ns nr :=
  .seq (addR R C T) (.whr C (.seq (WMX.dec C) (WMX.fwd X)))

theorem fwdBy_runs (X : Fin (ns + 1)) {R C T : Fin nr} (hRC : R ≠ C) (hRT : R ≠ T) (hCT : C ≠ T)
    (σ : WState ns nr) (hC : σ.val C = 0) (hT : σ.val T = 0) (hR : σ.val R ≤ cap) :
    Runs cap (fwdBy X R C T) σ (23 * σ.val R + 5)
      (fun τ => τ.sh X = σ.sh X + σ.val R ∧ τ.val C = 0 ∧ τ.st X = σ.st X ∧ SameExcept σ τ [X] [C]) := by
  have h1 := addR_spec cap hRC hRT hCT σ hT (by rw [hC]; omega)
  rw [hC, Nat.zero_add] at h1
  set n := σ.val R with hn
  have key := Runs.count (cap := cap) (K := C) (body := WMX.fwd X) 1 n
    (fun k τ => τ.sh X = σ.sh X + k ∧ τ.st X = σ.st X ∧ SameExcept σ τ [X] [C]) hR
    (fun k _ τ hτ _ => ⟨_, WXExec.fwd (cap := cap) X _, ⟨by simp [hτ.1]; omega, by simp [hτ.2.1], by
        refine (hτ.2.2.trans (sameExcept_setv _ (by simp) _)).trans (sameExcept_seth _ (by simp) _) |>.weaken
          (by simp) (by simp)⟩, by simp⟩)
    (σ.setv C n) ⟨by simp, by simp, sameExcept_setv _ (by simp) _⟩ (by simp)
  exact ((Runs.seqE h1 key).cost (by omega)).post (fun τ hτ => ⟨by rw [hτ.1.1], hτ.2, hτ.1.2.1, hτ.1.2.2⟩)

theorem encBit_unit (E : LinearCodeFamily) (n i j : ℕ) (hi : i < n) (hj : j < E.length n) :
    (List.ofFn (E.enc n (unitVec n i))).getD j false = decide ((⟨i, hi⟩ : Fin n) ∈ E.support n ⟨j, hj⟩) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn]
  exact enc_unit E n ⟨i, hi⟩ ⟨j, hj⟩

/-- One row: read the marker and the code bit, write it into the matrix, move the matrix head by `n`. -/
def rowBody (OE MAT : Fin (ns + 1)) (Q P LL C T : Fin nr) : WMX ns nr :=
  .seq (WMX.fwd OE) (.seq (.ifs OE (WMX.wr MAT true) (WMX.wr MAT false)) (.seq (WMX.fwd OE)
    (.seq (WMX.inc LL) (.seq (fwdBy MAT Q C T) (addR Q P T)))))

/-- Rows `< j` of column `i` are written. -/
def RowAt (E : LinearCodeFamily) (OE MAT : Fin (ns + 1)) (P LL C T : Fin nr) (σ0 : WState ns nr) (n i j : ℕ)
    (τ : WState ns nr) : Prop :=
  τ.sh OE = 2 * j ∧ τ.sh MAT = j * n + i ∧ τ.val P = j * n + i ∧ τ.val LL = j ∧ τ.val C = 0 ∧ τ.val T = 0 ∧
    (∀ p, readTapeBit (τ.st MAT) p = matPart E n i j p) ∧ τ.st OE = σ0.st OE ∧
    SameExcept σ0 τ [OE, MAT] [P, LL, C, T]

theorem rowBody_runs (E : LinearCodeFamily) {OE MAT : Fin (ns + 1)} (hOM : OE ≠ MAT) {Q P LL C T : Fin nr}
    (hR : [Q, P, LL, C, T].Nodup) (n i j : ℕ) (hi : i < n) (hjL : j < E.length n) (σ0 τ : WState ns nr)
    (hOE : RdEq (σ0.st OE) (FramedSim.pairs (List.ofFn (E.enc n (unitVec n i))))) (hQ : σ0.val Q = n)
    (hcap : (E.length n + 1) * n ≤ cap) (hτ : RowAt E OE MAT P LL C T σ0 n i j τ) :
    Runs cap (rowBody OE MAT Q P LL C T) τ (41 * n + 20) (RowAt E OE MAT P LL C T σ0 n i (j + 1)) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    not_false_eq_true] at hR
  obtain ⟨⟨q2, q3, q4, q5⟩, ⟨p1, p2, p3⟩, ⟨l1, l2⟩, c1⟩ := hR
  obtain ⟨hOh, hMh, hPv, hLv, hCv, hTv, hM, hst, hs⟩ := hτ
  have hQv : τ.val Q = n := by rw [hs.val (by simp [q2, q3, q4, q5]), hQ]
  have hLn : j * n + n ≤ (E.length n) * n := by nlinarith
  set b := decide ((⟨i, hi⟩ : Fin n) ∈ E.support n ⟨j, hjL⟩) with hb
  have hbit : readTapeBit (τ.st OE) (2 * j + 1) = b := by
    rw [hst, hOE (2 * j + 1), pairs_read_odd, encBit_unit E n i j hi hjL]
  -- 1. marker
  set τ1 := τ.seth OE (2 * j + 1) with hτ1
  have e1 : WXExec cap (WMX.fwd OE) τ τ1 1 := by
    have := WXExec.fwd (cap := cap) OE τ; rwa [hOh] at this
  -- 2. the bit
  set τ2 := τ1.sets MAT (writeTapeBit (τ.st MAT) (j * n + i) b) with hτ2
  have hw1 : wbit τ1 OE = b := by simp [wbit, hτ1, hbit]
  have e2 : WXExec cap (.ifs OE (WMX.wr MAT true) (WMX.wr MAT false)) τ1 τ2 2 := by
    have hwr := fun c => WXExec.wr (cap := cap) MAT c τ1
    have hM1 : τ1.sh MAT = j * n + i := by simp [hτ1, Function.update_apply, Ne.symm hOM, hMh]
    have hM2 : τ1.st MAT = τ.st MAT := by simp [hτ1]
    rw [hM1, hM2] at hwr
    cases hbb : b
    · rw [hbb] at hw1
      exact WXExec.ifsF (P := WMX.wr MAT true) hw1 (by rw [hτ2, hbb]; exact hwr false)
    · rw [hbb] at hw1
      exact WXExec.ifsT (Q := WMX.wr MAT false) hw1 (by rw [hτ2, hbb]; exact hwr true)
  -- 3. past the bit
  set τ3 := τ2.seth OE (2 * j + 2) with hτ3
  have e3 : WXExec cap (WMX.fwd OE) τ2 τ3 1 := by
    have := WXExec.fwd (cap := cap) OE τ2
    have h2 : τ2.sh OE = 2 * j + 1 := by simp [hτ2, hτ1]
    rwa [h2] at this
  -- 4. count the row
  have e4 := WXExec.inc (cap := cap) LL τ3 (by simp [hτ3, hτ2, hτ1, hLv]; nlinarith)
  have hτ3LL : τ3.val LL = j := by simp [hτ3, hτ2, hτ1, hLv]
  rw [hτ3LL] at e4
  set τ4 := τ3.setv LL (j + 1) with hτ4
  have hτ4C : τ4.val C = 0 := by simp [hτ4, hτ3, hτ2, hτ1, Function.update_apply, Ne.symm l1, hCv]
  have hτ4T : τ4.val T = 0 := by simp [hτ4, hτ3, hτ2, hτ1, Function.update_apply, Ne.symm l2, hTv]
  have hτ4Q : τ4.val Q = n := by simp [hτ4, hτ3, hτ2, hτ1, Function.update_apply, q3, hQv]
  have hτ4P : τ4.val P = j * n + i := by simp [hτ4, hτ3, hτ2, hτ1, Function.update_apply, p1, hPv]
  -- 5. matrix head += n
  obtain ⟨τ5, e5, p5h, p5C, p5st, p5s⟩ := fwdBy_runs (cap := cap) MAT q4 q5 c1 τ4 hτ4C hτ4T
    (by rw [hτ4Q]; nlinarith)
  rw [hτ4Q] at p5h e5
  -- 6. P += n
  have h5T : τ5.val T = 0 := by rw [p5s.val (by simp [Ne.symm c1]), hτ4T]
  have h5Q : τ5.val Q = n := by rw [p5s.val (by simp [q4]), hτ4Q]
  have h5P : τ5.val P = j * n + i := by rw [p5s.val (by simp [p2]), hτ4P]
  have e6 := addR_spec cap q2 q5 p3 τ5 h5T (by rw [h5Q, h5P]; nlinarith)
  rw [h5Q, h5P] at e6
  refine ⟨_, WXExec.mono (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5 e6)))))
    (by omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [WState.setv_sh, p5s.sh (by simp [hOM])]; simp [hτ4, hτ3]; ring
  · rw [WState.setv_sh, p5h]; simp [hτ4, hτ3, hτ2, hτ1, Function.update_apply, Ne.symm hOM, hMh]; ring
  · simp; ring
  · rw [WState.setv_val, Function.update_of_ne (Ne.symm p1), p5s.val (by simp [l1])]; simp [hτ4]
  · rw [WState.setv_val, Function.update_of_ne (Ne.symm p2), p5C]
  · rw [WState.setv_val, Function.update_of_ne (Ne.symm p3), h5T]
  · intro p
    rw [WState.setv_st, p5st]
    simp only [hτ4, hτ3, hτ2, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_self]
    rw [readTapeBit_write, matPart_step E n ⟨i, hi⟩ ⟨j, hjL⟩ p, hM p]
  · rw [WState.setv_st, p5s.st (by simp [hOM])]
    simp [hτ4, hτ3, hτ2, hτ1, Function.update_apply, hOM, hst]
  · exact (((((hs.trans (sameExcept_seth _ (by simp) _)).trans (sameExcept_sets _ (by simp) _)).trans
      (sameExcept_seth _ (by simp) _)).trans (sameExcept_setv _ (by simp) _)).trans
      (p5s.weaken (by simp) (by simp))).trans (sameExcept_setv _ (by simp) _)

/-- Store the encoder's answer on `e_I` as column `I` of the matrix. -/
def rdCol (OE MAT : Fin (ns + 1)) (Q I P LL C T BR : Fin nr) : WMX ns nr :=
  .seq (addR I P T) (.seq (fwdBy MAT I C T) (.seq (.whs OE (rowBody OE MAT Q P LL C T))
    (.seq (rewindBy MAT P C T) (.seq (.wm (WM.clear P)) (rewindBy OE BR C T)))))

/-- The cost bound of `rdCol`. -/
def rdCost (n L B : ℕ) : ℕ := (L + 2) * (70 * n + 50) + 25 * B + 60

theorem rdCol_runs (E : LinearCodeFamily) {OE MAT : Fin (ns + 1)} (hOM : OE ≠ MAT) {Q I P LL C T BR : Fin nr}
    (hR : [Q, I, P, LL, C, T, BR].Nodup) (n i B : ℕ) (hi : i < n) (σ : WState ns nr)
    (hOE : RdEq (σ.st OE) (FramedSim.pairs (List.ofFn (E.enc n (unitVec n i)))))
    (hOEh : σ.sh OE = 0) (hMAT : ∀ p, readTapeBit (σ.st MAT) p = matPart E n i 0 p) (hMATh : σ.sh MAT = 0)
    (hQ : σ.val Q = n) (hI : σ.val I = i) (hP : σ.val P = 0) (hLL : σ.val LL = 0) (hC : σ.val C = 0)
    (hT : σ.val T = 0) (hBR : σ.val BR = B) (hB : 2 * E.length n ≤ B) (hcap : (E.length n + 1) * n + B ≤ cap) :
    Runs cap (rdCol OE MAT Q I P LL C T BR) σ (rdCost n (E.length n) B)
      (fun τ => (∀ p, readTapeBit (τ.st MAT) p = matPart E n (i + 1) 0 p) ∧ τ.sh MAT = 0 ∧ τ.sh OE = 0 ∧
        τ.st OE = σ.st OE ∧ τ.val P = 0 ∧ τ.val LL = E.length n ∧ τ.val C = 0 ∧ τ.val T = 0 ∧
        SameExcept σ τ [OE, MAT] [P, LL, C, T]) := by
  have hcapL : (E.length n + 1) * n ≤ cap := by omega
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    not_false_eq_true] at hR
  obtain ⟨⟨q1, q2, q3, q4, q5, q6⟩, ⟨i1, i2, i3, i4, i5⟩, ⟨p1, p2, p3, p4⟩, ⟨l1, l2, l3⟩, ⟨c1, c2⟩, t1⟩ := hR
  set L := E.length n with hL
  have hn1 : 1 ≤ n := by omega
  have hLn : L * n + n ≤ cap := by nlinarith
  have hncap : n ≤ cap := by nlinarith
  -- P := i, matrix head := i
  have e1 := addR_spec cap i1 i4 p3 σ hT (by rw [hP, hI]; omega)
  rw [hP, hI, Nat.zero_add] at e1
  obtain ⟨τ2, e2, p2h, p2C, p2st, p2s⟩ := fwdBy_runs (cap := cap) MAT i3 i4 c1 (σ.setv P i)
    (by simp [Function.update_apply, Ne.symm p2, hC]) (by simp [Function.update_apply, Ne.symm p3, hT])
    (by simp [Function.update_apply, Ne.symm i1, hI]; omega)
  have hτ2I : (σ.setv P i).val I = i := by simp [Function.update_apply, i1, hI]
  rw [hτ2I] at p2h e2
  have s2 : SameExcept σ τ2 [OE, MAT] [P, LL, C, T] :=
    (sameExcept_setv σ (by simp) i).trans (p2s.weaken (by simp) (by simp))
  have r0 : RowAt E OE MAT P LL C T σ n i 0 τ2 := ⟨by rw [p2s.sh (by simp [hOM]), WState.setv_sh, hOEh],
    by rw [p2h, WState.setv_sh, hMATh]; simp, by rw [p2s.val (by simp [p2])]; simp,
    by rw [p2s.val (by simp [l1])]; simp [Function.update_apply, Ne.symm p1, hLL],
    p2C, by rw [p2s.val (by simp [Ne.symm c1])]; simp [Function.update_apply, Ne.symm p3, hT],
    by intro p; rw [p2st]; exact hMAT p, by rw [p2s.st (by simp [hOM])]; rfl, s2⟩
  -- the rows
  have hrows := Runs.whs (cap := cap) (i := OE) (P := rowBody OE MAT Q P LL C T)
    (fun k τ => RowAt E OE MAT P LL C T σ n i (L - k) τ ∧ k ≤ L) (41 * n + 20)
    (RowAt E OE MAT P LL C T σ n i L)
    (fun τ hτ => by
      refine ⟨?_, by have h := hτ.1; rwa [Nat.sub_zero] at h⟩
      simp only [wbit, hτ.1.1, hτ.1.2.2.2.2.2.2.2.1]
      rw [hOE (2 * (L - 0)), pairs_read_even]; simp [hL])
    (fun k τ hτ => by
      have hk : L - (k + 1) < L := by omega
      refine ⟨by simp only [wbit, hτ.1.1, hτ.1.2.2.2.2.2.2.2.1]; rw [hOE, pairs_read_even]; simp [hL]; omega, ?_⟩
      have := rowBody_runs E hOM (by simp [q2, q3, q4, q5, p1, p2, p3, l1, l2, c1]) n i (L - (k + 1)) hi hk σ τ hOE
        hQ hcapL hτ.1
      refine this.post (fun ρ hρ => ⟨by rwa [show L - k = L - (k + 1) + 1 by omega], by omega⟩))
    L τ2 ⟨by simpa using r0, le_rfl⟩
  obtain ⟨τ3, e3, h3Oh, h3Mh, h3P, h3LL, h3C, h3T, h3M, h3st, h3s⟩ := hrows
  -- rewind the matrix, clear P, rewind the output
  obtain ⟨τ4, e4, h4Mh, h4C, h4st, h4s⟩ := rewindBy_runs (cap := cap) MAT p2 p3 c1 τ3 h3C h3T
    (by rw [h3P]; omega) (by rw [h3Mh, h3P])
  have h4P : τ4.val P = L * n + i := by rw [h4s.val (by simp [p2]), h3P]
  have e5 := wclear_spec cap P (L * n + i) τ4 h4P (by rw [h4P]; omega)
  have h4BR : τ4.val BR = B := by
    rw [h4s.val (by simp [Ne.symm c2]), h3s.val (by simp [Ne.symm p4, Ne.symm l3, Ne.symm c2, Ne.symm t1]), hBR]
  obtain ⟨τ6, e6, h6Oh, h6C, h6st, h6s⟩ := rewindBy_runs (cap := cap) OE (Ne.symm c2) (Ne.symm t1) c1 (τ4.setv P 0)
    (by simp [Function.update_apply, Ne.symm p2, h4C])
    (by simp [Function.update_apply, Ne.symm p3]; rw [h4s.val (by simp [Ne.symm c1]), h3T])
    (by simp [Function.update_apply, Ne.symm p4, h4BR]; omega)
    (by simp [Function.update_apply, Ne.symm p4, h4BR]; rw [h4s.sh (by simp [hOM]), h3Oh]; omega)
  simp only [WState.setv_val, Function.update_of_ne (Ne.symm p4), h4BR] at e6
  refine ⟨τ6, WXExec.mono (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq (WXExec.wm e5) e6)))))
    ?_, ?_, ?_, h6Oh, ?_, ?_, ?_, h6C, ?_, ?_⟩
  · simp only [rdCost]
    have : i ≤ n := by omega
    nlinarith
  · intro p
    rw [h6s.st (by simp [Ne.symm hOM]), WState.setv_st, h4st, h3M p, matPart_next_col]
  · rw [h6s.sh (by simp [Ne.symm hOM]), WState.setv_sh, h4Mh]
  · rw [h6st, WState.setv_st, h4s.st (by simp [hOM]), h3st]
  · rw [h6s.val (by simp [p2]), WState.setv_val, Function.update_self]
  · rw [h6s.val (by simp [l1]), WState.setv_val, Function.update_of_ne (Ne.symm p1),
      h4s.val (by simp [l1]), h3LL]
  · rw [h6s.val (by simp [Ne.symm c1]), WState.setv_val, Function.update_of_ne (Ne.symm p3),
      h4s.val (by simp [Ne.symm c1]), h3T]
  · exact ((h3s.trans (h4s.weaken (by simp) (by simp))).trans (sameExcept_setv _ (by simp) _)).trans
      (h6s.weaken (by simp) (by simp))

end NearCubicGates.Close.CheckedPCPP
