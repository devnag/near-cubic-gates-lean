import Proof.Wire_3_5.FinalPassWordMul

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.SignedSortKey

variable {ns nr : ℕ} (cap : ℕ)

/-! ## Moving a head by a count -/

/-- Forward `2·C` cells on stream `i`, counting in `PC`; `C` is restored through `T`. -/
def advC (i : Fin (ns + 1)) (C T PC : Fin nr) : WM ns nr :=
  .seq (.whr C (.seq (.dec C) (.seq (.inc T) (.seq (.fwd i) (.seq (.fwd i) (.seq (.inc PC) (.inc PC)))))))
    (WM.move T C)

/-- Back `2·C` cells on stream `i`, uncounting in `PC`; `C` is restored through `T`. -/
def retC (i : Fin (ns + 1)) (C T PC : Fin nr) : WM ns nr :=
  .seq (.whr C (.seq (.dec C) (.seq (.inc T) (.seq (.bwd i) (.seq (.bwd i) (.seq (.dec PC) (.dec PC)))))))
    (WM.move T C)

theorem advLoop_spec (i : Fin (ns + 1)) (C T PC : Fin nr) (hCT : C ≠ T) (hCP : C ≠ PC) (hTP : T ≠ PC) :
    ∀ (n : ℕ) (σ : WState ns nr), σ.val C = n → σ.val T + n ≤ cap → σ.val PC + 2 * n ≤ cap →
      WExec cap (.whr C (.seq (.dec C) (.seq (.inc T) (.seq (.fwd i) (.seq (.fwd i) (.seq (.inc PC) (.inc PC)))))))
        σ ((((σ.setv C 0).setv T (σ.val T + n)).seth i (σ.sh i + 2 * n)).setv PC (σ.val PC + 2 * n)) (19 * n + 1)
  | 0, σ, h0, _, _ => by
    refine WExec.cast cap (WExec.whrF h0) ?_ le_rfl
    wgen_eq [h0]
  | n + 1, σ, hn, hT, hP => by
    have s1 := WExec.dec (cap := cap) C σ (by omega)
    have s2 := WExec.inc (cap := cap) T (σ.setv C (σ.val C - 1)) (by simp [Function.update_of_ne (Ne.symm hCT)]; omega)
    obtain ⟨σ2, hσ2⟩ : ∃ τ : WState ns nr, τ = (σ.setv C (σ.val C - 1)).setv T (σ.val T + 1) := ⟨_, rfl⟩
    have s2' : WExec cap (.inc T) (σ.setv C (σ.val C - 1)) σ2 3 := by
      rw [hσ2]; simpa [Function.update_of_ne (Ne.symm hCT)] using s2
    have s3 := WExec.fwd (cap := cap) i σ2
    have s4 := WExec.fwd (cap := cap) i (σ2.seth i (σ2.sh i + 1))
    obtain ⟨σ4, hσ4⟩ : ∃ τ : WState ns nr, τ = σ2.seth i (σ2.sh i + 2) := ⟨_, rfl⟩
    have s4' : WExec cap (.fwd i) (σ2.seth i (σ2.sh i + 1)) σ4 1 := by
      rw [hσ4]; simpa [wseth_seth] using s4
    have hP4 : σ4.val PC = σ.val PC := by
      rw [hσ4, hσ2]; simp [Function.update_of_ne hCP.symm, Function.update_of_ne hTP.symm]
    have s5 := WExec.inc (cap := cap) PC σ4 (by omega)
    have s6 := WExec.inc (cap := cap) PC (σ4.setv PC (σ4.val PC + 1)) (by simp; omega)
    obtain ⟨σ6, hσ6⟩ : ∃ τ : WState ns nr, τ = σ4.setv PC (σ4.val PC + 2) := ⟨_, rfl⟩
    have s6' : WExec cap (.inc PC) (σ4.setv PC (σ4.val PC + 1)) σ6 3 := by
      rw [hσ6]; simpa [wsetv_setv] using s6
    have ih := advLoop_spec i C T PC hCT hCP hTP n σ6
      (by rw [hσ6, hσ4, hσ2]; simp [Function.update_of_ne hCP, Function.update_of_ne hCT, hn])
      (by rw [hσ6, hσ4, hσ2]; simp [Function.update_of_ne hTP]; omega)
      (by rw [hσ6, hσ4, hσ2]; simp [Function.update_of_ne hCP.symm, Function.update_of_ne hTP.symm]; omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq s1 (WExec.seq s2' (WExec.seq s3 (WExec.seq s4'
      (WExec.seq s5 s6'))))) ih) ?_ (by omega)
    rw [hσ6, hσ4, hσ2]
    wgen_eq [Function.update_of_ne hCT, Function.update_of_ne hCP, Function.update_of_ne hTP,
      Function.update_of_ne hCT.symm, Function.update_of_ne hCP.symm, Function.update_of_ne hTP.symm]

theorem advC_spec (i : Fin (ns + 1)) (C T PC : Fin nr) (hCT : C ≠ T) (hCP : C ≠ PC) (hTP : T ≠ PC)
    (n : ℕ) (σ : WState ns nr) (hn : σ.val C = n) (hT : σ.val T = 0) (hnc : n ≤ cap) (hP : σ.val PC + 2 * n ≤ cap) :
    WExec cap (advC i C T PC) σ ((σ.seth i (σ.sh i + 2 * n)).setv PC (σ.val PC + 2 * n)) (26 * n + 3) := by
  have h1 := advLoop_spec cap i C T PC hCT hCP hTP n σ hn (by omega) hP
  obtain ⟨σ1, hσ1⟩ : ∃ τ : WState ns nr,
      τ = (((σ.setv C 0).setv T (σ.val T + n)).seth i (σ.sh i + 2 * n)).setv PC (σ.val PC + 2 * n) := ⟨_, rfl⟩
  rw [← hσ1] at h1
  have h2 := wmove_spec cap T C hCT.symm n σ1 (by rw [hσ1]; simp [Function.update_of_ne hTP, hT])
    (by rw [hσ1]; simp [Function.update_of_ne hTP, hT]; omega)
    (by rw [hσ1]; simp [Function.update_of_ne hTP, Function.update_of_ne hCP, Function.update_of_ne hCT, hT]; omega)
  refine WExec.cast cap (WExec.seq h1 h2) ?_ (by omega)
  rw [hσ1]
  wgen_eq [Function.update_of_ne hCT, Function.update_of_ne hCP, Function.update_of_ne hTP,
    Function.update_of_ne hCT.symm, Function.update_of_ne hCP.symm, Function.update_of_ne hTP.symm, hT, hn]

theorem retLoop_spec (i : Fin (ns + 1)) (C T PC : Fin nr) (hCT : C ≠ T) (hCP : C ≠ PC) (hTP : T ≠ PC) :
    ∀ (n : ℕ) (σ : WState ns nr), σ.val C = n → σ.val T + n ≤ cap → σ.val PC ≤ cap →
      WExec cap (.whr C (.seq (.dec C) (.seq (.inc T) (.seq (.bwd i) (.seq (.bwd i) (.seq (.dec PC) (.dec PC)))))))
        σ ((((σ.setv C 0).setv T (σ.val T + n)).seth i (σ.sh i - 2 * n)).setv PC (σ.val PC - 2 * n)) (15 * n + 1)
  | 0, σ, h0, _, _ => by
    refine WExec.cast cap (WExec.whrF h0) ?_ le_rfl
    wgen_eq [h0]
  | n + 1, σ, hn, hT, hP => by
    have s1 := WExec.dec (cap := cap) C σ (by omega)
    have s2 := WExec.inc (cap := cap) T (σ.setv C (σ.val C - 1)) (by simp [Function.update_of_ne (Ne.symm hCT)]; omega)
    obtain ⟨σ2, hσ2⟩ : ∃ τ : WState ns nr, τ = (σ.setv C (σ.val C - 1)).setv T (σ.val T + 1) := ⟨_, rfl⟩
    have s2' : WExec cap (.inc T) (σ.setv C (σ.val C - 1)) σ2 3 := by
      rw [hσ2]; simpa [Function.update_of_ne (Ne.symm hCT)] using s2
    have s3 := WExec.bwd (cap := cap) i σ2
    have s4 := WExec.bwd (cap := cap) i (σ2.seth i (σ2.sh i - 1))
    obtain ⟨σ4, hσ4⟩ : ∃ τ : WState ns nr, τ = σ2.seth i (σ2.sh i - 2) := ⟨_, rfl⟩
    have s4' : WExec cap (.bwd i) (σ2.seth i (σ2.sh i - 1)) σ4 1 := by
      rw [hσ4]; simp only [WState.seth_sh, Function.update_self, wseth_seth] at s4
      rw [show σ2.sh i - 1 - 1 = σ2.sh i - 2 by omega] at s4; exact s4
    have hP4 : σ4.val PC = σ.val PC := by
      rw [hσ4, hσ2]; simp [Function.update_of_ne hCP.symm, Function.update_of_ne hTP.symm]
    have s5 := WExec.dec (cap := cap) PC σ4 (by omega)
    have s6 := WExec.dec (cap := cap) PC (σ4.setv PC (σ4.val PC - 1)) (by simp; omega)
    obtain ⟨σ6, hσ6⟩ : ∃ τ : WState ns nr, τ = σ4.setv PC (σ4.val PC - 2) := ⟨_, rfl⟩
    have s6' : WExec cap (.dec PC) (σ4.setv PC (σ4.val PC - 1)) σ6 1 := by
      rw [hσ6]; simp only [WState.setv_val, Function.update_self, wsetv_setv] at s6
      rw [show σ4.val PC - 1 - 1 = σ4.val PC - 2 by omega] at s6; exact s6
    have ih := retLoop_spec i C T PC hCT hCP hTP n σ6
      (by rw [hσ6, hσ4, hσ2]; simp [Function.update_of_ne hCP, Function.update_of_ne hCT, hn])
      (by rw [hσ6, hσ4, hσ2]; simp [Function.update_of_ne hTP]; omega)
      (by rw [hσ6, hσ4, hσ2]; simp [Function.update_of_ne hCP.symm, Function.update_of_ne hTP.symm]; omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq s1 (WExec.seq s2' (WExec.seq s3 (WExec.seq s4'
      (WExec.seq s5 s6'))))) ih) ?_ (by omega)
    rw [hσ6, hσ4, hσ2]
    wgen_eq [Function.update_of_ne hCT, Function.update_of_ne hCP, Function.update_of_ne hTP,
      Function.update_of_ne hCT.symm, Function.update_of_ne hCP.symm, Function.update_of_ne hTP.symm]

theorem retC_spec (i : Fin (ns + 1)) (C T PC : Fin nr) (hCT : C ≠ T) (hCP : C ≠ PC) (hTP : T ≠ PC)
    (n : ℕ) (σ : WState ns nr) (hn : σ.val C = n) (hT : σ.val T = 0) (hnc : n ≤ cap) (hP : σ.val PC ≤ cap) :
    WExec cap (retC i C T PC) σ ((σ.seth i (σ.sh i - 2 * n)).setv PC (σ.val PC - 2 * n)) (22 * n + 3) := by
  have h1 := retLoop_spec cap i C T PC hCT hCP hTP n σ hn (by omega) hP
  obtain ⟨σ1, hσ1⟩ : ∃ τ : WState ns nr,
      τ = (((σ.setv C 0).setv T (σ.val T + n)).seth i (σ.sh i - 2 * n)).setv PC (σ.val PC - 2 * n) := ⟨_, rfl⟩
  rw [← hσ1] at h1
  have h2 := wmove_spec cap T C hCT.symm n σ1 (by rw [hσ1]; simp [Function.update_of_ne hTP, hT])
    (by rw [hσ1]; simp [Function.update_of_ne hTP, hT]; omega)
    (by rw [hσ1]; simp [Function.update_of_ne hTP, Function.update_of_ne hCP, Function.update_of_ne hCT, hT]; omega)
  refine WExec.cast cap (WExec.seq h1 h2) ?_ (by omega)
  rw [hσ1]
  wgen_eq [Function.update_of_ne hCT, Function.update_of_ne hCP, Function.update_of_ne hTP,
    Function.update_of_ne hCT.symm, Function.update_of_ne hCP.symm, Function.update_of_ne hTP.symm, hT, hn]

/-! ## Appending to an output word -/

/-- Append bit `b` to the word on `O` (head at its end), counting in `OP`. -/
def emitC (O : Fin (ns + 1)) (OP : Fin nr) (b : Bool) : WM ns nr := .seq (.wr O b) (WM.fwdC O OP)

theorem writeTapeBit_end' (l : List Bool) (b : Bool) : writeTapeBit l l.length b = l ++ [b] := by
  induction l with
  | nil => rfl
  | cons a l ih => simpa [writeTapeBit] using ih

theorem emitC_spec (O : Fin (ns + 1)) (OP : Fin nr) (b : Bool) (σ : WState ns nr) (hO : σ.sh O = (σ.st O).length)
    (hc : σ.val OP < cap) :
    WExec cap (emitC O OP b) σ (((σ.sets O ((σ.st O) ++ [b])).seth O (σ.sh O + 1)).setv OP (σ.val OP + 1)) 7 := by
  have h1 := WExec.wr (cap := cap) O b σ
  rw [hO, writeTapeBit_end'] at h1
  have h2 := wfwdC_spec cap O OP (σ.sets O ((σ.st O) ++ [b])) (by simpa using hc)
  exact WExec.mono (WExec.seq h1 (by simpa [hO] using h2)) (by omega)

/-! ## New passes -/

/-- Write the word of `1` (low bit first) from the carry-in `true`. -/
def oneOut (_ _ c : Bool) : Bool := c
def oneNxt (_ _ _ : Bool) : Bool := false

theorem mapS_zero_state : ∀ (as bs : List Bool), as.length = bs.length →
    mapS oneOut oneNxt as bs false = (List.replicate as.length false, false)
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [mapS, oneOut, oneNxt, mapS_zero_state as bs (by simpa using h), List.length_cons, List.replicate_succ]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem binary_zero' : ∀ n : ℕ, binary n 0 = List.replicate n false
  | 0 => rfl
  | n + 1 => by simp [binary, binary_zero' n, List.replicate_succ]

theorem mapS_one (as bs : List Bool) (h : as.length = bs.length) (h1 : 1 ≤ as.length) :
    (mapS oneOut oneNxt as bs true).1 = binary as.length 1 := by
  obtain ⟨a, as', rfl⟩ : ∃ a as', as = a :: as' := by
    cases as with
    | nil => simp at h1
    | cons a as' => exact ⟨a, as', rfl⟩
  obtain ⟨b, bs', rfl⟩ : ∃ b bs', bs = b :: bs' := by
    cases bs with
    | nil => simp at h
    | cons b bs' => exact ⟨b, bs', rfl⟩
  simp only [mapS, oneOut, oneNxt, mapS_zero_state as' bs' (by simpa using h), List.length_cons]
  show true :: List.replicate as'.length false = (1 % 2 == 1) :: binary as'.length (1 / 2)
  rw [binary_zero']; rfl

/-- Keep the word; the state accumulates the parity `⊕ a_i b_i`. -/
def keepA (a _ _ : Bool) : Bool := a
def parNxt (a b c : Bool) : Bool := xor c (a && b)

/-- The parity of two words (up to the shorter length). -/
def parW : List Bool → List Bool → Bool
  | a :: as, b :: bs => xor (a && b) (parW as bs)
  | _, _ => false

theorem mapS_par : ∀ (as bs : List Bool) (c : Bool), as.length = bs.length →
    mapS keepA parNxt as bs c = (as, xor c (parW as bs))
  | [], [], c, _ => by simp [mapS, parW]
  | a :: as, b :: bs, c, h => by
    simp only [mapS, keepA, parNxt, mapS_par as bs _ (by simpa using h), parW, Bool.xor_assoc]
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

/-! ## Reversal -/

/-- One step of the reversal: read the next bit of `B` (forward), write it at `A` (then back to the previous bit). -/
def revStep (A B : Fin (ns + 1)) (C PC : Fin nr) : WM ns nr :=
  .seq (.fwd B) (.seq (.inc PC) (.seq (.fwd A) (.seq (.ifs B (.wr A true) (.wr A false)) (.seq (.fwd B)
    (.seq (.inc PC) (.seq (.bwd A) (.seq (.bwd A) (.seq (.bwd A) (.dec C)))))))))

/-- Copy `C` bits of `B` into `A` in reverse order. -/
def revLoop (A B : Fin (ns + 1)) (C PC : Fin nr) : WM ns nr := .whr C (revStep A B C PC)

theorem frameP_set : ∀ (ws : List Bool) (p : ℕ) (b : Bool) (rest : List Bool), p < ws.length →
    writeTapeBit (frameP ws ++ rest) (2 * p + 1) b = frameP (ws.set p b) ++ rest
  | [], _, _, _, h => absurd h (Nat.not_lt_zero _)
  | w :: ws, 0, b, rest, _ => by simp [frameP, writeTapeBit]
  | w :: ws, p + 1, b, rest, h => by
    have ih := frameP_set ws p b rest (by simpa using h)
    simp only [frameP_cons, List.set_cons_succ, List.cons_append]
    rw [show 2 * (p + 1) + 1 = (2 * p + 1) + 1 + 1 by omega]
    simp only [writeTapeBit]
    rw [ih]

theorem readTapeBit_frameP (ws rest : List Bool) (p : ℕ) (hp : p < ws.length) :
    readTapeBit (frameP ws ++ rest) (2 * p + 1) = ws.getD p false := by
  induction ws generalizing p with
  | nil => simp at hp
  | cons w ws ih =>
    cases p with
    | zero => simp [frameP, readTapeBit]
    | succ p =>
      have := ih p (by simpa using hp)
      simp only [frameP_cons, List.cons_append, List.getD_cons_succ]
      unfold readTapeBit at this ⊢
      rw [show 2 * (p + 1) + 1 = (2 * p + 1) + 1 + 1 by omega]
      simpa using this

theorem readTapeBit_frameP_marker (ws rest : List Bool) (p : ℕ) (hp : p < ws.length) :
    readTapeBit (frameP ws ++ rest) (2 * p) = true := by
  induction ws generalizing p with
  | nil => simp at hp
  | cons w ws ih =>
    cases p with
    | zero => simp [frameP, readTapeBit]
    | succ p =>
      have := ih p (by simpa using hp)
      simp only [frameP_cons, List.cons_append]
      unfold readTapeBit at this ⊢
      rw [show 2 * (p + 1) = 2 * p + 1 + 1 by omega]
      simpa using this

theorem drop_set_self : ∀ (ws : List Bool) (p : ℕ) (b : Bool), p < ws.length → (ws.set p b).drop p = b :: ws.drop (p + 1)
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | w :: ws, 0, b, _ => rfl
  | w :: ws, p + 1, b, h => by
    simp only [List.set_cons_succ, List.drop_succ_cons]
    exact drop_set_self ws p b (by simpa using h)

theorem length_set' (ws : List Bool) (p : ℕ) (b : Bool) : (ws.set p b).length = ws.length := List.length_set

/-- **The reversal**: `n` bits of `B` (from its head, read forward) land in bits `n−1, …, 0` of `A`. -/
theorem revLoop_spec (A B : Fin (ns + 1)) (C PC : Fin nr) (hAB : A ≠ B) (hCP : C ≠ PC) :
    ∀ (n : ℕ) (ws bs preB restA restB : List Bool) (σ : WState ns nr),
      σ.val C = n → n ≤ ws.length → n ≤ bs.length →
      σ.st A = frameP ws ++ restA → σ.sh A = 2 * (n - 1) →
      σ.st B = preB ++ frameP bs ++ restB → σ.sh B = preB.length →
      σ.val PC + 2 * n ≤ cap → n ≤ cap →
      ∃ τ, WExec cap (revLoop A B C PC) σ τ (26 * n + 1) ∧
        τ.st A = frameP ((bs.take n).reverse ++ ws.drop n) ++ restA ∧ τ.sh A = 0 ∧
        τ.st B = σ.st B ∧ τ.sh B = preB.length + 2 * n ∧ τ.val PC = σ.val PC + 2 * n ∧ τ.val C = 0 ∧
        WFrame (fun i => i = A ∨ i = B) (fun r => r = C ∨ r = PC) σ τ
  | 0, ws, bs, preB, restA, restB, σ, hC, _, _, hA, hhA, _, hhB, _, _ => by
    refine ⟨σ, WExec.whrF hC, by simpa using hA, by simpa using hhA, rfl, by simp [hhB], by simp, hC,
      WFrame.refl _ _ σ⟩
  | n + 1, ws, bs, preB, restA, restB, σ, hC, hw, hb, hA, hhA, hB, hhB, hP, hn => by
    obtain ⟨b0, bs', rfl⟩ : ∃ b0 bs', bs = b0 :: bs' := by
      cases bs with
      | nil => simp at hb
      | cons b0 bs' => exact ⟨b0, bs', rfl⟩
    simp only [List.length_cons] at hb
    have hAB' := Ne.symm hAB
    have hCP' := Ne.symm hCP
    -- forward on B, count
    have s1 := WExec.fwd (cap := cap) B σ
    have s2 := WExec.inc (cap := cap) PC (σ.seth B (σ.sh B + 1)) (by simp; omega)
    obtain ⟨σ2, hσ2⟩ : ∃ τ : WState ns nr, τ = (σ.seth B (preB.length + 1)).setv PC (σ.val PC + 1) := ⟨_, rfl⟩
    have s2' : WExec cap (.inc PC) (σ.seth B (σ.sh B + 1)) σ2 3 := by rw [hσ2, ← hhB]; simpa using s2
    -- forward on A
    have s3 := WExec.fwd (cap := cap) A σ2
    obtain ⟨σ3, hσ3⟩ : ∃ τ : WState ns nr, τ = σ2.seth A (2 * n + 1) := ⟨_, rfl⟩
    have s3' : WExec cap (.fwd A) σ2 σ3 1 := by
      rw [hσ3]
      have e : σ2.sh A = 2 * n := by rw [hσ2]; simp [Function.update_of_ne hAB, hhA]
      rw [← e]; exact s3
    -- copy the bit
    have hread : wbit σ3 B = b0 := by
      unfold wbit
      have e1 : σ3.st B = (preB ++ [true]) ++ b0 :: (frameP bs' ++ restB) := by
        rw [hσ3, hσ2]; simp [hB]
      have e2 : σ3.sh B = (preB ++ [true]).length := by
        rw [hσ3, hσ2]; simp [Function.update_of_ne hAB']
      rw [e1, e2, readTapeBit_mid]
    have hA3 : σ3.st A = frameP ws ++ restA := by rw [hσ3, hσ2]; simp [hA]
    have hhA3 : σ3.sh A = 2 * n + 1 := by rw [hσ3]; simp
    obtain ⟨σ4, hσ4⟩ : ∃ τ : WState ns nr, τ = σ3.sets A (frameP (ws.set n b0) ++ restA) := ⟨_, rfl⟩
    have s4 : WExec cap (.ifs B (.wr A true) (.wr A false)) σ3 σ4 2 := by
      have hw' := WExec.wr (cap := cap) A b0 σ3
      rw [hA3, hhA3, frameP_set ws n b0 restA (by omega), ← hσ4] at hw'
      cases b0
      · exact WExec.ifsF hread hw'
      · exact WExec.ifsT hread hw'
    -- forward on B, count
    have s5 := WExec.fwd (cap := cap) B σ4
    have s6 := WExec.inc (cap := cap) PC (σ4.seth B (σ4.sh B + 1)) (by rw [hσ4, hσ3, hσ2]; simp; omega)
    obtain ⟨σ6, hσ6⟩ : ∃ τ : WState ns nr, τ = (σ4.seth B (preB.length + 2)).setv PC (σ.val PC + 2) := ⟨_, rfl⟩
    have s6' : WExec cap (.inc PC) (σ4.seth B (σ4.sh B + 1)) σ6 3 := by
      have e1 : σ4.sh B = preB.length + 1 := by rw [hσ4, hσ3, hσ2]; simp [Function.update_of_ne hAB']
      have e2 : σ4.val PC = σ.val PC + 1 := by rw [hσ4, hσ3, hσ2]; simp
      rw [hσ6]; simpa [e1, e2] using s6
    -- back on A three times, count down
    have s7 := WExec.bwd (cap := cap) A σ6
    have s8 := WExec.bwd (cap := cap) A (σ6.seth A (σ6.sh A - 1))
    have s9 := WExec.bwd (cap := cap) A ((σ6.seth A (σ6.sh A - 1)).seth A ((σ6.seth A (σ6.sh A - 1)).sh A - 1))
    obtain ⟨σ9, hσ9⟩ : ∃ τ : WState ns nr, τ = σ6.seth A (2 * (n - 1)) := ⟨_, rfl⟩
    have hA6 : σ6.sh A = 2 * n + 1 := by rw [hσ6, hσ4, hσ3]; simp [Function.update_of_ne hAB]
    have s9' : WExec cap (.bwd A) ((σ6.seth A (σ6.sh A - 1)).seth A ((σ6.seth A (σ6.sh A - 1)).sh A - 1)) σ9 1 := by
      rw [hσ9]; simp only [WState.seth_sh, Function.update_self, wseth_seth, hA6] at s9 ⊢
      rw [show 2 * n + 1 - 1 - 1 - 1 = 2 * (n - 1) by omega] at s9; exact s9
    have s10 := WExec.dec (cap := cap) C σ9 (by rw [hσ9, hσ6, hσ4, hσ3, hσ2]; simp [Function.update_of_ne hCP]; omega)
    obtain ⟨σ10, hσ10⟩ : ∃ τ : WState ns nr, τ = σ9.setv C n := ⟨_, rfl⟩
    have s10' : WExec cap (.dec C) σ9 σ10 1 := by
      have e : σ9.val C = n + 1 := by rw [hσ9, hσ6, hσ4, hσ3, hσ2]; simp [Function.update_of_ne hCP, hC]
      rw [hσ10]; simpa [e] using s10
    -- the rest of the reversal
    have hn' : n ≤ ws.length := by omega
    obtain ⟨τ, hτ, h1, h2, h3, h4, h5, h6, hf⟩ := revLoop_spec A B C PC hAB hCP n (ws.set n b0) bs' (preB ++ [true, b0])
      restA restB σ10 (by rw [hσ10]; simp) (by rw [length_set']; omega) (by omega)
      (by rw [hσ10, hσ9, hσ6, hσ4]; simp)
      (by rw [hσ10, hσ9]; simp)
      (by rw [hσ10, hσ9, hσ6, hσ4, hσ3, hσ2]; simp [Function.update_of_ne hAB', hB])
      (by rw [hσ10, hσ9, hσ6]; simp [Function.update_of_ne hAB'])
      (by rw [hσ10, hσ9, hσ6]; simp [Function.update_of_ne hCP']; omega) (by omega)
    refine ⟨τ, ?_, ?_, h2, ?_, ?_, ?_, h6, ?_⟩
    · exact WExec.mono (WExec.whrT (by omega) (WExec.seq s1 (WExec.seq s2' (WExec.seq s3' (WExec.seq s4
        (WExec.seq s5 (WExec.seq s6' (WExec.seq s7 (WExec.seq s8 (WExec.seq s9' s10'))))))))) hτ) (by omega)
    · rw [h1, List.take_succ_cons, List.reverse_cons, List.append_assoc, drop_set_self ws n b0 (by omega)]
      rfl
    · rw [h3, hσ10, hσ9, hσ6, hσ4, hσ3, hσ2]; simp [Function.update_of_ne hAB']
    · rw [h4]; simp; omega
    · rw [h5, hσ10, hσ9, hσ6]; simp [Function.update_of_ne hCP']; omega
    · have f10 : WFrame (fun i => i = A ∨ i = B) (fun r => r = C ∨ r = PC) σ σ10 := by
        refine ⟨fun i hi => ?_, fun r hr => ?_, ?_⟩
        · have hiA : i ≠ A := fun h => hi (Or.inl h)
          have hiB : i ≠ B := fun h => hi (Or.inr h)
          rw [hσ10, hσ9, hσ6, hσ4, hσ3, hσ2]
          simp [Function.update_of_ne hiA, Function.update_of_ne hiB]
        · have hrC : r ≠ C := fun h => hr (Or.inl h)
          have hrP : r ≠ PC := fun h => hr (Or.inr h)
          rw [hσ10, hσ9, hσ6, hσ4, hσ3, hσ2]
          simp [Function.update_of_ne hrC, Function.update_of_ne hrP]
        · rw [hσ10, hσ9, hσ6, hσ4, hσ3, hσ2]; rfl
      exact f10.trans hf

end NearCubicWires.WireExponent3_5.FinalPass.Tm
