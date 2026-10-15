import Proof.Wire_3_5.FinalPassWordMul
import Proof.Wire_3_5.FinalPassHash

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Hash4
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.WireExponent3_5.GF2 NearCubicWires.WireExponent3_5.FinalPass.Tm

scoped notation "sO" => (0 : Fin 8)
scoped notation "sWIN" => (1 : Fin 8)
scoped notation "sSEED" => (2 : Fin 8)
scoped notation "sP" => (3 : Fin 8)
scoped notation "sX" => (4 : Fin 8)
scoped notation "sACC" => (5 : Fin 8)
scoped notation "sNEW" => (6 : Fin 8)
scoped notation "sST" => (7 : Fin 8)

scoped notation "rMR" => (0 : Fin 16)
scoped notation "rJC" => (1 : Fin 16)
scoped notation "rIC" => (2 : Fin 16)
scoped notation "rLC" => (3 : Fin 16)
scoped notation "rF" => (4 : Fin 16)
scoped notation "rG" => (5 : Fin 16)
scoped notation "rR" => (6 : Fin 16)
scoped notation "rRY" => (7 : Fin 16)
scoped notation "rSC" => (8 : Fin 16)
scoped notation "rT1" => (9 : Fin 16)
scoped notation "rT2" => (10 : Fin 16)
scoped notation "rBAD" => (11 : Fin 16)
scoped notation "rOC" => (12 : Fin 16)
scoped notation "rWC" => (13 : Fin 16)
scoped notation "rTC" => (14 : Fin 16)
scoped notation "rK" => (15 : Fin 16)

abbrev HState := WState 7 16
abbrev HProg := WM 7 16

/-! ## Horner's rule as a fold over the coefficient records -/

/-- One Horner step: `c ⊕ x·acc`. -/
def hornerStep (p ℓ x : ℕ) (acc c : ℕ) : ℕ := c ^^^ fmulShift p ℓ x acc

/-- The coefficients from the highest to the lowest. -/
def coefsRev {n : ℕ} (f : Fin n → ℕ) : List ℕ := (List.ofFn f).reverse

theorem hornerBits_fold (p ℓ x : ℕ) : ∀ (n : ℕ) (f : Fin n → ℕ),
    (coefsRev f).foldl (hornerStep p ℓ x) 0 = hornerBits p ℓ x n f
  | 0, _ => by simp [coefsRev, hornerBits]
  | n + 1, f => by
    unfold coefsRev
    rw [List.ofFn_succ, List.reverse_cons, List.foldl_append]
    have ih := hornerBits_fold p ℓ x n (fun r => f r.succ)
    unfold coefsRev at ih
    rw [ih]
    simp [hornerStep, hornerBits]

/-- The seed stream: one record `true, frame (binary ℓ c)` per coefficient, then `false`. -/
def seedWord (ℓ : ℕ) (cs : List ℕ) : List Bool := cs.flatMap (fun c => true :: frame (binary ℓ c)) ++ [false]

/-! ## Skipping a framed word -/

theorem readDrop (l : List Bool) (p k : ℕ) : readTapeBit l (p + k) = readTapeBit (l.drop p) k := by
  unfold readTapeBit
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem dropSucc {l t : List Bool} {p : ℕ} {a : Bool} (h : l.drop p = a :: t) : l.drop (p + 1) = t := by
  have := congrArg List.tail h
  simpa [List.tail_drop] using this

theorem dropAppend {l a t : List Bool} {p : ℕ} (h : l.drop p = a ++ t) : l.drop (p + a.length) = t := by
  rw [← List.drop_drop, h, List.drop_left]

section Skip
variable {ns nr : ℕ} (cap : ℕ)

/-- Skip the framed word under the head of `S`, counting the moves in `C`. -/
def skipWord (S : Fin (ns + 1)) (C : Fin nr) : WM ns nr := .seq (.whs S (.seq (WM.fwdC S C) (WM.fwdC S C))) (WM.fwdC S C)

theorem skipLoop_spec (S : Fin (ns + 1)) (C : Fin nr) (rest : List Bool) :
    ∀ (w : List Bool) (σ : WState ns nr), (σ.st S).drop (σ.sh S) = frame w ++ rest →
      σ.val C + 2 * w.length ≤ cap →
      WExec cap (.whs S (.seq (WM.fwdC S C) (WM.fwdC S C))) σ
        ((σ.seth S (σ.sh S + 2 * w.length)).setv C (σ.val C + 2 * w.length)) (w.length * 13 + 1)
  | [], σ, hd, _ => by
    have e : (σ.seth S (σ.sh S + 2 * ([] : List Bool).length)).setv C (σ.val C + 2 * ([] : List Bool).length) = σ := by
      simp only [List.length_nil, Nat.mul_zero, Nat.add_zero]
      rw [wseth_same, wsetv_same]
    rw [e]
    refine WExec.whsF ?_
    unfold wbit
    have := readDrop (σ.st S) (σ.sh S) 0
    simp only [Nat.add_zero] at this
    rw [this, hd]; rfl
  | b :: w, σ, hd, hc => by
    simp only [List.length_cons] at hc ⊢
    have hread : wbit σ S = true := by
      unfold wbit
      have := readDrop (σ.st S) (σ.sh S) 0
      simp only [Nat.add_zero] at this
      rw [this, hd]; rfl
    have h1 := wfwdC_spec cap S C σ (by omega)
    have h2 := wfwdC_spec cap S C ((σ.seth S (σ.sh S + 1)).setv C (σ.val C + 1)) (by simp; omega)
    obtain ⟨τ, hτ⟩ : ∃ τ : WState ns nr, τ = ((((σ.seth S (σ.sh S + 1)).setv C (σ.val C + 1)).seth S
        (((σ.seth S (σ.sh S + 1)).setv C (σ.val C + 1)).sh S + 1)).setv C
        (((σ.seth S (σ.sh S + 1)).setv C (σ.val C + 1)).val C + 1)) := ⟨_, rfl⟩
    rw [← hτ] at h2
    have hτs : τ.sh S = σ.sh S + 2 := by rw [hτ]; simp
    have hτc : τ.val C = σ.val C + 2 := by rw [hτ]; simp
    have hτst : τ.st S = σ.st S := by rw [hτ]; rfl
    have hd' : (τ.st S).drop (τ.sh S) = frame w ++ rest := by
      rw [hτst, hτs]
      have e : σ.sh S + 2 = σ.sh S + 1 + 1 := by omega
      rw [e]
      exact dropSucc (dropSucc (by rw [hd]; rfl))
    have ih := skipLoop_spec S C rest w τ hd' (by omega)
    refine WExec.cast cap (WExec.whsT hread (WExec.seq h1 h2) ih) ?_ (by omega)
    refine WState.eq ?_ ?_ ?_ ?_
    · funext j; by_cases hj : j = S
      · subst hj; simp [hτs]; omega
      · simp [hj, hτ]
    · rw [hτ]; rfl
    · funext r; by_cases hr : r = C
      · subst hr; simp [hτc]; omega
      · simp [hr, hτ]
    · rw [hτ]; rfl

theorem skipWord_spec (S : Fin (ns + 1)) (C : Fin nr) (rest w : List Bool) (σ : WState ns nr)
    (hd : (σ.st S).drop (σ.sh S) = frame w ++ rest) (hc : σ.val C + 2 * w.length + 1 ≤ cap) :
    WExec cap (skipWord S C) σ ((σ.seth S (σ.sh S + 2 * w.length + 1)).setv C (σ.val C + 2 * w.length + 1))
      (w.length * 13 + 7) := by
  have h1 := skipLoop_spec cap S C rest w σ hd (by omega)
  have h2 := wfwdC_spec cap S C ((σ.seth S (σ.sh S + 2 * w.length)).setv C (σ.val C + 2 * w.length)) (by simp; omega)
  refine WExec.cast cap (WExec.seq h1 h2) ?_ (by omega)
  refine WState.eq ?_ rfl ?_ rfl
  · funext j; by_cases hj : j = S
    · subst hj; simp
    · simp [hj]
  · funext r; by_cases hr : r = C
    · subst hr; simp
    · simp [hr]

end Skip

/-! ## One coefficient record -/

variable (cap : ℕ)

/-- One coefficient record: `ACC := c ⊕ x·ACC`, then the seed head moves to the next record. -/
def hornerRec : HProg :=
  .seq (WM.fwdC sSEED rSC) (.seq (mapPass zeroOut keepS sNEW sP rF rR) (.seq (mapPass copyOut keepS sST sX rF rR)
    (.seq (fmulW sACC sNEW sST sP rF rG rR rRY) (.seq (mapPass xorOut keepS sNEW sSEED rF rR)
    (.seq (mapPass copyOut keepS sACC sNEW rF rR) (skipWord sSEED rSC))))))

/-- One coefficient record of the seed stream. -/
def coefRec (ℓ c : ℕ) : List Bool := true :: frame (binary ℓ c)

/-- The invariant of the Horner loop before the records `rest`, with the accumulator `acc`. -/
def HInv (p ℓ x : ℕ) (all rest : List ℕ) (acc : ℕ) (σ : HState) : Prop :=
  σ.st sSEED = seedWord ℓ all ∧ (σ.st sSEED).drop (σ.sh sSEED) = rest.flatMap (coefRec ℓ) ++ [false] ∧
  σ.val rSC = σ.sh sSEED ∧
  σ.st sACC = frame (binary ℓ acc) ∧ σ.sh sACC = 0 ∧
  (∃ v, σ.st sNEW = frame (binary ℓ v)) ∧ σ.sh sNEW = 0 ∧ (∃ v, σ.st sST = frame (binary ℓ v)) ∧ σ.sh sST = 0 ∧
  σ.st sX = frame (binary ℓ x) ∧ σ.sh sX = 0 ∧ σ.st sP = frame (binary ℓ p) ∧ σ.sh sP = 0 ∧
  σ.val rF = 0 ∧ σ.val rG = 0 ∧ σ.val rR = 0 ∧ σ.val rRY = 0

/-- The streams and registers of Horner's rule. -/
def hornS (i : Fin 8) : Prop := i = sSEED ∨ i = sACC ∨ i = sNEW ∨ i = sST
def hornR (r : Fin 16) : Prop := r = rSC ∨ r = rF ∨ r = rG ∨ r = rR ∨ r = rRY

theorem mulLayout4 : MulLayout sACC sNEW sST sP rF rG rR rRY := by
  constructor <;> decide

/-- The cost of one record. -/
def recCost (ℓ : ℕ) : ℕ := ℓ * (mulStepCost ℓ + 2) + 14 * ℓ + 4 * (ℓ * 41 + 3) + ℓ * 13 + 40

theorem hornerRec_spec (p ℓ x c : ℕ) (all rest : List ℕ) (acc : ℕ) (σ : HState) (hℓ : 1 ≤ ℓ)
    (hcap : σ.val rSC + 2 * ℓ + 2 ≤ cap) (hcap2 : 2 * ℓ + 2 ≤ cap) (hI : HInv p ℓ x all (c :: rest) acc σ) :
    ∃ τ, WExec cap hornerRec σ τ (recCost ℓ) ∧ HInv p ℓ x all rest (hornerStep p ℓ x acc c) τ ∧ WFrame hornS hornR σ τ := by
  obtain ⟨hSD, hdrop, hSC, hA, hhA, ⟨vN, hN⟩, hhN, ⟨vS, hS⟩, hhS, hX, hhX, hP, hhP, hF, hG, hR, hRY⟩ := hI
  have hdrop' : (σ.st sSEED).drop (σ.sh sSEED) = true :: (frame (binary ℓ c) ++ (rest.flatMap (coefRec ℓ) ++ [false])) := by
    rw [hdrop]; simp [coefRec]
  -- 1: the record marker
  have s1 := wfwdC_spec cap sSEED rSC σ (by omega)
  obtain ⟨σ1, hσ1⟩ : ∃ τ : HState, τ = (σ.seth sSEED (σ.sh sSEED + 1)).setv rSC (σ.val rSC + 1) := ⟨_, rfl⟩
  rw [← hσ1] at s1
  have hd1 : (σ1.st sSEED).drop (σ1.sh sSEED) = frame (binary ℓ c) ++ (rest.flatMap (coefRec ℓ) ++ [false]) := by
    rw [hσ1]; simpa using dropSucc hdrop'
  -- 2: `NEW := 0`
  have s2 := mapPass_spec cap zeroOut keepS sNEW sP rF rR (by decide) (by decide) (by omega) (binary ℓ vN)
    (binary ℓ p) [] [false] false σ1 (by simp) (by rw [hσ1]; simp [hN, frame_eq_frameP])
    (by rw [hσ1]; simp [hhN]) (by rw [hσ1]; simp [hP, frame_eq_frameP]) (by rw [hσ1]; simp [hhP])
    (by rw [hσ1]; simp [hF]) (by rw [hσ1]; simp [hR]) (by simp; omega)
  rw [mapS_zero _ _ _ (by simp)] at s2
  obtain ⟨σ2, hσ2⟩ : ∃ τ : HState,
      τ = (σ1.sets sNEW (frameP (List.replicate (binary ℓ vN).length false) ++ false :: [])).setv rF (false).toNat :=
    ⟨_, rfl⟩
  rw [← hσ2] at s2
  -- 3: `ST := x`
  have s3 := mapPass_spec cap copyOut keepS sST sX rF rR (by decide) (by decide) (by omega) (binary ℓ vS) (binary ℓ x)
    [] [false] false σ2 (by simp) (by rw [hσ2, hσ1]; simp [hS, frame_eq_frameP])
    (by rw [hσ2, hσ1]; simp [hhS]) (by rw [hσ2, hσ1]; simp [hX, frame_eq_frameP]) (by rw [hσ2, hσ1]; simp [hhX])
    (by rw [hσ2]; simp) (by rw [hσ2, hσ1]; simp [hR]) (by simp; omega)
  rw [mapS_copy _ _ _ (by simp)] at s3
  obtain ⟨σ3, hσ3⟩ : ∃ τ : HState, τ = (σ2.sets sST (frameP (binary ℓ x) ++ false :: [])).setv rF (false).toNat :=
    ⟨_, rfl⟩
  rw [← hσ3] at s3
  -- 4: `NEW := x·ACC`
  have hM3 : MulInv sACC sNEW sST sP rF rG rR rRY ℓ p acc 0 x 0 σ3 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (rw [hσ3, hσ2, hσ1]) <;>
      simp [hA, hhA, hRY, hP, hhP, hG, hR, hhN, hhS, frame_eq_frameP, binary_zero]
  obtain ⟨σ4, s4, hM4, hF4⟩ := fmulW_spec cap sACC sNEW sST sP rF rG rR rRY mulLayout4 ℓ p x acc hℓ hcap2 σ3 hM3
  obtain ⟨h4A, h4hA, h4RY, h4N, h4hN, h4S, h4hS, h4P, h4hP, h4F, h4G, h4R⟩ := hM4
  have h4SD : σ4.st sSEED = σ.st sSEED ∧ σ4.sh sSEED = σ.sh sSEED + 1 := by
    have := hF4.1 sSEED (by simp [mulS])
    rw [this.1, this.2, hσ3, hσ2, hσ1]; simp
  have h4SC : σ4.val rSC = σ.val rSC + 1 := by
    rw [hF4.2.1 rSC (by simp [mulR]), hσ3, hσ2, hσ1]; simp
  -- 5: `NEW ^= c`
  have hsplit : σ4.st sSEED = (σ4.st sSEED).take (σ4.sh sSEED) ++ frameP (binary ℓ c) ++
      (false :: (rest.flatMap (coefRec ℓ) ++ [false])) := by
    have hd4 : (σ4.st sSEED).drop (σ4.sh sSEED) = frame (binary ℓ c) ++ (rest.flatMap (coefRec ℓ) ++ [false]) := by
      rw [h4SD.1, h4SD.2]; rw [hσ1] at hd1; simpa using hd1
    conv_lhs => rw [← List.take_append_drop (σ4.sh sSEED) (σ4.st sSEED), hd4]
    simp [frame_eq_frameP]
  have hlen4 : ((σ4.st sSEED).take (σ4.sh sSEED)).length = σ4.sh sSEED := by
    rw [List.length_take]
    apply Nat.min_eq_left
    by_contra hc
    have hd4 : (σ4.st sSEED).drop (σ4.sh sSEED) = frame (binary ℓ c) ++ (rest.flatMap (coefRec ℓ) ++ [false]) := by
      rw [h4SD.1, h4SD.2]; rw [hσ1] at hd1; simpa using hd1
    rw [List.drop_eq_nil_of_le (by omega)] at hd4
    simp [frame_eq_frameP] at hd4
  have s5 := mapPassAt_spec cap xorOut keepS sNEW sSEED rF rR (by decide) (by decide) (by omega)
    (binary ℓ (fmulShift p ℓ x acc)) (binary ℓ c) [] ((σ4.st sSEED).take (σ4.sh sSEED)) []
    (false :: (rest.flatMap (coefRec ℓ) ++ [false])) false σ4 (by simp) (by simp [h4N, frame_eq_frameP])
    (by simp [h4hN]) hsplit hlen4.symm (by simp [h4F]) h4R (by simp; omega)
  rw [mapS_xor _ _ _ (by simp), ← binary_xor] at s5
  obtain ⟨σ5, hσ5⟩ : ∃ τ : HState,
      τ = (σ4.sets sNEW ([] ++ frameP (binary ℓ (fmulShift p ℓ x acc ^^^ c)) ++ false :: [])).setv rF (false).toNat :=
    ⟨_, rfl⟩
  rw [← hσ5] at s5
  -- 6: `ACC := NEW`
  have s6 := mapPass_spec cap copyOut keepS sACC sNEW rF rR (by decide) (by decide) (by omega)
    (binary ℓ acc) (binary ℓ (fmulShift p ℓ x acc ^^^ c)) [] [false] false σ5 (by simp)
    (by rw [hσ5]; simp [h4A, frame_eq_frameP]) (by rw [hσ5]; simp [h4hA]) (by rw [hσ5]; simp)
    (by rw [hσ5]; simp [h4hN]) (by rw [hσ5]; simp) (by rw [hσ5]; simp [h4R]) (by simp; omega)
  rw [mapS_copy _ _ _ (by simp)] at s6
  obtain ⟨σ6, hσ6⟩ : ∃ τ : HState,
      τ = (σ5.sets sACC (frameP (binary ℓ (fmulShift p ℓ x acc ^^^ c)) ++ false :: [])).setv rF (false).toNat :=
    ⟨_, rfl⟩
  rw [← hσ6] at s6
  -- 7: skip the coefficient word
  have hd6 : (σ6.st sSEED).drop (σ6.sh sSEED) = frame (binary ℓ c) ++ (rest.flatMap (coefRec ℓ) ++ [false]) := by
    rw [hσ6, hσ5]; simp only [WState.setv_st, WState.sets_st, WState.setv_sh, WState.sets_sh]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), h4SD.1, h4SD.2]
    rw [hσ1] at hd1; simpa using hd1
  have s7 := skipWord_spec cap sSEED rSC (rest.flatMap (coefRec ℓ) ++ [false]) (binary ℓ c) σ6 hd6
    (by rw [hσ6, hσ5]; simp [h4SC]; omega)
  refine ⟨_, WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 (WExec.seq s6 s7))))))
    (by unfold recCost; simp only [binary_length]; omega), ?_, ?_⟩
  · have fr : WFrame hornS hornR σ ((σ6.seth sSEED (σ6.sh sSEED + 2 * (binary ℓ c).length + 1)).setv rSC
        (σ6.val rSC + 2 * (binary ℓ c).length + 1)) := by
      have f1 : WFrame hornS hornR σ σ1 := by
        rw [hσ1]; exact (frame_seth _ _ σ _ _ (by simp [hornS])).trans (frame_setv _ _ _ _ _ (by simp [hornR]))
      have f2 : WFrame hornS hornR σ1 σ2 := by
        rw [hσ2]; exact (frame_sets _ _ σ1 _ _ (by simp [hornS])).trans (frame_setv _ _ _ _ _ (by simp [hornR]))
      have f3 : WFrame hornS hornR σ2 σ3 := by
        rw [hσ3]; exact (frame_sets _ _ σ2 _ _ (by simp [hornS])).trans (frame_setv _ _ _ _ _ (by simp [hornR]))
      have f4 : WFrame hornS hornR σ3 σ4 :=
        hF4.mono (fun i hi => by rcases hi with h | h | h <;> simp [hornS, h])
          (fun r hr => by rcases hr with h | h | h | h <;> simp [hornR, h])
      have f5 : WFrame hornS hornR σ4 σ5 := by
        rw [hσ5]; exact (frame_sets _ _ σ4 _ _ (by simp [hornS])).trans (frame_setv _ _ _ _ _ (by simp [hornR]))
      have f6 : WFrame hornS hornR σ5 σ6 := by
        rw [hσ6]; exact (frame_sets _ _ σ5 _ _ (by simp [hornS])).trans (frame_setv _ _ _ _ _ (by simp [hornR]))
      have f7 := (frame_seth hornS hornR σ6 sSEED (σ6.sh sSEED + 2 * (binary ℓ c).length + 1) (by simp [hornS])).trans
        (frame_setv hornS hornR _ rSC (σ6.val rSC + 2 * (binary ℓ c).length + 1) (by simp [hornR]))
      exact f1.trans (f2.trans (f3.trans (f4.trans (f5.trans (f6.trans f7)))))
    have hXτ := fr.1 sX (by simp [hornS])
    have hPτ := fr.1 sP (by simp [hornS])
    have h6SD : σ6.st sSEED = σ.st sSEED ∧ σ6.sh sSEED = σ.sh sSEED + 1 := by
      rw [hσ6, hσ5]; simp only [WState.setv_st, WState.sets_st, WState.setv_sh, WState.sets_sh]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact h4SD
    refine ⟨?_, ?_, ?_, ?_, ?_, ⟨fmulShift p ℓ x acc ^^^ c, ?_⟩, ?_, ⟨(mulFrom p ℓ acc 0 ℓ 0 x).2, ?_⟩, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_⟩
    · simp only [WState.setv_st, WState.seth_st]; rw [h6SD.1, hSD]
    · simp only [WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh, Function.update_self]
      have := dropAppend hd6
      simp only [frame_length] at this
      rw [show σ6.sh sSEED + 2 * (binary ℓ c).length + 1 = σ6.sh sSEED + (2 * (binary ℓ c).length + 1) by omega]
      exact this
    · have h6SC : σ6.val rSC = σ.val rSC + 1 := by rw [hσ6, hσ5]; simp [h4SC]
      simp only [WState.setv_val, Function.update_self, WState.setv_sh, WState.seth_sh]
      rw [h6SC, h6SD.2, hSC]
    · rw [hσ6]; simp [frame_eq_frameP, hornerStep, Nat.xor_comm]
    · rw [hσ6, hσ5]; simp [h4hA]
    · rw [hσ6, hσ5]; simp [frame_eq_frameP]
    · rw [hσ6, hσ5]; simp [h4hN]
    · rw [hσ6, hσ5]; simp [h4S]
    · rw [hσ6, hσ5]; simp [h4hS]
    · rw [hXτ.1, hX]
    · rw [hXτ.2, hhX]
    · rw [hPτ.1, hP]
    · rw [hPτ.2, hhP]
    · rw [hσ6]; simp
    · rw [hσ6, hσ5]; simp [h4G]
    · rw [hσ6, hσ5]; simp [h4R]
    · rw [hσ6, hσ5]; simp [h4RY]
  · exact (by
      have f1 : WFrame hornS hornR σ σ1 := by
        rw [hσ1]; exact (frame_seth _ _ σ _ _ (by simp [hornS])).trans (frame_setv _ _ _ _ _ (by simp [hornR]))
      have f2 : WFrame hornS hornR σ1 σ2 := by
        rw [hσ2]; exact (frame_sets _ _ σ1 _ _ (by simp [hornS])).trans (frame_setv _ _ _ _ _ (by simp [hornR]))
      have f3 : WFrame hornS hornR σ2 σ3 := by
        rw [hσ3]; exact (frame_sets _ _ σ2 _ _ (by simp [hornS])).trans (frame_setv _ _ _ _ _ (by simp [hornR]))
      have f4 : WFrame hornS hornR σ3 σ4 :=
        hF4.mono (fun i hi => by rcases hi with h | h | h <;> simp [hornS, h])
          (fun r hr => by rcases hr with h | h | h | h <;> simp [hornR, h])
      have f5 : WFrame hornS hornR σ4 σ5 := by
        rw [hσ5]; exact (frame_sets _ _ σ4 _ _ (by simp [hornS])).trans (frame_setv _ _ _ _ _ (by simp [hornR]))
      have f6 : WFrame hornS hornR σ5 σ6 := by
        rw [hσ6]; exact (frame_sets _ _ σ5 _ _ (by simp [hornS])).trans (frame_setv _ _ _ _ _ (by simp [hornR]))
      have f7 := (frame_seth hornS hornR σ6 sSEED (σ6.sh sSEED + 2 * (binary ℓ c).length + 1) (by simp [hornS])).trans
        (frame_setv hornS hornR _ rSC (σ6.val rSC + 2 * (binary ℓ c).length + 1) (by simp [hornR]))
      exact f1.trans (f2.trans (f3.trans (f4.trans (f5.trans (f6.trans f7))))))

/-! ## The whole evaluation -/

theorem seedWord_length_ge (ℓ : ℕ) (all rest : List ℕ) (σ : HState) (hSD : σ.st sSEED = seedWord ℓ all)
    (hd : (σ.st sSEED).drop (σ.sh sSEED) = rest.flatMap (coefRec ℓ) ++ [false]) :
    σ.sh sSEED + (rest.flatMap (coefRec ℓ)).length + 1 = (seedWord ℓ all).length := by
  have h := congrArg List.length hd
  rw [List.length_drop, hSD] at h
  simp only [List.length_append, List.length_singleton] at h
  have hpos : σ.sh sSEED < (seedWord ℓ all).length := by
    by_contra hc
    rw [List.drop_eq_nil_of_le (by rw [hSD]; omega)] at hd
    simp at hd
  omega

theorem coefRec_length (ℓ c : ℕ) : (coefRec ℓ c).length = 2 * ℓ + 2 := by simp [coefRec, frame_length]

theorem seedWord_length (ℓ : ℕ) : ∀ all : List ℕ, (seedWord ℓ all).length = all.length * (2 * ℓ + 2) + 1
  | [] => by simp [seedWord]
  | c :: all => by
    have ih := seedWord_length ℓ all
    unfold seedWord at ih ⊢
    simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil, frame_length,
      binary_length] at ih ⊢
    rw [add_mul]; omega

theorem hornerLoop_spec (p ℓ x : ℕ) (all : List ℕ) (hℓ : 1 ≤ ℓ) (hcap : (seedWord ℓ all).length + 2 * ℓ + 2 ≤ cap) :
    ∀ (rest : List ℕ) (acc : ℕ) (σ : HState), HInv p ℓ x all rest acc σ →
      ∃ τ, WExec cap (.whs sSEED hornerRec) σ τ (rest.length * (recCost ℓ + 2) + 1) ∧
        HInv p ℓ x all [] (rest.foldl (hornerStep p ℓ x) acc) τ ∧ WFrame hornS hornR σ τ
  | [], acc, σ, hI => by
    refine ⟨σ, WExec.mono (WExec.whsF ?_) (by simp), hI, WFrame.refl _ _ σ⟩
    unfold wbit
    have := readDrop (σ.st sSEED) (σ.sh sSEED) 0
    simp only [Nat.add_zero] at this
    rw [this, hI.2.1]; rfl
  | c :: rest, acc, σ, hI => by
    have hlen := seedWord_length_ge ℓ all (c :: rest) σ hI.1 hI.2.1
    simp only [List.flatMap_cons, List.length_append, coefRec_length] at hlen
    have hread : wbit σ sSEED = true := by
      unfold wbit
      have := readDrop (σ.st sSEED) (σ.sh sSEED) 0
      simp only [Nat.add_zero] at this
      rw [this, hI.2.1]; simp only [List.flatMap_cons, coefRec, List.cons_append]; rfl
    obtain ⟨τ1, h1, hI1, hF1⟩ := hornerRec_spec cap p ℓ x c all rest acc σ hℓ (by rw [hI.2.2.1]; omega)
      (by omega) hI
    obtain ⟨τ, h2, hI2, hF2⟩ := hornerLoop_spec p ℓ x all hℓ hcap rest _ τ1 hI1
    exact ⟨τ, WExec.mono (WExec.whsT hread h1 h2) (by simp; ring_nf; omega), by simpa using hI2, hF1.trans hF2⟩

/-- **Horner's rule on the word tapes**: `ACC := Σ_r f_r x^r` from the seed records of `f(n−1), …, f(0)`. -/
def hornerW : HProg :=
  .seq (mapPass zeroOut keepS sACC sP rF rR) (.seq (.whs sSEED hornerRec) (WM.rewind sSEED rSC))

/-- The ready state of Horner's rule: the seed at its start, the words in place, the flags clear. -/
def HReady (p ℓ x : ℕ) (all : List ℕ) (σ : HState) : Prop :=
  σ.st sSEED = seedWord ℓ all ∧ σ.sh sSEED = 0 ∧ σ.val rSC = 0 ∧
  (∃ v, σ.st sACC = frame (binary ℓ v)) ∧ σ.sh sACC = 0 ∧
  (∃ v, σ.st sNEW = frame (binary ℓ v)) ∧ σ.sh sNEW = 0 ∧ (∃ v, σ.st sST = frame (binary ℓ v)) ∧ σ.sh sST = 0 ∧
  σ.st sX = frame (binary ℓ x) ∧ σ.sh sX = 0 ∧ σ.st sP = frame (binary ℓ p) ∧ σ.sh sP = 0 ∧
  σ.val rF = 0 ∧ σ.val rG = 0 ∧ σ.val rR = 0 ∧ σ.val rRY = 0

/-- The cost of Horner's rule. -/
def hornerCost (ℓ n : ℕ) : ℕ := ℓ * 41 + 3 + 1 + (n * (recCost ℓ + 2) + 1) + 1 + (5 * (n * (2 * ℓ + 2) + 1) + 1)

theorem hornerW_spec (p ℓ x : ℕ) (all : List ℕ) (hℓ : 1 ≤ ℓ) (hcap : (seedWord ℓ all).length + 2 * ℓ + 2 ≤ cap)
    (σ : HState) (hR : HReady p ℓ x all σ) :
    ∃ τ, WExec cap hornerW σ τ (hornerCost ℓ all.length) ∧
      HReady p ℓ x all τ ∧ τ.st sACC = frame (binary ℓ (all.foldl (hornerStep p ℓ x) 0)) ∧
      WFrame hornS hornR σ τ := by
  obtain ⟨hSD, hhSD, hSC, ⟨vA, hA⟩, hhA, hN, hhN, hS, hhS, hX, hhX, hP, hhP, hF, hG, hRr, hRY⟩ := hR
  have s1 := mapPass_spec cap zeroOut keepS sACC sP rF rR (by decide) (by decide) (by omega) (binary ℓ vA)
    (binary ℓ p) [] [false] false σ (by simp) (by simp [hA, frame_eq_frameP]) hhA (by simp [hP, frame_eq_frameP])
    hhP (by simp [hF]) hRr (by simp; omega)
  rw [mapS_zero _ _ _ (by simp)] at s1
  obtain ⟨σ1, hσ1⟩ : ∃ τ : HState,
      τ = (σ.sets sACC (frameP (List.replicate (binary ℓ vA).length false) ++ false :: [])).setv rF (false).toNat :=
    ⟨_, rfl⟩
  rw [← hσ1] at s1
  have hI1 : HInv p ℓ x all all 0 σ1 := by
    rw [hσ1]
    refine ⟨?_, ?_, ?_, ?_, ?_, hN, hhN, hS, hhS, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hSD]
    · simp only [WState.setv_st, WState.sets_st, WState.setv_sh, WState.sets_sh]
      rw [Function.update_of_ne (by decide), hSD, hhSD, List.drop_zero]; rfl
    · simp [hSC, hhSD]
    · simp [frame_eq_frameP, binary_zero]
    · simp [hhA]
    · simp [hX]
    · simp [hhX]
    · simp [hP]
    · simp [hhP]
    · simp
    · simp [hG]
    · simp [hRr]
    · simp [hRY]
  obtain ⟨σ2, s2, hI2, hF2⟩ := hornerLoop_spec cap p ℓ x all hℓ hcap all 0 σ1 hI1
  obtain ⟨h2SD, h2d, h2SC, h2A, h2hA, h2N, h2hN, h2S, h2hS, h2X, h2hX, h2P, h2hP, h2F, h2G, h2R, h2RY⟩ := hI2
  have hlen := seedWord_length_ge ℓ all [] σ2 h2SD h2d
  simp only [List.flatMap_nil, List.length_nil, Nat.add_zero] at hlen
  have s3 := wrewind_spec cap sSEED rSC (σ2.sh sSEED) σ2 h2SC (by omega)
  have hlenAll : (seedWord ℓ all).length = all.length * (2 * ℓ + 2) + 1 := seedWord_length ℓ all
  refine ⟨_, WExec.mono (WExec.seq s1 (WExec.seq s2 s3)) (by unfold hornerCost; simp only [binary_length]; omega),
    ?_, ?_, ?_⟩
  · refine ⟨by simpa using h2SD, by simp, by simp, ⟨_, by simpa using h2A⟩, by simpa using h2hA, by simpa using h2N,
      by simpa using h2hN, by simpa using h2S, by simpa using h2hS, by simpa using h2X, by simpa using h2hX,
      by simpa using h2P, by simpa using h2hP, by simpa using h2F, by simpa using h2G, by simpa using h2R,
      by simpa using h2RY⟩
  · simpa using h2A
  · have f1 : WFrame hornS hornR σ σ1 := by
      rw [hσ1]; exact (frame_sets _ _ σ _ _ (by simp [hornS])).trans (frame_setv _ _ _ _ _ (by simp [hornR]))
    have f3 := frame_seth hornS hornR (σ2.setv rSC 0) sSEED (σ2.sh sSEED - σ2.sh sSEED) (by simp [hornS])
    exact f1.trans (hF2.trans ((frame_setv hornS hornR σ2 rSC 0 (by simp [hornR])).trans f3))

end NearCubicWires.WireExponent3_5.FinalPass.Hash4
