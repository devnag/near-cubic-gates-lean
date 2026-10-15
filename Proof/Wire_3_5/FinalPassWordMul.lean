import Proof.Wire_3_5.FinalPassWordMap
import Proof.Wire_3_5.GF2Machines

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.WireExponent3_5.GF2 NearCubicWires.WireExponent3_5.GF

/-! ## The bit functions of the passes -/

/-- Masked XOR `a ⊕ (c ∧ b)`; the state is kept. -/
def mxOut (a b c : Bool) : Bool := xor a (c && b)
def keepS (_ _ c : Bool) : Bool := c
/-- Shift in the carry; the next carry is the bit shifted out. -/
def shOut (_ _ c : Bool) : Bool := c
def shNxt (a _ _ : Bool) : Bool := a

theorem mapS_mx : ∀ (as bs : List Bool) (c : Bool), as.length = bs.length →
    mapS mxOut keepS as bs c = (List.zipWith (mx c) as bs, c)
  | [], [], _, _ => rfl
  | a :: as, b :: bs, c, h => by
    simp only [mapS, keepS, mapS_mx as bs c (by simpa using h), List.zipWith_cons_cons]
    rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

theorem mapS_shift : ∀ (as bs : List Bool) (c : Bool), as.length = bs.length →
    mapS shOut shNxt as bs c = (shiftIn c as, carryOut c as)
  | [], [], _, _ => rfl
  | a :: as, b :: bs, c, h => by
    simp only [mapS, shOut, shNxt, mapS_shift as bs a (by simpa using h)]
    rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

variable {ns nr : ℕ} (cap : ℕ)

/-- `τ` agrees with `σ` outside the streams `S` and the registers `Rg`. -/
def WFrame (S : Fin (ns + 1) → Prop) (Rg : Fin nr → Prop) (σ τ : WState ns nr) : Prop :=
  (∀ i, ¬ S i → τ.st i = σ.st i ∧ τ.sh i = σ.sh i) ∧ (∀ r, ¬ Rg r → τ.val r = σ.val r) ∧ τ.cell = σ.cell

theorem WFrame.refl (S : Fin (ns + 1) → Prop) (Rg : Fin nr → Prop) (σ : WState ns nr) : WFrame S Rg σ σ :=
  ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl, rfl⟩

theorem WFrame.trans {S : Fin (ns + 1) → Prop} {Rg : Fin nr → Prop} {σ τ ρ : WState ns nr} (h1 : WFrame S Rg σ τ)
    (h2 : WFrame S Rg τ ρ) : WFrame S Rg σ ρ :=
  ⟨fun i hi => ⟨((h2.1 i hi).1).trans (h1.1 i hi).1, ((h2.1 i hi).2).trans (h1.1 i hi).2⟩,
    fun r hr => (h2.2.1 r hr).trans (h1.2.1 r hr), h2.2.2.trans h1.2.2⟩

theorem WFrame.mono {S S' : Fin (ns + 1) → Prop} {Rg Rg' : Fin nr → Prop} {σ τ : WState ns nr} (h : WFrame S Rg σ τ)
    (hS : ∀ i, S i → S' i) (hR : ∀ r, Rg r → Rg' r) : WFrame S' Rg' σ τ :=
  ⟨fun i hi => h.1 i (fun h' => hi (hS i h')), fun r hr => h.2.1 r (fun h' => hr (hR r h')), h.2.2⟩

theorem frame_seth (S : Fin (ns + 1) → Prop) (Rg : Fin nr → Prop) (σ : WState ns nr) (i : Fin (ns + 1)) (x : ℕ)
    (hi : S i) : WFrame S Rg σ (σ.seth i x) :=
  ⟨fun j hj => ⟨rfl, by have : j ≠ i := fun h => hj (h ▸ hi); simp [Function.update_of_ne this]⟩,
    fun _ _ => rfl, rfl⟩

theorem frame_setv (S : Fin (ns + 1) → Prop) (Rg : Fin nr → Prop) (σ : WState ns nr) (r : Fin nr) (x : ℕ)
    (hr : Rg r) : WFrame S Rg σ (σ.setv r x) :=
  ⟨fun _ _ => ⟨rfl, rfl⟩, fun q hq => by have : q ≠ r := fun h => hq (h ▸ hr); simp [Function.update_of_ne this],
    rfl⟩

theorem frame_sets (S : Fin (ns + 1) → Prop) (Rg : Fin nr → Prop) (σ : WState ns nr) (i : Fin (ns + 1))
    (l : List Bool) (hi : S i) : WFrame S Rg σ (σ.sets i l) :=
  ⟨fun j hj => ⟨by have : j ≠ i := fun h => hj (h ▸ hi); simp [Function.update_of_ne this], rfl⟩,
    fun _ _ => rfl, rfl⟩

/-! ## The product -/

/-- The loop body of the product: one bit of the multiplier. -/
def mulStep (Y ACC ST Pm : Fin (ns + 1)) (F G R RY : Fin nr) : WM ns nr :=
  .seq (.fwd Y) (.seq (.inc RY) (.seq (.ifs Y (setFlag F true) (setFlag F false))
    (.seq (mapPass mxOut keepS ACC ST F R) (.seq (mapPass shOut shNxt ST Pm G R)
    (.seq (mapPass mxOut keepS ST Pm G R) (.seq (setFlag G false) (.seq (setFlag F false)
    (.seq (.fwd Y) (.inc RY)))))))))

/-- **The product** `ACC := fmulShift p ℓ x y` from `ACC = 0`, `ST = x`. -/
def fmulW (Y ACC ST Pm : Fin (ns + 1)) (F G R RY : Fin nr) : WM ns nr :=
  .seq (.whs Y (mulStep Y ACC ST Pm F G R RY)) (WM.rewind Y RY)

/-- The invariant of the product loop after `k` bits. -/
def MulInv (Y ACC ST Pm : Fin (ns + 1)) (F G R RY : Fin nr) (ℓ p y acc st k : ℕ) (σ : WState ns nr) : Prop :=
  σ.st Y = frame (binary ℓ y) ∧ σ.sh Y = 2 * k ∧ σ.val RY = 2 * k ∧
  σ.st ACC = frame (binary ℓ acc) ∧ σ.sh ACC = 0 ∧ σ.st ST = frame (binary ℓ st) ∧ σ.sh ST = 0 ∧
  σ.st Pm = frame (binary ℓ p) ∧ σ.sh Pm = 0 ∧ σ.val F = 0 ∧ σ.val G = 0 ∧ σ.val R = 0

/-- The streams and registers the product touches. -/
def mulS (Y ACC ST : Fin (ns + 1)) (i : Fin (ns + 1)) : Prop := i = Y ∨ i = ACC ∨ i = ST
def mulR (F G R RY : Fin nr) (r : Fin nr) : Prop := r = F ∨ r = G ∨ r = R ∨ r = RY

/-- The distinct tapes and registers of the product. -/
structure MulLayout (Y ACC ST Pm : Fin (ns + 1)) (F G R RY : Fin nr) : Prop where
  yA : Y ≠ ACC
  yS : Y ≠ ST
  yP : Y ≠ Pm
  aS : ACC ≠ ST
  aP : ACC ≠ Pm
  sP : ST ≠ Pm
  fG : F ≠ G
  fR : F ≠ R
  fY : F ≠ RY
  gR : G ≠ R
  gY : G ≠ RY
  rY : R ≠ RY

/-- Close a goal about fields of updated word states, using the layout's distinctness. -/
macro "wsimp" : tactic => `(tactic| simp [Function.update_apply, frame_eq_frameP, *])

theorem frame_binary (ℓ a : ℕ) : frame (binary ℓ a) = frameP (binary ℓ a) ++ false :: [] := by
  rw [frame_eq_frameP]

/-- The cost of one bit of the multiplier. -/
def mulStepCost (ℓ : ℕ) : ℕ := 3 * (ℓ * 41 + 3) + 40

theorem mulStep_spec (Y ACC ST Pm : Fin (ns + 1)) (F G R RY : Fin nr) (hL : MulLayout Y ACC ST Pm F G R RY)
    (ℓ p y acc st k : ℕ) (hℓ : 1 ≤ ℓ) (hk : k < ℓ) (hcap : 2 * ℓ + 2 ≤ cap) (σ : WState ns nr)
    (hI : MulInv Y ACC ST Pm F G R RY ℓ p y acc st k σ) :
    ∃ τ, WExec cap (mulStep Y ACC ST Pm F G R RY) σ τ (mulStepCost ℓ) ∧
      MulInv Y ACC ST Pm F G R RY ℓ p y (if y.testBit k then acc ^^^ st else acc) (lfsr p ℓ st) (k + 1) τ ∧
      WFrame (mulS Y ACC ST) (mulR F G R RY) σ τ := by
  obtain ⟨hY, hhY, hRY, hA, hhA, hS, hhS, hP, hhP, hF, hG, hR⟩ := hI
  obtain ⟨yA, yS, yP, aS, aP, sP, fG, fR, fY, gR, gY, rY⟩ := hL
  have yA' := Ne.symm yA; have yS' := Ne.symm yS; have yP' := Ne.symm yP; have aS' := Ne.symm aS
  have aP' := Ne.symm aP; have sP' := Ne.symm sP; have fG' := Ne.symm fG; have fR' := Ne.symm fR
  have fY' := Ne.symm fY; have gR' := Ne.symm gR; have gY' := Ne.symm gY; have rY' := Ne.symm rY
  set b := y.testBit k with hb
  -- 1, 2: forward on `Y`, count
  have s1 := WExec.fwd (cap := cap) Y σ
  have s2 := WExec.inc (cap := cap) RY (σ.seth Y (σ.sh Y + 1)) (by simp; omega)
  obtain ⟨σ2, hσ2⟩ : ∃ τ : WState ns nr, τ = (σ.seth Y (σ.sh Y + 1)).setv RY ((σ.seth Y (σ.sh Y + 1)).val RY + 1) :=
    ⟨_, rfl⟩
  rw [← hσ2] at s2
  -- 3: load the bit into `F`
  have hbit : wbit σ2 Y = b := by
    unfold wbit
    have e1 : σ2.st Y = frame (binary ℓ y) := by rw [hσ2]; simp [hY]
    have e2 : σ2.sh Y = 2 * k + 1 := by rw [hσ2]; simp [hhY]
    rw [e1, e2, read_frame_bit _ _ (by simpa using hk), binary_getElem]
  have hF2 : σ2.val F = (false).toNat := by rw [hσ2]; simp [fY, hF]
  have s3 : WExec cap (.ifs Y (setFlag F true) (setFlag F false)) σ2 (σ2.setv F b.toNat) 5 := by
    cases hbv : b
    · rw [hbv] at hbit
      exact WExec.mono (WExec.ifsF hbit (setFlag_spec cap F false false σ2 hF2 (by omega))) (by omega)
    · rw [hbv] at hbit
      exact WExec.mono (WExec.ifsT hbit (setFlag_spec cap F true false σ2 hF2 (by omega))) (by omega)
  obtain ⟨σ3, hσ3⟩ : ∃ τ : WState ns nr, τ = σ2.setv F b.toNat := ⟨_, rfl⟩
  rw [← hσ3] at s3
  -- 4: `ACC ^= F·ST`
  have s4 := mapPass_spec cap mxOut keepS ACC ST F R aS fR (by omega) (binary ℓ acc) (binary ℓ st) [] [false] b σ3
    (by simp) (by wsimp) (by wsimp) (by wsimp) (by wsimp) (by wsimp) (by wsimp) (by simp; omega)
  rw [mapS_mx _ _ _ (by simp), mx_binary] at s4
  obtain ⟨σ4, hσ4⟩ : ∃ τ : WState ns nr,
      τ = (σ3.sets ACC (frameP (binary ℓ (if b = true then acc ^^^ st else acc)) ++ false :: [])).setv F b.toNat :=
    ⟨_, rfl⟩
  rw [← hσ4] at s4
  -- 5: shift `ST`, carry into `G`
  have s5 := mapPass_spec cap shOut shNxt ST Pm G R sP gR (by omega) (binary ℓ st) (binary ℓ p) [] [false] false σ4
    (by simp) (by wsimp) (by wsimp) (by wsimp) (by wsimp) (by wsimp) (by wsimp) (by simp; omega)
  rw [mapS_shift _ _ _ (by simp)] at s5
  obtain ⟨σ5, hσ5⟩ : ∃ τ : WState ns nr,
      τ = (σ4.sets ST (frameP (shiftIn false (binary ℓ st)) ++ false :: [])).setv G
        (carryOut false (binary ℓ st)).toNat := ⟨_, rfl⟩
  rw [← hσ5] at s5
  -- 6: `ST ^= G·Pm`: the LFSR step
  have s6 := mapPass_spec cap mxOut keepS ST Pm G R sP gR (by omega) (shiftIn false (binary ℓ st)) (binary ℓ p) []
    [false] (carryOut false (binary ℓ st)) σ5 (by simp) (by wsimp) (by wsimp) (by wsimp) (by wsimp) (by wsimp)
    (by wsimp) (by simp; omega)
  rw [mapS_mx _ _ _ (by simp), ← lfsr_bits p ℓ st hℓ] at s6
  obtain ⟨σ6, hσ6⟩ : ∃ τ : WState ns nr,
      τ = (σ5.sets ST (frameP (binary ℓ (lfsr p ℓ st)) ++ false :: [])).setv G (carryOut false (binary ℓ st)).toNat :=
    ⟨_, rfl⟩
  rw [← hσ6] at s6
  -- 7, 8: clear the flags
  have s7 := setFlag_spec cap G false (carryOut false (binary ℓ st)) σ6 (by wsimp) (by omega)
  have s8 := setFlag_spec cap F false b (σ6.setv G (false).toNat) (by wsimp) (by omega)
  obtain ⟨σ8, hσ8⟩ : ∃ τ : WState ns nr, τ = (σ6.setv G (false).toNat).setv F (false).toNat := ⟨_, rfl⟩
  rw [← hσ8] at s8
  -- 9, 10: forward on `Y`, count
  have s9 := WExec.fwd (cap := cap) Y σ8
  have s10 := WExec.inc (cap := cap) RY (σ8.seth Y (σ8.sh Y + 1)) (by wsimp; omega)
  refine ⟨_, WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 (WExec.seq s6
    (WExec.seq s7 (WExec.seq s8 (WExec.seq s9 s10))))))))) (by
      unfold mulStepCost; simp only [binary_length, shiftIn_length]; omega), ?_, ?_⟩
  · subst hσ8 hσ6 hσ5 hσ4 hσ3 hσ2
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wsimp <;> omega
  · subst hσ8 hσ6 hσ5 hσ4 hσ3 hσ2
    refine ⟨fun i hi => ?_, fun r hr => ?_, rfl⟩
    · simp only [mulS, not_or] at hi
      obtain ⟨h1, h2, h3⟩ := hi
      exact ⟨by simp [Function.update_of_ne h2, Function.update_of_ne h3],
        by simp [Function.update_of_ne h1]⟩
    · simp only [mulR, not_or] at hr
      obtain ⟨h1, h2, h3, h4⟩ := hr
      simp [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h4]

/-- The product's fold over the multiplier bits `k, …, k + n − 1`. -/
def mulFrom (p ℓ y k n : ℕ) (acc st : ℕ) : ℕ × ℕ :=
  (List.range' k n).foldl (fun (s : ℕ × ℕ) j => (if y.testBit j then s.1 ^^^ s.2 else s.1, lfsr p ℓ s.2)) (acc, st)

theorem mulFrom_succ (p ℓ y k n acc st : ℕ) :
    mulFrom p ℓ y k (n + 1) acc st =
      mulFrom p ℓ y (k + 1) n (if y.testBit k then acc ^^^ st else acc) (lfsr p ℓ st) := by
  unfold mulFrom
  rw [List.range'_succ, List.foldl_cons]

theorem mulFrom_zero (p ℓ y k acc st : ℕ) : mulFrom p ℓ y k 0 acc st = (acc, st) := rfl

theorem fmulShift_eq_mulFrom (p ℓ x y : ℕ) : fmulShift p ℓ x y = (mulFrom p ℓ y 0 ℓ 0 x).1 := by
  unfold fmulShift mulFrom
  rw [List.range_eq_range']

theorem mulLoop_spec (Y ACC ST Pm : Fin (ns + 1)) (F G R RY : Fin nr) (hL : MulLayout Y ACC ST Pm F G R RY)
    (ℓ p y : ℕ) (hℓ : 1 ≤ ℓ) (hcap : 2 * ℓ + 2 ≤ cap) :
    ∀ (n k acc st : ℕ) (σ : WState ns nr), k + n = ℓ → MulInv Y ACC ST Pm F G R RY ℓ p y acc st k σ →
      ∃ τ, WExec cap (.whs Y (mulStep Y ACC ST Pm F G R RY)) σ τ (n * (mulStepCost ℓ + 2) + 1) ∧
        MulInv Y ACC ST Pm F G R RY ℓ p y (mulFrom p ℓ y k n acc st).1 (mulFrom p ℓ y k n acc st).2 ℓ τ ∧
        WFrame (mulS Y ACC ST) (mulR F G R RY) σ τ
  | 0, k, acc, st, σ, hk, hI => by
    refine ⟨σ, WExec.mono (WExec.whsF ?_) (by simp), ?_, WFrame.refl _ _ σ⟩
    · unfold wbit
      rw [hI.1, hI.2.1]
      have := read_frame_end (binary ℓ y)
      rw [binary_length] at this
      rw [show 2 * k = 2 * ℓ by omega]; exact this
    · rw [mulFrom_zero]
      have hkl : k = ℓ := by omega
      rw [hkl] at hI
      exact hI
  | n + 1, k, acc, st, σ, hk, hI => by
    have hread : wbit σ Y = true := by
      unfold wbit
      rw [hI.1, hI.2.1]
      exact read_frame_mark _ _ (by simp; omega)
    obtain ⟨τ1, h1, hI1, hF1⟩ := mulStep_spec cap Y ACC ST Pm F G R RY hL ℓ p y acc st k hℓ (by omega) hcap σ hI
    obtain ⟨τ, h2, hI2, hF2⟩ := mulLoop_spec Y ACC ST Pm F G R RY hL ℓ p y hℓ hcap n (k + 1) _ _ τ1 (by omega) hI1
    refine ⟨τ, WExec.mono (WExec.whsT hread h1 h2) (by ring_nf; omega), ?_, hF1.trans hF2⟩
    rw [mulFrom_succ]; exact hI2

theorem fmulW_spec (Y ACC ST Pm : Fin (ns + 1)) (F G R RY : Fin nr) (hL : MulLayout Y ACC ST Pm F G R RY)
    (ℓ p x y : ℕ) (hℓ : 1 ≤ ℓ) (hcap : 2 * ℓ + 2 ≤ cap) (σ : WState ns nr)
    (hI : MulInv Y ACC ST Pm F G R RY ℓ p y 0 x 0 σ) :
    ∃ τ, WExec cap (fmulW Y ACC ST Pm F G R RY) σ τ (ℓ * (mulStepCost ℓ + 2) + 14 * ℓ + 3) ∧
      MulInv Y ACC ST Pm F G R RY ℓ p y (fmulShift p ℓ x y) (mulFrom p ℓ y 0 ℓ 0 x).2 0 τ ∧
      WFrame (mulS Y ACC ST) (mulR F G R RY) σ τ := by
  obtain ⟨τ1, h1, hI1, hF1⟩ := mulLoop_spec cap Y ACC ST Pm F G R RY hL ℓ p y hℓ hcap ℓ 0 0 x σ (by omega) hI
  obtain ⟨hY, hhY, hRY, hA, hhA, hS, hhS, hP, hhP, hF, hG, hR⟩ := hI1
  have h2 := wrewind_spec cap Y RY (2 * ℓ) τ1 hRY (by omega)
  refine ⟨_, WExec.mono (WExec.seq h1 h2) (by omega), ?_, ?_⟩
  · have yA := hL.yA; have yS := hL.yS; have yP := hL.yP; have fY := hL.fY; have gY := hL.gY; have rY := hL.rY
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hY]
    · simp [hhY]
    · simp
    · simp [fmulShift_eq_mulFrom, hA]
    · simp [Function.update_of_ne (Ne.symm yA), hhA]
    · simp [hS]
    · simp [Function.update_of_ne (Ne.symm yS), hhS]
    · simp [hP]
    · simp [Function.update_of_ne (Ne.symm yP), hhP]
    · simp [Function.update_of_ne fY, hF]
    · simp [Function.update_of_ne gY, hG]
    · simp [Function.update_of_ne rY, hR]
  · refine hF1.trans ⟨fun i hi => ?_, fun r hr => ?_, rfl⟩
    · have : i ≠ Y := fun h => hi (Or.inl h)
      simp [Function.update_of_ne this]
    · have : r ≠ RY := fun h => hr (Or.inr (Or.inr (Or.inr h)))
      simp [Function.update_of_ne this]

/-! ## Zero, copy, XOR -/

def zeroOut (_ _ _ : Bool) : Bool := false
def copyOut (_ b _ : Bool) : Bool := b
def xorOut (a b _ : Bool) : Bool := xor a b

theorem mapS_zero : ∀ (as bs : List Bool) (c : Bool), as.length = bs.length →
    mapS zeroOut keepS as bs c = (List.replicate as.length false, c)
  | [], [], _, _ => rfl
  | a :: as, b :: bs, c, h => by
    simp only [mapS, keepS, mapS_zero as bs c (by simpa using h), List.length_cons, List.replicate_succ]
    rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

theorem mapS_copy : ∀ (as bs : List Bool) (c : Bool), as.length = bs.length → mapS copyOut keepS as bs c = (bs, c)
  | [], [], _, _ => rfl
  | a :: as, b :: bs, c, h => by
    simp only [mapS, keepS, mapS_copy as bs c (by simpa using h)]
    rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

theorem mapS_xor : ∀ (as bs : List Bool) (c : Bool), as.length = bs.length →
    mapS xorOut keepS as bs c = (List.zipWith xor as bs, c)
  | [], [], _, _ => rfl
  | a :: as, b :: bs, c, h => by
    simp only [mapS, keepS, mapS_xor as bs c (by simpa using h), List.zipWith_cons_cons]
    rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

theorem binary_zero (ℓ : ℕ) : binary ℓ 0 = List.replicate ℓ false := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih => show (0 % 2 == 1) :: binary ℓ (0 / 2) = _; rw [Nat.zero_div, ih]; rfl

end NearCubicWires.WireExponent3_5.FinalPass.Tm
