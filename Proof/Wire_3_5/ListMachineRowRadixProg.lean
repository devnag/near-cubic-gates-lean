import Proof.Wire_3_5.ListMachineRowRadixEnc
import Proof.Wire_3_5.FinalPassWordLib

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm

/-! ## The residue test -/

section Res
variable (cap : ℕ) (X C T : List Bool)

/-- The residue test's state: heads on `X`, `C`, `T`, the cell. -/
def rS (a b c : ℕ) (x : Bool) : WState 2 0 := ⟨![a, b, c], ![X, C, T], ![], x⟩

def addF : WM 2 0 := .seq (.whs 1 (.seq (.fwd 1) (.fwd 2))) (.fwd 1)
def skipF : WM 2 0 := .seq (.whs 1 (.fwd 1)) (.fwd 1)
def elemR : WM 2 0 := .seq (.fwd 0) (.seq (.ifs 0 addF skipF) (.fwd 0))
/-- **The residue test.** -/
def resP : WM 2 0 := .seq (.whs 0 elemR) (.ifs 2 (.setc true) (.setc false))

theorem rS_fwd0 (a b c : ℕ) (x : Bool) : WExec cap (.fwd 0) (rS X C T a b c x) (rS X C T (a + 1) b c x) 1 :=
  WExec.cast cap (WExec.fwd 0 _) (WState.eq (by funext i; fin_cases i <;> simp [rS]) rfl rfl rfl) le_rfl
theorem rS_fwd1 (a b c : ℕ) (x : Bool) : WExec cap (.fwd 1) (rS X C T a b c x) (rS X C T a (b + 1) c x) 1 :=
  WExec.cast cap (WExec.fwd 1 _) (WState.eq (by funext i; fin_cases i <;> simp [rS]) rfl rfl rfl) le_rfl
theorem rS_fwd2 (a b c : ℕ) (x : Bool) : WExec cap (.fwd 2) (rS X C T a b c x) (rS X C T a b (c + 1) x) 1 :=
  WExec.cast cap (WExec.fwd 2 _) (WState.eq (by funext i; fin_cases i <;> simp [rS]) rfl rfl rfl) le_rfl

theorem rS_bit0 (a b c : ℕ) (x : Bool) : wbit (rS X C T a b c x) 0 = readTapeBit X a := rfl
theorem rS_bit1 (a b c : ℕ) (x : Bool) : wbit (rS X C T a b c x) 1 = readTapeBit C b := rfl
theorem rS_bit2 (a b c : ℕ) (x : Bool) : wbit (rS X C T a b c x) 2 = readTapeBit T c := rfl

theorem read_field (pre rest : List Bool) (k i : ℕ) (hi : i ≤ k) :
    readTapeBit (pre ++ List.replicate k true ++ false :: rest) (pre.length + i) = decide (i < k) := by
  unfold readTapeBit
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  by_cases h : i < k
  · rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by omega)]
    simp [h]
  · have : i = k := by omega
    subst this
    rw [List.getElem_append_right (by simp)]
    simp

/-- The contribution loop: the field `1^k 0` moves both `C` and `T` by `k`. -/
theorem addLoop (a h : ℕ) (x : Bool) : ∀ (k : ℕ) (pre rest : List Bool), C = pre ++ List.replicate k true ++ false :: rest →
    WExec cap (.whs 1 (.seq (.fwd 1) (.fwd 2))) (rS X C T a pre.length h x) (rS X C T a (pre.length + k) (h + k) x)
      (5 * k + 1)
  | 0, pre, rest, hC => by
    refine WExec.cast cap (WExec.whsF ?_) (by simp) le_rfl
    rw [rS_bit1, hC]; simpa using read_field pre rest 0 0 le_rfl
  | k + 1, pre, rest, hC => by
    have hb : wbit (rS X C T a pre.length h x) 1 = true := by
      rw [rS_bit1, hC]; simpa using read_field pre rest (k + 1) 0 (by omega)
    have hC' : C = (pre ++ [true]) ++ List.replicate k true ++ false :: rest := by
      rw [hC, List.replicate_succ]; simp
    have ih := addLoop a (h + 1) x k (pre ++ [true]) rest hC'
    simp only [List.length_append, List.length_singleton] at ih
    have t := WExec.whsT hb (WExec.seq (rS_fwd1 cap X C T a pre.length h x) (rS_fwd2 cap X C T a (pre.length + 1) h x)) ih
    exact WExec.cast cap t (by congr 1 <;> omega) (by omega)

theorem skipLoop (a h : ℕ) (x : Bool) : ∀ (k : ℕ) (pre rest : List Bool), C = pre ++ List.replicate k true ++ false :: rest →
    WExec cap (.whs 1 (.fwd 1)) (rS X C T a pre.length h x) (rS X C T a (pre.length + k) h x) (3 * k + 1)
  | 0, pre, rest, hC => by
    refine WExec.cast cap (WExec.whsF ?_) (by simp) le_rfl
    rw [rS_bit1, hC]; simpa using read_field pre rest 0 0 le_rfl
  | k + 1, pre, rest, hC => by
    have hb : wbit (rS X C T a pre.length h x) 1 = true := by
      rw [rS_bit1, hC]; simpa using read_field pre rest (k + 1) 0 (by omega)
    have hC' : C = (pre ++ [true]) ++ List.replicate k true ++ false :: rest := by
      rw [hC, List.replicate_succ]; simp
    have ih := skipLoop a h x k (pre ++ [true]) rest hC'
    simp only [List.length_append, List.length_singleton] at ih
    have t := WExec.whsT hb (rS_fwd1 cap X C T a pre.length h x) ih
    exact WExec.cast cap t (by congr 1; omega) (by omega)

/-- One element: its bit decides whether its field moves `T`. -/
theorem elemR_spec (pX : List Bool) (bit : Bool) (restX : List Bool) (hX : X = pX ++ true :: bit :: restX)
    (pre rest : List Bool) (k : ℕ) (hC : C = pre ++ List.replicate k true ++ false :: rest) (h : ℕ) (x : Bool) :
    WExec cap elemR (rS X C T pX.length pre.length h x)
      (rS X C T (pX.length + 2) (pre.length + (k + 1)) (h + if bit then k else 0) x) (5 * k + 8) := by
  have h1 := rS_fwd0 cap X C T pX.length pre.length h x
  have hb : wbit (rS X C T (pX.length + 1) pre.length h x) 0 = bit := by
    rw [rS_bit0, hX]
    have := Streaming.read_append (pX ++ [true]) restX bit
    simpa [List.append_assoc] using this
  cases bit
  · have hs := skipLoop cap X C T (pX.length + 1) h x k pre rest hC
    have h2 := WExec.seq hs (rS_fwd1 cap X C T (pX.length + 1) (pre.length + k) h x)
    have h3 := WExec.ifsF (P := addF) (Q := skipF) hb h2
    have h4 := WExec.seq h3 (rS_fwd0 cap X C T (pX.length + 1) (pre.length + k + 1) h x)
    exact WExec.cast cap (WExec.seq h1 h4) (by simp [Nat.add_assoc]) (by omega)
  · have ha := addLoop cap X C T (pX.length + 1) h x k pre rest hC
    have h2 := WExec.seq ha (rS_fwd1 cap X C T (pX.length + 1) (pre.length + k) (h + k) x)
    have h3 := WExec.ifsT (P := addF) (Q := skipF) hb h2
    have h4 := WExec.seq h3 (rS_fwd0 cap X C T (pX.length + 1) (pre.length + k + 1) (h + k) x)
    exact WExec.cast cap (WExec.seq h1 h4) (by simp [Nat.add_assoc]) (by omega)

/-- The cost of the element loop. -/
def resLoopCost (cs : List ℕ) : ℕ := (cs.map fun k => 5 * k + 10).sum + 1

/-- The element loop. -/
theorem resLoop (x : Bool) : ∀ (bs : List Bool) (cs : List ℕ) (pX pC Ct : List Bool) (h : ℕ),
    bs.length = cs.length → X = pX ++ frame bs → C = pC ++ fieldsU cs ++ Ct →
    WExec cap (.whs 0 elemR) (rS X C T pX.length pC.length h x)
      (rS X C T (pX.length + 2 * bs.length) (pC.length + (fieldsU cs).length) (h + dotB bs cs) x) (resLoopCost cs)
  | [], cs, pX, pC, Ct, h, hl, hX, _ => by
    have hc : cs = [] := by cases cs <;> simp_all
    subst hc
    refine WExec.cast cap (WExec.whsF ?_) (by simp [fieldsU, dotB]) (by simp [resLoopCost])
    rw [rS_bit0, hX]
    simpa [frame] using Streaming.read_append pX [] false
  | b :: bs, [], _, _, _, _, hl, _, _ => by simp at hl
  | b :: bs, k :: cs, pX, pC, Ct, h, hl, hX, hC => by
    have hX' : X = pX ++ true :: b :: frame bs := by rw [hX]; rfl
    have hC' : C = pC ++ List.replicate k true ++ false :: (fieldsU cs ++ Ct) := by
      rw [hC]; simp [fieldsU, List.append_assoc]
    have he := elemR_spec cap X C T pX b (frame bs) hX' pC (fieldsU cs ++ Ct) k hC' h x
    have hX2 : X = (pX ++ [true, b]) ++ frame bs := by rw [hX']; simp
    have hC2 : C = (pC ++ (List.replicate k true ++ [false])) ++ fieldsU cs ++ Ct := by
      rw [hC]; simp [fieldsU, List.append_assoc]
    have ih := resLoop x bs cs (pX ++ [true, b]) (pC ++ (List.replicate k true ++ [false])) Ct
      (h + if b then k else 0) (by simpa using hl) hX2 hC2
    have hb : wbit (rS X C T pX.length pC.length h x) 0 = true := by
      rw [rS_bit0, hX']; exact Streaming.read_append pX (b :: frame bs) true
    simp only [List.length_append, List.length_cons, List.length_nil, List.length_replicate] at ih
    have t := WExec.whsT hb he ih
    have e1 : (fieldsU (k :: cs)).length = k + 1 + (fieldsU cs).length := by simp [fieldsU]; omega
    have e2 : dotB (b :: bs) (k :: cs) = (if b then k else 0) + dotB bs cs := rfl
    have e3 : resLoopCost (k :: cs) = 5 * k + 10 + resLoopCost cs := by simp [resLoopCost]; omega
    refine WExec.cast cap t ?_ (by rw [e3])
    rw [e1, e2]
    congr 1
    · simp; omega
    · omega
    · ring

/-- **The residue test**: the result cell receives the pattern's bit at the masked sum. -/
theorem resP_spec (bs : List Bool) (cs : List ℕ) (hl : bs.length = cs.length) (hX : X = frame bs)
    (hC : C = fieldsU cs) (x : Bool) :
    WExec cap resP (rS X C T 0 0 0 x)
      (rS X C T (2 * bs.length) (fieldsU cs).length (dotB bs cs) (readTapeBit T (dotB bs cs))) (resLoopCost cs + 3) := by
  have hl' := resLoop cap X C T x bs cs [] [] [] 0 hl (by simpa using hX) (by simpa using hC)
  simp only [List.length_nil, Nat.zero_add] at hl'
  have hfin : WExec cap (.ifs 2 (.setc true) (.setc false))
      (rS X C T (2 * bs.length) (fieldsU cs).length (dotB bs cs) x)
      (rS X C T (2 * bs.length) (fieldsU cs).length (dotB bs cs) (readTapeBit T (dotB bs cs))) 2 := by
    cases hT : readTapeBit T (dotB bs cs)
    · exact WExec.ifsF (by rw [rS_bit2, hT]) (WExec.cast cap (WExec.setc false _) rfl le_rfl)
    · exact WExec.ifsT (by rw [rS_bit2, hT]) (WExec.cast cap (WExec.setc true _) rfl le_rfl)
  exact WExec.cast cap (WExec.seq hl' hfin) rfl (by omega)

end Res

/-! ## The odometer -/

section Inc
variable (cap : ℕ)

/-- The odometer's state: the word `X` (written), the position word `Z`, their heads, carry and search registers, the
cell. -/
def iS (X Z : List Bool) (hx hz f g : ℕ) (c : Bool) : WState 1 2 := ⟨![hx, hz], ![X, Z], ![f, g], c⟩

def fw2 : WM 1 2 := .seq (.fwd 0) (.fwd 1)
def bw2 : WM 1 2 := .seq (.bwd 0) (.bwd 1)
def toEnd : WM 1 2 := .whs 0 (.seq fw2 fw2)
/-- Search back for a set cell of stream `s`, two cells per element. -/
def seekL (s : Fin 2) : WM 1 2 := .whr 1 (.ifs s (.dec 1) (.seq bw2 bw2))
def seek (s : Fin 2) : WM 1 2 := .seq (.inc 1) (seekL s)
def wrapB : WM 1 2 :=
  .seq (.wr 0 false) (.seq (seek 1) (.seq (.wr 0 true) (.seq bw2 (.ifs 1 (.seq (.dec 0) (.setc false)) bw2))))
def findB : WM 1 2 :=
  .seq (seek 0) (.seq (.wr 0 false) (.seq fw2 (.seq fw2 (.seq (.wr 0 true) (.seq (.dec 0) (.setc true))))))
def stepI : WM 1 2 := .ifs 0 wrapB findB
/-- **The odometer.** -/
def incP : WM 1 2 := .seq toEnd (.seq bw2 (.seq (.inc 0) (.whr 0 stepI)))

variable (X Z : List Bool)

theorem iS_bit0 (hx hz f g : ℕ) (c : Bool) : wbit (iS X Z hx hz f g c) 0 = readTapeBit X hx := rfl
theorem iS_bit1 (hx hz f g : ℕ) (c : Bool) : wbit (iS X Z hx hz f g c) 1 = readTapeBit Z hz := rfl

theorem fw2_spec (h f g : ℕ) (c : Bool) : WExec cap fw2 (iS X Z h h f g c) (iS X Z (h + 1) (h + 1) f g c) 3 := by
  have h1 := WExec.fwd (cap := cap) 0 (iS X Z h h f g c)
  have h2 := WExec.fwd (cap := cap) 1 ((iS X Z h h f g c).seth 0 ((iS X Z h h f g c).sh 0 + 1))
  refine WExec.cast cap (WExec.seq h1 h2) (WState.eq ?_ rfl rfl rfl) le_rfl
  funext i; fin_cases i <;> simp [iS]

theorem bw2_spec (h f g : ℕ) (c : Bool) : WExec cap bw2 (iS X Z h h f g c) (iS X Z (h - 1) (h - 1) f g c) 3 := by
  have h1 := WExec.bwd (cap := cap) 0 (iS X Z h h f g c)
  have h2 := WExec.bwd (cap := cap) 1 ((iS X Z h h f g c).seth 0 ((iS X Z h h f g c).sh 0 - 1))
  refine WExec.cast cap (WExec.seq h1 h2) (WState.eq ?_ rfl rfl rfl) le_rfl
  funext i; fin_cases i <;> simp [iS]

theorem wr_spec (h f g : ℕ) (c b : Bool) :
    WExec cap (.wr 0 b) (iS X Z h h f g c) (iS (writeTapeBit X h b) Z h h f g c) 1 := by
  refine WExec.cast cap (WExec.wr 0 b _) (WState.eq rfl ?_ rfl rfl) le_rfl
  funext i; fin_cases i <;> simp [iS]

theorem inc_spec (r : Fin 2) (h f g : ℕ) (c : Bool) (hv : (![f, g] : Fin 2 → ℕ) r < cap) :
    WExec cap (.inc r) (iS X Z h h f g c)
      (iS X Z h h (if r = 0 then f + 1 else f) (if r = 1 then g + 1 else g) c) 3 := by
  refine WExec.cast cap (WExec.inc r _ hv) (WState.eq rfl rfl ?_ rfl) le_rfl
  funext i; fin_cases r <;> fin_cases i <;> simp [iS]

theorem dec_spec (r : Fin 2) (h f g : ℕ) (c : Bool) (hv : (![f, g] : Fin 2 → ℕ) r ≤ cap) :
    WExec cap (.dec r) (iS X Z h h f g c)
      (iS X Z h h (if r = 0 then f - 1 else f) (if r = 1 then g - 1 else g) c) 1 := by
  refine WExec.cast cap (WExec.dec r _ hv) (WState.eq rfl rfl ?_ rfl) le_rfl
  funext i; fin_cases r <;> fin_cases i <;> simp [iS]

theorem setc_spec (h f g : ℕ) (c v : Bool) : WExec cap (.setc v) (iS X Z h h f g c) (iS X Z h h f g v) 1 :=
  WExec.cast cap (WExec.setc v _) rfl le_rfl

/-- The search loop: from element `e + i` back to element `e`, the first one whose bit is set. -/
theorem seekL_spec (s : Fin 2) (hcap : 1 ≤ cap) (F : ℕ) (c : Bool) (e : ℕ) : ∀ i : ℕ,
    (∀ j ≤ i, readTapeBit ((![X, Z] : Fin 2 → List Bool) s) (2 * (e + j) + 1) = decide (j = 0)) →
    WExec cap (seekL s) (iS X Z (2 * (e + i) + 1) (2 * (e + i) + 1) F 1 c) (iS X Z (2 * e + 1) (2 * e + 1) F 0 c)
      (10 * i + 5)
  | 0, hb => by
    have hbit : wbit (iS X Z (2 * (e + 0) + 1) (2 * (e + 0) + 1) F 1 c) s = true := by
      have := hb 0 le_rfl
      fin_cases s <;> simpa [iS_bit0, iS_bit1] using this
    have hd := dec_spec cap X Z 1 (2 * (e + 0) + 1) F 1 c (by simpa using hcap)
    simp only [Fin.isValue, one_ne_zero, if_false, if_true, Nat.sub_self] at hd
    have t := WExec.whrT (r := 1) (P := .ifs s (.dec 1) (.seq bw2 bw2)) (by simp [iS])
      (WExec.ifsT hbit hd) (WExec.whrF (by simp [iS]))
    exact WExec.cast cap t (by simp) (by omega)
  | i + 1, hb => by
    have hbit : wbit (iS X Z (2 * (e + (i + 1)) + 1) (2 * (e + (i + 1)) + 1) F 1 c) s = false := by
      have := hb (i + 1) le_rfl
      fin_cases s <;> simpa [iS_bit0, iS_bit1] using this
    have h1 := bw2_spec cap X Z (2 * (e + (i + 1)) + 1) F 1 c
    have h2 := bw2_spec cap X Z (2 * (e + (i + 1)) + 1 - 1) F 1 c
    have hm := WExec.seq h1 h2
    have e1 : 2 * (e + (i + 1)) + 1 - 1 - 1 = 2 * (e + i) + 1 := by omega
    rw [e1] at hm
    have ih := seekL_spec s hcap F c e i (fun j hj => hb j (by omega))
    have t := WExec.whrT (r := 1) (P := .ifs s (.dec 1) (.seq bw2 bw2)) (by simp [iS]) (WExec.ifsF hbit hm) ih
    exact WExec.cast cap t rfl (by omega)

theorem seek_spec (s : Fin 2) (hcap : 1 ≤ cap) (F : ℕ) (c : Bool) (e i : ℕ)
    (hb : ∀ j ≤ i, readTapeBit ((![X, Z] : Fin 2 → List Bool) s) (2 * (e + j) + 1) = decide (j = 0)) :
    WExec cap (seek s) (iS X Z (2 * (e + i) + 1) (2 * (e + i) + 1) F 0 c) (iS X Z (2 * e + 1) (2 * e + 1) F 0 c)
      (10 * i + 9) := by
  have h1 := inc_spec cap X Z 1 (2 * (e + i) + 1) F 0 c (by simp; omega)
  simp only [Fin.isValue, one_ne_zero, if_false, if_true, Nat.zero_add] at h1
  exact WExec.cast cap (WExec.seq h1 (seekL_spec cap X Z s hcap F c e i hb)) rfl (by omega)

/-- The walk to the end of the framed word. -/
theorem toEnd_spec (w : List Bool) (hX : X = frame w) (c : Bool) : ∀ n j, j + n = w.length →
    WExec cap toEnd (iS X Z (2 * j) (2 * j) 0 0 c) (iS X Z (2 * w.length) (2 * w.length) 0 0 c) (9 * n + 1)
  | 0, j, hj => by
    have hj' : j = w.length := by omega
    subst hj'
    refine WExec.whsF ?_
    rw [iS_bit0, hX]; exact Row.frame_read_end w
  | n + 1, j, hj => by
    have hb : wbit (iS X Z (2 * j) (2 * j) 0 0 c) 0 = true := by
      rw [iS_bit0, hX]; exact frame_read_mark w j (by omega)
    have h1 := fw2_spec cap X Z (2 * j) 0 0 c
    have h2 := fw2_spec cap X Z (2 * j + 1) 0 0 c
    have ih := toEnd_spec w hX c n (j + 1) (by omega)
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring] at ih
    exact WExec.cast cap (WExec.whsT hb (WExec.seq h1 h2) ih) rfl (by omega)

end Inc

/-! ## The one-hot word under writes -/

theorem frame_set (b : Bool) : ∀ (w : List Bool) (e : ℕ), e < w.length →
    writeTapeBit (frame w) (2 * e + 1) b = frame (w.set e b)
  | [], _, h => by simp at h
  | x :: w, 0, _ => by simp [frame, writeTapeBit]
  | x :: w, e + 1, h => by
    have ih := frame_set b w e (by simpa using h)
    rw [show 2 * (e + 1) + 1 = (2 * e + 1) + 1 + 1 by ring]
    simp only [frame, List.set_cons_succ, writeTapeBit] at ih ⊢
    rw [ih]

theorem encT_mid_getElem (K : ℕ) (ρ z : List ℕ) (t j : ℕ) (hj : j ≤ K)
    (h : ρ.length * (K + 1) + j < (encT K (ρ ++ [t] ++ z)).length) :
    (encT K (ρ ++ [t] ++ z))[ρ.length * (K + 1) + j] = decide (j = t) := by
  have e : encT K (ρ ++ [t] ++ z) = encT K ρ ++ (ohB K t ++ encT K z) := by simp [encT]
  rw [List.getElem_of_eq e, List.getElem_append_right (by simp), List.getElem_append_left (by simp; omega)]
  simp [ohB, encT_length]

theorem encT_mid_set (K : ℕ) (ρ z : List ℕ) (t j : ℕ) (hj : j ≤ K) (b : Bool) :
    (encT K (ρ ++ [t] ++ z)).set (ρ.length * (K + 1) + j) b = encT K ρ ++ (ohB K t).set j b ++ encT K z := by
  simp only [encT_append]
  have e1 : encT K [t] = ohB K t := by simp [encT]
  rw [e1, List.append_assoc, List.set_append_right _ _ (by simp), encT_length, Nat.add_sub_cancel_left,
    List.set_append_left _ _ (by simp; omega), ← List.append_assoc]

theorem ohB_move (K t t' : ℕ) : ((ohB K t).set t false).set t' true = ohB K t' := by
  apply List.ext_getElem (by simp)
  intro n h1 h2
  simp only [List.getElem_set, ohB_getElem]
  by_cases a : t' = n
  · subst a; simp
  · by_cases b : t = n
    · subst b; simp [a, Ne.symm a]
    · simp [a, b, Ne.symm a, Ne.symm b]

theorem readX_mid (K : ℕ) (ρ z : List ℕ) (t j : ℕ) (hj : j ≤ K) :
    readTapeBit (frame (encT K (ρ ++ [t] ++ z))) (2 * (ρ.length * (K + 1) + j) + 1) = decide (j = t) := by
  have hl : ρ.length * (K + 1) + j < (encT K (ρ ++ [t] ++ z)).length := by
    simp only [encT_length, List.length_append, List.length_singleton]; nlinarith
  rw [frame_read_bit _ _ hl, encT_mid_getElem K ρ z t j hj hl]

theorem writeX_mid (K : ℕ) (ρ z : List ℕ) (t j : ℕ) (hj : j ≤ K) (b : Bool) :
    writeTapeBit (frame (encT K (ρ ++ [t] ++ z))) (2 * (ρ.length * (K + 1) + j) + 1) b =
      frame (encT K ρ ++ (ohB K t).set j b ++ encT K z) := by
  have hl : ρ.length * (K + 1) + j < (encT K (ρ ++ [t] ++ z)).length := by
    simp only [encT_length, List.length_append, List.length_singleton]; nlinarith
  rw [frame_set b _ _ hl, encT_mid_set K ρ z t j hj b]

theorem writeX_mid' (K : ℕ) (ρ z : List ℕ) (j : ℕ) (hj : j ≤ K) (b : Bool) (B : List Bool) (hB : B.length = K + 1) :
    writeTapeBit (frame (encT K ρ ++ B ++ encT K z)) (2 * (ρ.length * (K + 1) + j) + 1) b =
      frame (encT K ρ ++ B.set j b ++ encT K z) := by
  have hl : ρ.length * (K + 1) + j < (encT K ρ ++ B ++ encT K z).length := by
    simp only [List.length_append, encT_length, hB]; omega
  rw [frame_set b _ _ hl, List.append_assoc, List.set_append_right _ _ (by simp), encT_length,
    Nat.add_sub_cancel_left, List.set_append_left _ _ (by omega), ← List.append_assoc]

theorem encT_snoc_zero (K : ℕ) (ρ : List ℕ) (m : ℕ) :
    encT K ρ ++ ohB K 0 ++ encT K (List.replicate m 0) = encT K (ρ ++ List.replicate (m + 1) 0) := by
  simp [List.replicate_succ, encT]

/-! ## The odometer loop -/

section IncLoop
variable (cap : ℕ)

/-- The per-block cost bound of the odometer loop. -/
def incBlk (K : ℕ) : ℕ := 10 * K + 45

theorem allK_nil (K : ℕ) : allK K [] = true := rfl

/-- **The odometer loop**, from the last cell of the block of the last position of `ρ` (the positions after it
already wrapped to `0`): the carry propagates left and the word becomes that of `incT K ρ`; the cell receives
`¬ allK ρ`. -/
theorem incLoop (hcap : 1 ≤ cap) (K N : ℕ) : ∀ (n : ℕ) (ρ : List ℕ) (m : ℕ) (c : Bool),
    ρ.length = n + 1 → (∀ x ∈ ρ, x ≤ K) → (ρ.length + m) * (K + 1) ≤ N →
    ∃ h', WExec cap (.whr 0 stepI)
      (iS (frame (encT K (ρ ++ List.replicate m 0))) (zW K N) (2 * (n * (K + 1) + K) + 1)
        (2 * (n * (K + 1) + K) + 1) 1 0 c)
      (iS (frame (encT K (incT K ρ ++ List.replicate m 0))) (zW K N) h' h' 0 0 (!allK K ρ))
      ((n + 1) * incBlk K + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ρ m c hlen hd hN
  obtain ⟨ρ', t, rfl⟩ : ∃ ρ' t, ρ = ρ' ++ [t] :=
    ⟨ρ.dropLast, ρ.getLast (List.ne_nil_of_length_eq_add_one hlen), (List.dropLast_append_getLast _).symm⟩
  have hn : ρ'.length = n := by simpa using hlen
  have htK : t ≤ K := hd t (by simp)
  have hd' : ∀ x ∈ ρ', x ≤ K := fun x hx => hd x (by simp [hx])
  set z := List.replicate m 0 with hz
  set X0 := frame (encT K (ρ' ++ [t] ++ z)) with hX0
  set Zw := zW K N with hZw
  have hb0 : wbit (iS X0 Zw (2 * (n * (K + 1) + K) + 1) (2 * (n * (K + 1) + K) + 1) 1 0 c) 0 = decide (K = t) := by
    rw [iS_bit0, hX0, ← hn]; exact readX_mid K ρ' z t K le_rfl
  by_cases hlt : t < K
  · -- the carry stops in this block
    have hb : wbit (iS X0 Zw (2 * (n * (K + 1) + K) + 1) (2 * (n * (K + 1) + K) + 1) 1 0 c) 0 = false := by
      rw [hb0]; simp; omega
    have hs := seek_spec cap X0 Zw 0 hcap 1 c (n * (K + 1) + t) (K - t) (by
      intro j hj
      simp only [Matrix.cons_val_zero]
      rw [hX0, ← hn, show ρ'.length * (K + 1) + t + j = ρ'.length * (K + 1) + (t + j) by ring,
        readX_mid K ρ' z t (t + j) (by omega)]
      simp)
    rw [show n * (K + 1) + t + (K - t) = n * (K + 1) + K by omega] at hs
    have w1 := wr_spec cap X0 Zw (2 * (n * (K + 1) + t) + 1) 1 0 c false
    have eX1 : writeTapeBit X0 (2 * (n * (K + 1) + t) + 1) false = frame (encT K ρ' ++ (ohB K t).set t false ++ encT K z) := by
      rw [hX0, ← hn]; exact writeX_mid K ρ' z t t htK false
    rw [eX1] at w1
    set X1 := frame (encT K ρ' ++ (ohB K t).set t false ++ encT K z) with hX1
    have f1 := fw2_spec cap X1 Zw (2 * (n * (K + 1) + t) + 1) 1 0 c
    have f2 := fw2_spec cap X1 Zw (2 * (n * (K + 1) + t) + 1 + 1) 1 0 c
    have w2 := wr_spec cap X1 Zw (2 * (n * (K + 1) + t) + 1 + 1 + 1) 1 0 c true
    have eX2 : writeTapeBit X1 (2 * (n * (K + 1) + t) + 1 + 1 + 1) true = frame (encT K (ρ' ++ [t + 1] ++ z)) := by
      rw [hX1, show 2 * (n * (K + 1) + t) + 1 + 1 + 1 = 2 * (ρ'.length * (K + 1) + (t + 1)) + 1 by rw [hn]; ring,
        writeX_mid' K ρ' z (t + 1) (by omega) true _ (by simp), ohB_move]
      simp [encT]
    rw [eX2] at w2
    set X2 := frame (encT K (ρ' ++ [t + 1] ++ z)) with hX2
    set q := 2 * (n * (K + 1) + t) + 1 + 1 + 1 with hq
    have d1 := dec_spec cap X2 Zw 0 q 1 0 c (by simp; omega)
    simp only [Fin.isValue, if_true, zero_ne_one, if_false, Nat.sub_self] at d1
    have s1 := setc_spec cap X2 Zw q 0 0 c true
    have body := WExec.seq hs (WExec.seq w1 (WExec.seq f1 (WExec.seq f2 (WExec.seq w2 (WExec.seq d1 s1)))))
    have hstep := WExec.ifsF (P := wrapB) (Q := findB) hb body
    have tt := WExec.whrT (r := 0) (P := stepI) (by simp [iS]) hstep (WExec.whrF (by simp [iS]))
    refine ⟨q, WExec.cast cap tt ?_ ?_⟩
    · rw [incT_snoc, if_pos hlt, allK_snoc]
      have : ¬ (K ≤ t) := by omega
      simp [this, hX2, hz]
    · unfold incBlk; rw [Nat.add_mul, Nat.one_mul]
      have : K - t ≤ K := Nat.sub_le K t
      nlinarith
  · -- the block wraps to `0`
    have htK' : t = K := by omega
    subst htK'
    have hb : wbit (iS X0 Zw (2 * (n * (t + 1) + t) + 1) (2 * (n * (t + 1) + t) + 1) 1 0 c) 0 = true := by
      rw [hb0]; simp
    have w1 := wr_spec cap X0 Zw (2 * (n * (t + 1) + t) + 1) 1 0 c false
    have eX1 : writeTapeBit X0 (2 * (n * (t + 1) + t) + 1) false = frame (encT t ρ' ++ (ohB t t).set t false ++ encT t z) := by
      rw [hX0, ← hn]; exact writeX_mid t ρ' z t t le_rfl false
    rw [eX1] at w1
    set X1 := frame (encT t ρ' ++ (ohB t t).set t false ++ encT t z) with hX1
    have hs := seek_spec cap X1 Zw 1 hcap 1 c (n * (t + 1)) t (by
      intro j hj
      simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [hZw, zW_bit t N (n * (t + 1) + j) (by
        have : (ρ'.length + 1 + m) * (t + 1) ≤ N := by simpa using hN
        rw [hn] at this; nlinarith)]
      have : (n * (t + 1) + j) % (t + 1) = j := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right]; exact Nat.mod_eq_of_lt (by omega)
      rw [this])
    have w2 := wr_spec cap X1 Zw (2 * (n * (t + 1)) + 1) 1 0 c true
    have eX2 : writeTapeBit X1 (2 * (n * (t + 1)) + 1) true = frame (encT t (ρ' ++ List.replicate (m + 1) 0)) := by
      rw [hX1, show 2 * (n * (t + 1)) + 1 = 2 * (ρ'.length * (t + 1) + 0) + 1 by rw [hn]; ring,
        writeX_mid' t ρ' z 0 (by omega) true _ (by simp), ohB_move, hz, encT_snoc_zero]
    rw [eX2] at w2
    set X2 := frame (encT t (ρ' ++ List.replicate (m + 1) 0)) with hX2
    have b1 := bw2_spec cap X2 Zw (2 * (n * (t + 1)) + 1) 1 0 c
    rw [show 2 * (n * (t + 1)) + 1 - 1 = 2 * (n * (t + 1)) by omega] at b1
    have hmark : wbit (iS X2 Zw (2 * (n * (t + 1))) (2 * (n * (t + 1))) 1 0 c) 1 = decide (n * (t + 1) = 0) := by
      rw [iS_bit1, hZw, zW_mark t N (n * (t + 1)) (by
        have : (ρ'.length + 1 + m) * (t + 1) ≤ N := by simpa using hN
        rw [hn] at this; nlinarith)]
    cases n with
    | zero =>
      have hρ' : ρ' = [] := List.eq_nil_of_length_eq_zero hn
      subst hρ'
      have hb1 : wbit (iS X2 Zw (2 * (0 * (t + 1))) (2 * (0 * (t + 1))) 1 0 c) 1 = true := by rw [hmark]; simp
      have d1 := dec_spec cap X2 Zw 0 (2 * (0 * (t + 1))) 1 0 c (by simp; omega)
      simp only [Fin.isValue, if_true, zero_ne_one, if_false, Nat.sub_self] at d1
      have s1 := setc_spec cap X2 Zw (2 * (0 * (t + 1))) 0 0 c false
      have hif := WExec.ifsT (P := .seq (.dec 0) (.setc false)) (Q := bw2) hb1 (WExec.seq d1 s1)
      have body := WExec.seq w1 (WExec.seq hs (WExec.seq w2 (WExec.seq b1 hif)))
      have hstep := WExec.ifsT (P := wrapB) (Q := findB) hb body
      have tt := WExec.whrT (r := 0) (P := stepI) (by simp [iS]) hstep (WExec.whrF (by simp [iS]))
      refine ⟨2 * (0 * (t + 1)), WExec.cast cap tt ?_ ?_⟩
      · rw [incT_snoc, if_neg (lt_irrefl t), incT_nil, allK_snoc, allK_nil]
        simp [hX2, List.replicate_succ, hz]
      · unfold incBlk; omega
    | succ n' =>
      have hb1 : wbit (iS X2 Zw (2 * ((n' + 1) * (t + 1))) (2 * ((n' + 1) * (t + 1))) 1 0 c) 1 = false := by
        rw [hmark]; simp
      have b2 := bw2_spec cap X2 Zw (2 * ((n' + 1) * (t + 1))) 1 0 c
      rw [show 2 * ((n' + 1) * (t + 1)) - 1 = 2 * (n' * (t + 1) + t) + 1 by ring_nf; omega] at b2
      have hif := WExec.ifsF (P := .seq (.dec 0) (.setc false)) (Q := bw2) hb1 b2
      have body := WExec.seq w1 (WExec.seq hs (WExec.seq w2 (WExec.seq b1 hif)))
      have hstep := WExec.ifsT (P := wrapB) (Q := findB) hb body
      obtain ⟨h', ih'⟩ := ih n' (by omega) ρ' (m + 1) c (by omega) hd' (by
        have : (ρ'.length + 1 + m) * (t + 1) ≤ N := by simpa using hN
        rw [show ρ'.length + (m + 1) = ρ'.length + 1 + m by ring]; exact this)
      have tt := WExec.whrT (r := 0) (P := stepI) (by simp [iS]) hstep ih'
      refine ⟨h', WExec.cast cap tt ?_ ?_⟩
      · rw [incT_snoc, if_neg (lt_irrefl t), allK_snoc]
        simp [List.replicate_succ, List.append_assoc, hz]
      · unfold incBlk; ring_nf; omega

/-- The odometer's cost bound. -/
def incCost (K P : ℕ) : ℕ := 9 * (P * (K + 1)) + P * incBlk K + 20

/-- **The odometer**: the word of `τ` becomes the word of `incT K τ`; the cell receives `¬ allK τ`; both registers
end at `0`. -/
theorem incP_spec (hcap : 1 ≤ cap) (K : ℕ) (τ : List ℕ) (hτ : τ ≠ []) (hd : ∀ x ∈ τ, x ≤ K) (c : Bool) :
    ∃ h', WExec cap incP (iS (frame (encT K τ)) (zW K (τ.length * (K + 1))) 0 0 0 0 c)
      (iS (frame (encT K (incT K τ))) (zW K (τ.length * (K + 1))) h' h' 0 0 (!allK K τ)) (incCost K τ.length) := by
  obtain ⟨n, hn⟩ : ∃ n, τ.length = n + 1 := ⟨τ.length - 1, by have := List.length_pos_of_ne_nil hτ; omega⟩
  set X := frame (encT K τ) with hX
  set Zw := zW K (τ.length * (K + 1)) with hZw
  have te := toEnd_spec cap X Zw (encT K τ) hX c (encT K τ).length 0 (by simp)
  simp only [Nat.mul_zero] at te
  have hw : (encT K τ).length = n * (K + 1) + K + 1 := by rw [encT_length, hn]; ring
  rw [hw] at te
  have b1 := bw2_spec cap X Zw (2 * (n * (K + 1) + K + 1)) 0 0 c
  rw [show 2 * (n * (K + 1) + K + 1) - 1 = 2 * (n * (K + 1) + K) + 1 by omega] at b1
  have i1 := inc_spec cap X Zw 0 (2 * (n * (K + 1) + K) + 1) 0 0 c (by simp; omega)
  simp only [Fin.isValue, if_true, zero_ne_one, if_false, Nat.zero_add] at i1
  obtain ⟨h', hl⟩ := incLoop cap hcap K (τ.length * (K + 1)) n τ 0 c hn hd (by simp)
  simp only [List.replicate_zero, List.append_nil] at hl
  refine ⟨h', WExec.cast cap (WExec.seq te (WExec.seq b1 (WExec.seq i1 hl))) rfl ?_⟩
  unfold incCost
  have e : n * (K + 1) + K + 1 = (n + 1) * (K + 1) := by ring
  rw [hn, e]
  omega

end IncLoop

end NearCubicWires.WireExponent3_5.ListMachine.Row
