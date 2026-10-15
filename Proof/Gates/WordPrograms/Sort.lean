import Proof.Gates.WordPrograms.RecLoop
import Proof.Gates.WordPrograms.BinW
import Proof.Wire_3_5.SelectionMachineSortW
import Mathlib.Data.Nat.Bitwise

set_option autoImplicit false

namespace NearCubicGates.Close.WordPrograms
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn keyStream keyRec sortW sortW_spec sortCost rc sorted)
open NearCubicWires.WireExponent3_5.UnionMachine.RegRat (copyB copyB_spec ltB ltB_spec)

variable {ns nr : ℕ}

/-! ## Sorting -/

theorem keyStream_eq (W : ℕ) (hW : 1 ≤ W) (l : List ℕ) : keyStream W l = recStream (l.map (binary W)) := by
  unfold keyStream recStream StablePartition.stream StablePartition.recordsBits
  congr 1
  rw [List.flatMap_map, List.flatMap_map]
  congr 1
  funext x
  obtain ⟨w, rfl⟩ : ∃ w, W = w + 1 := ⟨W - 1, by omega⟩
  rfl

/-- **Sort the record stream on `S`** (scratch stream `S'`, scratch registers `CA CB K`). -/
def sortRecs (S S' : Fin (ns + 1)) (CA CB K : Fin nr) : WMX ns nr := .wm (sortW S S' CA CB K)

/-- **The sort.** From the record stream of the width-`W` numbers `l` on `S` (head `0`), a scratch stream `S'` of the
same length (head `0`) and the registers `CA CB K` at `0`: `S` holds the record stream of `sorted l` (the numbers in
nondecreasing order, `Sort.sorted_perm`, `Sort.sorted_pairwise`), `S'` some list of the same length, everything else
unchanged. -/
theorem sortRecs_spec (cap W : ℕ) {S S' : Fin (ns + 1)} {CA CB K : Fin nr} (hSS' : S ≠ S') (hC : CA ≠ CB)
    (hKA : K ≠ CA) (hKB : K ≠ CB) (σ : WState ns nr) (l : List ℕ) (hW : 1 ≤ W) (hl : ∀ x ∈ l, x < 2 ^ W)
    (hS : σ.st S = recStream (l.map (binary W))) (hSh : σ.sh S = 0)
    (hS' : (σ.st S').length = (recStream (l.map (binary W))).length) (hS'h : σ.sh S' = 0) (hCA : σ.val CA = 0)
    (hCB : σ.val CB = 0) (hK : σ.val K = 0) (hcap : (recStream (l.map (binary W))).length + 2 ≤ cap) :
    ∃ junk : List Bool, junk.length = (recStream (l.map (binary W))).length ∧
      WXExec cap (sortRecs S S' CA CB K) σ ((σ.sets S (recStream ((sorted l).map (binary W)))).sets S' junk)
        (sortCost W l.length) := by
  rw [← keyStream_eq W hW] at hS hS' hcap ⊢
  have hr : ∀ r ∈ [CA, CB, K], σ.val r = 0 := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> assumption
  obtain ⟨junk, hj, h⟩ := sortW_spec cap W hSS' hC hKA hKB σ l hW hl hS hSh hS' hS'h hr hcap
  rw [keyStream_eq W hW] at h
  exact ⟨junk, hj, WXExec.wm h⟩

theorem sortCost_le (W N : ℕ) : sortCost W N ≤ 400 * (N + 1) * (W + 1) ^ 2 := by
  unfold sortCost rc
  rcases W with _ | w
  · simp; omega
  · simp only [Nat.add_sub_cancel]
    nlinarith [Nat.zero_le N, Nat.zero_le w, Nat.mul_le_mul_left N (Nat.zero_le w)]

theorem recStream_map_length (W : ℕ) (l : List ℕ) :
    (recStream (l.map (binary W))).length = l.length * (2 * W + 1) + 1 := by
  rw [recStream_length W _ (by intro w hw; obtain ⟨x, _, rfl⟩ := List.mem_map.mp hw; simp), List.length_map]

/-! ## Bitwise passes -/

/-- The xor pass. -/
def xorO (a b _ : Bool) : Bool := xor a b

/-- The and pass. -/
def andO (a b _ : Bool) : Bool := a && b

theorem mapS_xor : ∀ (w x y : ℕ) (c : Bool), mapS xorO keepS (binary w x) (binary w y) c = (binary w (x ^^^ y), c)
  | 0, _, _, _ => rfl
  | w + 1, x, y, c => by
    show (xorO (x % 2 == 1) (y % 2 == 1) c :: (mapS xorO keepS (binary w (x / 2)) (binary w (y / 2)) c).1,
      (mapS xorO keepS (binary w (x / 2)) (binary w (y / 2)) c).2) = (((x ^^^ y) % 2 == 1) :: binary w ((x ^^^ y) / 2), c)
    rw [mapS_xor w (x / 2) (y / 2) c, Nat.xor_div_two]
    have hm := @Nat.xor_mod_two_eq x y
    have hx := Nat.mod_two_eq_zero_or_one x
    have hy := Nat.mod_two_eq_zero_or_one y
    simp only [xorO]
    congr 1
    congr 1
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> simp [hx, hy] <;> omega

theorem mapS_and : ∀ (w x y : ℕ) (c : Bool), mapS andO keepS (binary w x) (binary w y) c = (binary w (x &&& y), c)
  | 0, _, _, _ => rfl
  | w + 1, x, y, c => by
    show (andO (x % 2 == 1) (y % 2 == 1) c :: (mapS andO keepS (binary w (x / 2)) (binary w (y / 2)) c).1,
      (mapS andO keepS (binary w (x / 2)) (binary w (y / 2)) c).2) = (((x &&& y) % 2 == 1) :: binary w ((x &&& y) / 2), c)
    rw [mapS_and w (x / 2) (y / 2) c, Nat.and_div_two]
    have hm := @Nat.and_mod_two_eq_one x y
    have hx := Nat.mod_two_eq_zero_or_one x
    have hy := Nat.mod_two_eq_zero_or_one y
    simp only [andO]
    congr 1
    congr 1
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> simp_all

/-- `A := a xor b`. -/
def xorW (A B : Fin (ns + 1)) (F R : Fin nr) : WM ns nr := mapPass xorO keepS A B F R

/-- `A := a and b`. -/
def andW (A B : Fin (ns + 1)) (F R : Fin nr) : WM ns nr := mapPass andO keepS A B F R

theorem xorW_spec (cap W : ℕ) {A B : Fin (ns + 1)} {F R : Fin nr} (hAB : A ≠ B) (hFR : F ≠ R) (σ : WState ns nr)
    (a b : ℕ) (hA : NumOn σ A W a) (hB : NumOn σ B W b) (hF : σ.val F = 0) (hR : σ.val R = 0)
    (hcap : 2 * W + 1 ≤ cap) : WExec cap (xorW A B F R) σ (σ.sets A (frame (binary W (a ^^^ b)))) (41 * W + 3) := by
  have h := mapPass_spec cap xorO keepS A B F R hAB hFR (by omega) (binary W a) (binary W b) [] [false] false σ
    (by simp) (by rw [hA.1, BinW.frame_frameP]) hA.2 (by rw [hB.1, BinW.frame_frameP]) hB.2 (by simp [hF]) hR
    (by simp; omega)
  rw [mapS_xor, binary_length] at h
  refine WExec.cast cap h ?_ (by omega)
  rw [Bool.toNat_false, BinW.setv_same (by simp [hF]), BinW.frame_frameP]

theorem andW_spec (cap W : ℕ) {A B : Fin (ns + 1)} {F R : Fin nr} (hAB : A ≠ B) (hFR : F ≠ R) (σ : WState ns nr)
    (a b : ℕ) (hA : NumOn σ A W a) (hB : NumOn σ B W b) (hF : σ.val F = 0) (hR : σ.val R = 0)
    (hcap : 2 * W + 1 ≤ cap) : WExec cap (andW A B F R) σ (σ.sets A (frame (binary W (a &&& b)))) (41 * W + 3) := by
  have h := mapPass_spec cap andO keepS A B F R hAB hFR (by omega) (binary W a) (binary W b) [] [false] false σ
    (by simp) (by rw [hA.1, BinW.frame_frameP]) hA.2 (by rw [hB.1, BinW.frame_frameP]) hB.2 (by simp [hF]) hR
    (by simp; omega)
  rw [mapS_and, binary_length] at h
  refine WExec.cast cap h ?_ (by omega)
  rw [Bool.toNat_false, BinW.setv_same (by simp [hF]), BinW.frame_frameP]

/-! ## Key comparison -/

theorem xor_lt_iff (a b P : ℕ) : a ^^^ b < 2 ^ P ↔ a / 2 ^ P = b / 2 ^ P := by
  rw [← Nat.div_eq_zero_iff_lt (by positivity), Nat.xor_div_two_pow]
  constructor
  · intro h
    have := Nat.xor_xor_cancel_left (a / 2 ^ P) (b / 2 ^ P)
    rw [h, Nat.xor_zero] at this
    exact this
  · intro h; rw [h, Nat.xor_self]

/-- `F := [a / 2^P = b / 2^P]` (the keys of two records with `P`-bit payloads), `T` scratch (any width-`W` word), `MP`
holds `2^P`. -/
def keyEqW (A B T MP : Fin (ns + 1)) (F R : Fin nr) : WM ns nr :=
  .seq (copyB T A F R) (.seq (xorW T B F R) (ltB T MP F R))

theorem keyEqW_spec (cap W P : ℕ) {A B T MP : Fin (ns + 1)} {F R : Fin nr} (hTA : T ≠ A) (hTB : T ≠ B) (hTM : T ≠ MP)
    (hFR : F ≠ R) (σ : WState ns nr) (a b t : ℕ) (hA : NumOn σ A W a) (hB : NumOn σ B W b) (hT : NumOn σ T W t)
    (hM : NumOn σ MP W (2 ^ P)) (hF : σ.val F = 0) (hR : σ.val R = 0) (ha : a < 2 ^ W) (hb : b < 2 ^ W)
    (hPW : P < W) (hcap : 2 * W + 1 ≤ cap) :
    WExec cap (keyEqW A B T MP F R) σ ((σ.sets T (frame (binary W (a ^^^ b)))).setv F
      (decide (a / 2 ^ P = b / 2 ^ P)).toNat) (123 * W + 11) := by
  have h1 := copyB_spec cap W hTA hFR σ t a hT hA hF hR hcap
  have h2 := xorW_spec cap W hTB hFR (σ.sets T (frame (binary W a))) a b (BinW.numOn_sets_self σ T W a hT.2)
    (BinW.numOn_sets_ne hB (Ne.symm hTB) _) (by simp [hF]) (by simp [hR]) hcap
  rw [BinW.sets_sets] at h2
  have hab : a ^^^ b < 2 ^ W := Nat.xor_lt_two_pow ha hb
  have h3 := ltB_spec cap W hTM hFR (σ.sets T (frame (binary W (a ^^^ b)))) (a ^^^ b) (2 ^ P)
    (BinW.numOn_sets_self σ T W _ hT.2) (BinW.numOn_sets_ne hM (Ne.symm hTM) _) (by simp [hF]) (by simp [hR]) hab
    (Nat.pow_lt_pow_right (by norm_num) hPW) hcap
  rw [show decide (a ^^^ b < 2 ^ P) = decide (a / 2 ^ P = b / 2 ^ P) by simp only [xor_lt_iff]] at h3
  exact WExec.mono (WExec.seq h1 (WExec.seq h2 h3)) (by omega)

/-- `F := [a / 2^P = b / 2^P]` as a `WMX` instruction. -/
def keyEq (A B T MP : Fin (ns + 1)) (F R : Fin nr) : WMX ns nr := .wm (keyEqW A B T MP F R)

theorem keyEq_spec (cap W P : ℕ) {A B T MP : Fin (ns + 1)} {F R : Fin nr} (hTA : T ≠ A) (hTB : T ≠ B) (hTM : T ≠ MP)
    (hFR : F ≠ R) (σ : WState ns nr) (a b t : ℕ) (hA : NumOn σ A W a) (hB : NumOn σ B W b) (hT : NumOn σ T W t)
    (hM : NumOn σ MP W (2 ^ P)) (hF : σ.val F = 0) (hR : σ.val R = 0) (ha : a < 2 ^ W) (hb : b < 2 ^ W)
    (hPW : P < W) (hcap : 2 * W + 1 ≤ cap) :
    WXExec cap (keyEq A B T MP F R) σ ((σ.sets T (frame (binary W (a ^^^ b)))).setv F
      (decide (a / 2 ^ P = b / 2 ^ P)).toNat) (123 * W + 11) :=
  WXExec.wm (keyEqW_spec cap W P hTA hTB hTM hFR σ a b t hA hB hT hM hF hR ha hb hPW hcap)

/-- `A := a xor b`, `A := a and b` as `WMX` instructions. -/
def xorX (A B : Fin (ns + 1)) (F R : Fin nr) : WMX ns nr := .wm (xorW A B F R)
def andX (A B : Fin (ns + 1)) (F R : Fin nr) : WMX ns nr := .wm (andW A B F R)

/-! Programs are opaque to consumers: use the spec theorems. -/
attribute [irreducible] sortRecs xorW andW keyEqW keyEq

end NearCubicGates.Close.WordPrograms
