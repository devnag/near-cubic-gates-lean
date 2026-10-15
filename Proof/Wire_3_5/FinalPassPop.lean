import Proof.Wire_3_5.FinalPassWordMul

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Pop
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.FinalPass.Tm

/-! ## The reference -/

def cornerBit (sgn a b c d : Bool) : Bool :=
  let δ : ℤ := (if a then 1 else 0) - (if b then 1 else 0) - (if c then 1 else 0) + (if d then 1 else 0)
  if sgn then decide (δ = 1) else decide (δ = -1)

/-- The population bits: one residual bit per group of four corners. -/
def popBits (sgn : Bool) : List Bool → List Bool
  | a :: b :: c :: d :: rest => cornerBit sgn a b c d :: popBits sgn rest
  | _ => []

/-- The bit of one group, as a function of the list of its corners. -/
def popG (sgn : Bool) : List Bool → Bool
  | [a, b, c, d] => cornerBit sgn a b c d
  | _ => false

/-- The two cells written per group: the marker `m`, then `g` of the group. -/
def groupOut (m : Bool) (g : List Bool → Bool) : List Bool → List Bool
  | a :: b :: c :: d :: rest => m :: g [a, b, c, d] :: groupOut m g rest
  | _ => []

theorem groupOut_pop (sgn : Bool) : ∀ xs : List Bool, groupOut true (popG sgn) xs = frameP (popBits sgn xs)
  | a :: b :: c :: d :: rest => by simp [groupOut, popBits, popG, groupOut_pop sgn rest]
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | [_, _, _] => rfl

theorem groupOut_blank (g : List Bool → Bool) :
    ∀ (n : ℕ) (xs : List Bool), xs.length = 4 * n → groupOut false (fun _ => false) xs = List.replicate (2 * n) false
  | 0, xs, h => by
    obtain rfl : xs = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
    rfl
  | n + 1, a :: b :: c :: d :: rest, h => by
    have h' : rest.length = 4 * n := by simp at h; omega
    rw [groupOut, groupOut_blank g n rest h']
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega, List.replicate_succ, List.replicate_succ]
  | _ + 1, [], h => by simp at h
  | _ + 1, [_], h => by simp only [List.length_cons, List.length_nil] at h; omega
  | _ + 1, [_, _], h => by simp only [List.length_cons, List.length_nil] at h; omega
  | _ + 1, [_, _, _], h => by simp only [List.length_cons, List.length_nil] at h; omega

theorem popBits_length (sgn : Bool) :
    ∀ (n : ℕ) (xs : List Bool), xs.length = 4 * n → (popBits sgn xs).length = n
  | 0, xs, h => by
    obtain rfl : xs = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
    rfl
  | n + 1, a :: b :: c :: d :: rest, h => by
    have h' : rest.length = 4 * n := by simp at h; omega
    simp [popBits, popBits_length sgn n rest h']
  | _ + 1, [], h => by simp at h
  | _ + 1, [_], h => by simp only [List.length_cons, List.length_nil] at h; omega
  | _ + 1, [_, _], h => by simp only [List.length_cons, List.length_nil] at h; omega
  | _ + 1, [_, _, _], h => by simp only [List.length_cons, List.length_nil] at h; omega

/-! ## Cell lemmas -/

theorem writeTapeBit_mid1 (pre tail : List Bool) (a old v : Bool) :
    writeTapeBit (pre ++ a :: old :: tail) (pre.length + 1) v = pre ++ a :: v :: tail := by
  have h := writeTapeBit_mid' (pre ++ [a]) tail old v
  simpa using h

theorem readTapeBit_mid1 (pre tail : List Bool) (a b : Bool) :
    readTapeBit (pre ++ a :: b :: tail) (pre.length + 1) = b := by
  have h := readTapeBit_mid (pre ++ [a]) tail b
  simpa using h

variable {ns nr : ℕ} (cap : ℕ)

theorem wr_at (i : Fin (ns + 1)) (v : Bool) (σ : WState ns nr) (pre tail l : List Bool) (o : Bool)
    (hs : σ.st i = pre ++ o :: tail) (hh : σ.sh i = pre.length) (hl : pre ++ v :: tail = l) :
    WExec cap (.wr i v) σ (σ.sets i l) 1 := by
  have h := WExec.wr (cap := cap) i v σ
  rwa [hs, hh, writeTapeBit_mid', hl] at h

theorem fwd_to (i : Fin (ns + 1)) (σ : WState ns nr) (x : ℕ) (hx : σ.sh i + 1 = x) :
    WExec cap (.fwd i) σ (σ.seth i x) 1 := by
  rw [← hx]; exact WExec.fwd i σ

/-! ## Reading one group -/

/-- Read `k` bits of the framed word on `X` (head on a marker), branching on each, then write the marker `m` and the
bit `g` of the bits read on `Z`, and step `Z` past both cells. -/
def tree (X Z : Fin (ns + 1)) (m : Bool) (g : List Bool → Bool) : ℕ → List Bool → WM ns nr
  | 0, acc => .seq (.wr Z m) (.seq (.fwd Z) (.seq (.wr Z (g acc)) (.fwd Z)))
  | k + 1, acc => .seq (.fwd X) (.ifs X (.seq (.fwd X) (tree X Z m g k (acc ++ [true])))
      (.seq (.fwd X) (tree X Z m g k (acc ++ [false]))))

theorem tree_spec (X Z : Fin (ns + 1)) (hXZ : X ≠ Z) (m : Bool) (g : List Bool → Bool) (rest Q zr : List Bool)
    (z0 z1 : Bool) :
    ∀ (k : ℕ) (acc bs P : List Bool) (σ : WState ns nr), bs.length = k →
      σ.st X = P ++ frameP bs ++ rest → σ.sh X = P.length →
      σ.st Z = Q ++ z0 :: z1 :: zr → σ.sh Z = Q.length →
      ∃ τ, WExec cap (tree X Z m g k acc) σ τ (5 * k + 7) ∧ τ.st X = σ.st X ∧ τ.sh X = σ.sh X + 2 * k ∧
        τ.st Z = Q ++ m :: g (acc ++ bs) :: zr ∧ τ.sh Z = Q.length + 2 ∧
        WFrame (fun i => i = X ∨ i = Z) (fun _ => False) σ τ
  | 0, acc, bs, P, σ, hl, _, _, hZ, hhZ => by
    obtain rfl : bs = [] := List.eq_nil_of_length_eq_zero hl
    have s1 := wr_at cap Z m σ Q (z1 :: zr) (Q ++ m :: z1 :: zr) z0 hZ hhZ rfl
    have s2 := fwd_to cap Z (σ.sets Z (Q ++ m :: z1 :: zr)) (Q.length + 1) (by simp [hhZ])
    have s3 := wr_at cap Z (g acc) ((σ.sets Z (Q ++ m :: z1 :: zr)).seth Z (Q.length + 1)) (Q ++ [m]) zr
      (Q ++ m :: g acc :: zr) z1 (by simp) (by simp) (by simp)
    have s4 := fwd_to cap Z (((σ.sets Z (Q ++ m :: z1 :: zr)).seth Z (Q.length + 1)).sets Z (Q ++ m :: g acc :: zr))
      (Q.length + 2) (by simp)
    refine ⟨_, WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4)), ?_, ?_, ?_, ?_, ?_⟩
    · simp [Function.update_of_ne hXZ]
    · simp [Function.update_of_ne hXZ]
    · simp
    · simp
    · refine ⟨fun i hi => ?_, fun _ _ => rfl, rfl⟩
      have hiZ : i ≠ Z := fun h => hi (Or.inr h)
      simp [Function.update_of_ne hiZ]
  | k + 1, acc, bs, P, σ, hl, hX, hhX, hZ, hhZ => by
    obtain ⟨b, bs', rfl⟩ : ∃ b bs', bs = b :: bs' := by
      cases bs with
      | nil => simp at hl
      | cons b bs' => exact ⟨b, bs', rfl⟩
    have hl' : bs'.length = k := by simpa using hl
    have s1 := fwd_to cap X σ (P.length + 1) (by omega)
    have hb : wbit (σ.seth X (P.length + 1)) X = b := by
      unfold wbit
      simp only [WState.seth_st, WState.seth_sh, Function.update_self]
      rw [hX]
      have e : P ++ frameP (b :: bs') ++ rest = P ++ true :: b :: (frameP bs' ++ rest) := by simp
      rw [e, readTapeBit_mid1]
    have s2 := fwd_to cap X (σ.seth X (P.length + 1)) (P.length + 2) (by simp)
    obtain ⟨τ, hτ, h1, h2, h3, h4, h5⟩ := tree_spec X Z hXZ m g rest Q zr z0 z1 k (acc ++ [b]) bs' (P ++ [true, b])
      ((σ.seth X (P.length + 1)).seth X (P.length + 2)) hl' (by simp [hX]) (by simp)
      (by simp [hZ]) (by simp [Function.update_of_ne (Ne.symm hXZ), hhZ])
    refine ⟨τ, ?_, ?_, ?_, ?_, h4, ?_⟩
    · cases b
      · exact WExec.mono (WExec.seq s1 (WExec.ifsF hb (WExec.seq s2 hτ))) (by omega)
      · exact WExec.mono (WExec.seq s1 (WExec.ifsT hb (WExec.seq s2 hτ))) (by omega)
    · rw [h1]; simp
    · rw [h2]; simp; omega
    · rw [h3]; simp
    · exact ((frame_seth _ _ σ X _ (Or.inl rfl)).trans (frame_seth _ _ _ X _ (Or.inl rfl))).trans h5

/-! ## The group loop -/

/-- One group: branch on the sign cell `SG`, then read the four corners and write the two cells. -/
def popBody (X Z SG : Fin (ns + 1)) (m : Bool) (g : Bool → List Bool → Bool) : WM ns nr :=
  .ifs SG (tree X Z m (g true) 4 []) (tree X Z m (g false) 4 [])

/-- All groups, counted in `R`. -/
def groupLoop (X Z SG : Fin (ns + 1)) (R : Fin nr) (m : Bool) (g : Bool → List Bool → Bool) : WM ns nr :=
  .whs X (.seq (popBody X Z SG m g) (.inc R))

theorem popBody_spec (X Z SG : Fin (ns + 1)) (hXZ : X ≠ Z) (m : Bool) (g : Bool → List Bool → Bool) (sgn : Bool)
    (a b c d : Bool) (rest P Q zr : List Bool) (z0 z1 : Bool) (σ : WState ns nr)
    (hX : σ.st X = P ++ frameP [a, b, c, d] ++ rest) (hhX : σ.sh X = P.length)
    (hZ : σ.st Z = Q ++ z0 :: z1 :: zr) (hhZ : σ.sh Z = Q.length) (hsg : wbit σ SG = sgn) :
    ∃ τ, WExec cap (popBody X Z SG m g) σ τ 28 ∧ τ.st X = σ.st X ∧ τ.sh X = σ.sh X + 8 ∧
      τ.st Z = Q ++ m :: g sgn [a, b, c, d] :: zr ∧ τ.sh Z = Q.length + 2 ∧
      WFrame (fun i => i = X ∨ i = Z) (fun _ => False) σ τ := by
  obtain ⟨τ, hτ, h1, h2, h3, h4, h5⟩ :=
    tree_spec cap X Z hXZ m (g sgn) rest Q zr z0 z1 4 [] [a, b, c, d] P σ rfl hX hhX hZ hhZ
  refine ⟨τ, ?_, h1, h2, by simpa using h3, h4, h5⟩
  cases sgn
  · exact WExec.ifsF hsg hτ
  · exact WExec.ifsT hsg hτ

theorem groupLoop_spec (X Z SG : Fin (ns + 1)) (R : Fin nr) (hXZ : X ≠ Z) (hSX : SG ≠ X) (hSZ : SG ≠ Z)
    (m : Bool) (g : Bool → List Bool → Bool) (sgn : Bool) (rest : List Bool) :
    ∀ (n : ℕ) (xs P Q zr : List Bool) (σ : WState ns nr), xs.length = 4 * n →
      σ.st X = P ++ frameP xs ++ false :: rest → σ.sh X = P.length →
      σ.st Z = Q ++ zr → σ.sh Z = Q.length → 2 * n ≤ zr.length →
      wbit σ SG = sgn → σ.val R + n ≤ cap →
      ∃ τ, WExec cap (groupLoop X Z SG R m g) σ τ (34 * n + 1) ∧ τ.st X = σ.st X ∧ τ.sh X = σ.sh X + 8 * n ∧
        τ.st Z = Q ++ groupOut m (g sgn) xs ++ zr.drop (2 * n) ∧ τ.sh Z = Q.length + 2 * n ∧
        τ.val R = σ.val R + n ∧ WFrame (fun i => i = X ∨ i = Z) (fun r => r = R) σ τ
  | 0, xs, P, Q, zr, σ, hl, hX, hhX, hZ, hhZ, _, _, _ => by
    obtain rfl : xs = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    refine ⟨σ, WExec.whsF ?_, rfl, by simp, by simp [hZ, groupOut], by simp [hhZ], by simp, WFrame.refl _ _ σ⟩
    unfold wbit; rw [hX, hhX]; simpa using readTapeBit_mid P rest false
  | n + 1, xs, P, Q, zr, σ, hl, hX, hhX, hZ, hhZ, hzr, hsg, hR => by
    obtain ⟨a, b, c, d, xs', rfl⟩ : ∃ a b c d xs', xs = a :: b :: c :: d :: xs' := by
      match xs, hl with
      | a :: b :: c :: d :: xs', _ => exact ⟨a, b, c, d, xs', rfl⟩
      | [], h => simp only [List.length_nil] at h; omega
      | [_], h => simp only [List.length_cons, List.length_nil] at h; omega
      | [_, _], h => simp only [List.length_cons, List.length_nil] at h; omega
      | [_, _, _], h => simp only [List.length_cons, List.length_nil] at h; omega
    have hl' : xs'.length = 4 * n := by simp at hl; omega
    obtain ⟨z0, z1, zr', rfl⟩ : ∃ z0 z1 zr', zr = z0 :: z1 :: zr' := by
      match zr, hzr with
      | z0 :: z1 :: zr', _ => exact ⟨z0, z1, zr', rfl⟩
      | [], h => simp only [List.length_nil] at h; omega
      | [_], h => simp only [List.length_cons, List.length_nil] at h; omega
    have hzr' : 2 * n ≤ zr'.length := by simp at hzr; omega
    have hread0 : wbit σ X = true := by
      unfold wbit; rw [hX, hhX]
      simpa using readTapeBit_mid P (a :: (frameP [b, c, d] ++ frameP xs' ++ false :: rest)) true
    obtain ⟨τ1, e1, h1X, h1hX, h1Z, h1hZ, f1⟩ := popBody_spec cap X Z SG hXZ m g sgn a b c d
      (frameP xs' ++ false :: rest) P Q zr' z0 z1 σ (by rw [hX]; simp) hhX (by simpa using hZ) hhZ hsg
    have hR1 : τ1.val R = σ.val R := f1.2.1 R (fun h => h)
    have e2 := WExec.inc (cap := cap) R τ1 (by omega)
    have hsg2 : wbit (τ1.setv R (τ1.val R + 1)) SG = sgn := by
      have hf := f1.1 SG (by rintro (h | h) <;> contradiction)
      rw [← hsg]; unfold wbit; simp [hf.1, hf.2]
    obtain ⟨τ, e3, h3X, h3hX, h3Z, h3hZ, h3R, f3⟩ := groupLoop_spec X Z SG R hXZ hSX hSZ m g sgn rest n xs'
      (P ++ frameP [a, b, c, d]) (Q ++ [m, g sgn [a, b, c, d]]) zr' (τ1.setv R (τ1.val R + 1)) hl'
      (by simp [h1X, hX]) (by simp [h1hX, hhX]) (by simp [h1Z]) (by simp [h1hZ]) hzr' hsg2
      (by simp [hR1]; omega)
    refine ⟨τ, WExec.mono (WExec.whsT hread0 (WExec.seq e1 e2) e3) (by omega), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h3X]; simp [h1X]
    · rw [h3hX]; simp [h1hX]; omega
    · rw [h3Z]; simp [groupOut]
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega, List.drop_succ_cons, List.drop_succ_cons]
    · rw [h3hZ]; simp; omega
    · rw [h3R]; simp [hR1]; omega
    · exact (f1.mono (fun _ h => h) (fun _ h => h.elim)).trans
        ((frame_setv (fun i => i = X ∨ i = Z) (fun r => r = R) τ1 R _ rfl).trans f3)

/-! ## Returning the heads -/

/-- `k` steps back on stream `i`. -/
def bwdN (i : Fin (ns + 1)) : ℕ → WM ns nr
  | 0 => .skip
  | k + 1 => .seq (.bwd i) (bwdN i k)

theorem bwdN_spec (i : Fin (ns + 1)) :
    ∀ (k : ℕ) (σ : WState ns nr), WExec cap (bwdN i k) σ (σ.seth i (σ.sh i - k)) (2 * k)
  | 0, σ => WExec.cast cap (WExec.skip σ) (by rw [Nat.sub_zero, wseth_same]) le_rfl
  | k + 1, σ => by
    have h1 := WExec.bwd (cap := cap) i σ
    have h2 := bwdN_spec i k (σ.seth i (σ.sh i - 1))
    refine WExec.cast cap (WExec.seq h1 h2) ?_ (by omega)
    rw [wseth_seth]
    congr 1
    simp only [WState.seth_sh, Function.update_self]
    omega

/-- Return `Z` by two cells and `X` by eight cells per counted group. -/
def rewindXZ (X Z : Fin (ns + 1)) (R : Fin nr) : WM ns nr :=
  .whr R (.seq (.dec R) (.seq (bwdN Z 2) (bwdN X 8)))

theorem rewindXZ_spec (X Z : Fin (ns + 1)) (R : Fin nr) (hXZ : X ≠ Z) :
    ∀ (n : ℕ) (σ : WState ns nr), σ.val R = n → n ≤ cap →
      ∃ τ, WExec cap (rewindXZ X Z R) σ τ (25 * n + 1) ∧ τ.sh X = σ.sh X - 8 * n ∧ τ.sh Z = σ.sh Z - 2 * n ∧
        τ.val R = 0 ∧ τ.st = σ.st ∧ WFrame (fun i => i = X ∨ i = Z) (fun r => r = R) σ τ
  | 0, σ, h0, _ => ⟨σ, WExec.whrF h0, by simp, by simp, h0, rfl, WFrame.refl _ _ σ⟩
  | n + 1, σ, hn, hc => by
    have s1 := WExec.dec (cap := cap) R σ (by omega)
    have s2 := bwdN_spec cap Z 2 (σ.setv R (σ.val R - 1))
    have s3 := bwdN_spec cap X 8 ((σ.setv R (σ.val R - 1)).seth Z ((σ.setv R (σ.val R - 1)).sh Z - 2))
    obtain ⟨τ, hτ, h1, h2, h3, h4, h5⟩ := rewindXZ_spec X Z R hXZ n
      (((σ.setv R (σ.val R - 1)).seth Z ((σ.setv R (σ.val R - 1)).sh Z - 2)).seth X
        (((σ.setv R (σ.val R - 1)).seth Z ((σ.setv R (σ.val R - 1)).sh Z - 2)).sh X - 8)) (by simp [hn]) (by omega)
    refine ⟨τ, WExec.mono (WExec.whrT (by omega) (WExec.seq s1 (WExec.seq s2 s3)) hτ) (by omega), ?_, ?_, h3, ?_, ?_⟩
    · rw [h1]; simp [Function.update_of_ne hXZ]; omega
    · rw [h2]; simp [Function.update_of_ne (Ne.symm hXZ)]; omega
    · rw [h4]; simp
    · exact ((((frame_setv (fun i => i = X ∨ i = Z) (fun r => r = R) σ R _ rfl).trans (frame_seth _ _ _ Z _ (Or.inr rfl))).trans
        (frame_seth _ _ _ X _ (Or.inl rfl)))).trans h5

/-! ## The pass -/

/-- **The stage-3 pass**: all groups, then return the heads. -/
def pass (X Z SG : Fin (ns + 1)) (R : Fin nr) (m : Bool) (g : Bool → List Bool → Bool) : WM ns nr :=
  .seq (groupLoop X Z SG R m g) (rewindXZ X Z R)

/-- The step bound of one pass over `n` groups. -/
def passCost (n : ℕ) : ℕ := 59 * n + 3

theorem pass_spec (X Z SG : Fin (ns + 1)) (R : Fin nr) (hXZ : X ≠ Z) (hSX : SG ≠ X) (hSZ : SG ≠ Z)
    (m : Bool) (g : Bool → List Bool → Bool) (sgn : Bool) (n : ℕ) (xs restX zold : List Bool) (σ : WState ns nr)
    (hl : xs.length = 4 * n) (hX : σ.st X = frameP xs ++ false :: restX) (hhX : σ.sh X = 0)
    (hZ : σ.st Z = zold) (hhZ : σ.sh Z = 0) (hz : 2 * n ≤ zold.length) (hsg : wbit σ SG = sgn)
    (hR : σ.val R = 0) (hc : n ≤ cap) :
    WExec cap (pass X Z SG R m g) σ (σ.sets Z (groupOut m (g sgn) xs ++ zold.drop (2 * n))) (passCost n) := by
  obtain ⟨τ1, e1, h1X, h1hX, h1Z, h1hZ, h1R, f1⟩ := groupLoop_spec cap X Z SG R hXZ hSX hSZ m g sgn restX n xs [] []
    zold σ hl (by simpa using hX) (by simpa using hhX) (by simpa using hZ) (by simpa using hhZ) hz hsg (by omega)
  obtain ⟨τ2, e2, h2X, h2Z, h2R, h2st, f2⟩ := rewindXZ_spec cap X Z R hXZ n τ1 (by omega) hc
  refine WExec.cast cap (WExec.seq e1 e2) ?_ (by unfold passCost; omega)
  refine WState.eq ?_ ?_ ?_ ?_
  · funext j
    simp only [WState.sets_sh]
    by_cases hjX : j = X
    · subst hjX; rw [h2X, h1hX, hhX]; omega
    · by_cases hjZ : j = Z
      · subst hjZ; rw [h2Z, h1hZ, hhZ]; simp
      · have hj : ¬ (j = X ∨ j = Z) := by rintro (h | h) <;> contradiction
        rw [(f2.1 j hj).2, (f1.1 j hj).2]
  · funext j
    rw [h2st]
    simp only [WState.sets_st, Function.update_apply]
    by_cases hjZ : j = Z
    · subst hjZ; simp [h1Z]
    · rw [if_neg hjZ]
      by_cases hjX : j = X
      · subst hjX; exact h1X
      · have hj : ¬ (j = X ∨ j = Z) := by rintro (h | h) <;> contradiction
        exact (f1.1 j hj).1
  · funext r
    simp only [WState.sets_val]
    by_cases hr : r = R
    · subst hr; rw [h2R, hR]
    · rw [f2.2.1 r hr, f1.2.1 r hr]
  · simp only [WState.sets_cell]; rw [f2.2.2, f1.2.2]

/-- Write the population bits. -/
def pop (X Z SG : Fin (ns + 1)) (R : Fin nr) : WM ns nr := pass X Z SG R true popG

/-- Blank the scratch again. -/
def blankOut (X Z SG : Fin (ns + 1)) (R : Fin nr) : WM ns nr := pass X Z SG R false (fun _ _ => false)

theorem pop_spec (X Z SG : Fin (ns + 1)) (R : Fin nr) (hXZ : X ≠ Z) (hSX : SG ≠ X) (hSZ : SG ≠ Z)
    (sgn : Bool) (n : ℕ) (xs restX zold : List Bool) (σ : WState ns nr)
    (hl : xs.length = 4 * n) (hX : σ.st X = frameP xs ++ false :: restX) (hhX : σ.sh X = 0)
    (hZ : σ.st Z = zold) (hhZ : σ.sh Z = 0) (hz : 2 * n ≤ zold.length) (hsg : wbit σ SG = sgn)
    (hR : σ.val R = 0) (hc : n ≤ cap) :
    WExec cap (pop X Z SG R) σ (σ.sets Z (frameP (popBits sgn xs) ++ zold.drop (2 * n))) (passCost n) := by
  have h := pass_spec cap X Z SG R hXZ hSX hSZ true popG sgn n xs restX zold σ hl hX hhX hZ hhZ hz hsg hR hc
  rwa [groupOut_pop] at h

theorem blank_spec (X Z SG : Fin (ns + 1)) (R : Fin nr) (hXZ : X ≠ Z) (hSX : SG ≠ X) (hSZ : SG ≠ Z)
    (sgn : Bool) (n : ℕ) (xs restX zold : List Bool) (σ : WState ns nr)
    (hl : xs.length = 4 * n) (hX : σ.st X = frameP xs ++ false :: restX) (hhX : σ.sh X = 0)
    (hZ : σ.st Z = zold) (hhZ : σ.sh Z = 0) (hz : 2 * n ≤ zold.length) (hsg : wbit σ SG = sgn)
    (hR : σ.val R = 0) (hc : n ≤ cap) :
    WExec cap (blankOut X Z SG R) σ (σ.sets Z (List.replicate (2 * n) false ++ zold.drop (2 * n))) (passCost n) := by
  have h := pass_spec cap X Z SG R hXZ hSX hSZ false (fun _ _ => false) sgn n xs restX zold σ hl hX hhX hZ hhZ hz
    hsg hR hc
  rwa [groupOut_blank (fun _ => false) n xs hl] at h

/-- The scratch after `pop` then `blankOut` is blank again. -/
theorem blank_restore (n c : ℕ) (w : List Bool) (hw : w.length = 2 * n) (hc : 2 * n ≤ c) :
    List.replicate (2 * n) false ++ (w ++ (List.replicate c false).drop (2 * n)).drop (2 * n) =
      List.replicate c false := by
  rw [List.drop_append_of_le_length (by omega), List.drop_eq_nil_of_le (by omega), List.nil_append,
    List.drop_replicate, List.replicate_append_replicate, Nat.add_sub_cancel' hc]

/-! ## The standalone block -/

/-- Streams of the standalone block: `0` the point, `1` the scratch, `2` the sign cell; one register. -/
abbrev S3 := WState 2 1

/-- **The stage-3 machine**. -/
def stage3Machine : Machine (2 + 3) (pop (ns := 2) (nr := 1) 0 1 2 0).toProg.size :=
  (pop (ns := 2) (nr := 1) 0 1 2 0).toProg.compile

/-- The input data: a blank scratch of capacity `c + 1`, the sign cell, one blank register. -/
def stage3In (sgn : Bool) (c : ℕ) : Fin 3 → List Bool := ![List.replicate (c + 1) false, [sgn], regTape c 0]

/-- The output data: the population bits on the scratch. -/
def stage3Out (sgn : Bool) (c : ℕ) (X : List Bool) : Fin 3 → List Bool :=
  ![frameP (popBits sgn X) ++ (List.replicate (c + 1) false).drop (2 * (X.length / 4)), [sgn], regTape c 0]

/-- **Stage 3** (corners in, population bits out): from the framed corners of `L` occurrences on tape 0, the
scratch (tape 2) receives `frameP (popBits sgn X)`; every head returns to `0`, every other tape is unchanged. -/
theorem stage3_step (sgn : Bool) (c L : ℕ) (hc : 2 * L ≤ c) (X : List Bool) (b : Bool) (hX : X.length = 4 * L) :
    Step stage3Machine (passCost L) (fun _ => 0) (Fin.addCases (m := 2) (n := 3) ![frame X, [b]] (stage3In sgn c))
      (fun _ => 0) (Fin.addCases (m := 2) (n := 3) ![frame X, [b]] (stage3Out sgn c X)) := by
  let σ : S3 := ⟨fun _ => 0, ![frame X, List.replicate (c + 1) false, [sgn]], fun _ => 0, b⟩
  have h := pop_spec c 0 1 2 0 (by decide) (by decide) (by decide) sgn L X [] (List.replicate (c + 1) false) σ hX
    (by simp [σ, frame_eq_frameP]) rfl rfl rfl (by simp; omega) rfl rfl (by omega)
  have hs := (WExec.exec c h).step
  have hq : X.length / 4 = L := by omega
  refine Step.congr (Step.congr_in hs ?_ ?_) ?_ ?_
  · funext j; simp only [wenc]; split <;> rfl
  · funext j; fin_cases j <;> rfl
  · funext j; simp only [wenc]; split <;> rfl
  · funext j; fin_cases j <;> simp [wenc, stage3Out, hq, σ, role] <;> rfl

end NearCubicWires.WireExponent3_5.FinalPass.Pop
