import Proof.Wire_3_5.PrimAsmPopBlockW

/-! # PA (d)-SYM, part 8: the POP record, written (Route B)

The POP row's input word `frame (popRowRec walkLen θ R Lg cap (oneWC P s) (popStates …))` as the emission schedule
`PopRec.popEmit_eq`: the setup fields, the constant term, the states (each: marker, coefficient, the visits' blocks, the
store's end), the end. The table stream carries C5's `flatTable` (per visit: marker, rows of levels `J, …, 0`).

* `visitsW`/**`visitsW_spec`**: all visits of one state (loop counter `60`);
* `stateW`/**`stateW_spec`**: one state (then the table stream rewound to its start by `58`).

Paper quantity of the main type: the POP record's states `stateE c (visits' blocks)` (`PopRec.stateRec_marks`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.PopRecW
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec NearCubicWires.WireExponent3_5.PrimAsm.Emit
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRecW NearCubicWires.WireExponent3_5.PrimAsm.PopRec
open NearCubicWires.WireExponent3_5.PrimAsm.LevelW NearCubicWires.WireExponent3_5.PrimAsm.LevelWordW
open NearCubicWires.WireExponent3_5.PrimAsm.PopBlockW

variable {ns nr : ℕ} (cap : ℕ)

theorem blockRegs_setv {X : PReg nr} {τ : WState ns nr} {Lp d r4 G off Lg Sv J M L s' c VW : ℕ} {sgn : Bool}
    (hB : BlockRegs X τ Lp d r4 G off Lg Sv J M L s' c VW sgn) (t : Fin 64)
    (ht : (58 ≤ t.val ∧ t.val ≤ 60) ∨ t.val = 63) (x : ℕ) :
    BlockRegs X (τ.setv (X t) x) Lp d r4 G off Lg Sv J M L s' c VW sgn :=
  hB.of_val fun i h1 h2 => wsetv_val_ne _ _ (X.injective.ne (Fin.ne_of_val_ne (by omega)))

theorem flatMap_range_length (f : ℕ → List Bool) (V : ℕ) :
    ∀ m, (∀ k < m, (f k).length = V) → ((List.range m).flatMap f).length = m * V
  | 0, _ => by simp
  | m + 1, h => by
    rw [List.range_succ, List.flatMap_append, List.length_append, flatMap_range_length f V m (fun k hk => h k (by omega))]
    simp [h m (by omega)]
    ring

theorem getD_cons_succ' (b : Bool) (w : List Bool) (i : ℕ) : (b :: w).getD (1 + i) false = w.getD i false := by
  rw [Nat.add_comm]; rfl

theorem levelE_length_eq (M Sv J L : ℕ) (rowF rowG : ℕ → List Bool) (hF : ∀ j ≤ J, (rowF j).length = L)
    (hG : ∀ j ≤ J, (rowG j).length = L) : (levelE M Sv J rowF).length = (levelE M Sv J rowG).length := by
  unfold levelE
  simp only [List.length_append, List.length_flatMap]
  congr 2
  refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
  have hjJ : j ≤ J := by
    unfold FinalPass.ListEval.levels at hj
    simp only [List.mem_reverse, List.mem_range] at hj
    omega
  rw [levelRecE_length, levelRecE_length, hF j hjJ, hG j hjJ]

/-! ## All visits of a state -/

section Visits
variable (O S : Fin (ns + 1)) (X : PReg nr)

/-- **All visits of one state** (`52 = walkLen` visits, counter `60`). -/
def visitsW : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (X 52) (X 60) (X 62))
  (.whr (X 60) (.seq (.dec (X 60)) (visitW O S X)))

/-- The visits' blocks, emitted. -/
def visitsE (n Lp d r4 G off Lg Sv J M s' c : ℕ) (sgn : Bool) (rowK : ℕ → ℕ → List Bool) : List Bool :=
  (List.range n).flatMap fun k =>
    blockE Lp d (labSum (sliceLabs r4 G off Lg)) (sliceLabs r4 G off Lg) (levelE M Sv J (rowK k)) s' sgn c true ++
    blockE Lp d (labSum (sliceLabs r4 G off Lg)) (sliceLabs r4 G off Lg) (levelE M Sv J (rowK k)) s' sgn c false

/-- The table stream's visit words. -/
def tableW (n J : ℕ) (rowK : ℕ → ℕ → List Bool) : List Bool :=
  (List.range n).flatMap fun k => true :: (FinalPass.ListEval.levels J).flatMap fun j => frame (rowK k j)

/-- A bound on one state's visits' cost. -/
def visitsBound (cap n J M s c Lp d r4 G off Lg : ℕ) : ℕ :=
  n * (2 * blockBound cap J M s c Lp d r4 G off Lg + 30 * cap + 24) + 18 * n + 10

theorem visitsW_spec (hOS : O ≠ S) (τ : WState ns nr) (n Lp d r4 G off Lg Sv J M L s' c : ℕ)
    (sgn : Bool) (hB : BlockRegs X τ Lp d r4 G off Lg Sv J M L s' c ((J + 1) * (2 * L + 1)) sgn)
    (h52 : τ.val (X 52) = n) (h60 : τ.val (X 60) = 0) (Mlab : ℕ) (hM : off + Lg + (r4 + 4) * G ≤ Mlab)
    (rowK : ℕ → ℕ → List Bool) (hrows : ∀ k < n, ∀ j ≤ J, (rowK k j).length = L)
    (ho : τ.sh O = (τ.st O).length)
    (hS : ∀ i < (tableW n J rowK).length, readTapeBit (τ.st S) (τ.sh S + i) = (tableW n J rowK).getD i false)
    (hcap : lvCap Sv J J ≤ cap) (hJc : J + 1 ≤ cap) (hLc : L ≤ cap) (hMc : M ≤ cap) (hsc : s' ≤ cap)
    (hcc : c + 1 ≤ cap) (hVc : (J + 1) * (2 * L + 1) ≤ cap) (hnc : n ≤ cap)
    (hbig : τ.val (X 0) + (visitsE n Lp d r4 G off Lg Sv J M s' c sgn rowK).length + 2 + labCapA Lp d +
      (pieceA Lp d).length + labCapB r4 G off Lg Mlab ≤ cap) :
    ∃ m, WExec cap (visitsW O S X) τ
      (lSt O S (X 0) τ (visitsE n Lp d r4 G off Lg Sv J M s' c sgn rowK)
        (τ.sh S + n * (1 + (J + 1) * (2 * L + 1)))) m ∧
      m ≤ visitsBound cap n J M s' c Lp d r4 G off Lg := by
  have hne : ∀ {i k : Fin 64}, i ≠ k → X i ≠ X k := fun h => X.injective.ne h
  have n0 : ∀ i : Fin 64, i ≠ 0 → X i ≠ X 0 := fun i h => hne h
  obtain ⟨VW, hVW⟩ : ∃ x, x = (J + 1) * (2 * L + 1) := ⟨_, rfl⟩
  rw [← hVW] at hB hVc ⊢
  obtain ⟨vE, hvE⟩ : ∃ f : ℕ → List Bool, f = fun k =>
      blockE Lp d (labSum (sliceLabs r4 G off Lg)) (sliceLabs r4 G off Lg) (levelE M Sv J (rowK k)) s' sgn c true ++
      blockE Lp d (labSum (sliceLabs r4 G off Lg)) (sliceLabs r4 G off Lg) (levelE M Sv J (rowK k)) s' sgn c false :=
    ⟨_, rfl⟩
  have hvEk : ∀ k, vE k =
      blockE Lp d (labSum (sliceLabs r4 G off Lg)) (sliceLabs r4 G off Lg) (levelE M Sv J (rowK k)) s' sgn c true ++
      blockE Lp d (labSum (sliceLabs r4 G off Lg)) (sliceLabs r4 G off Lg) (levelE M Sv J (rowK k)) s' sgn c false := by
    intro k; rw [hvE]
  have hvEdef : visitsE n Lp d r4 G off Lg Sv J M s' c sgn rowK = (List.range n).flatMap vE := by rw [hvE]; rfl
  rw [hvEdef] at hbig ⊢
  have hlenV : ∀ k < n, (vE k).length = (vE 0).length := by
    intro k hk
    rw [hvEk, hvEk]
    simp only [List.length_append, blockE_length, pieceP_length]
    rw [levelE_length_eq M Sv J L (rowK k) (rowK 0) (hrows k hk) (hrows 0 (by omega))]
  have hwk : ∀ k < n, (true :: (FinalPass.ListEval.levels J).flatMap fun j => frame (rowK k j)).length = 1 + VW := by
    intro k hk
    rw [List.length_cons, List.length_flatMap]
    have : ∀ a ∈ FinalPass.ListEval.levels J, (frame (rowK k a)).length = 2 * L + 1 := by
      intro a ha
      have haJ : a ≤ J := by
        unfold FinalPass.ListEval.levels at ha
        simp only [List.mem_reverse, List.mem_range] at ha
        omega
      rw [frame_length, hrows k hk a haJ]
    rw [List.map_congr_left this, List.map_const', List.sum_replicate, levels_length, hVW]
    simp; ring
  have e1 := FinalPass.Hash4.wcopyR_spec cap (X 52) (X 60) (X 62) (hne (by decide)) (hne (by decide))
    (hne (by decide)) τ h60 hB.h62 (by omega)
  rw [h52] at e1
  let S' : ℕ → WState ns nr := fun k =>
    lSt O S (X 0) (τ.setv (X 60) (n - k)) ((List.range k).flatMap vE) (τ.sh S + k * (1 + VW))
  have hS'0 : S' 0 = τ.setv (X 60) n := by
    simp only [S', List.range_zero, List.flatMap_nil, Nat.zero_mul, Nat.add_zero, Nat.sub_zero]
    exact lSt_nil _
  have hloop := UnionMachine.Round.wloop cap (X 60) (visitW O S X)
    (2 * blockBound cap J M s' c Lp d r4 G off Lg + 30 * cap + 20) n S'
    (fun k _ => by simp only [S']; rw [lSt_val_ne (n0 60 (by decide))]; simp)
    hnc
    (fun k hk => by
      have hτS : (S' k).setv (X 60) (n - k - 1) =
          lSt O S (X 0) (τ.setv (X 60) (n - k - 1)) ((List.range k).flatMap vE) (τ.sh S + k * (1 + VW)) := by
        simp only [S']
        rw [lSt_setv _ _ _ _ (n0 60 (by decide)), wsetv_setv]
      rw [hτS]
      have hpre : ((List.range k).flatMap vE).length = k * (vE 0).length :=
        flatMap_range_length vE _ k (fun i hi => hlenV i (by omega))
      have htot : ((List.range n).flatMap vE).length = n * (vE 0).length := flatMap_range_length vE _ n hlenV
      have hkn : (k + 1) * (vE 0).length ≤ n * (vE 0).length := Nat.mul_le_mul_right _ (by omega)
      have hvk := hlenV k hk
      have hlk : (blockE Lp d (labSum (sliceLabs r4 G off Lg)) (sliceLabs r4 G off Lg) (levelE M Sv J (rowK k)) s' sgn c
          true).length ≤ (vE k).length := by simp only [hvE, List.length_append]; omega
      have hk1 : (k + 1) * (vE 0).length = k * (vE 0).length + (vE 0).length := by ring
      have hv0 : (lSt O S (X 0) (τ.setv (X 60) (n - k - 1)) ((List.range k).flatMap vE)
          (τ.sh S + k * (1 + VW))).val (X 0) = τ.val (X 0) + k * (vE 0).length := by
        rw [lSt_val_self, wsetv_val_ne _ _ (n0 60 (by decide)).symm, hpre]
      have hTk : (blockE Lp d (labSum (sliceLabs r4 G off Lg)) (sliceLabs r4 G off Lg) (levelE M Sv J (rowK k)) s' sgn c
          true).length + (blockE Lp d (labSum (sliceLabs r4 G off Lg)) (sliceLabs r4 G off Lg) (levelE M Sv J (rowK k)) s'
          sgn c false).length = (vE 0).length := by
        rw [← hvk, hvEk, List.length_append]
      obtain ⟨m, em, bm⟩ := visitW_spec cap O S X hOS
        (lSt O S (X 0) (τ.setv (X 60) (n - k - 1)) ((List.range k).flatMap vE) (τ.sh S + k * (1 + VW)))
        Lp d r4 G off Lg Sv J M L s' c sgn (by rw [← hVW]; exact (blockRegs_setv hB 60 (by decide) _).lSt _ _) Mlab hM
        (rowK k) (hrows k hk) (lSt_ho hOS _ (by simp [ho]) _ _)
        (fun i hi => by
          rw [lSt_stS hOS, lSt_shS]
          change readTapeBit (τ.st S) (τ.sh S + k * (1 + VW) + 1 + i) = _
          have hidx : k * (1 + VW) + (1 + i) < (tableW n J rowK).length := by
            unfold tableW
            rw [flatMap_range_length _ (1 + VW) n hwk]
            have h1 := hwk k hk
            rw [List.length_cons] at h1
            have : k * (1 + VW) + (1 + VW) ≤ n * (1 + VW) := by
              rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
            omega
          have h1 := hS _ hidx
          unfold tableW at h1
          rw [getD_flatMap_block _ (1 + VW) (List.range n) (fun a ha => hwk a (List.mem_range.mp ha)) k
            (by simp; exact hk) (1 + i) (by have := hwk k hk; rw [List.length_cons] at this; omega),
            List.getElem_range, getD_cons_succ'] at h1
          rw [← h1]
          congr 1
          omega)
        hcap hJc hLc hMc hsc hcc (by rw [← hVW]; exact hVc)
        (by rw [hv0]; omega) (by rw [hv0]; omega) (by rw [hv0, List.length_append]; omega)
      rw [lSt_lSt hOS, lSt_shS, ← hVW] at em
      refine WExec.mono (WExec.cast cap em ?_ le_rfl) bm
      simp only [S']
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, hvEk k, show n - k - 1 = n - (k + 1) by omega,
        show τ.sh S + k * (1 + VW) + 1 + VW = τ.sh S + (k + 1) * (1 + VW) by ring])
  rw [hS'0] at hloop
  simp only [S', Nat.sub_self] at hloop
  refine ⟨_, WExec.cast cap (WExec.seq e1 hloop) ?_ le_rfl, ?_⟩
  · rw [setv_eq_self h60]
  · unfold visitsBound
    generalize blockBound cap J M s' c Lp d r4 G off Lg = BB
    have : n * (2 * BB + 30 * cap + 20 + 4) ≤ n * (2 * BB + 30 * cap + 24) := le_refl _
    omega

end Visits

theorem blockRegs_s {X : PReg nr} {τ : WState ns nr} {Lp d r4 G off Lg Sv J M L s' c VW : ℕ} {sgn : Bool}
    (hB : BlockRegs X τ Lp d r4 G off Lg Sv J M L s' c VW sgn) (x : ℕ) :
    BlockRegs X (τ.setv (X 49) x) Lp d r4 G off Lg Sv J M L x c VW sgn := by
  have hv : ∀ i : Fin 64, i ≠ 49 → (τ.setv (X 49) x).val (X i) = τ.val (X i) :=
    fun i hi => wsetv_val_ne _ _ (X.injective.ne hi)
  exact
  { h1 := by rw [hv 1 (by decide)]; exact hB.h1
    h2 := by rw [hv 2 (by decide)]; exact hB.h2
    h3 := by rw [hv 3 (by decide)]; exact hB.h3
    h4 := by rw [hv 4 (by decide)]; exact hB.h4
    h13 := by rw [hv 13 (by decide)]; exact hB.h13
    h14 := by rw [hv 14 (by decide)]; exact hB.h14
    h19 := by rw [hv 19 (by decide)]; exact hB.h19
    h20 := by rw [hv 20 (by decide)]; exact hB.h20
    h21 := by rw [hv 21 (by decide)]; exact hB.h21
    h44 := by rw [hv 44 (by decide)]; exact hB.h44
    h45 := by rw [hv 45 (by decide)]; exact hB.h45
    h46 := by rw [hv 46 (by decide)]; exact hB.h46
    h47 := by rw [hv 47 (by decide)]; exact hB.h47
    h48 := by rw [hv 48 (by decide)]; exact hB.h48
    h50 := by rw [hv 50 (by decide)]; exact hB.h50
    h51 := by rw [hv 51 (by decide)]; exact hB.h51
    h57 := by rw [hv 57 (by decide)]; exact hB.h57
    h61 := by rw [hv 61 (by decide)]; exact hB.h61
    h62 := by rw [hv 62 (by decide)]; exact hB.h62
    hz1 := fun i h5 h12 => by rw [hv i (Fin.ne_of_val_ne (by show i.val ≠ 49; omega))]; exact hB.hz1 i h5 h12
    hz2 := fun i h5 h12 => by rw [hv i (Fin.ne_of_val_ne (by show i.val ≠ 49; omega))]; exact hB.hz2 i h5 h12
    h49 := by simp }

theorem flatMap_range_mono (f : ℕ → List Bool) (a : ℕ) :
    ∀ b, a ≤ b → ((List.range a).flatMap f).length ≤ ((List.range b).flatMap f).length
  | 0, h => by rw [Nat.le_zero.mp h]
  | b + 1, h => by
    rcases Nat.lt_or_ge a (b + 1) with h1 | h1
    · have := flatMap_range_mono f a b (by omega)
      rw [List.range_succ, List.flatMap_append, List.length_append]
      omega
    · rw [show a = b + 1 by omega]

/-! ## One state -/

section State
variable (O S : Fin (ns + 1)) (X : PReg nr)

/-- **One state**: its marker and coefficient (the constant `cw`), its visits' blocks, the store's end; then the table
stream rewound to its start (`58`). -/
def stateW (cw : List Bool) : WM ns nr :=
  .seq (emitW O (X 0) ([true, true] ++ (cw ++ [true, false])))
  (.seq (visitsW O S X)
  (.seq (emitW O (X 0) [true, false])
  (.seq (FinalPass.Hash4.wcopyR (X 58) (X 61) (X 62))
  (WM.rewind S (X 61)))))

/-- A state, emitted from its coefficient word. -/
def stateEw (cw blks : List Bool) : List Bool := [true, true] ++ ((cw ++ [true, false]) ++ (blks ++ [true, false]))

/-- A bound on one state's cost. -/
def stateBound (cap n J M s c Lp d r4 G off Lg cwl : ℕ) : ℕ :=
  visitsBound cap n J M s c Lp d r4 G off Lg + 8 * cwl + 30 * cap + 100

theorem stateW_spec (hOS : O ≠ S) (cw : List Bool) (τ : WState ns nr) (n Lp d r4 G off Lg Sv J M L s' c : ℕ)
    (sgn : Bool) (hB : BlockRegs X τ Lp d r4 G off Lg Sv J M L s' c ((J + 1) * (2 * L + 1)) sgn)
    (h52 : τ.val (X 52) = n) (h58 : τ.val (X 58) = n * (1 + (J + 1) * (2 * L + 1))) (h60 : τ.val (X 60) = 0)
    (Mlab : ℕ) (hM : off + Lg + (r4 + 4) * G ≤ Mlab)
    (rowK : ℕ → ℕ → List Bool) (hrows : ∀ k < n, ∀ j ≤ J, (rowK k j).length = L)
    (ho : τ.sh O = (τ.st O).length)
    (hS : ∀ i < (tableW n J rowK).length, readTapeBit (τ.st S) (τ.sh S + i) = (tableW n J rowK).getD i false)
    (hcap : lvCap Sv J J ≤ cap) (hJc : J + 1 ≤ cap) (hLc : L ≤ cap) (hMc : M ≤ cap) (hsc : s' ≤ cap)
    (hcc : c + 1 ≤ cap) (hVc : (J + 1) * (2 * L + 1) ≤ cap) (hnc : n ≤ cap)
    (hTc : n * (1 + (J + 1) * (2 * L + 1)) ≤ cap)
    (hbig : τ.val (X 0) + (stateEw cw (visitsE n Lp d r4 G off Lg Sv J M s' c sgn rowK)).length + 2 + labCapA Lp d +
      (pieceA Lp d).length + labCapB r4 G off Lg Mlab ≤ cap) :
    ∃ m, WExec cap (stateW O S X cw) τ
      (lSt O S (X 0) τ (stateEw cw (visitsE n Lp d r4 G off Lg Sv J M s' c sgn rowK)) (τ.sh S)) m ∧
      m ≤ stateBound cap n J M s' c Lp d r4 G off Lg cw.length := by
  have hne : ∀ {i k : Fin 64}, i ≠ k → X i ≠ X k := fun h => X.injective.ne h
  have n0 : ∀ i : Fin 64, i ≠ 0 → X i ≠ X 0 := fun i h => hne h
  obtain ⟨vs, hvs⟩ : ∃ x, x = visitsE n Lp d r4 G off Lg Sv J M s' c sgn rowK := ⟨_, rfl⟩
  rw [← hvs] at hbig ⊢
  have hlS : (stateEw cw vs).length = 2 + (cw.length + 2) + (vs.length + 2) := by
    unfold stateEw; simp only [List.length_append, List.length_cons, List.length_nil]; omega
  rw [hlS] at hbig
  obtain ⟨TW, hTW⟩ : ∃ x, x = n * (1 + (J + 1) * (2 * L + 1)) := ⟨_, rfl⟩
  rw [← hTW] at h58 hTc
  have e1 := emitW_spec cap O (X 0) ([true, true] ++ (cw ++ [true, false])) τ ho
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  rw [← lSt_self (S := S) hOS] at e1
  have hl1 : ([true, true] ++ (cw ++ [true, false])).length = cw.length + 4 := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  obtain ⟨m2, e2, b2⟩ := visitsW_spec cap O S X hOS (lSt O S (X 0) τ ([true, true] ++ (cw ++ [true, false])) (τ.sh S)) n Lp d r4 G off Lg Sv J M L s' c sgn
    (hB.lSt _ _) (by rw [lSt_val_ne (n0 52 (by decide))]; exact h52) (by rw [lSt_val_ne (n0 60 (by decide))]; exact h60)
    Mlab hM rowK hrows (lSt_ho hOS τ ho _ _) (by rw [lSt_stS hOS, lSt_shS]; exact hS) hcap hJc hLc hMc hsc hcc hVc hnc
    (by rw [lSt_val_self, ← hvs, hl1]; omega)
  rw [lSt_lSt hOS, lSt_shS, ← hvs, ← hTW] at e2
  have e3 := emitW_spec cap O (X 0) [true, false] (lSt O S (X 0) τ ([true, true] ++ (cw ++ [true, false]) ++ vs) (τ.sh S + TW)) (lSt_ho hOS τ ho _ _)
    (by rw [lSt_val_self, List.length_append, hl1]; simp only [List.length_cons, List.length_nil]; omega)
  rw [lSt_append hOS] at e3
  have e4 := FinalPass.Hash4.wcopyR_spec cap (X 58) (X 61) (X 62) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (lSt O S (X 0) τ ([true, true] ++ (cw ++ [true, false]) ++ vs ++ [true, false]) (τ.sh S + TW))
    (by rw [lSt_val_ne (n0 61 (by decide))]; exact hB.h61) (by rw [lSt_val_ne (n0 62 (by decide))]; exact hB.h62)
    (by rw [lSt_val_ne (n0 58 (by decide)), h58]; exact hTc)
  rw [lSt_val_ne (n0 58 (by decide)), h58, lSt_setv _ _ _ _ (n0 61 (by decide))] at e4
  have e5 := wrewind_spec cap S (X 61) TW (lSt O S (X 0) (τ.setv (X 61) TW) ([true, true] ++ (cw ++ [true, false]) ++ vs ++ [true, false]) (τ.sh S + TW))
    (by rw [lSt_val_ne (n0 61 (by decide))]; simp) (by rw [lSt_val_ne (n0 61 (by decide))]; simp; exact hTc)
  rw [lSt_setv _ _ _ _ (n0 61 (by decide)), lSt_seth, lSt_shS, wsetv_setv, setv_eq_self hB.h61,
    show τ.sh S + TW - TW = τ.sh S by omega] at e5
  refine ⟨_, WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5)))) ?_ le_rfl, ?_⟩
  · unfold stateEw; simp only [List.append_assoc]
  · unfold stateBound
    generalize visitsBound cap n J M s' c Lp d r4 G off Lg = VB at b2 ⊢
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

end State

theorem stateBound_mono (cap n J M s s' c Lp d r4 G off Lg cwl cwl' : ℕ) (hs : s ≤ s') (hw : cwl ≤ cwl') :
    stateBound cap n J M s c Lp d r4 G off Lg cwl ≤ stateBound cap n J M s' c Lp d r4 G off Lg cwl' := by
  unfold stateBound visitsBound blockBound dataBound
  gcongr

/-! ## The population's states -/

/-- The states, emitted: `s` itself with coefficient word `cwP`, or `1, …, M` with `cwN` when `s = 0`. -/
def statesAbs (s n Lp d r4 G off Lg Sv J M c : ℕ) (sgn : Bool) (rowK : ℕ → ℕ → List Bool) (cwP cwN : List Bool) :
    List Bool :=
  if s = 0 then (List.range M).flatMap fun i => stateEw cwN (visitsE n Lp d r4 G off Lg Sv J M (i + 1) c sgn rowK)
  else stateEw cwP (visitsE n Lp d r4 G off Lg Sv J M s c sgn rowK)

section States
variable (O S : Fin (ns + 1)) (X : PReg nr)

/-- **The population's states** (`63 = s`; state counter `59`, `49 = s'`). -/
def statesW (cwP cwN : List Bool) : WM ns nr :=
  .ifr (X 63)
    (.seq (FinalPass.Hash4.wcopyR (X 63) (X 49) (X 61)) (.seq (stateW O S X cwP) (WM.clear (X 49))))
    (.seq (FinalPass.Hash4.wcopyR (X 44) (X 59) (X 61))
      (.seq (.whr (X 59) (.seq (.dec (X 59)) (.seq (.inc (X 49)) (stateW O S X cwN)))) (WM.clear (X 49))))

/-- A bound on the states' cost. -/
def statesBound (cap n J M c Lp d r4 G off Lg cwl : ℕ) : ℕ :=
  (M + 1) * (stateBound cap n J M M c Lp d r4 G off Lg cwl + 8) + 40 * cap + 100

theorem statesW_spec (hOS : O ≠ S) (cwP cwN : List Bool) (τ : WState ns nr) (s n Lp d r4 G off Lg Sv J M L c : ℕ)
    (sgn : Bool) (hB : BlockRegs X τ Lp d r4 G off Lg Sv J M L 0 c ((J + 1) * (2 * L + 1)) sgn)
    (h52 : τ.val (X 52) = n) (h58 : τ.val (X 58) = n * (1 + (J + 1) * (2 * L + 1))) (h59 : τ.val (X 59) = 0)
    (h60 : τ.val (X 60) = 0) (h63 : τ.val (X 63) = s) (hsM : s ≤ M)
    (Mlab : ℕ) (hM : off + Lg + (r4 + 4) * G ≤ Mlab)
    (rowK : ℕ → ℕ → List Bool) (hrows : ∀ k < n, ∀ j ≤ J, (rowK k j).length = L)
    (ho : τ.sh O = (τ.st O).length)
    (hS : ∀ i < (tableW n J rowK).length, readTapeBit (τ.st S) (τ.sh S + i) = (tableW n J rowK).getD i false)
    (hcap : lvCap Sv J J ≤ cap) (hJc : J + 1 ≤ cap) (hLc : L ≤ cap) (hMc : M ≤ cap)
    (hcc : c + 1 ≤ cap) (hVc : (J + 1) * (2 * L + 1) ≤ cap) (hnc : n ≤ cap)
    (hTc : n * (1 + (J + 1) * (2 * L + 1)) ≤ cap)
    (hbig : τ.val (X 0) + (statesAbs s n Lp d r4 G off Lg Sv J M c sgn rowK cwP cwN).length + 2 + labCapA Lp d +
      (pieceA Lp d).length + labCapB r4 G off Lg Mlab ≤ cap) :
    ∃ m, WExec cap (statesW O S X cwP cwN) τ
      (lSt O S (X 0) τ (statesAbs s n Lp d r4 G off Lg Sv J M c sgn rowK cwP cwN) (τ.sh S)) m ∧
      m ≤ statesBound cap n J M c Lp d r4 G off Lg (cwP.length + cwN.length) := by
  have hne : ∀ {i k : Fin 64}, i ≠ k → X i ≠ X k := fun h => X.injective.ne h
  have n0 : ∀ i : Fin 64, i ≠ 0 → X i ≠ X 0 := fun i h => hne h
  have hSB : ∀ s', s' ≤ M → ∀ cw : List Bool, cw.length ≤ cwP.length + cwN.length →
      stateBound cap n J M s' c Lp d r4 G off Lg cw.length ≤
        stateBound cap n J M M c Lp d r4 G off Lg (cwP.length + cwN.length) :=
    fun s' hs' cw hcw => stateBound_mono _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hs' hcw
  by_cases hs0 : s = 0
  · -- the zero coordinate: the states `1, …, M`, coefficient `−1`
    have hA : statesAbs s n Lp d r4 G off Lg Sv J M c sgn rowK cwP cwN =
        (List.range M).flatMap fun i => stateEw cwN (visitsE n Lp d r4 G off Lg Sv J M (i + 1) c sgn rowK) := by
      unfold statesAbs; rw [if_pos hs0]
    rw [hA] at hbig ⊢
    obtain ⟨f, hf⟩ : ∃ f : ℕ → List Bool, f = fun i => stateEw cwN (visitsE n Lp d r4 G off Lg Sv J M (i + 1) c sgn rowK) :=
      ⟨_, rfl⟩
    have hfi : ∀ i, f i = stateEw cwN (visitsE n Lp d r4 G off Lg Sv J M (i + 1) c sgn rowK) := fun i => by rw [hf]
    rw [show (List.range M).flatMap (fun i => stateEw cwN (visitsE n Lp d r4 G off Lg Sv J M (i + 1) c sgn rowK)) =
      (List.range M).flatMap f by rw [hf]] at hbig ⊢
    have e1 := FinalPass.Hash4.wcopyR_spec cap (X 44) (X 59) (X 61) (hne (by decide)) (hne (by decide))
      (hne (by decide)) τ h59 hB.h61 (by rw [hB.h44]; exact hMc)
    rw [hB.h44] at e1
    let S' : ℕ → WState ns nr := fun i =>
      lSt O S (X 0) ((τ.setv (X 59) (M - i)).setv (X 49) i) ((List.range i).flatMap f) (τ.sh S)
    have hS'0 : S' 0 = τ.setv (X 59) M := by
      simp only [S', List.range_zero, List.flatMap_nil, Nat.sub_zero]
      have hx : (τ.setv (X 59) M).val (X 49) = 0 := by
        rw [wsetv_val_ne _ _ (hne (show (49 : Fin 64) ≠ 59 by decide))]; exact hB.h49
      rw [setv_eq_self hx]
      exact lSt_nil _
    have hloop := UnionMachine.Round.wloop cap (X 59) (.seq (.inc (X 49)) (stateW O S X cwN))
      (3 + 1 + stateBound cap n J M M c Lp d r4 G off Lg (cwP.length + cwN.length)) M S'
      (fun i _ => by simp only [S']; rw [lSt_val_ne (n0 59 (by decide))]; simp [wsetv_val_ne _ _ (hne (by decide) :
        X 59 ≠ X 49)])
      hMc
      (fun i hi => by
        have hτS : (S' i).setv (X 59) (M - i - 1) =
            lSt O S (X 0) ((τ.setv (X 59) (M - i - 1)).setv (X 49) i) ((List.range i).flatMap f) (τ.sh S) := by
          simp only [S']
          rw [lSt_setv _ _ _ _ (n0 59 (by decide)), wsetv_comm _ _ _ (hne (by decide) : X 49 ≠ X 59), wsetv_setv]
        rw [hτS]
        have ei := WExec.inc (cap := cap) (X 49)
          (lSt O S (X 0) ((τ.setv (X 59) (M - i - 1)).setv (X 49) i) ((List.range i).flatMap f) (τ.sh S))
          (by rw [lSt_val_ne (n0 49 (by decide))]; simp; omega)
        rw [lSt_val_ne (n0 49 (by decide)), show ((τ.setv (X 59) (M - i - 1)).setv (X 49) i).val (X 49) + 1 = i + 1 by simp,
          lSt_setv _ _ _ _ (n0 49 (by decide)), wsetv_setv] at ei
        have hpre := flatMap_range_mono f (i + 1) M (by omega)
        rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.length_append] at hpre
        have hBi := (blockRegs_s (blockRegs_setv hB 59 (by decide) (M - i - 1)) (i + 1)).lSt (O := O) (S := S)
          ((List.range i).flatMap f) (τ.sh S)
        obtain ⟨m, em, bm⟩ := stateW_spec cap O S X hOS cwN
          (lSt O S (X 0) ((τ.setv (X 59) (M - i - 1)).setv (X 49) (i + 1)) ((List.range i).flatMap f) (τ.sh S))
          n Lp d r4 G off Lg Sv J M L (i + 1) c sgn hBi
          (by rw [lSt_val_ne (n0 52 (by decide))]; simp [wsetv_val_ne _ _ (hne (by decide) : X 52 ≠ X 49),
            wsetv_val_ne _ _ (hne (by decide) : X 52 ≠ X 59), h52])
          (by rw [lSt_val_ne (n0 58 (by decide))]; simp [wsetv_val_ne _ _ (hne (by decide) : X 58 ≠ X 49),
            wsetv_val_ne _ _ (hne (by decide) : X 58 ≠ X 59), h58])
          (by rw [lSt_val_ne (n0 60 (by decide))]; simp [wsetv_val_ne _ _ (hne (by decide) : X 60 ≠ X 49),
            wsetv_val_ne _ _ (hne (by decide) : X 60 ≠ X 59), h60])
          Mlab hM rowK hrows (lSt_ho hOS _ (by simp [ho]) _ _) (by rw [lSt_stS hOS, lSt_shS]; exact hS)
          hcap hJc hLc hMc (by omega) hcc hVc hnc hTc
          (by
            rw [lSt_val_self, wsetv_val_ne _ _ (n0 49 (by decide)).symm, wsetv_val_ne _ _ (n0 59 (by decide)).symm,
              ← hfi]
            omega)
        rw [lSt_lSt hOS, lSt_shS, ← hfi] at em
        refine WExec.mono (WExec.cast cap (WExec.seq ei em) ?_ le_rfl) ?_
        · simp only [S']
          rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, show M - i - 1 = M - (i + 1) by omega]
        · have := hSB (i + 1) (by omega) cwN (by omega)
          omega)
    rw [hS'0] at hloop
    simp only [S', Nat.sub_self] at hloop
    have e3 := wclear_spec cap (X 49) M (lSt O S (X 0) ((τ.setv (X 59) 0).setv (X 49) M) ((List.range M).flatMap f) (τ.sh S))
      (by rw [lSt_val_ne (n0 49 (by decide))]; simp) (by rw [lSt_val_ne (n0 49 (by decide))]; simp; exact hMc)
    have hx0 : (τ.setv (X 59) 0).val (X 49) = 0 := by
      rw [wsetv_val_ne _ _ (hne (show (49 : Fin 64) ≠ 59 by decide))]; exact hB.h49
    have hfin : lSt O S (X 0) (((τ.setv (X 59) 0).setv (X 49) M).setv (X 49) 0) ((List.range M).flatMap f) (τ.sh S) =
        lSt O S (X 0) τ ((List.range M).flatMap f) (τ.sh S) := by
      rw [wsetv_setv, setv_eq_self hx0, setv_eq_self h59]
    rw [lSt_setv _ _ _ _ (n0 49 (by decide)), hfin] at e3
    refine ⟨_, WExec.ifrF (by rw [h63]; exact hs0) (WExec.seq e1 (WExec.seq hloop e3)), ?_⟩
    unfold statesBound
    generalize stateBound cap n J M M c Lp d r4 G off Lg (cwP.length + cwN.length) = SB
    have : (M + 1) * (SB + 8) = M * (SB + 8) + (SB + 8) := by ring
    have : M * (3 + 1 + SB + 4) = M * (SB + 8) := by ring
    omega
  · -- one state `s`, coefficient `1`
    have hA : statesAbs s n Lp d r4 G off Lg Sv J M c sgn rowK cwP cwN =
        stateEw cwP (visitsE n Lp d r4 G off Lg Sv J M s c sgn rowK) := by
      unfold statesAbs; rw [if_neg hs0]
    rw [hA] at hbig ⊢
    have e1 := FinalPass.Hash4.wcopyR_spec cap (X 63) (X 49) (X 61) (hne (by decide)) (hne (by decide))
      (hne (by decide)) τ hB.h49 hB.h61 (by rw [h63]; omega)
    rw [h63] at e1
    obtain ⟨m, em, bm⟩ := stateW_spec cap O S X hOS cwP (τ.setv (X 49) s) n Lp d r4 G off Lg Sv J M L s c sgn
      (blockRegs_s hB s) (by rw [wsetv_val_ne _ _ (hne (by decide))]; exact h52)
      (by rw [wsetv_val_ne _ _ (hne (by decide))]; exact h58) (by rw [wsetv_val_ne _ _ (hne (by decide))]; exact h60)
      Mlab hM rowK hrows ho hS hcap hJc hLc hMc (by omega) hcc hVc hnc hTc
      (by rw [wsetv_val_ne _ _ (n0 49 (by decide)).symm]; exact hbig)
    have e3 := wclear_spec cap (X 49) s (lSt O S (X 0) (τ.setv (X 49) s)
      (stateEw cwP (visitsE n Lp d r4 G off Lg Sv J M s c sgn rowK)) ((τ.setv (X 49) s).sh S))
      (by rw [lSt_val_ne (n0 49 (by decide))]; simp) (by rw [lSt_val_ne (n0 49 (by decide))]; simp; omega)
    rw [lSt_setv _ _ _ _ (n0 49 (by decide)), wsetv_setv, setv_eq_self hB.h49] at e3
    refine ⟨_, WExec.ifrT (by rw [h63]; exact hs0) (WExec.seq e1 (WExec.seq em e3)), ?_⟩
    unfold statesBound
    have := hSB s hsM cwP (by omega)
    generalize stateBound cap n J M M c Lp d r4 G off Lg (cwP.length + cwN.length) = SB at this ⊢
    have : (M + 1) * (SB + 8) = M * (SB + 8) + (SB + 8) := by ring
    omega

end States

/-! ## The setup fields and the constant term -/

section Setup
variable (O S : Fin (ns + 1)) (X : PReg nr)

/-- `A` copies of `u` (keeping `A`), then `v`. -/
def rt (A : Fin 64) (u v : List Bool) : WM ns nr := .seq (repRegW O (X 0) (X A) (X 61) (X 62) u) (emitW O (X 0) v)

theorem rt_spec (A : Fin 64) (hA61 : A ≠ 61) (hA62 : A ≠ 62) (u v : List Bool) (σ : WState ns nr)
    (a : ℕ) (ha : σ.val (X A) = a) (h61 : σ.val (X 61) = 0) (h62 : σ.val (X 62) = 0)
    (ho : σ.sh O = (σ.st O).length) (hac : a ≤ cap) (hc : σ.val (X 0) + a * u.length + v.length ≤ cap) :
    WExec cap (rt O X A u v) σ (appendO σ O (X 0) (reps a u ++ v))
      (18 * a + 3 + 1 + (a * (8 * u.length + 4) + 1) + 1 + 8 * v.length) := by
  have hne : ∀ {i k : Fin 64}, i ≠ k → X i ≠ X k := fun h => X.injective.ne h
  have e1 := repRegW_spec cap O (X 0) (X A) (X 61) (X 62) (hne hA61) (hne hA62) (hne (by decide)) (hne (by decide))
    u σ h61 h62 ho (by omega) (by rw [ha]; omega)
  rw [ha] at e1
  have e2 := emitW_spec cap O (X 0) v (appendO σ O (X 0) (reps a u)) (by simp [ho])
    (by simp [FiltRecW.reps_length]; omega)
  rw [appendO_append] at e2
  exact WExec.seq e1 e2

/-- **The setup fields**: `R` (`54`), `Lg` (`55`), the walk length twice (`52`), `θ` (`53`), two flags, the empty
field, `cap` (`56`). -/
def setupW : WM ns nr :=
  .seq (rt O X 54 (m2 true) [true, false])
  (.seq (rt O X 55 (m2 false) [true, false])
  (.seq (rt O X 52 (m3 false) (m2 false ++ [true, false]))
  (.seq (rt O X 52 (m3 false) (m2 false ++ [true, false]))
  (.seq (rt O X 53 (m2 true) (m2 false ++ [true, false]))
  (.seq (emitW O (X 0) ((m2 false ++ [true, false]) ++ (m2 false ++ [true, false]) ++ [true, false]))
  (rt O X 56 (m2 false) [true, false]))))))

/-- A bound on the setup fields' cost. -/
def setupBound (n θ R Lg cp : ℕ) : ℕ := 100 * (R + Lg + 2 * n + θ + cp) + 400

theorem setupW_spec (τ : WState ns nr) (n θ R Lg cp : ℕ) (h52 : τ.val (X 52) = n) (h53 : τ.val (X 53) = θ)
    (h54 : τ.val (X 54) = R) (h55 : τ.val (X 55) = Lg) (h56 : τ.val (X 56) = cp) (h61 : τ.val (X 61) = 0)
    (h62 : τ.val (X 62) = 0) (ho : τ.sh O = (τ.st O).length) (hc : τ.val (X 0) + (setupE n θ R Lg cp).length ≤ cap)
    (hnc : n ≤ cap) (hθc : θ ≤ cap) (hRc : R ≤ cap) (hLc : Lg ≤ cap) (hcc : cp ≤ cap) :
    ∃ m, WExec cap (setupW O X) τ (appendO τ O (X 0) (setupE n θ R Lg cp)) m ∧ m ≤ setupBound n θ R Lg cp := by
  have hR' : ∀ i k : Fin 64, X i = X k ↔ i = k := fun i k => X.injective.eq_iff
  have hl : (setupE n θ R Lg cp).length = (4 * R + 2) + (4 * Lg + 2) + (8 * n + 6) + (8 * n + 6) + (4 * θ + 6) + 6 + 6 +
      2 + (4 * cp + 2) := by
    unfold setupE
    simp only [List.length_append, FiltRecW.reps_length, m2, m3, List.length_cons, List.length_nil]
    ring
  have hv : ∀ (u : List Bool) (i : Fin 64), i ≠ 0 → (appendO τ O (X 0) u).val (X i) = τ.val (X i) := by
    intro u i hi; simp [hR', hi]
  have hoo : ∀ u : List Bool, (appendO τ O (X 0) u).sh O = ((appendO τ O (X 0) u).st O).length := by
    intro u; simp [ho]
  have hvo : ∀ u : List Bool, (appendO τ O (X 0) u).val (X 0) = τ.val (X 0) + u.length := by intro u; simp
  have e1 := rt_spec cap O X 54 (by decide) (by decide) (m2 true) [true, false] τ R h54 h61 h62 ho hRc
    (by simp [m2]; omega)
  set u1 := reps R (m2 true) ++ [true, false] with hu1
  have hl1 : u1.length = 4 * R + 2 := by simp [hu1, FiltRecW.reps_length, m2]; ring
  have e2 := rt_spec cap O X 55 (by decide) (by decide) (m2 false) [true, false] (appendO τ O (X 0) u1) Lg
    (by rw [hv _ _ (by decide), h55]) (by rw [hv _ _ (by decide), h61]) (by rw [hv _ _ (by decide), h62]) (hoo _) hLc
    (by rw [hvo, hl1]; simp [m2]; omega)
  rw [appendO_append] at e2
  set u2 := u1 ++ (reps Lg (m2 false) ++ [true, false]) with hu2
  have hl2 : u2.length = 4 * R + 2 + (4 * Lg + 2) := by simp [hu2, hl1, FiltRecW.reps_length, m2]; ring
  have e3 := rt_spec cap O X 52 (by decide) (by decide) (m3 false) (m2 false ++ [true, false])
    (appendO τ O (X 0) u2) n (by rw [hv _ _ (by decide), h52]) (by rw [hv _ _ (by decide), h61])
    (by rw [hv _ _ (by decide), h62]) (hoo _) hnc (by rw [hvo, hl2]; simp [m2, m3]; omega)
  rw [appendO_append] at e3
  set u3 := u2 ++ (reps n (m3 false) ++ (m2 false ++ [true, false])) with hu3
  have hl3 : u3.length = 4 * R + 2 + (4 * Lg + 2) + (8 * n + 6) := by
    simp [hu3, hl2, FiltRecW.reps_length, m2, m3]; ring
  have e4 := rt_spec cap O X 52 (by decide) (by decide) (m3 false) (m2 false ++ [true, false])
    (appendO τ O (X 0) u3) n (by rw [hv _ _ (by decide), h52]) (by rw [hv _ _ (by decide), h61])
    (by rw [hv _ _ (by decide), h62]) (hoo _) hnc (by rw [hvo, hl3]; simp [m2, m3]; omega)
  rw [appendO_append] at e4
  set u4 := u3 ++ (reps n (m3 false) ++ (m2 false ++ [true, false])) with hu4
  have hl4 : u4.length = 4 * R + 2 + (4 * Lg + 2) + (8 * n + 6) + (8 * n + 6) := by
    simp [hu4, hl3, FiltRecW.reps_length, m2, m3]; ring
  have e5 := rt_spec cap O X 53 (by decide) (by decide) (m2 true) (m2 false ++ [true, false])
    (appendO τ O (X 0) u4) θ (by rw [hv _ _ (by decide), h53]) (by rw [hv _ _ (by decide), h61])
    (by rw [hv _ _ (by decide), h62]) (hoo _) hθc (by rw [hvo, hl4]; simp [m2]; omega)
  rw [appendO_append] at e5
  set u5 := u4 ++ (reps θ (m2 true) ++ (m2 false ++ [true, false])) with hu5
  have hl5 : u5.length = 4 * R + 2 + (4 * Lg + 2) + (8 * n + 6) + (8 * n + 6) + (4 * θ + 6) := by
    simp [hu5, hl4, FiltRecW.reps_length, m2]; ring
  have e6 := emitW_spec cap O (X 0) ((m2 false ++ [true, false]) ++ (m2 false ++ [true, false]) ++ [true, false])
    (appendO τ O (X 0) u5) (hoo _) (by rw [hvo, hl5]; simp [m2]; omega)
  rw [appendO_append] at e6
  set u6 := u5 ++ ((m2 false ++ [true, false]) ++ (m2 false ++ [true, false]) ++ [true, false]) with hu6
  have hl6 : u6.length = 4 * R + 2 + (4 * Lg + 2) + (8 * n + 6) + (8 * n + 6) + (4 * θ + 6) + 14 := by
    simp [hu6, hl5, m2]
  have e7 := rt_spec cap O X 56 (by decide) (by decide) (m2 false) [true, false]
    (appendO τ O (X 0) u6) cp (by rw [hv _ _ (by decide), h56]) (by rw [hv _ _ (by decide), h61])
    (by rw [hv _ _ (by decide), h62]) (hoo _) hcc (by rw [hvo, hl6]; simp [m2]; omega)
  rw [appendO_append] at e7
  refine ⟨_, WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6
    e7)))))) ?_ le_rfl, ?_⟩
  · congr 1
    rw [hu6, hu5, hu4, hu3, hu2, hu1]
    unfold setupE
    simp only [List.append_assoc]
  · unfold setupBound
    simp only [m2, m3, List.length_cons, List.length_nil, List.length_append]
    omega

/-- The constant term's head at level 2: the term's marker and its coefficient `1`. -/
def oneHead : List Bool := m2 true ++ (ListMachine.Rec.coefWord 1).flatMap m2

/-- One factor of the constant term at level 2: `true :: polyWord [[]]`. -/
def oneVisit : List Bool := (true :: ListMachine.Rec.polyWord [[]]).flatMap m2

/-- The constant term's field, emitted: for `s = 0` the term `1` with `walkLen` empty factors, else empty. -/
def oneE (s n : ℕ) : List Bool :=
  if s = 0 then oneHead ++ reps n oneVisit ++ (m2 false ++ [true, false]) else [true, false]

/-- **The constant term's field** (`63 = s`, `52 = walkLen`). -/
def oneW : WM ns nr :=
  .ifr (X 63) (emitW O (X 0) [true, false])
    (.seq (emitW O (X 0) oneHead) (rt O X 52 oneVisit (m2 false ++ [true, false])))

/-- A bound on the constant term's cost. -/
def oneBound (n : ℕ) : ℕ := n * (8 * oneVisit.length + 4) + 18 * n + 8 * oneHead.length + 200

theorem oneW_spec (τ : WState ns nr) (s n : ℕ) (h63 : τ.val (X 63) = s) (h52 : τ.val (X 52) = n)
    (h61 : τ.val (X 61) = 0) (h62 : τ.val (X 62) = 0) (ho : τ.sh O = (τ.st O).length) (hnc : n ≤ cap)
    (hc : τ.val (X 0) + (oneE s n).length ≤ cap) :
    ∃ m, WExec cap (oneW O X) τ (appendO τ O (X 0) (oneE s n)) m ∧ m ≤ oneBound n := by
  have hR' : ∀ i k : Fin 64, X i = X k ↔ i = k := fun i k => X.injective.eq_iff
  by_cases hs : s = 0
  · have hoE : oneE s n = oneHead ++ reps n oneVisit ++ (m2 false ++ [true, false]) := by unfold oneE; rw [if_pos hs]
    rw [hoE] at hc ⊢
    simp only [List.length_append, FiltRecW.reps_length, m2, List.length_cons, List.length_nil] at hc
    have e1 := emitW_spec cap O (X 0) oneHead τ ho (by omega)
    have e2 := rt_spec cap O X 52 (by decide) (by decide) oneVisit (m2 false ++ [true, false])
      (appendO τ O (X 0) oneHead) n (by simp [hR', h52]) (by simp [hR', h61]) (by simp [hR', h62]) (by simp [ho]) hnc
      (by simp only [appendO_val, Function.update_self, m2, List.length_append, List.length_cons, List.length_nil]
          omega)
    rw [appendO_append] at e2
    refine ⟨_, WExec.ifrF (by rw [h63]; exact hs) (WExec.seq e1 (WExec.cast cap e2 (by simp only [List.append_assoc])
      le_rfl)), ?_⟩
    unfold oneBound
    simp only [m2, List.length_cons, List.length_nil, List.length_append]
    omega
  · have hoE : oneE s n = [true, false] := by unfold oneE; rw [if_neg hs]
    rw [hoE] at hc ⊢
    exact ⟨_, WExec.ifrT (by rw [h63]; exact hs) (emitW_spec cap O (X 0) [true, false] τ ho hc),
      by unfold oneBound; simp⟩

end Setup

/-! ## The POP record -/

/-- **The POP record, emitted** (abstract numbers): the setup fields, the constant term, the states, the end. -/
def popRecAbs (n θ R Lgc cp s Lp d r4 G off Lg Sv J M c : ℕ) (sgn : Bool) (rowK : ℕ → ℕ → List Bool)
    (cwP cwN : List Bool) : List Bool :=
  setupE n θ R Lgc cp ++ (oneE s n ++ (statesAbs s n Lp d r4 G off Lg Sv J M c sgn rowK cwP cwN ++ [true, false])) ++
    [false]

section Record
variable (O S : Fin (ns + 1)) (X : PReg nr)

/-- **The POP row's input word, written.** -/
def popRecW (cwP cwN : List Bool) : WM ns nr :=
  .seq (setupW O X) (.seq (oneW O X) (.seq (statesW O S X cwP cwN) (emitW O (X 0) ([true, false] ++ [false]))))

/-- A bound on the POP record's cost. -/
def popRecBound (cap n θ R Lgc cp J M c Lp d r4 G off Lg cwl : ℕ) : ℕ :=
  setupBound n θ R Lgc cp + oneBound n + statesBound cap n J M c Lp d r4 G off Lg cwl + 40

theorem popRecW_spec (hOS : O ≠ S) (cwP cwN : List Bool) (τ : WState ns nr)
    (n θ R Lgc cp s Lp d r4 G off Lg Sv J M L c : ℕ) (sgn : Bool)
    (hB : BlockRegs X τ Lp d r4 G off Lg Sv J M L 0 c ((J + 1) * (2 * L + 1)) sgn)
    (h52 : τ.val (X 52) = n) (h53 : τ.val (X 53) = θ) (h54 : τ.val (X 54) = R) (h55 : τ.val (X 55) = Lgc)
    (h56 : τ.val (X 56) = cp) (h58 : τ.val (X 58) = n * (1 + (J + 1) * (2 * L + 1))) (h59 : τ.val (X 59) = 0)
    (h60 : τ.val (X 60) = 0) (h63 : τ.val (X 63) = s) (hsM : s ≤ M)
    (Mlab : ℕ) (hM : off + Lg + (r4 + 4) * G ≤ Mlab)
    (rowK : ℕ → ℕ → List Bool) (hrows : ∀ k < n, ∀ j ≤ J, (rowK k j).length = L)
    (ho : τ.sh O = (τ.st O).length)
    (hS : ∀ i < (tableW n J rowK).length, readTapeBit (τ.st S) (τ.sh S + i) = (tableW n J rowK).getD i false)
    (hcap : lvCap Sv J J ≤ cap) (hJc : J + 1 ≤ cap) (hLc : L ≤ cap) (hMc : M ≤ cap)
    (hcc : c + 1 ≤ cap) (hVc : (J + 1) * (2 * L + 1) ≤ cap) (hnc : n ≤ cap)
    (hTc : n * (1 + (J + 1) * (2 * L + 1)) ≤ cap) (hθc : θ ≤ cap) (hRc : R ≤ cap) (hLgc : Lgc ≤ cap) (hcpc : cp ≤ cap)
    (hbig : τ.val (X 0) + (popRecAbs n θ R Lgc cp s Lp d r4 G off Lg Sv J M c sgn rowK cwP cwN).length + 2 +
      labCapA Lp d + (pieceA Lp d).length + labCapB r4 G off Lg Mlab ≤ cap) :
    ∃ m, WExec cap (popRecW O S X cwP cwN) τ
      (lSt O S (X 0) τ (popRecAbs n θ R Lgc cp s Lp d r4 G off Lg Sv J M c sgn rowK cwP cwN) (τ.sh S)) m ∧
      m ≤ popRecBound cap n θ R Lgc cp J M c Lp d r4 G off Lg (cwP.length + cwN.length) := by
  have hne : ∀ {i k : Fin 64}, i ≠ k → X i ≠ X k := fun h => X.injective.ne h
  have n0 : ∀ i : Fin 64, i ≠ 0 → X i ≠ X 0 := fun i h => hne h
  obtain ⟨sE, hsE⟩ : ∃ x, x = setupE n θ R Lgc cp := ⟨_, rfl⟩
  obtain ⟨oE, hoE⟩ : ∃ x, x = oneE s n := ⟨_, rfl⟩
  obtain ⟨stE, hstE⟩ : ∃ x, x = statesAbs s n Lp d r4 G off Lg Sv J M c sgn rowK cwP cwN := ⟨_, rfl⟩
  have hpr : popRecAbs n θ R Lgc cp s Lp d r4 G off Lg Sv J M c sgn rowK cwP cwN =
      sE ++ (oE ++ (stE ++ [true, false])) ++ [false] := by rw [hsE, hoE, hstE]; rfl
  rw [hpr] at hbig ⊢
  simp only [List.length_append, List.length_cons, List.length_nil] at hbig
  obtain ⟨m1, e1, b1⟩ := setupW_spec cap O X τ n θ R Lgc cp h52 h53 h54 h55 h56 hB.h61 hB.h62 ho
    (by rw [← hsE]; omega) hnc hθc hRc hLgc hcpc
  rw [← hsE, ← lSt_self (S := S) hOS] at e1
  obtain ⟨m2, e2, b2⟩ := oneW_spec cap O X (lSt O S (X 0) τ sE (τ.sh S)) s n
    (by rw [lSt_val_ne (n0 63 (by decide))]; exact h63) (by rw [lSt_val_ne (n0 52 (by decide))]; exact h52)
    (by rw [lSt_val_ne (n0 61 (by decide))]; exact hB.h61) (by rw [lSt_val_ne (n0 62 (by decide))]; exact hB.h62)
    (lSt_ho hOS τ ho _ _) hnc (by rw [lSt_val_self, ← hoE]; omega)
  rw [← hoE, lSt_append hOS] at e2
  obtain ⟨m3, e3, b3⟩ := statesW_spec cap O S X hOS cwP cwN (lSt O S (X 0) τ (sE ++ oE) (τ.sh S)) s n Lp d r4 G off Lg
    Sv J M L c sgn (hB.lSt _ _) (by rw [lSt_val_ne (n0 52 (by decide))]; exact h52)
    (by rw [lSt_val_ne (n0 58 (by decide))]; exact h58) (by rw [lSt_val_ne (n0 59 (by decide))]; exact h59)
    (by rw [lSt_val_ne (n0 60 (by decide))]; exact h60) (by rw [lSt_val_ne (n0 63 (by decide))]; exact h63) hsM
    Mlab hM rowK hrows (lSt_ho hOS τ ho _ _) (by rw [lSt_stS hOS, lSt_shS]; exact hS) hcap hJc hLc hMc hcc hVc hnc hTc
    (by rw [lSt_val_self, ← hstE, List.length_append]; omega)
  rw [lSt_lSt hOS, lSt_shS, ← hstE] at e3
  have e4 := emitW_spec cap O (X 0) ([true, false] ++ [false]) (lSt O S (X 0) τ (sE ++ oE ++ stE) (τ.sh S))
    (lSt_ho hOS τ ho _ _) (by rw [lSt_val_self]; simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  rw [lSt_append hOS] at e4
  refine ⟨_, WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) ?_ le_rfl, ?_⟩
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
  · unfold popRecBound
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

end Record

end NearCubicWires.WireExponent3_5.PrimAsm.PopRecW
