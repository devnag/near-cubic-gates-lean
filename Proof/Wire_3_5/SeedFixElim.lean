import Proof.Wire_3_5.SeedFixConsLoop
import Proof.Wire_3_5.SeedFixGaussPad

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SeedFix
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.GF2 NearCubicWires.WireExponent3_5.JoinElimination
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write)
open NearCubicWires.RepairOrdinary.ZeroPadding (pad)

/-! ## The system's rows are masks over the remaining bits -/

theorem fold_mask_lt (n : ℕ) (c : ℕ → Bool) : ∀ (l : List ℕ) (acc : ℕ), (∀ j ∈ l, j < n) → acc < 2 ^ n →
    l.foldl (fun acc j => if c j then acc ||| (1 <<< j) else acc) acc < 2 ^ n
  | [], _, _, h => h
  | j :: l, acc, hl, h => by
    rw [List.foldl_cons]
    refine fold_mask_lt n c l _ (fun j' hj' => hl j' (List.mem_cons_of_mem _ hj')) ?_
    split
    · have hj : j < n := hl j List.mem_cons_self
      have h1 : 1 <<< j < 2 ^ n := by rw [Nat.one_shiftLeft]; exact Nat.pow_lt_pow_right (by norm_num) hj
      exact Nat.or_lt_two_pow h h1
    · exact h

theorem system_lt (p ℓ twoH k plen pre : ℕ) (cons : List (ℕ × ℕ)) :
    ∀ r ∈ system p ℓ twoH k plen pre cons, r.1 < 2 ^ (twoH * ℓ - plen) := by
  intro r hr
  unfold system at hr
  simp only [List.mem_flatMap, List.mem_map] at hr
  obtain ⟨con, _, cc, _, rfl⟩ := hr
  exact fold_mask_lt (twoH * ℓ - plen)
    (fun j => (JoinElimination.fmul p ℓ (2 ^ ((plen + j) % ℓ)) (JoinElimination.fpow p ℓ con.1 ((plen + j) / ℓ))).testBit cc)
    (List.range (twoH * ℓ - plen)) 0 (fun j hj => List.mem_range.mp hj) (Nat.two_pow_pos _)

theorem system_length (p ℓ twoH k plen pre : ℕ) (cons : List (ℕ × ℕ)) :
    (system p ℓ twoH k plen pre cons).length = cons.length * k := by
  unfold system
  simp [List.length_flatMap, List.map_const', List.sum_replicate]

/-! ## The bank (tapes 0–23 the record loop's, 24 the stage log, 25 the pass output, 26 the pivots, 27 the rank tape,
28 the column counter, 29 the flag `G`, 30 the exponent tape `X`) -/

def bank31 (p ℓ twoH plen pfx m cap cap2 cap3 cap4 RV cL cE : ℕ) (R : Regs) (O S W P K C G X : List Bool) :
    Fin 31 → List Bool :=
  ![List.replicate twoH true ++ [false], List.replicate ℓ true ++ [false], frame (binary ℓ R.a), frame (binary ℓ R.c),
    R.T ++ List.replicate m false, frame (binary ℓ p), R.fl, frame (binary ℓ R.x), frame (binary ℓ R.z), [false],
    List.replicate cap false, List.replicate cap2 false, List.replicate cap3 false, List.replicate RV false,
    frame (binary plen pfx), frame (binary ℓ R.mc), R.r, [R.b], [false], O, frame (binary ℓ 1),
    List.replicate cap4 false, S, List.replicate cL false, List.replicate cE false, W, P, K, C, G, X]

def c24Term : Fin 1 → Fin 24 := ![19]

theorem install_c24Term (A : Fin 24 → List Bool) (v : Fin 1 → List Bool) :
    RecoveryRootRound.install c24Term A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18, v 0, A 20, A 21, A 22, A 23] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_c24Term (H : Fin 24 → ℕ) (v : Fin 1 → ℕ) :
    dockH c24Term H v = ![H 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, H 11, H 12, H 13, H 14, H 15, H 16, H 17, H 18, v 0, H 20, H 21, H 22, H 23] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_other _ _ _ _ (by decide)

def e31Set : Fin 1 → Fin 31 := ![29]

theorem install_e31Set (A : Fin 31 → List Bool) (v : Fin 1 → List Bool) :
    RecoveryRootRound.install e31Set A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18, A 19, A 20, A 21, A 22, A 23, A 24, A 25, A 26, A 27, A 28, v 0, A 30] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

def e31Gauss : Fin 10 → Fin 31 := ![19, 25, 26, 9, 10, 27, 28, 29, 11, 24]

theorem install_e31Gauss (A : Fin 31 → List Bool) (v : Fin 10 → List Bool) :
    RecoveryRootRound.install e31Gauss A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, v 3, v 4, v 8, A 12, A 13, A 14, A 15, A 16, A 17, A 18, v 0, A 20, A 21, A 22, A 23, v 9, v 1, v 2, v 5, v 6, v 7, A 30] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 3
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 4
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 5
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 6
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 7
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 8
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 9
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

def e31Def : Fin 4 → Fin 31 := ![28, 27, 30, 24]

theorem install_e31Def (A : Fin 31 → List Bool) (v : Fin 4 → List Bool) :
    RecoveryRootRound.install e31Def A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18, A 19, A 20, A 21, A 22, A 23, v 3, A 25, A 26, v 1, v 0, A 29, v 2] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 3
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

def selE1 : Fin 24 → Bool :=
  ![false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, true, false, false, true, false]
def selG : Fin 9 → Bool := ![true, false, false, false, false, true, true, false, false]
def selD : Fin 3 → Bool := ![true, true, true]

noncomputable def termR := RecoveryFocus.machine c24Term Gauss.termM
/-- The rows of every record, the terminator, the record and rows heads rewound. -/
noncomputable def rowsAllM := TapeEmbedding.machine 6 (MaskedReset.machine (Composition.machine loopM termR) selE1)
noncomputable def setG := RecoveryFocus.machine e31Set setM
noncomputable def gaussE := RecoveryFocus.machine e31Gauss (MaskedReset.machine Gauss.gaussM selG)
noncomputable def defE := RecoveryFocus.machine e31Def (MaskedReset.machine Deficit.machine selD)

/-- The flag set, the elimination, the count exponent. -/
noncomputable def countM := Composition.machine (Composition.machine setG gaussE) defE

/-- **The elimination block**: the rows, then the count. -/
noncomputable def elimM := Composition.machine rowsAllM countM

def loopCost (ℓ twoH k plen n : ℕ) : ℕ := n * (recCost ℓ twoH k plen + 2) + 1
def rowsAllCost (ℓ twoH k plen n : ℕ) : ℕ := 2 * (loopCost ℓ twoH k plen n + 1 + 1) + 2
def countCost (nrows rest : ℕ) : ℕ := 1 + 1 + (2 * Gauss.gaussCost nrows rest + 2) + 1 + (2 * Deficit.cost rest + 2)
def elimCost (ℓ twoH k plen n : ℕ) : ℕ :=
  rowsAllCost ℓ twoH k plen n + 1 + countCost (n * k) (twoH * ℓ - plen)

theorem loopH_zero (p ℓ twoH k plen pfx : ℕ) (cons : List (ℕ × ℕ)) : loopH p ℓ twoH k plen pfx cons 0 = fun _ => 0 := by
  funext j; fin_cases j <;> simp [loopH, hd24, rowsI]

/-- **The rows of all records**, terminated, with every head back at cell 0. -/
theorem rowsAll_run (p ℓ twoH k plen pfx m cap cap2 cap3 cap4 RV cL cE : ℕ) (R0 : Regs) (cons : List (ℕ × ℕ))
    (stale backingO W P K C G X : List Bool) (hℓ : 1 ≤ ℓ) (hkl : k ≤ ℓ) (h0 : R0.Ok ℓ twoH)
    (hcap : 2 * ℓ + 2 ≤ cap) (hcap2 : ℓ * (innerCost ℓ + 2) + 1 ≤ cap2)
    (hcap2' : ℓ * (mulIterCost ℓ + 2) + 1 ≤ cap2) (hcap2'' : plen * (phACost ℓ + 2) + 1 ≤ cap2)
    (hcap3 : tableCost ℓ twoH ≤ cap3) (hcap3' : passesCost ℓ plen (twoH * ℓ) ≤ cap3)
    (hcap4 : k * (rowCost ℓ plen (twoH * ℓ) + 2) + 1 ≤ cap4) (hplen : plen ≤ twoH * ℓ) (hm : 1 ≤ m)
    (hRV : 2 * ℓ + 1 ≤ RV) (hcL : 2 * ℓ + 1 ≤ cL) (hcE : loopCost ℓ twoH k plen cons.length + 1 + 1 ≤ cE) :
    Step rowsAllM (rowsAllCost ℓ twoH k plen cons.length) (fun _ => 0)
      (bank31 p ℓ twoH plen pfx m cap cap2 cap3 cap4 RV cL cE R0 backingO (consTape ℓ k cons stale) W P K C G X)
      (fun _ => 0)
      (bank31 p ℓ twoH plen pfx m cap cap2 cap3 cap4 RV cL cE (regsAt p ℓ twoH k plen R0 cons cons.length)
        (overlay (rowsI p ℓ twoH k plen pfx cons cons.length ++ [false]) backingO) (consTape ℓ k cons stale)
        W P K C G X) := by
  have hl := loop_run p ℓ twoH k plen pfx m cap cap2 cap3 cap4 RV cL R0 cons stale backingO hℓ hkl h0 hcap hcap2 hcap2'
    hcap2'' hcap3 hcap3' hcap4 hplen hm hRV hcL
  rw [loopH_zero] at hl
  set n := cons.length
  set rows := rowsI p ℓ twoH k plen pfx cons n
  have ht := dockRun (Gauss.term_run rows backingO) c24Term (by decide) (loopH p ℓ twoH k plen pfx cons n)
    (loopA p ℓ twoH k plen pfx m cap cap2 cap3 cap4 RV cL R0 cons stale backingO n)
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [dockH_c24Term, install_c24Term] at ht
  have hs := hl.seq ht
  have hm1 := hs.mask (cap := cE) selE1 (fun _ _ => rfl) hcE
  have he := hm1.embed (fun _ : Fin 6 => 0) ![W, P, K, C, G, X]
  refine (he.congr_in ?_ ?_).congr ?_ ?_
  · funext j; fin_cases j <;> rfl
  · funext j; fin_cases j <;> rfl
  · funext j; fin_cases j <;> rfl
  · funext j; fin_cases j <;> rfl

/-- **The flag set, the elimination and the count exponent**, from the terminated rows of a system. -/
theorem count_run (p ℓ twoH plen pfx m cap cap2 cap3 cap4 RV cL cE cK cC : ℕ) (R : Regs) (rowsL : List Row)
    (hrows : ∀ r ∈ rowsL, r.1 < 2 ^ (twoH * ℓ - plen)) (stale S W P Xold : List Bool) (g0 : Bool)
    (hcapG : 2 * (twoH * ℓ - plen) + 13 ≤ cap)
    (hcapG' : rowsL.length * (Gauss.rowCost (twoH * ℓ - plen) + 2) + 3 ≤ cap2)
    (hcapG'' : rowsL.length * (2 * (twoH * ℓ - plen) + 1) + 1 ≤ cap2) (hcK : twoH * ℓ - plen ≤ cK)
    (hcE2 : Gauss.gaussCost rowsL.length (twoH * ℓ - plen) ≤ cE) (hcE3 : Deficit.cost (twoH * ℓ - plen) ≤ cE) :
    ∃ O' W' P' : List Bool, Step countM
      (countCost rowsL.length (twoH * ℓ - plen)) (fun _ => 0)
      (bank31 p ℓ twoH plen pfx m cap cap2 cap3 cap4 RV cL cE R
        (Gauss.rowsTape (rowsL.map (Gauss.rowBits (twoH * ℓ - plen))) stale) S W P (pad cK [])
        (pad cC (List.replicate (twoH * ℓ - plen) true)) [g0] Xold)
      (fun _ => 0)
      (bank31 p ℓ twoH plen pfx m cap cap2 cap3 cap4 RV cL cE R O' S W' P' (pad cK [])
        (pad cC (List.replicate (twoH * ℓ - plen) true)) [(gauss (twoH * ℓ - plen) rowsL).1]
        (overlay (List.replicate (twoH * ℓ - plen - (gauss (twoH * ℓ - plen) rowsL).2) true ++ [false]) Xold)) := by
  set rest := twoH * ℓ - plen
  set gg := gauss rest rowsL
  set C := pad cC (List.replicate rest true)
  set E := List.replicate cE false
  set RT := Gauss.rowsTape (rowsL.map (Gauss.rowBits rest)) stale
  -- 1: the flag set
  have h1 : Step setM 1 (fun _ => 0) ![[g0]] (fun _ => 0) ![[true]] :=
    ((set_run g0).congr_in (by funext j; fin_cases j; rfl) rfl).congr (by funext j; fin_cases j; rfl) rfl
  have s1 := dockKeep h1 e31Set (by decide) (fun _ => 0)
    (bank31 p ℓ twoH plen pfx m cap cap2 cap3 cap4 RV cL cE R RT S W P (pad cK []) C [g0] Xold)
    (fun _ => rfl) (by intro j; fin_cases j; rfl)
  rw [install_e31Set] at s1
  have s1' := s1.congr (tout' := bank31 p ℓ twoH plen pfx m cap cap2 cap3 cap4 RV cL cE R RT S W P (pad cK []) C [true]
    Xold) rfl (by funext j; fin_cases j <;> rfl)
  -- 2: the elimination, the rows, rank and counter heads rewound
  obtain ⟨hR, R', W', P', hg⟩ := gaussP_run rest rowsL hrows stale W P cap cap2 cK cC hcapG hcapG' hcapG''
  have hm2 := hg.mask (cap := cE) selG (by intro j _; fin_cases j <;> rfl) hcE2
  have hm2' : Step (MaskedReset.machine Gauss.gaussM selG) (2 * Gauss.gaussCost rowsL.length rest + 2) (fun _ => 0)
      ![RT, W, P, [false], List.replicate cap false, pad cK [], C, [true], List.replicate cap2 false, E] (fun _ => 0)
      ![R', W', P', [false], List.replicate cap false, pad cK (List.replicate gg.2 true), C, [gg.1],
        List.replicate cap2 false, E] := by
    refine (hm2.congr_in ?_ ?_).congr ?_ ?_ <;> funext j <;> fin_cases j <;> rfl
  have s2 := dockKeep hm2' e31Gauss (by decide) (fun _ => 0)
    (bank31 p ℓ twoH plen pfx m cap cap2 cap3 cap4 RV cL cE R RT S W P (pad cK []) C [true] Xold)
    (fun _ => rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_e31Gauss] at s2
  have s2' := s2.congr (tout' := bank31 p ℓ twoH plen pfx m cap cap2 cap3 cap4 RV cL cE R R' S W' P'
    (pad cK (List.replicate gg.2 true)) C [gg.1] Xold) rfl (by funext j; fin_cases j <;> rfl)
  -- 3: the count exponent, the rank tape blank again
  have hd := deficit_run rest gg.2 cC cK Xold (gauss_rank_le rest rowsL hrows) hcK
  have hd' : Step Deficit.machine (Deficit.cost rest) (fun _ => 0) ![C, pad cK (List.replicate gg.2 true), Xold]
      ![rest, rest, rest - gg.2] ![C, pad cK [], overlay (List.replicate (rest - gg.2) true ++ [false]) Xold] :=
    hd.congr_in (by funext j; fin_cases j <;> rfl) rfl
  have hm3 := maskZero hd' selD (by intro j hj; fin_cases j <;> simp [selD] at hj) hcE3
  have hm3' : Step (MaskedReset.machine Deficit.machine selD) (2 * Deficit.cost rest + 2) (fun _ => 0)
      ![C, pad cK (List.replicate gg.2 true), Xold, E] (fun _ => 0)
      ![C, pad cK [], overlay (List.replicate (rest - gg.2) true ++ [false]) Xold, E] := by
    refine (hm3.congr_in rfl ?_).congr rfl ?_ <;> funext j <;> fin_cases j <;> rfl
  have s3 := dockKeep hm3' e31Def (by decide) (fun _ => 0)
    (bank31 p ℓ twoH plen pfx m cap cap2 cap3 cap4 RV cL cE R R' S W' P' (pad cK (List.replicate gg.2 true)) C [gg.1]
      Xold) (fun _ => rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_e31Def] at s3
  have s3' := s3.congr (tout' := bank31 p ℓ twoH plen pfx m cap cap2 cap3 cap4 RV cL cE R R' S W' P' (pad cK []) C
    [gg.1] (overlay (List.replicate (rest - gg.2) true ++ [false]) Xold)) rfl (by funext j; fin_cases j <;> rfl)
  exact ⟨R', W', P', (s1'.seq s2').seq s3'⟩

theorem elim_run (p ℓ twoH k plen pfx m cap cap2 cap3 cap4 RV cL cE cK cC : ℕ) (R0 : Regs) (cons : List (ℕ × ℕ))
    (stale backingO W P Xold : List Bool) (g0 : Bool) (hp : GF.ModulusOk p ℓ) (hℓ : 1 ≤ ℓ) (hkl : k ≤ ℓ)
    (h0 : R0.Ok ℓ twoH) (hcons : ∀ con ∈ cons, con.1 < 2 ^ ℓ)
    (hcap : 2 * ℓ + 2 ≤ cap) (hcap2 : ℓ * (innerCost ℓ + 2) + 1 ≤ cap2)
    (hcap2' : ℓ * (mulIterCost ℓ + 2) + 1 ≤ cap2) (hcap2'' : plen * (phACost ℓ + 2) + 1 ≤ cap2)
    (hcap3 : tableCost ℓ twoH ≤ cap3) (hcap3' : passesCost ℓ plen (twoH * ℓ) ≤ cap3)
    (hcap4 : k * (rowCost ℓ plen (twoH * ℓ) + 2) + 1 ≤ cap4) (hplen : plen ≤ twoH * ℓ) (hm : 1 ≤ m)
    (hRV : 2 * ℓ + 1 ≤ RV) (hcL : 2 * ℓ + 1 ≤ cL)
    (hcapG : 2 * (twoH * ℓ - plen) + 13 ≤ cap)
    (hcapG' : cons.length * k * (Gauss.rowCost (twoH * ℓ - plen) + 2) + 3 ≤ cap2)
    (hcapG'' : cons.length * k * (2 * (twoH * ℓ - plen) + 1) + 1 ≤ cap2) (hcK : twoH * ℓ - plen ≤ cK)
    (hcE1 : loopCost ℓ twoH k plen cons.length + 1 + 1 ≤ cE)
    (hcE2 : Gauss.gaussCost (cons.length * k) (twoH * ℓ - plen) ≤ cE) (hcE3 : Deficit.cost (twoH * ℓ - plen) ≤ cE) :
    ∃ O' W' P' : List Bool, Step elimM (elimCost ℓ twoH k plen cons.length) (fun _ => 0)
      (bank31 p ℓ twoH plen pfx m cap cap2 cap3 cap4 RV cL cE R0 backingO (consTape ℓ k cons stale) W P (pad cK [])
        (pad cC (List.replicate (twoH * ℓ - plen) true)) [g0] Xold)
      (fun _ => 0)
      (bank31 p ℓ twoH plen pfx m cap cap2 cap3 cap4 RV cL cE (regsAt p ℓ twoH k plen R0 cons cons.length) O'
        (consTape ℓ k cons stale) W' P' (pad cK []) (pad cC (List.replicate (twoH * ℓ - plen) true))
        [(gauss (twoH * ℓ - plen) (system p ℓ twoH k plen pfx cons)).1]
        (overlay (List.replicate (twoH * ℓ - plen - (gauss (twoH * ℓ - plen) (system p ℓ twoH k plen pfx cons)).2) true
          ++ [false]) Xold)) := by
  have h1 := rowsAll_run p ℓ twoH k plen pfx m cap cap2 cap3 cap4 RV cL cE R0 cons stale backingO W P (pad cK [])
    (pad cC (List.replicate (twoH * ℓ - plen) true)) [g0] Xold hℓ hkl h0 hcap hcap2 hcap2' hcap2'' hcap3 hcap3' hcap4
    hplen hm hRV hcL hcE1
  set rowsL := system p ℓ twoH k plen pfx cons
  have hlen : rowsL.length = cons.length * k := system_length p ℓ twoH k plen pfx cons
  have eR : overlay (rowsI p ℓ twoH k plen pfx cons cons.length ++ [false]) backingO =
      Gauss.rowsTape (rowsL.map (Gauss.rowBits (twoH * ℓ - plen)))
        (backingO.drop ((rowsI p ℓ twoH k plen pfx cons cons.length).length + 1)) := by
    rw [Gauss.overlay_term]
    unfold Gauss.rowsTape
    rw [loop_system p ℓ twoH k plen pfx cons hp hℓ hplen hcons]
  rw [eR] at h1
  obtain ⟨O', W', P', h2⟩ := count_run p ℓ twoH plen pfx m cap cap2 cap3 cap4 RV cL cE cK cC
    (regsAt p ℓ twoH k plen R0 cons cons.length) rowsL (system_lt p ℓ twoH k plen pfx cons)
    (backingO.drop ((rowsI p ℓ twoH k plen pfx cons cons.length).length + 1)) (consTape ℓ k cons stale) W P Xold g0
    hcapG (by rw [hlen]; exact hcapG') (by rw [hlen]; exact hcapG'') hcK (by rw [hlen]; exact hcE2) hcE3
  refine ⟨O', W', P', ?_⟩
  have hall := h1.seq h2
  unfold elimM elimCost
  rw [← hlen]
  exact hall

/-- **The ports the builders read** after `elim_run`: the flag cell `G`, the exponent tape `X`, the blank rank tape and
the unchanged counter; every head is back at cell 0. -/
theorem elim_ports (p ℓ twoH k plen pfx m cap cap2 cap3 cap4 RV cL cE cK cC : ℕ) (R0 : Regs) (cons : List (ℕ × ℕ))
    (stale backingO W P Xold : List Bool) (g0 : Bool) (hp : GF.ModulusOk p ℓ) (hℓ : 1 ≤ ℓ) (hkl : k ≤ ℓ)
    (h0 : R0.Ok ℓ twoH) (hcons : ∀ con ∈ cons, con.1 < 2 ^ ℓ)
    (hcap : 2 * ℓ + 2 ≤ cap) (hcap2 : ℓ * (innerCost ℓ + 2) + 1 ≤ cap2)
    (hcap2' : ℓ * (mulIterCost ℓ + 2) + 1 ≤ cap2) (hcap2'' : plen * (phACost ℓ + 2) + 1 ≤ cap2)
    (hcap3 : tableCost ℓ twoH ≤ cap3) (hcap3' : passesCost ℓ plen (twoH * ℓ) ≤ cap3)
    (hcap4 : k * (rowCost ℓ plen (twoH * ℓ) + 2) + 1 ≤ cap4) (hplen : plen ≤ twoH * ℓ) (hm : 1 ≤ m)
    (hRV : 2 * ℓ + 1 ≤ RV) (hcL : 2 * ℓ + 1 ≤ cL)
    (hcapG : 2 * (twoH * ℓ - plen) + 13 ≤ cap)
    (hcapG' : cons.length * k * (Gauss.rowCost (twoH * ℓ - plen) + 2) + 3 ≤ cap2)
    (hcapG'' : cons.length * k * (2 * (twoH * ℓ - plen) + 1) + 1 ≤ cap2) (hcK : twoH * ℓ - plen ≤ cK)
    (hcE1 : loopCost ℓ twoH k plen cons.length + 1 + 1 ≤ cE)
    (hcE2 : Gauss.gaussCost (cons.length * k) (twoH * ℓ - plen) ≤ cE) (hcE3 : Deficit.cost (twoH * ℓ - plen) ≤ cE) :
    ∃ A' : Fin 31 → List Bool, Step elimM (elimCost ℓ twoH k plen cons.length) (fun _ => 0)
      (bank31 p ℓ twoH plen pfx m cap cap2 cap3 cap4 RV cL cE R0 backingO (consTape ℓ k cons stale) W P (pad cK [])
        (pad cC (List.replicate (twoH * ℓ - plen) true)) [g0] Xold) (fun _ => 0) A' ∧
      A' 29 = [(gauss (twoH * ℓ - plen) (system p ℓ twoH k plen pfx cons)).1] ∧
      A' 30 = overlay (List.replicate (twoH * ℓ - plen - (gauss (twoH * ℓ - plen) (system p ℓ twoH k plen pfx cons)).2)
        true ++ [false]) Xold ∧
      A' 27 = pad cK [] ∧ A' 28 = pad cC (List.replicate (twoH * ℓ - plen) true) := by
  obtain ⟨O', W', P', h⟩ := elim_run p ℓ twoH k plen pfx m cap cap2 cap3 cap4 RV cL cE cK cC R0 cons stale backingO W P
    Xold g0 hp hℓ hkl h0 hcons hcap hcap2 hcap2' hcap2'' hcap3 hcap3' hcap4 hplen hm hRV hcL hcapG hcapG' hcapG'' hcK
    hcE1 hcE2 hcE3
  exact ⟨_, h, rfl, rfl, rfl, rfl⟩

/-- **The count**: the flag and the exponent written by `elim_run` are `condProbGauss`'s count, `0` or
`2^{rest − rank}`, the number of completions of the prefix meeting every constraint. -/
theorem elim_count (p ℓ twoH k plen pfx : ℕ) (cons : List (ℕ × ℕ)) :
    (if (gauss (twoH * ℓ - plen) (system p ℓ twoH k plen pfx cons)).1 then
        2 ^ (twoH * ℓ - plen - (gauss (twoH * ℓ - plen) (system p ℓ twoH k plen pfx cons)).2) else 0) =
      (condProbGauss p ℓ twoH k plen pfx cons).1 :=
  count_eq p ℓ twoH k plen pfx cons

/-! ## The cost in a named class -/

theorem recCost_le (ℓ twoH k plen q : ℕ) (hq : 1 ≤ q) (hl : ℓ ≤ q) (ht : twoH ≤ q) (hk : k ≤ q)
    (hp : plen ≤ twoH * ℓ) : recCost ℓ twoH k plen ≤ 1033 * q ^ 4 := by
  have hc := consCost_le ℓ twoH k plen q hq hl ht hk hp
  unfold recCost labCost tgtCost clrCost
  have h4 : q ≤ q ^ 4 := by
    calc q = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ 4 := Nat.pow_le_pow_right hq (by norm_num)
  have h1 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ hq
  omega

/-- **The block's cost**: `≤ 3000 q⁶` for `ℓ, 2h, k` and the number of constraints `≤ q`. -/
theorem elimCost_le (ℓ twoH k plen n q : ℕ) (hq : 1 ≤ q) (hl : ℓ ≤ q) (ht : twoH ≤ q) (hk : k ≤ q) (hn : n ≤ q)
    (hp : plen ≤ twoH * ℓ) : elimCost ℓ twoH k plen n ≤ 3000 * q ^ 6 := by
  have hrec := recCost_le ℓ twoH k plen q hq hl ht hk hp
  have hq2 : twoH * ℓ ≤ q ^ 2 := by rw [sq]; exact Nat.mul_le_mul ht hl
  have hnk : n * k ≤ q ^ 2 := by rw [sq]; exact Nat.mul_le_mul hn hk
  have hr : twoH * ℓ - plen ≤ q ^ 2 := le_trans (Nat.sub_le _ _) hq2
  have hQ : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
  have hg := Gauss.gaussCost_le (n * k) (twoH * ℓ - plen) (q ^ 2) hQ hnk hr
  have e6 : (q ^ 2) ^ 3 = q ^ 6 := by ring
  rw [e6] at hg
  have hloop : loopCost ℓ twoH k plen n ≤ 1036 * q ^ 5 := by
    unfold loopCost
    have hm : n * (recCost ℓ twoH k plen + 2) ≤ q * (1035 * q ^ 4) := Nat.mul_le_mul hn (by
      have : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ hq
      omega)
    have e : q * (1035 * q ^ 4) = 1035 * q ^ 5 := by ring
    have h5 : 1 ≤ q ^ 5 := Nat.one_le_pow _ _ hq
    omega
  have hdef : Deficit.cost (twoH * ℓ - plen) ≤ 6 * q ^ 2 := by unfold Deficit.cost; omega
  unfold elimCost rowsAllCost countCost
  have h56 : q ^ 5 ≤ q ^ 6 := Nat.pow_le_pow_right hq (by norm_num)
  have h26 : q ^ 2 ≤ q ^ 6 := Nat.pow_le_pow_right hq (by norm_num)
  have h16 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ hq
  omega

/-- **The block in a named class** (any class of degree `≥ 6`, e.g. preprocessing when `E.Apre ≥ 6`). -/
theorem elim_within {E : Envelope} {cls : BudgetClass} {q kk psi ℓ twoH k plen n : ℕ} (hq : 1 ≤ q) (hl : ℓ ≤ q)
    (ht : twoH ≤ q) (hk : k ≤ q) (hn : n ≤ q) (hp : plen ≤ twoH * ℓ) (hd : 6 ≤ classDeg E cls) :
    Within E cls 3000 q kk psi (elimCost ℓ twoH k plen n) :=
  Within.of_poly hq (elimCost_le ℓ twoH k plen n q hq hl ht hk hn hp) hd

end NearCubicWires.WireExponent3_5.SeedFix
