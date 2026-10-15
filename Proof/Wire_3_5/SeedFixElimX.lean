import Proof.Wire_3_5.SeedFixElim

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SeedFix
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.GF2 NearCubicWires.WireExponent3_5.JoinElimination
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write)
open NearCubicWires.RepairOrdinary.ZeroPadding (pad)

namespace ElimX

/-- The column state after the elimination's last column. -/
def gFin (nvars : ℕ) (rows : List Row) (stale W P : List Bool) : Gauss.ColState :=
  Gauss.colState ⟨rows.map (Gauss.rowBits nvars), 0, stale, W, P⟩ nvars

theorem gaussPX_run (nvars : ℕ) (rows : List Row) (hrows : ∀ r ∈ rows, r.1 < 2 ^ nvars) (stale W P : List Bool)
    (cap cap' cK cC : ℕ) (hcap : 2 * nvars + 13 ≤ cap) (hcap' : rows.length * (Gauss.rowCost nvars + 2) + 3 ≤ cap')
    (hcap'' : rows.length * (2 * nvars + 1) + 1 ≤ cap') :
    Step Gauss.gaussM (Gauss.gaussCost rows.length nvars)
      ![0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![Gauss.rowsTape (rows.map (Gauss.rowBits nvars)) stale, W, P, [false], List.replicate cap false, pad cK [],
        pad cC (List.replicate nvars true), [true], List.replicate cap' false]
      ![3 * (gFin nvars rows stale W P).reps.length, 0, 0, 0, 0, (gauss nvars rows).2, nvars, 0, 0]
      ![Gauss.rowsTape (gFin nvars rows stale W P).reps (gFin nvars rows stale W P).stale, (gFin nvars rows stale W P).W,
        (gFin nvars rows stale W P).P, [false], List.replicate cap false, pad cK (List.replicate (gauss nvars rows).2 true),
        pad cC (List.replicate nvars true), [(gauss nvars rows).1], List.replicate cap' false] := by
  let s0 : Gauss.ColState := ⟨rows.map (Gauss.rowBits nvars), 0, stale, W, P⟩
  have h0 : ∀ r ∈ s0.reps, r.length = nvars + 1 := by
    intro r hr
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hr
    simp [Gauss.rowBits]
  have hm : s0.reps.length = rows.length := by simp [s0]
  have hraw := Gauss.gauss_raw s0 nvars cap cap' h0 hcap (by rw [hm]; exact hcap') (by rw [hm]; exact hcap'')
  have hcnt : (Gauss.colState s0 nvars).reps.length ≤ rows.length := hm ▸ Gauss.colState_count s0 nvars
  have hsteps : nvars * (Gauss.colBound s0.reps.length nvars + 2) + 1 + 1 +
      (3 * (Gauss.colState s0 nvars).reps.length + 1) ≤ Gauss.gaussCost rows.length nvars := by
    unfold Gauss.gaussCost
    rw [hm]
    omega
  have hg : Gauss.gaussDrop nvars rows =
      ((Gauss.colState s0 nvars).reps.all (fun r => !(r.headD false)), (Gauss.colState s0 nvars).rank) := by
    have hp := Gauss.colState_passes s0 nvars
    unfold Gauss.gaussDrop
    simp only [s0] at hp
    rw [← hp]
  have hgauss := Gauss.gaussDrop_eq nvars rows hrows
  rw [hg] at hgauss
  have hpad := (hraw.enlarge hsteps).pad ![0, 0, 0, 0, 0, cK, cC, 0, 0]
  show Step Gauss.gaussM (Gauss.gaussCost rows.length nvars) _ _
    ![3 * (Gauss.colState s0 nvars).reps.length, 0, 0, 0, 0, (gauss nvars rows).2, nvars, 0, 0]
    ![Gauss.rowsTape (Gauss.colState s0 nvars).reps (Gauss.colState s0 nvars).stale, (Gauss.colState s0 nvars).W,
      (Gauss.colState s0 nvars).P, [false], List.replicate cap false, pad cK (List.replicate (gauss nvars rows).2 true),
      pad cC (List.replicate nvars true), [(gauss nvars rows).1], List.replicate cap' false]
  rw [← hgauss]
  refine (hpad.congr_in ?_ ?_).congr ?_ ?_
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> simp [pad, Gauss.colA, s0]
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> simp [pad]

theorem countX_run (p ℓ twoH plen pfx m cap cap2 cap3 cap4 RV cL cE cK cC : ℕ) (R : Regs) (rowsL : List Row)
    (hrows : ∀ r ∈ rowsL, r.1 < 2 ^ (twoH * ℓ - plen)) (stale S W P Xold : List Bool) (g0 : Bool)
    (hcapG : 2 * (twoH * ℓ - plen) + 13 ≤ cap)
    (hcapG' : rowsL.length * (Gauss.rowCost (twoH * ℓ - plen) + 2) + 3 ≤ cap2)
    (hcapG'' : rowsL.length * (2 * (twoH * ℓ - plen) + 1) + 1 ≤ cap2) (hcK : twoH * ℓ - plen ≤ cK)
    (hcE2 : Gauss.gaussCost rowsL.length (twoH * ℓ - plen) ≤ cE) (hcE3 : Deficit.cost (twoH * ℓ - plen) ≤ cE) :
    Step countM
      (countCost rowsL.length (twoH * ℓ - plen)) (fun _ => 0)
      (bank31 p ℓ twoH plen pfx m cap cap2 cap3 cap4 RV cL cE R
        (Gauss.rowsTape (rowsL.map (Gauss.rowBits (twoH * ℓ - plen))) stale) S W P (pad cK [])
        (pad cC (List.replicate (twoH * ℓ - plen) true)) [g0] Xold)
      (fun _ => 0)
      (bank31 p ℓ twoH plen pfx m cap cap2 cap3 cap4 RV cL cE R
        (Gauss.rowsTape (gFin (twoH * ℓ - plen) rowsL stale W P).reps (gFin (twoH * ℓ - plen) rowsL stale W P).stale) S
        (gFin (twoH * ℓ - plen) rowsL stale W P).W (gFin (twoH * ℓ - plen) rowsL stale W P).P (pad cK [])
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
  have hg := gaussPX_run rest rowsL hrows stale W P cap cap2 cK cC hcapG hcapG' hcapG''
  set R' := Gauss.rowsTape (gFin rest rowsL stale W P).reps (gFin rest rowsL stale W P).stale
  set W' := (gFin rest rowsL stale W P).W
  set P' := (gFin rest rowsL stale W P).P
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
  exact (s1'.seq s2').seq s3'

/-- The block's stale rows, pass-output and pivot tapes. -/
def elimStale (p ℓ twoH k plen pfx : ℕ) (cons : List (ℕ × ℕ)) (backingO : List Bool) : List Bool :=
  backingO.drop ((rowsI p ℓ twoH k plen pfx cons cons.length).length + 1)
def elimO (p ℓ twoH k plen pfx : ℕ) (cons : List (ℕ × ℕ)) (backingO W P : List Bool) : List Bool :=
  Gauss.rowsTape (gFin (twoH * ℓ - plen) (system p ℓ twoH k plen pfx cons) (elimStale p ℓ twoH k plen pfx cons backingO) W P).reps
    (gFin (twoH * ℓ - plen) (system p ℓ twoH k plen pfx cons) (elimStale p ℓ twoH k plen pfx cons backingO) W P).stale
def elimW (p ℓ twoH k plen pfx : ℕ) (cons : List (ℕ × ℕ)) (backingO W P : List Bool) : List Bool :=
  (gFin (twoH * ℓ - plen) (system p ℓ twoH k plen pfx cons) (elimStale p ℓ twoH k plen pfx cons backingO) W P).W
def elimP (p ℓ twoH k plen pfx : ℕ) (cons : List (ℕ × ℕ)) (backingO W P : List Bool) : List Bool :=
  (gFin (twoH * ℓ - plen) (system p ℓ twoH k plen pfx cons) (elimStale p ℓ twoH k plen pfx cons backingO) W P).P

theorem elimX_run (p ℓ twoH k plen pfx m cap cap2 cap3 cap4 RV cL cE cK cC : ℕ) (R0 : Regs) (cons : List (ℕ × ℕ))
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
    Step elimM (elimCost ℓ twoH k plen cons.length) (fun _ => 0)
      (bank31 p ℓ twoH plen pfx m cap cap2 cap3 cap4 RV cL cE R0 backingO (consTape ℓ k cons stale) W P (pad cK [])
        (pad cC (List.replicate (twoH * ℓ - plen) true)) [g0] Xold)
      (fun _ => 0)
      (bank31 p ℓ twoH plen pfx m cap cap2 cap3 cap4 RV cL cE (regsAt p ℓ twoH k plen R0 cons cons.length)
        (elimO p ℓ twoH k plen pfx cons backingO W P) (consTape ℓ k cons stale)
        (elimW p ℓ twoH k plen pfx cons backingO W P) (elimP p ℓ twoH k plen pfx cons backingO W P) (pad cK []) (pad cC (List.replicate (twoH * ℓ - plen) true))
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
  have h2 := countX_run p ℓ twoH plen pfx m cap cap2 cap3 cap4 RV cL cE cK cC
    (regsAt p ℓ twoH k plen R0 cons cons.length) rowsL (system_lt p ℓ twoH k plen pfx cons)
    (backingO.drop ((rowsI p ℓ twoH k plen pfx cons cons.length).length + 1)) (consTape ℓ k cons stale) W P Xold g0
    hcapG (by rw [hlen]; exact hcapG') (by rw [hlen]; exact hcapG'') hcK (by rw [hlen]; exact hcE2) hcE3
  have hall := h1.seq h2
  unfold elimM elimCost
  rw [← hlen]
  exact hall

end ElimX

end NearCubicWires.WireExponent3_5.SeedFix
