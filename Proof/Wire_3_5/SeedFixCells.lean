import Proof.Wire_3_5.SeedFixSplit
import Proof.Wire_3_5.SeedFixSampFlat

/-! # C4.Sb, machine part 10: the eight cell words of a walk

Edge slot `k` of a walk `w` reads the cell `(w k, w (k+1))` on even slots and `(w (k+1), w k)` on odd slots
(`cellOf`), and a cell's number is `v + N·u` (`cellNumC`), so its `2kh`-bit word is the low digit word followed by the
high one. From the digit stream `d₀ … d₇` and the rotated stream `d₁ … d₇ d₀` (the split) the cell block writes the
eight framed cell words: `pairs(d_{k+1}) ++ frame(d_k)` on even slots and `pairs(d_k) ++ frame(d_{k+1})` on odd ones.

Paper quantities of the main type: the framed words of the eight cells of the walk (`cells_run`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SeedFix
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.WireExponent3_5.Block
open NearCubicWires.WireExponent3_5.GF2 NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write)
open Split

namespace Cells

/-! ## Slot maps (tapes 0 the digit stream, 1 the rotated stream, 2 the cell stream) -/

def c3N : Fin 2 → Fin 3 := ![1, 2]

theorem install_c3N (A : Fin 3 → List Bool) (v : Fin 2 → List Bool) :
    RecoveryRootRound.install c3N A v = ![A 0, v 0, v 1] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_c3N (H : Fin 3 → ℕ) (v : Fin 2 → ℕ) :
    dockH c3N H v = ![H 0, v 0, v 1] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_other _ _ _ _ (by decide)

def c3n : Fin 1 → Fin 3 := ![1]

theorem install_c3n (A : Fin 3 → List Bool) (v : Fin 1 → List Bool) :
    RecoveryRootRound.install c3n A v = ![A 0, v 0, A 2] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_c3n (H : Fin 3 → ℕ) (v : Fin 1 → ℕ) :
    dockH c3n H v = ![H 0, v 0, H 2] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_other _ _ _ _ (by decide)

def c3G : Fin 2 → Fin 3 := ![0, 2]

theorem install_c3G (A : Fin 3 → List Bool) (v : Fin 2 → List Bool) :
    RecoveryRootRound.install c3G A v = ![v 0, A 1, v 1] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_c3G (H : Fin 3 → ℕ) (v : Fin 2 → ℕ) :
    dockH c3G H v = ![v 0, H 1, v 1] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_other _ _ _ _ (by decide)

def c3g : Fin 1 → Fin 3 := ![0]

theorem install_c3g (A : Fin 3 → List Bool) (v : Fin 1 → List Bool) :
    RecoveryRootRound.install c3g A v = ![v 0, A 1, A 2] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_c3g (H : Fin 3 → ℕ) (v : Fin 1 → ℕ) :
    dockH c3g H v = ![v 0, H 1, H 2] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_other _ _ _ _ (by decide)

def c3E : Fin 1 → Fin 3 := ![2]

theorem install_c3E (A : Fin 3 → List Bool) (v : Fin 1 → List Bool) :
    RecoveryRootRound.install c3E A v = ![A 0, A 1, v 0] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_c3E (H : Fin 3 → ℕ) (v : Fin 1 → ℕ) :
    dockH c3E H v = ![H 0, H 1, v 0] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_other _ _ _ _ (by decide)

/-! ## One even and one odd cell -/

/-- An even slot: the rotated word's pairs, then the digit word framed. -/
noncomputable def cellE := Composition.machine (Composition.machine (RecoveryFocus.machine c3N (PairsC.machine true))
  (RecoveryFocus.machine c3n nudgeM)) (RecoveryFocus.machine c3G frameT)

/-- An odd slot: the digit word's pairs, then the rotated word framed. -/
noncomputable def cellO := Composition.machine (Composition.machine (RecoveryFocus.machine c3G (PairsC.machine true))
  (RecoveryFocus.machine c3g nudgeM)) (RecoveryFocus.machine c3N frameT)

def cellCost (a b : ℕ) : ℕ := (2 * a + 1) + 1 + 1 + 1 + (2 * b + 1 + 1 + 1)

theorem cellE_run (pG pN g n tG tN o B : List Bool) :
    Step cellE (cellCost n.length g.length) ![pG.length, pN.length, o.length]
      ![pG ++ frame g ++ tG, pN ++ frame n ++ tN, overlay o B]
      ![pG.length + (frame g).length, pN.length + (frame n).length, (o ++ (pairsOf n ++ frame g)).length]
      ![pG ++ frame g ++ tG, pN ++ frame n ++ tN, overlay (o ++ (pairsOf n ++ frame g)) B] := by
  set SG := pG ++ frame g ++ tG
  set SN := pN ++ frame n ++ tN
  have h1 := PairsC.run true pN n tN o B
  simp only [owC, if_true] at h1
  have s1 := dockRun h1 c3N (by decide) ![pG.length, pN.length, o.length] ![SG, SN, overlay o B]
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  rw [dockH_c3N, install_c3N] at s1
  have s2 := dockRun (nudge_run SN (pN.length + 2 * n.length)) c3n (by decide)
    ![pG.length, pN.length + 2 * n.length, (o ++ pairsOf n).length] ![SG, SN, overlay (o ++ pairsOf n) B]
    (by intro i; fin_cases i; rfl) (by intro i; fin_cases i; rfl)
  rw [dockH_c3n, install_c3n] at s2
  have h3 := frameT_run pG g tG (o ++ pairsOf n) B
  have s3 := dockRun h3 c3G (by decide) ![pG.length, pN.length + 2 * n.length + 1, (o ++ pairsOf n).length]
    ![SG, SN, overlay (o ++ pairsOf n) B] (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  rw [dockH_c3G, install_c3G] at s3
  have hall := ((s1.congr (hout' := ![pG.length, pN.length + 2 * n.length, (o ++ pairsOf n).length])
      (tout' := ![SG, SN, overlay (o ++ pairsOf n) B]) (by funext i; fin_cases i <;> rfl)
      (by funext i; fin_cases i <;> rfl)).seq
    (s2.congr (hout' := ![pG.length, pN.length + 2 * n.length + 1, (o ++ pairsOf n).length])
      (tout' := ![SG, SN, overlay (o ++ pairsOf n) B]) (by funext i; fin_cases i <;> rfl)
      (by funext i; fin_cases i <;> rfl))).seq s3
  refine hall.congr ?_ ?_
  · funext i; fin_cases i
    · rfl
    · show pN.length + 2 * n.length + 1 = pN.length + (frame n).length; rw [frame_length]; omega
    · show (o ++ pairsOf n ++ frame g).length = (o ++ (pairsOf n ++ frame g)).length; simp
  · funext i; fin_cases i
    · rfl
    · rfl
    · show overlay (o ++ pairsOf n ++ frame g) B = overlay (o ++ (pairsOf n ++ frame g)) B; rw [List.append_assoc]

theorem cellO_run (pG pN g n tG tN o B : List Bool) :
    Step cellO (cellCost g.length n.length) ![pG.length, pN.length, o.length]
      ![pG ++ frame g ++ tG, pN ++ frame n ++ tN, overlay o B]
      ![pG.length + (frame g).length, pN.length + (frame n).length, (o ++ (pairsOf g ++ frame n)).length]
      ![pG ++ frame g ++ tG, pN ++ frame n ++ tN, overlay (o ++ (pairsOf g ++ frame n)) B] := by
  set SG := pG ++ frame g ++ tG
  set SN := pN ++ frame n ++ tN
  have h1 := PairsC.run true pG g tG o B
  simp only [owC, if_true] at h1
  have s1 := dockRun h1 c3G (by decide) ![pG.length, pN.length, o.length] ![SG, SN, overlay o B]
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  rw [dockH_c3G, install_c3G] at s1
  have s2 := dockRun (nudge_run SG (pG.length + 2 * g.length)) c3g (by decide)
    ![pG.length + 2 * g.length, pN.length, (o ++ pairsOf g).length] ![SG, SN, overlay (o ++ pairsOf g) B]
    (by intro i; fin_cases i; rfl) (by intro i; fin_cases i; rfl)
  rw [dockH_c3g, install_c3g] at s2
  have h3 := frameT_run pN n tN (o ++ pairsOf g) B
  have s3 := dockRun h3 c3N (by decide) ![pG.length + 2 * g.length + 1, pN.length, (o ++ pairsOf g).length]
    ![SG, SN, overlay (o ++ pairsOf g) B] (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  rw [dockH_c3N, install_c3N] at s3
  have hall := ((s1.congr (hout' := ![pG.length + 2 * g.length, pN.length, (o ++ pairsOf g).length])
      (tout' := ![SG, SN, overlay (o ++ pairsOf g) B]) (by funext i; fin_cases i <;> rfl)
      (by funext i; fin_cases i <;> rfl)).seq
    (s2.congr (hout' := ![pG.length + 2 * g.length + 1, pN.length, (o ++ pairsOf g).length])
      (tout' := ![SG, SN, overlay (o ++ pairsOf g) B]) (by funext i; fin_cases i <;> rfl)
      (by funext i; fin_cases i <;> rfl))).seq s3
  refine hall.congr ?_ ?_
  · funext i; fin_cases i
    · show pG.length + 2 * g.length + 1 = pG.length + (frame g).length; rw [frame_length]; omega
    · rfl
    · show (o ++ pairsOf g ++ frame n).length = (o ++ (pairsOf g ++ frame n)).length; simp
  · funext i; fin_cases i
    · rfl
    · rfl
    · show overlay (o ++ pairsOf g ++ frame n) B = overlay (o ++ (pairsOf g ++ frame n)) B; rw [List.append_assoc]

/-! ## Two cells, then the eight -/

noncomputable def pairM := Composition.machine cellE cellO

def pairCost (a b c d : ℕ) : ℕ := cellCost b a + 1 + cellCost c d

theorem pair_run (S T pG pN g0 g1 n0 n1 tG tN o B : List Bool) (hS : S = pG ++ frame g0 ++ (frame g1 ++ tG))
    (hT : T = pN ++ frame n0 ++ (frame n1 ++ tN)) :
    Step pairM (pairCost g0.length n0.length g1.length n1.length) ![pG.length, pN.length, o.length]
      ![S, T, overlay o B]
      ![(pG ++ frame g0 ++ frame g1).length, (pN ++ frame n0 ++ frame n1).length,
        (o ++ (pairsOf n0 ++ frame g0) ++ (pairsOf g1 ++ frame n1)).length]
      ![S, T, overlay (o ++ (pairsOf n0 ++ frame g0) ++ (pairsOf g1 ++ frame n1)) B] := by
  have h1 := cellE_run pG pN g0 n0 (frame g1 ++ tG) (frame n1 ++ tN) o B
  rw [← hS, ← hT] at h1
  have hS' : S = (pG ++ frame g0) ++ frame g1 ++ tG := by rw [hS]; simp
  have hT' : T = (pN ++ frame n0) ++ frame n1 ++ tN := by rw [hT]; simp
  have h2 := cellO_run (pG ++ frame g0) (pN ++ frame n0) g1 n1 tG tN (o ++ (pairsOf n0 ++ frame g0)) B
  rw [← hS', ← hT'] at h2
  have hall := (h1.congr (hout' := ![(pG ++ frame g0).length, (pN ++ frame n0).length,
      (o ++ (pairsOf n0 ++ frame g0)).length]) (tout' := ![S, T, overlay (o ++ (pairsOf n0 ++ frame g0)) B])
      (by funext i; fin_cases i <;> simp) (by funext i; fin_cases i <;> rfl)).seq h2
  refine hall.congr ?_ ?_
  · funext i; fin_cases i <;> simp <;> omega
  · funext i; fin_cases i <;> rfl

/-- The eight framed cell words of digit words `g₀ … g₇` (the walk's vertices), slot by slot. -/
def cellsOut (g0 g1 g2 g3 g4 g5 g6 g7 : List Bool) : List Bool :=
  (pairsOf g1 ++ frame g0) ++ (pairsOf g1 ++ frame g2) ++ (pairsOf g3 ++ frame g2) ++ (pairsOf g3 ++ frame g4) ++
    (pairsOf g5 ++ frame g4) ++ (pairsOf g5 ++ frame g6) ++ (pairsOf g7 ++ frame g6) ++ (pairsOf g7 ++ frame g0)

noncomputable def cellsInner :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine pairM pairM) pairM) pairM)
    (RecoveryFocus.machine c3E EndF.machine)

def selC3 : Fin 3 → Bool := ![true, true, true]

/-- **The cell block**: the eight framed cell words and a terminator, every head back at cell 0. -/
noncomputable def cellsM := MaskedReset.machine cellsInner selC3

def cellsInnerCost (r : ℕ) : ℕ :=
  pairCost r r r r + 1 + pairCost r r r r + 1 + pairCost r r r r + 1 + pairCost r r r r + 1 + 1

theorem cells_run (r : ℕ) (g0 g1 g2 g3 g4 g5 g6 g7 tG tN CLo : List Bool) (cap : ℕ)
    (h0 : g0.length = r) (h1 : g1.length = r) (h2 : g2.length = r) (h3 : g3.length = r) (h4 : g4.length = r)
    (h5 : g5.length = r) (h6 : g6.length = r) (h7 : g7.length = r) (hcap : cellsInnerCost r ≤ cap) :
    Step cellsM (2 * cellsInnerCost r + 2) (fun _ => 0)
      ![[g0, g1, g2, g3, g4, g5, g6, g7].flatMap frame ++ tG, [g1, g2, g3, g4, g5, g6, g7, g0].flatMap frame ++ tN,
        CLo, List.replicate cap false]
      (fun _ => 0)
      ![[g0, g1, g2, g3, g4, g5, g6, g7].flatMap frame ++ tG, [g1, g2, g3, g4, g5, g6, g7, g0].flatMap frame ++ tN,
        overlay (cellsOut g0 g1 g2 g3 g4 g5 g6 g7 ++ [false]) CLo, List.replicate cap false] := by
  set S := [g0, g1, g2, g3, g4, g5, g6, g7].flatMap frame ++ tG
  set T := [g1, g2, g3, g4, g5, g6, g7, g0].flatMap frame ++ tN
  set c01 := (pairsOf g1 ++ frame g0) ++ (pairsOf g1 ++ frame g2)
  set c23 := (pairsOf g3 ++ frame g2) ++ (pairsOf g3 ++ frame g4)
  set c45 := (pairsOf g5 ++ frame g4) ++ (pairsOf g5 ++ frame g6)
  set c67 := (pairsOf g7 ++ frame g6) ++ (pairsOf g7 ++ frame g0)
  have p0 := pair_run S T [] [] g0 g1 g1 g2 ([g2, g3, g4, g5, g6, g7].flatMap frame ++ tG)
    ([g3, g4, g5, g6, g7, g0].flatMap frame ++ tN) [] CLo (by simp [S]) (by simp [T])
  have p1 := pair_run S T (frame g0 ++ frame g1) (frame g1 ++ frame g2) g2 g3 g3 g4
    ([g4, g5, g6, g7].flatMap frame ++ tG) ([g5, g6, g7, g0].flatMap frame ++ tN) c01 CLo
    (by simp [S]) (by simp [T])
  have p2 := pair_run S T (frame g0 ++ frame g1 ++ (frame g2 ++ frame g3))
    (frame g1 ++ frame g2 ++ (frame g3 ++ frame g4)) g4 g5 g5 g6
    ([g6, g7].flatMap frame ++ tG) ([g7, g0].flatMap frame ++ tN) (c01 ++ c23) CLo
    (by simp [S]) (by simp [T])
  have p3 := pair_run S T (frame g0 ++ frame g1 ++ (frame g2 ++ frame g3) ++ (frame g4 ++ frame g5))
    (frame g1 ++ frame g2 ++ (frame g3 ++ frame g4) ++ (frame g5 ++ frame g6)) g6 g7 g7 g0
    tG tN (c01 ++ c23 ++ c45) CLo (by simp [S]) (by simp [T])
  have hE := dockRun (EndF.run (c01 ++ c23 ++ c45 ++ c67) CLo) c3E (by decide)
    ![(frame g0 ++ frame g1 ++ (frame g2 ++ frame g3) ++ (frame g4 ++ frame g5) ++ (frame g6 ++ frame g7)).length,
      (frame g1 ++ frame g2 ++ (frame g3 ++ frame g4) ++ (frame g5 ++ frame g6) ++ (frame g7 ++ frame g0)).length,
      (c01 ++ c23 ++ c45 ++ c67).length] ![S, T, overlay (c01 ++ c23 ++ c45 ++ c67) CLo]
    (by intro i; fin_cases i; rfl) (by intro i; fin_cases i; rfl)
  rw [dockH_c3E, install_c3E] at hE
  have q01 := p0.congr (hout' := ![(frame g0 ++ frame g1).length, (frame g1 ++ frame g2).length, c01.length])
    (tout' := ![S, T, overlay c01 CLo]) (by funext i; fin_cases i <;> simp [c01])
    (by funext i; fin_cases i <;> simp [c01])
  have q12 := p1.congr (hout' := ![(frame g0 ++ frame g1 ++ (frame g2 ++ frame g3)).length,
      (frame g1 ++ frame g2 ++ (frame g3 ++ frame g4)).length, (c01 ++ c23).length])
    (tout' := ![S, T, overlay (c01 ++ c23) CLo]) (by funext i; fin_cases i <;> simp [c23])
    (by funext i; fin_cases i <;> simp [c23])
  have q23 := p2.congr (hout' := ![(frame g0 ++ frame g1 ++ (frame g2 ++ frame g3) ++ (frame g4 ++ frame g5)).length,
      (frame g1 ++ frame g2 ++ (frame g3 ++ frame g4) ++ (frame g5 ++ frame g6)).length, (c01 ++ c23 ++ c45).length])
    (tout' := ![S, T, overlay (c01 ++ c23 ++ c45) CLo]) (by funext i; fin_cases i <;> simp [c45])
    (by funext i; fin_cases i <;> simp [c45])
  have q34 := p3.congr (hout' := ![(frame g0 ++ frame g1 ++ (frame g2 ++ frame g3) ++ (frame g4 ++ frame g5) ++
        (frame g6 ++ frame g7)).length,
      (frame g1 ++ frame g2 ++ (frame g3 ++ frame g4) ++ (frame g5 ++ frame g6) ++ (frame g7 ++ frame g0)).length,
      (c01 ++ c23 ++ c45 ++ c67).length])
    (tout' := ![S, T, overlay (c01 ++ c23 ++ c45 ++ c67) CLo]) (by funext i; fin_cases i <;> simp [c67])
    (by funext i; fin_cases i <;> simp [c67])
  have q0 := q01.congr_in (hin' := fun _ => 0) (tin' := ![S, T, CLo]) (by funext i; fin_cases i <;> rfl)
    (by funext i; fin_cases i <;> simp [overlay])
  have hall := (((q0.seq q12).seq q23).seq q34).seq hE
  rw [h0, h1, h2, h3, h4, h5, h6, h7] at hall
  have hm := hall.mask (cap := cap) selC3 (by intro i _; fin_cases i <;> rfl) hcap
  have eo : c01 ++ c23 ++ c45 ++ c67 ++ [false] = cellsOut g0 g1 g2 g3 g4 g5 g6 g7 ++ [false] := by
    simp [c01, c23, c45, c67, cellsOut]
  rw [eo] at hm
  refine (hm.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> fin_cases i <;> rfl

/-! ## The cell words of the counter's walk (the link to `cellOf` and `cellNumC`) -/

theorem binary_mod : ∀ (w n : ℕ), binary w (n % 2 ^ w) = binary w n
  | 0, _ => rfl
  | w + 1, n => by
    rw [show binary (w + 1) (n % 2 ^ (w + 1)) = (n % 2 ^ (w + 1) % 2 == 1) :: binary w (n % 2 ^ (w + 1) / 2) from rfl,
      show binary (w + 1) n = (n % 2 == 1) :: binary w (n / 2) from rfl]
    have h1 : n % 2 ^ (w + 1) % 2 = n % 2 := by
      rw [pow_succ', Nat.mod_mul_right_mod]
    have h2 : n % 2 ^ (w + 1) / 2 = n / 2 % 2 ^ w := by
      rw [pow_succ', Nat.mod_mul_right_div_self]
    rw [h1, h2, binary_mod w (n / 2)]

theorem frame_append (u v : List Bool) : frame (u ++ v) = pairsOf u ++ frame v := by
  rw [frame_pairs, frame_pairs, pairsOf_append, List.append_assoc]

/-- A cell's `2kh`-bit word: the column's digit word, then the row's. -/
theorem cellNum_binary (kh : ℕ) (u v : Fin (2 ^ kh)) :
    binary (2 * kh) (cellNumC ((u, v) : Fin (2 ^ kh) × Fin (2 ^ kh))) = binary kh v ++ binary kh u := by
  unfold cellNumC
  rw [two_mul, binary_add_split]
  have hv := v.isLt
  congr 1
  · rw [← binary_mod kh, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hv]
  · rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hv, Nat.zero_add]

section Link
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Sampler
variable (P : SeedParams)

/-- The digit word of the counter's walk at slot `k`. -/
def digW (j : ℕ) (k : Fin 8) : List Bool := binary P.kh (wOf P j k : ℕ)

theorem digW_length (j : ℕ) (k : Fin 8) : (digW P j k).length = P.kh := binary_length _ _

theorem digsOf_eq (j : ℕ) :
    digsOf P.ell P.kh j = [digW P j 0, digW P j 1, digW P j 2, digW P j 3, digW P j 4, digW P j 5, digW P j 6,
      digW P j 7] := by
  have e : ∀ k : Fin 8, binary P.kh (j / 2 ^ (8 + 8 * P.ell) / 2 ^ ((k : ℕ) * P.kh)) = digW P j k := by
    intro k
    unfold digW wOf
    rw [binary_mod]
    congr 2
    · rw [← pow_mul, ← pow_add]; ring_nf
    · rw [SeedParams.N, ← pow_mul, mul_comm]
  unfold digsOf fields8
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append]
  rw [← e 0, ← e 1, ← e 2, ← e 3, ← e 4, ← e 5, ← e 6, ← e 7]
  rfl

/-- The framed word of slot `k`'s cell. -/
def cellW (j : ℕ) (k : Fin 8) : List Bool :=
  binary (2 * P.kh) (cellNumC (cellOf (by norm_num) (wOf P j) k))

/-- **The cell block's output is the eight framed cell words of the counter's walk.** -/
theorem cellsOut_eq (j : ℕ) :
    cellsOut (digW P j 0) (digW P j 1) (digW P j 2) (digW P j 3) (digW P j 4) (digW P j 5) (digW P j 6)
      (digW P j 7) = (List.finRange 8).flatMap fun k => frame (cellW P j k) := by
  have ce : ∀ k : Fin 8, cellW P j k = if (k : ℕ) % 2 = 0 then digW P j (nextSlot (by norm_num) k) ++ digW P j k
      else digW P j k ++ digW P j (nextSlot (by norm_num) k) := by
    intro k
    unfold cellW cellOf
    split <;> exact cellNum_binary P.kh _ _
  have c0 : cellW P j 0 = digW P j 1 ++ digW P j 0 := by rw [ce, if_pos (by decide)]; rfl
  have c1 : cellW P j 1 = digW P j 1 ++ digW P j 2 := by rw [ce, if_neg (by decide)]; rfl
  have c2 : cellW P j 2 = digW P j 3 ++ digW P j 2 := by rw [ce, if_pos (by decide)]; rfl
  have c3 : cellW P j 3 = digW P j 3 ++ digW P j 4 := by rw [ce, if_neg (by decide)]; rfl
  have c4 : cellW P j 4 = digW P j 5 ++ digW P j 4 := by rw [ce, if_pos (by decide)]; rfl
  have c5 : cellW P j 5 = digW P j 5 ++ digW P j 6 := by rw [ce, if_neg (by decide)]; rfl
  have c6 : cellW P j 6 = digW P j 7 ++ digW P j 6 := by rw [ce, if_pos (by decide)]; rfl
  have c7 : cellW P j 7 = digW P j 7 ++ digW P j 0 := by rw [ce, if_neg (by decide)]; rfl
  have hL : List.finRange 8 = [0, 1, 2, 3, 4, 5, 6, 7] := by decide
  rw [hL]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, c0, c1, c2, c3, c4, c5, c6, c7, frame_append,
    cellsOut, List.append_assoc]

end Link

end Cells

end NearCubicWires.WireExponent3_5.SeedFix
