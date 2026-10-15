import Proof.Wire_3_5.CompilerMachinePoolDense

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-- **A uniform body once per entry of a framed list**, driven by the frame's marks: the source head reads cell
`2j` before pass `j`. -/
theorem frameRun {t s : ℕ} (body : Machine t s) (src : Fin t) (l tl : List Bool) (bH : ℕ → Fin t → ℕ)
    (bA : ℕ → Fin t → List Bool) (hsrcA : ∀ j, bA j src = frame l ++ tl) (hsrcH : ∀ j, bH j src = 2 * j) (c : ℕ)
    (hstep : ∀ j, j < l.length → Step body c (bH j) (bA j) (bH (j + 1)) (bA (j + 1))) :
    Step (StreamController.machine body src) (l.length * (c + 2) + 1) (bH 0) (bA 0) (bH l.length) (bA l.length) := by
  let W : WhileBody t s :=
    { body := body
      tape := src
      bound := l.length
      H := bH
      A := bA
      cost := fun _ => c
      step := fun j hj => hstep j hj
      cont := fun j hj => by
        show readTapeBit (bA j src) (bH j src) = true
        rw [hsrcA, hsrcH, read_prefix _ _ _ (by simp; omega)]
        exact read_frame_mark l j hj
      halt := by
        show readTapeBit (bA l.length src) (bH l.length src) = false
        rw [hsrcA, hsrcH, read_prefix _ _ _ (by simp)]
        exact read_frame_end l }
  have hW := W.run
  rw [W.rest_const c (fun _ => rfl)] at hW
  exact hW

/-- The coordinate loop's state: the two buffers' written parts, the accumulated sums, the three registers. -/
structure CoordSt where
  L : List Bool
  R : List Bool
  P : ℕ
  N : ℕ
  rp : List Bool
  rn : List Bool
  tmp : List Bool

/-- One coordinate's effect on the state (`coord_step`). -/
def cstep (h : ℕ) (st : CoordSt) (c : Coord) : CoordSt where
  L := if c.1 then st.L ++ pairF h c.2.1 (pn c.2.2) else st.L
  R := if c.1 then st.R else st.R ++ pairF h c.2.1 (pn c.2.2)
  P := accP c.2.1 st.P (pn c.2.2).2
  N := accN c.2.1 st.N (pn c.2.2).1
  rp := overlay (frame (binary h (pn c.2.2).1)) st.rp
  rn := overlay (frame (binary h (pn c.2.2).2)) st.rn
  tmp := tmpAfter h c.2.1 st.P st.N (pn c.2.2).1 (pn c.2.2).2 st.tmp

theorem cfold_L (h : ℕ) : ∀ (cs : List Coord) (st : CoordSt), (cs.foldl (cstep h) st).L = st.L ++ leftPart h cs
  | [], st => by simp [leftPart]
  | c :: cs, st => by
    rw [List.foldl_cons, cfold_L h cs]
    by_cases hc : c.1 = true <;> simp [cstep, leftPart, hc, List.append_assoc]

theorem cfold_R (h : ℕ) : ∀ (cs : List Coord) (st : CoordSt), (cs.foldl (cstep h) st).R = st.R ++ rightPart h cs
  | [], st => by simp [rightPart]
  | c :: cs, st => by
    rw [List.foldl_cons, cfold_R h cs]
    by_cases hc : c.1 = true <;> simp [cstep, rightPart, hc, List.append_assoc]

theorem cfold_P (h : ℕ) : ∀ (cs : List Coord) (st : CoordSt),
    (cs.foldl (cstep h) st).P = st.P + (cs.map fun c => if c.2.1 then (pn c.2.2).2 else 0).sum
  | [], st => by simp
  | c :: cs, st => by
    rw [List.foldl_cons, cfold_P h cs]
    cases hc : c.2.1 <;>
      simp only [cstep, accP, hc, List.map_cons, List.sum_cons, if_true, if_false, Bool.false_eq_true] <;> omega

theorem cfold_N (h : ℕ) : ∀ (cs : List Coord) (st : CoordSt),
    (cs.foldl (cstep h) st).N = st.N + (cs.map fun c => if c.2.1 then (pn c.2.2).1 else 0).sum
  | [], st => by simp
  | c :: cs, st => by
    rw [List.foldl_cons, cfold_N h cs]
    cases hc : c.2.1 <;>
      simp only [cstep, accN, hc, List.map_cons, List.sum_cons, if_true, if_false, Bool.false_eq_true] <;> omega

theorem read_frame_bit' (l tl : List Bool) (j : ℕ) (hj : j < l.length) : readTapeBit (frame l ++ tl) (2 * j + 1) = l[j] := by
  rw [read_prefix _ _ _ (by simp; omega)]
  exact read_frame_bit l j hj

/-- The children cursor's word of a list of coordinates: each weight's P/N pair. -/
def pairsOf (h : ℕ) (cs : List Coord) : List Bool := cs.flatMap fun c => pairEnc h (pn c.2.2)

/-- The coordinate loop's bank from a state. -/
def loopA (NM SD FR BL BR PA0 NA0 : List Bool) (h cap : ℕ) (st : CoordSt) : Fin 11 → List Bool :=
  pA NM SD FR st.rp st.rn (overlay st.L BL) (overlay st.R BR) (overlay (frame (binary h st.P)) PA0)
    (overlay (frame (binary h st.N)) NA0) st.tmp (List.replicate cap false)

theorem coords_run (h : ℕ) (cs : List Coord) (pre post tS tF BL BR PA0 NA0 : List Bool) (st : CoordSt) (cap : ℕ)
    (hcap : 2 * h + 1 ≤ cap) :
    Step (StreamController.machine coordBody 1) (cs.length * (coordCost h + 2) + 1)
      (pH pre.length 0 0 st.L.length st.R.length)
      (loopA (pre ++ pairsOf h cs ++ post) (frame (cs.map fun c => c.1) ++ tS) (frame (cs.map fun c => c.2.1) ++ tF)
        BL BR PA0 NA0 h cap st)
      (pH (pre.length + (pairsOf h cs).length) (2 * cs.length) (2 * cs.length) (cs.foldl (cstep h) st).L.length
        (cs.foldl (cstep h) st).R.length)
      (loopA (pre ++ pairsOf h cs ++ post) (frame (cs.map fun c => c.1) ++ tS) (frame (cs.map fun c => c.2.1) ++ tF)
        BL BR PA0 NA0 h cap (cs.foldl (cstep h) st)) := by
  set NM := pre ++ pairsOf h cs ++ post
  set SD := frame (cs.map fun c => c.1) ++ tS
  set FR := frame (cs.map fun c => c.2.1) ++ tF
  have hr := frameRun coordBody 1 (cs.map fun c => c.1) tS
    (fun j => pH (pre.length + (pairsOf h (cs.take j)).length) (2 * j) (2 * j)
      ((cs.take j).foldl (cstep h) st).L.length ((cs.take j).foldl (cstep h) st).R.length)
    (fun j => loopA NM SD FR BL BR PA0 NA0 h cap ((cs.take j).foldl (cstep h) st))
    (fun j => rfl) (fun j => rfl) (coordCost h) (by
      intro j hj
      rw [List.length_map] at hj
      set st' := (cs.take j).foldl (cstep h) st
      have hS : NM = (pre ++ pairsOf h (cs.take j)) ++ pairEnc h (pn cs[j].2.2) ++
          (pairsOf h (cs.drop (j + 1)) ++ post) := by
        simp only [NM, pairsOf]
        rw [enc_split (fun c => pairEnc h (pn c.2.2)) cs j hj]
        simp [List.append_assoc]
      have hs : readTapeBit SD (2 * j + 1) = cs[j].1 := by
        have := read_frame_bit' (cs.map fun c => c.1) tS j (by simpa using hj)
        simpa using this
      have hf : readTapeBit FR (2 * j + 1) = cs[j].2.1 := by
        have := read_frame_bit' (cs.map fun c => c.2.1) tF j (by simpa using hj)
        simpa using this
      have b := coord_step h (pn cs[j].2.2).1 (pn cs[j].2.2).2 st'.P st'.N (pre ++ pairsOf h (cs.take j))
        (pairsOf h (cs.drop (j + 1)) ++ post) SD FR st'.rp st'.rn st'.L BL st'.R BR PA0 NA0 st'.tmp (2 * j) (2 * j) cap
        cs[j].1 cs[j].2.1 hs hf hcap
      rw [← hS] at b
      simp only [Prod.mk.eta] at b
      have ht : cs.take (j + 1) = cs.take j ++ [cs[j]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some]
      have hst : (cs.take (j + 1)).foldl (cstep h) st = cstep h st' cs[j] := by
        rw [ht, List.foldl_append]; rfl
      have hpre : (pre ++ pairsOf h (cs.take j) ++ pairEnc h (pn cs[j].2.2)).length =
          pre.length + (pairsOf h (cs.take (j + 1))).length := by
        rw [ht, pairsOf, pairsOf, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
        simp only [List.length_append]
        omega
      have hpre0 : (pre ++ pairsOf h (cs.take j)).length = pre.length + (pairsOf h (cs.take j)).length := by simp
      rw [hpre, hpre0] at b
      rw [hst]
      have e2 : 2 * j + 1 + 1 = 2 * (j + 1) := by omega
      rw [e2] at b
      exact b)
  rw [List.length_map, List.take_length] at hr
  simpa [pairsOf] using hr

end NearCubicWires.WireExponent3_5.CompilerMachine.Pool
