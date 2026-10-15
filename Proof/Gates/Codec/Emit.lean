import Proof.Gates.Codec.Copy

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Codec

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.RepairOrdinary.Streaming
open NearCubicGates.Close.Interfaces

variable {ns nr : ℕ} (cap : ℕ)

theorem appendO_nil (σ : WState ns nr) (o : Fin (ns + 1)) (OP : Fin nr) (ho : σ.sh o = (σ.st o).length) :
    appendO σ o OP [] = σ := by
  refine WState.eq ?_ ?_ ?_ rfl
  · funext j; by_cases hj : j = o
    · subst hj; simp [appendO]
    · simp [appendO, Function.update_of_ne hj]
  · funext j; by_cases hj : j = o
    · subst hj; simp [appendO]
    · simp [appendO, Function.update_of_ne hj]
  · funext r; by_cases hr : r = OP
    · subst hr; simp [appendO]
    · simp [appendO, Function.update_of_ne hr]

/-- Append one raw bit. -/
theorem emitBit_spec (o : Fin (ns + 1)) (OP : Fin nr) (b : Bool) (σ : WState ns nr) (ho : σ.sh o = (σ.st o).length)
    (hc : σ.val OP < cap) : WExec cap (emitC o OP b) σ (appendO σ o OP [b]) 7 := by
  have h := emitC_spec cap o OP b σ ho hc
  simpa [appendO] using h

def emitMarks (o : Fin (ns + 1)) (OP : Fin nr) : List Bool → WM ns nr
  | [] => .skip
  | b :: bs => .seq (emitPair o OP b) (emitMarks o OP bs)

theorem emitMarks_spec (o : Fin (ns + 1)) (OP : Fin nr) :
    ∀ (bs : List Bool) (σ : WState ns nr), σ.sh o = (σ.st o).length → σ.val OP + 2 * bs.length ≤ cap →
      WExec cap (emitMarks o OP bs) σ (appendO σ o OP (marks bs)) (16 * bs.length)
  | [], σ, ho, _ => by
    rw [show marks ([] : List Bool) = [] by simp [marks], appendO_nil σ o OP ho]
    exact WExec.mono (WExec.skip σ) (by simp)
  | b :: bs, σ, ho, hc => by
    have h1 := emitPair_spec cap o OP b σ ho (by simp at hc; omega)
    have h2 := emitMarks_spec o OP bs (appendO σ o OP [true, b]) (by simp [appendO, ho])
      (by simp [appendO] at hc ⊢; omega)
    refine WExec.cast cap (WExec.seq h1 h2) ?_ (by simp; omega)
    rw [appendO_append]; simp [marks]

/-- The body transcoding one `bitWord b` into `marks [b]` (the bit's value via `R 4`). -/
def bitBody (ε : Bool) (s o : Fin (ns + 1)) (R : Fin 8 ↪ Fin nr) : WM ns nr :=
  .seq (readNatM ε s (R 1) (R 2) (R 4) (R 3) (R 6))
    (.ifr (R 4) (.seq (emitPair o (R 7) true) (.dec (R 4))) (emitPair o (R 7) false))

theorem bitBody_spec (ε : Bool) (s o : Fin (ns + 1)) (hso : s ≠ o) (R : Fin 8 ↪ Fin nr) (b : Bool)
    (pre rest : List Bool) (σ : WState ns nr) (hst : σ.st s = pre ++ enc ε (bitWord b) ++ rest)
    (hsh : σ.sh s = pre.length) (ho : σ.sh o = (σ.st o).length) (hz : ∀ i ∈ [1, 2, 3, 4, 6], σ.val (R i) = 0)
    (hcap : σ.val (R 7) + 4 ≤ cap) (hc4 : 4 ≤ cap) :
    WExec cap (bitBody ε s o R) σ ((appendO σ o (R 7) (marks [b])).seth s (pre.length + stp ε * (bitWord b).length))
      380 := by
  have hl : natBitLength (if b then 1 else 0) = 1 := by split_ifs <;> simp [natBitLength]
  have h1 := readNatM_spec cap ε s (R 1) (R 2) (R 4) (R 3) (R 6) (Rne R (by decide)) (Rne R (by decide))
    (Rne R (by decide)) (Rne R (by decide)) (Rne R (by decide)) (Rne R (by decide)) (Rne R (by decide))
    (Rne R (by decide)) (Rne R (by decide)) (Rne R (by decide)) (if b then 1 else 0) pre rest σ
    (by simpa [bitWord] using hst) hsh (hz 1 (by simp)) (hz 2 (by simp)) (hz 3 (by simp)) (hz 6 (by simp))
    (by rw [hz 4 (by simp), hl]; omega)
  set σ1 := (σ.seth s (pre.length + stp ε * (natWord (if b then 1 else 0)).length)).setv (R 4)
    (σ.val (R 4) + if b then 1 else 0) with hσ1
  have ho1 : σ1.sh o = (σ1.st o).length := by simp [hσ1, Function.update_of_ne (Ne.symm hso), ho]
  have h47 : R 4 ≠ R 7 := Rne R (by decide)
  have hv7 : σ1.val (R 7) = σ.val (R 7) := by simp [hσ1, Function.update_of_ne (Ne.symm h47)]
  cases b with
  | false =>
    have h2 := emitPair_spec cap o (R 7) false σ1 ho1 (by rw [hv7]; omega)
    have hz4 : σ1.val (R 4) = 0 := by simp [hσ1, hz 4 (by simp)]
    refine WExec.cast cap (WExec.seq h1 (WExec.ifrF hz4 h2)) ?_ (by simp [natBitLength])
    refine WState.eq ?_ ?_ ?_ rfl
    · funext j; by_cases hj : j = s
      · subst hj; simp [hσ1, appendO, Function.update_of_ne hso, bitWord, marks]
      · by_cases hjo : j = o
        · subst hjo; simp [hσ1, appendO, Function.update_of_ne hj, marks]
        · simp [hσ1, appendO, Function.update_of_ne hj, Function.update_of_ne hjo]
    · funext j; by_cases hjo : j = o
      · subst hjo; simp [hσ1, appendO, Function.update_of_ne (Ne.symm hso), marks]
      · simp [hσ1, appendO, Function.update_of_ne hjo]
    · funext r; by_cases hr7 : r = R 7
      · subst hr7; simp [hσ1, appendO, Function.update_of_ne (Ne.symm h47), marks]
      · by_cases hr4 : r = R 4
        · subst hr4; simp [hσ1, appendO, Function.update_of_ne hr7, hz 4 (by simp)]
        · simp [hσ1, appendO, Function.update_of_ne hr7, Function.update_of_ne hr4]
  | true =>
    have h2 := emitPair_spec cap o (R 7) true σ1 ho1 (by rw [hv7]; omega)
    have h3 := WExec.dec (cap := cap) (R 4) (appendO σ1 o (R 7) [true, true]) (by
      simp [appendO, Function.update_of_ne h47, hσ1, hz 4 (by simp)]; omega)
    have hnz : σ1.val (R 4) ≠ 0 := by simp [hσ1, hz 4 (by simp)]
    refine WExec.cast cap (WExec.seq h1 (WExec.ifrT hnz (WExec.seq h2 h3))) ?_ (by simp [natBitLength])
    refine WState.eq ?_ ?_ ?_ rfl
    · funext j; by_cases hj : j = s
      · subst hj; simp [hσ1, appendO, Function.update_of_ne hso, bitWord, marks]
      · by_cases hjo : j = o
        · subst hjo; simp [hσ1, appendO, Function.update_of_ne hj, marks]
        · simp [hσ1, appendO, Function.update_of_ne hj, Function.update_of_ne hjo]
    · funext j; by_cases hjo : j = o
      · subst hjo; simp [hσ1, appendO, Function.update_of_ne (Ne.symm hso), marks]
      · simp [hσ1, appendO, Function.update_of_ne hjo]
    · funext r; by_cases hr7 : r = R 7
      · subst hr7; simp [hσ1, appendO, Function.update_of_ne (Ne.symm h47), marks]
      · by_cases hr4 : r = R 4
        · subst hr4; simp [hσ1, appendO, Function.update_of_ne hr7, hz 4 (by simp)]
        · simp [hσ1, appendO, Function.update_of_ne hr7, Function.update_of_ne hr4]

/-- Transcode `listWord bitWord w` (encoding `ε`) on `s` into `marks w` appended to `o`. -/
def transBits (ε : Bool) (s o : Fin (ns + 1)) (R : Fin 8 ↪ Fin nr) : WM ns nr :=
  .seq (readNatM ε s (R 1) (R 2) (R 0) (R 3) (R 6)) (listLoop (R 0) (bitBody ε s o R))

theorem flatMap_singleton (w : List Bool) : (w.flatMap fun b => [b]) = w := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [List.flatMap_cons, ih]

theorem transBits_spec (ε : Bool) (s o : Fin (ns + 1)) (hso : s ≠ o) (R : Fin 8 ↪ Fin nr) (w : List Bool)
    (pre rest : List Bool) (σ : WState ns nr) (hst : σ.st s = pre ++ enc ε (listWord bitWord w) ++ rest)
    (hsh : σ.sh s = pre.length) (ho : σ.sh o = (σ.st o).length) (hz : ∀ i : Fin 8, i ≠ 7 → σ.val (R i) = 0)
    (hcap : 2 ^ (natBitLength w.length + 1) ≤ cap) (hlen : w.length ≤ cap)
    (hcapo : σ.val (R 7) + 2 * w.length + 4 ≤ cap) (hc4 : 4 ≤ cap) :
    WExec cap (transBits ε s o R) σ
      ((appendO σ o (R 7) (marks w)).seth s (pre.length + stp ε * (listWord bitWord w).length))
      ((natBitLength w.length + 2) * (40 * 2 ^ natBitLength w.length + 40) + 1 + ((w.map fun _ => 380 + 4).sum + 1)) := by
  have hsplit : enc ε (listWord bitWord w) = enc ε (natWord w.length) ++ w.flatMap fun b => enc ε (bitWord b) := by
    unfold listWord; rw [NearCubicWires.WireExponent3_5.PrimAsm.CopyNat.enc_append, enc_flatMap]
  have h1 := readNatM_spec cap ε s (R 1) (R 2) (R 0) (R 3) (R 6) (Rne R (by decide)) (Rne R (by decide))
    (Rne R (by decide)) (Rne R (by decide)) (Rne R (by decide)) (Rne R (by decide)) (Rne R (by decide))
    (Rne R (by decide)) (Rne R (by decide)) (Rne R (by decide)) w.length pre
    ((w.flatMap fun b => enc ε (bitWord b)) ++ rest) σ (by rw [hst, hsplit]; simp [List.append_assoc]) hsh
    (hz 1 (by decide)) (hz 2 (by decide)) (hz 3 (by decide)) (hz 6 (by decide))
    (by rw [hz 0 (by decide)]; simpa using hcap)
  set σ1 := (σ.seth s (pre.length + stp ε * (natWord w.length).length)).setv (R 0) (σ.val (R 0) + w.length) with hσ1
  have hok1 : ∀ i ∈ [1, 2, 3, 4, 6], σ1.val (R i) = 0 := by
    intro i hi
    have hi0 : i ≠ 0 := by intro e; subst e; simp at hi
    have hi7 : i ≠ 7 := by intro e; subst e; simp at hi
    simp [hσ1, Function.update_of_ne (Rne R hi0), hz i hi7]
  have hv7 : σ1.val (R 7) = σ.val (R 7) := by simp [hσ1, Function.update_of_ne (Rne R (show (7 : Fin 8) ≠ 0 by decide))]
  have h2 := copyLoop_spec cap s o hso (R 0) (R 7) (Rne R (by decide)) (bitBody ε s o R)
    (fun b => enc ε (bitWord b)) (fun b => [b]) (fun _ => 380) (fun σ => ∀ i ∈ [1, 2, 3, 4, 6], σ.val (R i) = 0)
    (σ.val (R 7) + 2 * w.length)
    (fun σ x h i hi => by simpa using h i hi)
    (fun σ x h i hi => by
      have hi0 : i ≠ 0 := by intro e; subst e; simp at hi
      simp [Function.update_of_ne (Rne R hi0), h i hi])
    (fun σ u h i hi => by
      have hi7 : i ≠ 7 := by intro e; subst e; simp at hi
      simp [appendO, Function.update_of_ne (Rne R hi7), h i hi])
    w ?_ (pre ++ enc ε (natWord w.length)) rest σ1 hok1
    (by simp only [hσ1, WState.setv_st, WState.seth_st]; rw [hst, hsplit]; simp [List.append_assoc])
    (by simp [hσ1, WireExponent3_5.PrimAsm.ParseNat.enc_length])
    (by simp [hσ1, Function.update_of_ne (Ne.symm hso), ho])
    (by simp [hσ1, hz 0 (by decide)]) hlen
    (by rw [hv7, flatMap_singleton, marks_length])
  · refine WExec.cast cap (WExec.seq h1 h2) ?_ (le_refl _)
    rw [flatMap_singleton]
    refine WState.eq ?_ ?_ ?_ rfl
    · funext j; by_cases hj : j = s
      · subst hj
        have hfl : (w.flatMap fun b => enc ε (bitWord b)).length = stp ε * (w.flatMap bitWord).length := by
          rw [← enc_flatMap, WireExponent3_5.PrimAsm.ParseNat.enc_length]
        simp [hσ1, appendO, Function.update_of_ne hso, listWord, hfl, WireExponent3_5.PrimAsm.ParseNat.enc_length]
        ring
      · by_cases hjo : j = o
        · subst hjo; simp [hσ1, appendO, Function.update_of_ne hj, ho]
        · simp [hσ1, appendO, Function.update_of_ne hj, Function.update_of_ne hjo]
    · funext j; by_cases hjo : j = o
      · subst hjo; simp [hσ1, appendO, Function.update_of_ne (Ne.symm hso)]
      · simp [hσ1, appendO, Function.update_of_ne hjo]
    · funext r; by_cases hr0 : r = R 0
      · subst hr0; simp [hσ1, appendO, Function.update_of_ne (Rne R (show (0 : Fin 8) ≠ 7 by decide)), hz 0 (by decide)]
      · by_cases hr7 : r = R 7
        · subst hr7; simp [hσ1, appendO, Function.update_of_ne hr0]
        · simp [hσ1, appendO, Function.update_of_ne hr0, Function.update_of_ne hr7]
  · intro b _ pre' rest' σ' hok hst' hsh' ho' hV'
    have := bitBody_spec cap ε s o hso R b pre' rest' σ' hst' hsh' ho' hok (by rw [marks_length] at hV'; simp at hV'; omega) hc4
    rw [WireExponent3_5.PrimAsm.ParseNat.enc_length]
    exact this

end NearCubicGates.Close.Codec
