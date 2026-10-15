import Proof.Gates.Setup.Entry

set_option autoImplicit false

namespace NearCubicGates.Close.Setup

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.RepairOrdinary.Streaming NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.CanonicalWitnessCodec NearCubicWires.Bindings.CLW20Lemma311 NearCubicWires.ExecutableInterfaces
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP NearCubicGates.Close.Interfaces
open NearCubicGates.Close.Worker (width pcpp gadgets oracleOK)
open NearCubicGates.Close.Worker.Format (readCount readField readBits countWord)

/-! ## The oracle field of the guess word -/

theorem readCount_split : ∀ (w : List Bool), false ∈ w → w = countWord (readCount w).1 ++ (readCount w).2
  | [], h => absurd h (by simp)
  | true :: r, h => by
    have h' : false ∈ r := by simpa using h
    have ih := readCount_split r h'
    simp only [readCount, countWord] at ih ⊢
    conv_lhs => rw [ih]
    simp [List.replicate_succ]
  | false :: r, _ => by simp [readCount, countWord]

theorem readCount_le : ∀ (u r : List Bool), (readCount (u ++ false :: r)).1 ≤ u.length
  | [], r => by simp [readCount]
  | true :: u, r => by
    have := readCount_le u r
    simp only [List.cons_append, readCount, List.length_cons]
    omega
  | false :: u, r => by simp [readCount]

theorem readCount_length : ∀ (w : List Bool), (readCount w).2.length + (readCount w).1 + 1 ≤ w.length + 1
  | [] => by simp [readCount]
  | true :: r => by have := readCount_length r; simp only [readCount, List.length_cons]; omega
  | false :: r => by simp [readCount]

theorem ofFn_getD_take (r : List Bool) (l : ℕ) (h : l ≤ r.length) :
    List.ofFn (fun i : Fin l => r.getD i.val false) = r.take l := by
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp only [List.getElem_ofFn, List.getElem_take]
  rw [List.getD_eq_getElem]

theorem prefixBits_length (bits : List Bool) (m : ℕ) : (Codec.prefixBits bits m).length = m := by
  simp [Codec.prefixBits]

/-- **The oracle field of the guess word is physical.** -/
theorem guessWord_split (N : ℕ) (bits : List Bool) (pad : ℕ) (hpad : N / 16 + 1 ≤ pad) :
    guessWord N bits pad = countWord (readField (guessWord N bits pad)).1.length ++
        (readField (guessWord N bits pad)).1 ++ (readField (guessWord N bits pad)).2 ∧
      (readField (guessWord N bits pad)).1.length = (readCount (guessWord N bits pad)).1 ∧
      (readCount (guessWord N bits pad)).1 ≤ N / 16 ∧
      (readField (guessWord N bits pad)).2 = (guessWord N bits pad).drop (oracleEnd (guessWord N bits pad)) := by
  set w := guessWord N bits pad with hw
  set u := Codec.prefixBits bits (N / 16) with hu
  have hwu : w = u ++ false :: List.replicate (pad - 1) false := by
    rw [hw, guessWord, ← hu]
    congr 1
    obtain ⟨p, rfl⟩ : ∃ p, pad = p + 1 := ⟨pad - 1, by omega⟩
    simp [List.replicate_succ]
  have hul : u.length = N / 16 := prefixBits_length bits _
  have hfalse : false ∈ w := by rw [hwu]; simp
  set l := (readCount w).1 with hl
  set r := (readCount w).2 with hr
  have hsplit : w = countWord l ++ r := readCount_split w hfalse
  have hle : l ≤ N / 16 := by rw [hl, hwu, ← hul]; exact readCount_le u _
  have hwlen : w.length = N / 16 + pad := by rw [hwu]; simp [hul]; omega
  have hrlen : l ≤ r.length := by
    have := congrArg List.length hsplit
    simp [countWord] at this
    omega
  have hrf : readField w = (r.take l, r.drop l) := by
    unfold readField readBits
    rw [← hl, ← hr, ofFn_getD_take r l hrlen]
  have htl : (r.take l).length = l := by simp; omega
  refine ⟨?_, ?_, hle, ?_⟩
  · rw [hrf, htl]
    simp only
    rw [List.append_assoc, List.take_append_drop]
    exact hsplit
  · rw [hrf, htl]
  · rw [hrf]
    have he : oracleEnd w = (countWord l).length + l := by simp [oracleEnd, countWord, ← hl]; omega
    rw [he]
    conv_rhs => rw [hsplit]
    rw [List.drop_append]
    simp

/-! ## The supports record -/

theorem rowPrefix_supports (P : ThreeQueryPCPP) (q : ℕ) :
    Codec.rowPrefix (suppRows P q) (P.code.length q) = marks (supportsWord P.code q) := by
  unfold Codec.rowPrefix supportsWord
  rw [Codec.marks_flatMap, ← List.map_coe_finRange_eq_range, List.flatMap_map]
  congr 1
  funext j
  simp [suppRows, j.isLt]

theorem frame_supports (P : ThreeQueryPCPP) (q : ℕ) :
    RepairOrdinary.frame (supportsWord P.code q) = Codec.rowPrefix (suppRows P q) (P.code.length q) ++ [false] := by
  rw [rowPrefix_supports, Codec.frame_eq_marks]

theorem rowPrefix_supports_length (P : ThreeQueryPCPP) (q : ℕ) :
    (Codec.rowPrefix (suppRows P q) (P.code.length q)).length = 2 * (supportsWord P.code q).length := by
  rw [rowPrefix_supports, marks_length]

/-! ## The checked circuit word -/

theorem checkedWord_eq (P : ThreeQueryPCPP) (D : Circuit) :
    (checkedCircuit P.code D).word = natWord (D.n + P.code.length D.n) ++
      (encodeBooleanCircuit (checkedCircuit P.code D).D).bits := rfl

theorem frame_append_marks (u v : List Bool) : RepairOrdinary.frame (u ++ v) = marks u ++ RepairOrdinary.frame v := by
  rw [Codec.frame_eq_marks, Codec.frame_eq_marks, WireExponent3_5.PrimAsm.WriteNat.marks_append, List.append_assoc]

end NearCubicGates.Close.Setup
