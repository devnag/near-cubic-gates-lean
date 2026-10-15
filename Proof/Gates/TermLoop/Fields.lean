import Proof.Gates.TermLoop.Defs
import Proof.Gates.Setup.Words

set_option autoImplicit false

namespace NearCubicGates.Close.TermLoop

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.RepairOrdinary.Streaming NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP NearCubicGates.Close.Interfaces
open NearCubicWires.CanonicalWitnessCodec
open NearCubicGates.Close.Setup
open NearCubicGates.Close.Worker (width pcpp gadgets sysCount)
open NearCubicGates.Close.Worker.Format (readCount readField readBits countWord readMany)

theorem fieldPos_zero (w : List Bool) (p : ℕ) : fieldPos w p 0 = p := rfl

theorem fieldPos_succ (w : List Bool) (p k : ℕ) : fieldPos w p (k + 1) = fieldEnd w (fieldPos w p k) :=
  Codec.iter_succ' _ _ _

theorem le_fieldEnd (w : List Bool) (p : ℕ) : p < fieldEnd w p := by unfold fieldEnd; omega

theorem fieldPos_mono (w : List Bool) (p : ℕ) {j k : ℕ} (h : j ≤ k) : fieldPos w p j ≤ fieldPos w p k := by
  induction k with
  | zero => rw [Nat.le_zero.1 h]
  | succ k ih =>
    rcases Nat.lt_or_ge j (k + 1) with hj | hj
    · rw [fieldPos_succ]; exact (ih (by omega)).trans (le_fieldEnd w _).le
    · rw [show j = k + 1 by omega]

theorem readField_at (w : List Bool) (p : ℕ) :
    readField (w.drop p) = (Codec.fieldBits w (p + Codec.fieldLen w p + 1) (Codec.fieldLen w p),
      w.drop (fieldEnd w p)) := Codec.readField_drop w p

theorem fieldAt_eq (w : List Bool) (p k : ℕ) :
    fieldAt w p k = Codec.fieldBits w (fieldPos w p k + Codec.fieldLen w (fieldPos w p k) + 1)
      (Codec.fieldLen w (fieldPos w p k)) := by
  unfold fieldAt; rw [readField_at]

theorem fieldAt_length (w : List Bool) (p k : ℕ) : (fieldAt w p k).length = Codec.fieldLen w (fieldPos w p k) := by
  rw [fieldAt_eq, Codec.fieldBits_length]

/-- `n` fields read in a row from position `p`. -/
theorem readMany_fields (w : List Bool) (p n : ℕ) :
    readMany readField n (w.drop p) = ((List.range n).map (fieldAt w p), w.drop (fieldPos w p n)) := by
  rw [Codec.readMany_iter readField w (fun p => Codec.fieldBits w (p + Codec.fieldLen w p + 1) (Codec.fieldLen w p))
    (fieldEnd w) (readField_at w) n p]
  congr 1
  apply List.map_congr_left
  intro i _
  rw [fieldAt_eq]; rfl

/-! ## The decoded guess -/

section Guess
variable (s : GateSources) (P : ThreeQueryPCPP) (g : GateParams)
variable {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ) (B : Outer.OuterGuess (width s g N))

theorem guess_oracle
    (hdec : Worker.Decodes (width s g N) (guessWord N bits pad) B) :
    (theGuess s P g x bits pad).oracle = B := by
  exact Worker.decodeGuess_oracle_eq s P g N x _ B hdec

/-- **The decoded witness prefixes are the term fields.** -/
theorem termField_eq
    (hdec : Worker.Decodes (width s g N) (guessWord N bits pad) B)
    (_hpad : N / 16 + 1 ≤ pad) (a : ℕ) (ha : a < gadgets s g N) (t : Fin 10) :
    (theGuess s P g x bits pad).witnesses a t = termField s P g x bits pad B a t := by
  have ho := guess_oracle s P g x bits pad B hdec
  have hp0 := pairEnd_drop (guessWord N bits pad)
  unfold theGuess at ho ⊢
  rw [Worker.decodeGuess_witnesses, ho, hp0, Worker.readMany_circ, readMany_fields]
  unfold termField fieldsStart auxN
  have hk : 10 * a + t.val < 10 * gadgets s g N := by have := t.isLt; omega
  simp [List.getD_eq_getElem?_getD, hk]

/-- The decoded circuits are the transcoded ones (`circs`), at every auxiliary name. -/
theorem circuits_eq
    (hdec : Worker.Decodes (width s g N) (guessWord N bits pad) B)
    (_hpad : N / 16 + 1 ≤ pad) (j : ℕ) (hj : j < auxN s P g x B) :
    (theGuess s P g x bits pad).circuits j = circs s g N bits pad j := by
  have ho := guess_oracle s P g x bits pad B hdec
  have hp0 := pairEnd_drop (guessWord N bits pad)
  unfold theGuess at ho ⊢
  refine Worker.decodeGuess_circuits_at s P g N x (guessWord N bits pad) _ hp0 j ?_
  show j < (pcpp s P g x (Worker.decodeGuess s P g N x (guessWord N bits pad)).oracle).proofBits + gadgets s g N
  rw [ho]; exact hj

end Guess

/-! ## Physical fields -/

theorem readCount_all_true : ∀ l : List Bool, false ∉ l → (readCount l).1 = l.length
  | [], _ => rfl
  | true :: r, h => by
    simp only [readCount, List.length_cons]
    rw [readCount_all_true r (fun hr => h (List.mem_cons_of_mem _ hr))]
  | false :: _, h => absurd (List.mem_cons_self) h

/-- **A field whose end lies inside the word is physical.** -/
theorem field_split (w : List Bool) (p : ℕ) (h : fieldEnd w p ≤ w.length) :
    w = w.take p ++ (countWord (readField (w.drop p)).1.length ++ (readField (w.drop p)).1) ++
      w.drop (fieldEnd w p) ∧ (readField (w.drop p)).1.length = Codec.fieldLen w p ∧ p ≤ w.length := by
  set l := (readCount (w.drop p)).1 with hl
  set r := (readCount (w.drop p)).2 with hr
  have hfl : Codec.fieldLen w p = l := rfl
  have hp : p ≤ w.length := (le_fieldEnd w p).le.trans h
  have hfalse : false ∈ w.drop p := by
    by_contra hn
    have := readCount_all_true _ hn
    rw [List.length_drop, ← hl] at this
    unfold fieldEnd at h
    rw [hfl] at h
    omega
  have hsplit : w.drop p = countWord l ++ r := readCount_split _ hfalse
  have hlen : (w.drop p).length = l + 1 + r.length := by
    rw [hsplit]; simp [countWord]; omega
  have hlr : l ≤ r.length := by
    unfold fieldEnd at h; rw [hfl] at h; rw [List.length_drop] at hlen; omega
  have hrf : readField (w.drop p) = (r.take l, r.drop l) := by
    unfold readField readBits
    rw [← hl, ← hr, ofFn_getD_take r l hlr]
  have htl : (r.take l).length = l := by simp; omega
  have hend : w.drop (fieldEnd w p) = r.drop l := by
    unfold fieldEnd
    rw [hfl, show p + l + 1 + l = p + (l + 1 + l) by omega, ← List.drop_drop, hsplit,
      show l + 1 + l = (countWord l).length + l by
        simp only [countWord, List.length_append, List.length_replicate, List.length_cons, List.length_nil],
      ← List.drop_drop, List.drop_left]
  refine ⟨?_, by rw [hrf, htl, hfl], hp⟩
  rw [hrf, htl, hend]
  conv_lhs => rw [← List.take_append_drop p w, hsplit]
  simp only [List.append_assoc, List.take_append_drop]

end NearCubicGates.Close.TermLoop
