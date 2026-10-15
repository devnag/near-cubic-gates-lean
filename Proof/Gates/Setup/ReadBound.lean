import Proof.Gates.Codec.Transcode
import Proof.Gates.Codec.Field
import Proof.Gates.Worker.Format

set_option autoImplicit false

namespace NearCubicGates.Close.Setup

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary.Streaming
open NearCubicGates.Close NearCubicGates.Close.Worker.Format

theorem natWord_len (v : ℕ) : (natWord v).length = 2 * natBitLength v + 1 := by simp

theorem natBitLength_le_of_lt (v L : ℕ) (h : v < 2 ^ L) : natBitLength v ≤ L + 1 := by
  unfold natBitLength
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · simp
  · have := Nat.log_lt_of_lt_pow (by omega) h
    omega

theorem readCount_snd_le (w : List Bool) : (readCount w).2.length + (readCount w).1 ≤ w.length := by
  induction w with
  | nil => simp [readCount]
  | cons b l ih =>
    cases b with
    | false => simp [readCount]
    | true => simp [readCount]; omega

theorem readField_fst_len (w : List Bool) : (readField w).1.length ≤ w.length := by
  have := readCount_snd_le w
  simp only [readField, readBits, List.length_ofFn]; omega

theorem readField_snd_le (w : List Bool) : (readField w).2.length ≤ w.length := by
  have := readCount_snd_le w
  simp only [readField, readBits, List.length_drop]; omega

theorem readNum_lt (w : List Bool) : (readNum w).1 < 2 ^ w.length :=
  lt_of_lt_of_le (Codec.value_lt_two_pow _) (Nat.pow_le_pow_right (by norm_num) (readField_fst_len w))

theorem readNum_snd_le (w : List Bool) : (readNum w).2.length ≤ w.length := readField_snd_le w

theorem readInt_abs_lt (w : List Bool) : (readInt w).1.natAbs < 2 ^ w.length := by
  have h := readNum_lt w.tail
  have ht : 2 ^ w.tail.length ≤ 2 ^ w.length := Nat.pow_le_pow_right (by norm_num) (by simp)
  simp only [readInt]
  split <;> simp <;> omega

theorem readInt_snd_le (w : List Bool) : (readInt w).2.length ≤ w.length := by
  have := readNum_snd_le w.tail
  simp only [readInt]
  have : w.tail.length ≤ w.length := by simp
  omega

theorem intWord_len_le (z : ℤ) (L : ℕ) (h : z.natAbs < 2 ^ L) : (Interfaces.intWord z).length ≤ 2 * L + 8 := by
  have h1 := natBitLength_le_of_lt _ _ h
  have h2 : natBitLength (if z < 0 then 1 else 0) ≤ 1 := by split <;> simp [natBitLength]
  simp only [Interfaces.intWord, List.length_append, natWord_len]
  omega

/-- A reader that returns a suffix-length remainder and outputs bounded in terms of its input length, iterated. -/
theorem readMany_bound {α : Type} (rd : List Bool → α × List Bool) (f : α → ℕ) (G : ℕ → ℕ) (hG : Monotone G)
    (h1 : ∀ w, (rd w).2.length ≤ w.length) (h2 : ∀ w, f (rd w).1 ≤ G w.length) :
    ∀ n w, (readMany rd n w).2.length ≤ w.length ∧ (readMany rd n w).1.length = n ∧
      ∀ a ∈ (readMany rd n w).1, f a ≤ G w.length
  | 0, w => by simp [readMany]
  | n + 1, w => by
    obtain ⟨i1, i2, i3⟩ := readMany_bound rd f G hG h1 h2 n (rd w).2
    refine ⟨?_, ?_, ?_⟩
    · simp only [readMany]; exact i1.trans (h1 w)
    · simp only [readMany, List.length_cons, i2]
    · intro a ha
      simp only [readMany, List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact h2 w
      · exact (i3 a ha).trans (hG (h1 w))

theorem flatMap_len_le {α : Type} (f : α → List Bool) (c : ℕ) :
    ∀ xs : List α, (∀ a ∈ xs, (f a).length ≤ c) → (xs.flatMap f).length ≤ xs.length * c
  | [], _ => by simp
  | a :: xs, h => by
    have := flatMap_len_le f c xs (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have := h a (List.mem_cons_self)
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    nlinarith

theorem readGate_snd_le (q : ℕ) (w : List Bool) : (readGate q w).2.length ≤ w.length := by
  obtain ⟨i1, -, -⟩ := readMany_bound readInt (fun _ => 0) (fun _ => 0) (fun _ _ _ => le_rfl) readInt_snd_le
    (fun _ => le_rfl) q w
  exact (readInt_snd_le _).trans i1

theorem gateWord_read_le (q : ℕ) (w : List Bool) :
    (Interfaces.gateWord (readGate q w).1).length ≤ (q + 1) * (2 * w.length + 11) := by
  obtain ⟨i1, i2, i3⟩ := readMany_bound readInt (fun z => z.natAbs + 1) (fun L => 2 ^ L)
    (fun a b h => Nat.pow_le_pow_right (by norm_num) h) readInt_snd_le (fun w => readInt_abs_lt w) q w
  set ws := (readMany readInt q w).1 with hws
  have hwt : ∀ z ∈ List.ofFn (readGate q w).1.weight, (Interfaces.intWord z).length ≤ 2 * w.length + 8 := by
    intro z hz
    rw [List.mem_ofFn] at hz
    obtain ⟨i, rfl⟩ := hz
    show (Interfaces.intWord (ws.getD i.val 0)).length ≤ _
    rcases Nat.lt_or_ge i.val ws.length with hi | hi
    · rw [List.getD_eq_getElem _ _ hi]
      have hm := i3 _ (List.getElem_mem hi)
      have hlt : (ws[i.val]).natAbs < 2 ^ w.length := by omega
      exact intWord_len_le _ _ hlt
    · rw [List.getD_eq_default _ _ hi]
      have := intWord_len_le (0 : ℤ) 0 (by simp)
      omega
  have hf := flatMap_len_le Interfaces.intWord (2 * w.length + 8) _ hwt
  have hth : (Interfaces.intWord (readGate q w).1.threshold).length ≤ 2 * w.length + 8 := by
    show (Interfaces.intWord (readInt (readMany readInt q w).2).1).length ≤ _
    have h := readInt_abs_lt (readMany readInt q w).2
    have h' : (readInt (readMany readInt q w).2).1.natAbs < 2 ^ w.length :=
      lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) i1)
    exact intWord_len_le _ _ h'
  have hq := natBitLength_le_of_lt q q Nat.lt_two_pow_self
  simp only [Interfaces.gateWord, Interfaces.listWord, List.length_append, natWord_len, List.length_ofFn] at hf ⊢
  nlinarith

theorem circuitWord_read_le (q : ℕ) (l : List Bool) :
    (Interfaces.circuitWord (readCircuit q l).1).length ≤ 40 * (l.length + 1) ^ 2 * (q + 1) := by
  set k := readCount l with hk
  have hk1 : k.1 + k.2.length ≤ l.length := by have := readCount_snd_le l; rw [← hk] at this; omega
  obtain ⟨g1, g2, g3⟩ := readMany_bound (readGate q) (fun G => (Interfaces.gateWord G).length)
    (fun L => (q + 1) * (2 * L + 11)) (fun a b h => Nat.mul_le_mul_left _ (by omega)) (readGate_snd_le q)
    (gateWord_read_le q) k.1 k.2
  set gs := readMany (readGate q) k.1 k.2 with hgs
  obtain ⟨c1, c2, c3⟩ := readMany_bound readInt (fun z => (Interfaces.intWord z).length) (fun L => 2 * L + 8)
    (fun a b h => by show 2 * a + 8 ≤ 2 * b + 8; omega) readInt_snd_le (fun w => intWord_len_le _ _ (readInt_abs_lt w))
    k.1 gs.2
  set cs := readMany readInt k.1 gs.2 with hcs
  have ht : (readField cs.2).1.length ≤ l.length := (readField_fst_len _).trans (by omega)
  have hG := flatMap_len_le Interfaces.gateWord ((q + 1) * (2 * k.2.length + 11)) gs.1 g3
  have hC := flatMap_len_le Interfaces.intWord (2 * gs.2.length + 8) cs.1 c3
  have hB := flatMap_len_le Interfaces.bitWord 3 (readField cs.2).1 (fun b _ => by
    cases b <;> simp [Interfaces.bitWord, natBitLength])
  have hn1 := natBitLength_le_of_lt k.1 k.1 Nat.lt_two_pow_self
  have hn3 := natBitLength_le_of_lt (readField cs.2).1.length ((readField cs.2).1.length) Nat.lt_two_pow_self
  have e1 : (Interfaces.circuitWord (readCircuit q l).1).length =
      (2 * natBitLength gs.1.length + 1 + (gs.1.flatMap Interfaces.gateWord).length) +
      (2 * natBitLength cs.1.length + 1 + (cs.1.flatMap Interfaces.intWord).length) +
      (2 * natBitLength (readField cs.2).1.length + 1 + ((readField cs.2).1.flatMap Interfaces.bitWord).length) := by
    simp only [readCircuit, Interfaces.circuitWord, Interfaces.listWord, List.length_append, natWord_len]
    rfl
  rw [g2] at hG
  rw [c2] at hC
  have hk2 : k.2.length ≤ l.length := by omega
  have hgs2 : gs.2.length ≤ l.length := g1.trans hk2
  have hkl : k.1 ≤ l.length := by omega
  have a1 : k.1 * ((q + 1) * (2 * k.2.length + 11)) ≤ (l.length + 1) * ((q + 1) * (2 * l.length + 11)) :=
    Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ (by omega))
  have a2 : k.1 * (2 * gs.2.length + 8) ≤ (l.length + 1) * (2 * l.length + 8) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hq1 : 1 ≤ q + 1 := by omega
  have hp : natBitLength gs.1.length ≤ k.1 + 1 := by rw [g2]; exact hn1
  have hr : natBitLength cs.1.length ≤ k.1 + 1 := by rw [c2]; exact hn1
  have b1 : (l.length + 1) * ((q + 1) * (2 * l.length + 11)) ≤ 11 * ((l.length + 1) ^ 2 * (q + 1)) := by
    have : 2 * l.length + 11 ≤ 11 * (l.length + 1) := by omega
    calc (l.length + 1) * ((q + 1) * (2 * l.length + 11)) ≤ (l.length + 1) * ((q + 1) * (11 * (l.length + 1))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ this)
      _ = 11 * ((l.length + 1) ^ 2 * (q + 1)) := by ring
  have b2 : (l.length + 1) * (2 * l.length + 8) ≤ 8 * ((l.length + 1) ^ 2 * (q + 1)) := by
    have : 2 * l.length + 8 ≤ 8 * (l.length + 1) := by omega
    calc (l.length + 1) * (2 * l.length + 8) ≤ (l.length + 1) * (8 * (l.length + 1)) := Nat.mul_le_mul_left _ this
      _ = 8 * ((l.length + 1) ^ 2 * 1) := by ring
      _ ≤ 8 * ((l.length + 1) ^ 2 * (q + 1)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hq1)
  have b3 : l.length + 1 ≤ (l.length + 1) ^ 2 * (q + 1) := by
    calc l.length + 1 ≤ (l.length + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
      _ = (l.length + 1) ^ 2 * 1 := by ring
      _ ≤ (l.length + 1) ^ 2 * (q + 1) := Nat.mul_le_mul_left _ hq1
  have e40 : 40 * (l.length + 1) ^ 2 * (q + 1) = 40 * ((l.length + 1) ^ 2 * (q + 1)) := by ring
  rw [e1, e40]
  omega

/-- **The circuit stream** written by the transcoder: `aux` decoded circuits. -/
theorem cwPrefix_le (w : List Bool) (q p0 aux : ℕ) :
    (Codec.cwPrefix (Codec.circAt w q p0) aux).length ≤ aux * (80 * (w.length + 1) ^ 2 * (q + 1)) := by
  unfold Codec.cwPrefix
  refine (flatMap_len_le (fun j => marks (Interfaces.circuitWord (Codec.circAt w q p0 j)))
    (80 * (w.length + 1) ^ 2 * (q + 1)) (List.range aux) (fun j _ => ?_)).trans (by simp)
  have h := circuitWord_read_le q (w.drop (Codec.circPos w q p0 j))
  have hd : (w.drop (Codec.circPos w q p0 j)).length ≤ w.length := by simp
  have hp : (w.drop (Codec.circPos w q p0 j)).length + 1 ≤ w.length + 1 := by omega
  have hp2 := Nat.pow_le_pow_left hp 2
  rw [Codec.marks_length]
  show 2 * (Interfaces.circuitWord (readCircuit q (w.drop (Codec.circPos w q p0 j))).1).length ≤ _
  nlinarith

end NearCubicGates.Close.Setup
