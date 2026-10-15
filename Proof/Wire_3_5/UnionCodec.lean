import Proof.Wire_3_5.TransferUnion
import Proof.Circuits.CanonicalWitnessCodec

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation

section Readers

/-- The leading `true` bits of a word and the rest. -/
def countOnes : List Bool → ℕ × List Bool
  | true :: w => ((countOnes w).1 + 1, (countOnes w).2)
  | w => (0, w)

theorem countOnes_replicate (k : ℕ) (w : List Bool) :
    countOnes (List.replicate k true ++ false :: w) = (k, false :: w) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, List.cons_append, countOnes, ih]

/-- Reads one framed natural `natWord v` off the front of a word (canonical form only). -/
def readNat (w : List Bool) : Option (ℕ × List Bool) :=
  match countOnes w with
  | (k, false :: rest) =>
      if natWord (CanonicalBinary.bitsValue (rest.take k)) ++ rest.drop k = w then
        some (CanonicalBinary.bitsValue (rest.take k), rest.drop k)
      else none
  | _ => none

theorem bitsValue_fixedWidth (L n : ℕ) :
    CanonicalBinary.bitsValue (WilliamsPublishedForm.fixedWidthNatBits L n) = n % 2 ^ L := by
  induction L generalizing n with
  | zero => simp [WilliamsPublishedForm.fixedWidthNatBits, CanonicalBinary.bitsValue, Nat.mod_one]
  | succ L ih =>
      have hs : WilliamsPublishedForm.fixedWidthNatBits (L + 1) n =
          n.testBit 0 :: WilliamsPublishedForm.fixedWidthNatBits L (n / 2) := by
        simp only [WilliamsPublishedForm.fixedWidthNatBits, List.ofFn_succ, Fin.val_zero, Fin.val_succ,
          Nat.testBit_div_two]
      rw [hs, CanonicalBinary.bitsValue, ih, pow_succ, mul_comm (2 ^ L) 2, Nat.mod_mul]
      congr 1
      rw [Nat.testBit_zero]
      rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]

theorem readNat_natWord (n : ℕ) (t : List Bool) : readNat (natWord n ++ t) = some (n, t) := by
  have hlen : (WilliamsPublishedForm.fixedWidthNatBits (natBitLength n) n).length = natBitLength n := by
    simp [WilliamsPublishedForm.fixedWidthNatBits]
  have hval : CanonicalBinary.bitsValue (WilliamsPublishedForm.fixedWidthNatBits (natBitLength n) n) = n := by
    rw [bitsValue_fixedWidth]
    exact Nat.mod_eq_of_lt (Nat.lt_pow_succ_log_self (by norm_num) n)
  have hw : natWord n ++ t = List.replicate (natBitLength n) true ++
      false :: (WilliamsPublishedForm.fixedWidthNatBits (natBitLength n) n ++ t) := by
    simp [natWord, WilliamsPublishedForm.framedNatBits]
  unfold readNat
  rw [hw, countOnes_replicate]
  simp only [List.take_left' hlen, List.drop_left' hlen, hval]
  rw [if_pos hw]

theorem readNat_sound {w : List Bool} {v : ℕ} {r : List Bool} (h : readNat w = some (v, r)) :
    w = natWord v ++ r := by
  unfold readNat at h
  split at h
  · split_ifs at h with hw
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hw.symm
  · simp at h

/-- The integer of a sign bit and a magnitude. -/
def signedOf (b : Bool) (n : ℕ) : ℤ := if b then -(n : ℤ) else n

/-- Reads one integer word `intWord z` (sign bit, framed magnitude; canonical form only, so no negative zero). -/
def readInt : List Bool → Option (ℤ × List Bool)
  | [] => none
  | b :: w => (readNat w).bind fun p =>
      if intWord (signedOf b p.1) ++ p.2 = b :: w then some (signedOf b p.1, p.2) else none

theorem readInt_intWord (z : ℤ) (t : List Bool) : readInt (intWord z ++ t) = some (z, t) := by
  have hz : signedOf (decide (z < 0)) z.natAbs = z := by
    unfold signedOf
    by_cases h : z < 0
    · simp [h, abs_of_neg h]
    · simp [h, abs_of_nonneg (not_lt.mp h)]
  simp only [intWord, List.cons_append, readInt, readNat_natWord, Option.bind_some, hz, if_true]

theorem readInt_sound {w : List Bool} {z : ℤ} {r : List Bool} (h : readInt w = some (z, r)) :
    w = intWord z ++ r := by
  match w, h with
  | b :: w, h =>
      simp only [readInt, Option.bind_eq_some_iff] at h
      obtain ⟨p, _, hp⟩ := h
      split_ifs at hp with hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      exact hw.symm

/-- Reads a vector of `k` items with the item reader `rd`. -/
def readVec {β : Type} (rd : List Bool → Option (β × List Bool)) :
    (k : ℕ) → List Bool → Option ((Fin k → β) × List Bool)
  | 0, w => some (Fin.elim0, w)
  | k + 1, w => (rd w).bind fun p => (readVec rd k p.2).map fun r => ((Fin.cons p.1 r.1 : Fin (k + 1) → β), r.2)

/-- The word of a vector: the items' words in order. -/
def encVec {β : Type} (enc : β → List Bool) {k : ℕ} (f : Fin k → β) : List Bool :=
  (List.ofFn fun i => enc (f i)).flatten

theorem readVec_encVec {β : Type} (rd : List Bool → Option (β × List Bool)) (enc : β → List Bool)
    (hrd : ∀ b t, rd (enc b ++ t) = some (b, t)) :
    ∀ (k : ℕ) (f : Fin k → β) (t : List Bool), readVec rd k (encVec enc f ++ t) = some (f, t)
  | 0, f, t => by
      simp only [readVec, encVec, List.ofFn_zero, List.flatten_nil, List.nil_append, Option.some.injEq, Prod.mk.injEq,
        and_true]
      funext i; exact i.elim0
  | k + 1, f, t => by
      have hk := readVec_encVec rd enc hrd k (Fin.tail f)
      simp only [encVec, List.ofFn_succ, List.flatten_cons, List.append_assoc] at hk ⊢
      simp only [readVec, hrd, Option.bind_some]
      rw [show (List.ofFn fun i : Fin k => enc (f i.succ)) = List.ofFn fun i => enc (Fin.tail f i) from rfl, hk,
        Option.map_some, Fin.cons_self_tail]

theorem readVec_sound {β : Type} (rd : List Bool → Option (β × List Bool)) (enc : β → List Bool)
    (hrd : ∀ w b r, rd w = some (b, r) → w = enc b ++ r) :
    ∀ (k : ℕ) (w : List Bool) (f : Fin k → β) (r : List Bool), readVec rd k w = some (f, r) → w = encVec enc f ++ r
  | 0, w, f, r, h => by
      simp only [readVec, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      simp [encVec]
  | k + 1, w, f, r, h => by
      simp only [readVec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨p, hp, q, hq, hfr⟩ := h
      simp only [Prod.mk.injEq] at hfr
      obtain ⟨rfl, rfl⟩ := hfr
      have h1 := hrd w p.1 p.2 hp
      have h2 := readVec_sound rd enc hrd k p.2 q.1 q.2 hq
      rw [h1, h2]
      simp only [encVec, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, List.flatten_cons, List.append_assoc]

end Readers

section Atoms

/-- The canonical decoder of a circuit of a class mode (the Theorem 2.5 codecs). -/
def decodeAtom : (m : Mode) → (q code : ℕ) → Option (m.Circuit q)
  | .thr, q, code => CanonicalWitnessCodec.decodeNormalizedThresholdThresholdCircuit q code
  | .sym, q, code => CanonicalWitnessCodec.decodeNormalizedSymmetricThresholdCircuit q code

theorem decodeAtom_code (m : Mode) (q : ℕ) (C : m.Circuit q) : decodeAtom m q (m.code C) = some C := by
  cases m
  · exact CanonicalWitnessCodec.decodeNormalizedThresholdThresholdCircuit_encode C
  · exact CanonicalWitnessCodec.decodeNormalizedSymmetricThresholdCircuit_encode C

theorem code_of_decodeAtom {m : Mode} {q code : ℕ} {C : m.Circuit q} (h : decodeAtom m q code = some C) :
    m.code C = code := by
  cases m
  · exact CanonicalWitnessCodec.encodeNormalizedThresholdThresholdCircuit_of_decode h
  · exact CanonicalWitnessCodec.encodeNormalizedSymmetricThresholdCircuit_of_decode h

/-- The word of one grid entry: the sign `σ` and the atom's code. -/
def encEntry (m : Mode) (q : ℕ) (e : ℤ × m.Circuit q) : List Bool := intWord e.1 ++ natWord (m.code e.2)

/-- Reads one grid entry, rejecting codes that are not canonical atoms of the mode. -/
def readEntry (m : Mode) (q : ℕ) (w : List Bool) : Option ((ℤ × m.Circuit q) × List Bool) :=
  (readInt w).bind fun p => (readNat p.2).bind fun c => (decodeAtom m q c.1).map fun C => ((p.1, C), c.2)

theorem readEntry_encEntry (m : Mode) (q : ℕ) (e : ℤ × m.Circuit q) (t : List Bool) :
    readEntry m q (encEntry m q e ++ t) = some (e, t) := by
  simp only [readEntry, encEntry, List.append_assoc, readInt_intWord, Option.bind_some, readNat_natWord,
    decodeAtom_code, Option.map_some]

theorem readEntry_sound (m : Mode) (q : ℕ) (w : List Bool) (e : ℤ × m.Circuit q) (r : List Bool)
    (h : readEntry m q w = some (e, r)) : w = encEntry m q e ++ r := by
  simp only [readEntry, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨p, hp, c, hc, C, hC, he⟩ := h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  rw [readInt_sound hp, readNat_sound hc, ← code_of_decodeAtom hC]
  simp [encEntry]

end Atoms

section Guess
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B}

/-- The tag bit of a class mode (as in `UnionGuess.word`). -/
def modeTag : Mode → Bool
  | .thr => true
  | .sym => false

/-- The guess after its tag bit: oracle code, the entries variable-major, then zero padding only. -/
def decodeBody (S : UnionSetup I) {N : ℕ} (z : BitInput N) (m : Mode) (w : List Bool) : Option (UnionGuess S z) :=
  (readNat w).bind fun p =>
    (CanonicalWitnessCodec.decodeBooleanCircuit (S.pcp.nativeWidth N) p.1).bind fun oracle =>
      (readVec (readVec (readEntry m (S.request z oracle).arity) (S.gridSize (S.request z oracle).arity))
          ((S.pcppOf z oracle).systematicBits + (S.pcppOf z oracle).auxiliaryBits) p.2).bind fun r =>
        if r.2.all (fun b => !b) then
          some ⟨oracle, m, fun X a => (r.1 X a).1, fun X a => (r.1 X a).2⟩
        else none

/-- **The guess decoder** of the union machine: the tag bit, then the body. -/
def decodeGuess (S : UnionSetup I) {N : ℕ} (z : BitInput N) : List Bool → Option (UnionGuess S z)
  | [] => none
  | b :: w => decodeBody S z (if b then .thr else .sym) w

/-- **The guess encoder**: the guess word of `UnionAccepts`. -/
def encodeGuess {S : UnionSetup I} {N : ℕ} {z : BitInput N} (g : UnionGuess S z) : List Bool := g.word

variable {S : UnionSetup I} {N : ℕ} {z : BitInput N}

/-- The encoder's length bound is the `UnionAccepts` word bound, verbatim. -/
theorem encodeGuess_length_le_iff (g : UnionGuess S z) : (encodeGuess g).length ≤ N / 16 ↔ g.word.length ≤ N / 16 :=
  Iff.rfl

theorem word_eq (g : UnionGuess S z) :
    g.word = modeTag g.mode :: (natWord (ExecutableInterfaces.encodeBooleanCircuit g.oracle) ++
      encVec (encVec (encEntry g.mode g.q)) (fun X a => (g.sign X a, g.atom X a))) := by
  obtain ⟨oracle, m, sign, atom⟩ := g
  cases m <;> rfl

theorem all_replicate_false (k : ℕ) : (List.replicate k false).all (fun b => !b) = true :=
  List.all_eq_true.2 fun x hx => by rw [List.eq_of_mem_replicate hx]; rfl

/-- **Round trip**: a guess word, padded with zeros, decodes to the guess. -/
theorem decodeGuess_encodeGuess (g : UnionGuess S z) (k : ℕ) :
    decodeGuess S z (encodeGuess g ++ List.replicate k false) = some g := by
  unfold encodeGuess
  rw [word_eq, List.cons_append]
  obtain ⟨oracle, m, sign, atom⟩ := g
  have hm : (if modeTag m then Mode.thr else Mode.sym) = m := by cases m <;> rfl
  simp only [decodeGuess, hm]
  unfold decodeBody
  rw [List.append_assoc, readNat_natWord, Option.bind_some, CanonicalWitnessCodec.decodeBooleanCircuit_encode,
    Option.bind_some, readVec_encVec _ _ (fun b t => readVec_encVec _ _ (readEntry_encEntry m _) _ b t),
    Option.bind_some,
    all_replicate_false, if_pos rfl]

/-- The body decoder accepts only canonical words followed by zeros. -/
theorem decodeBody_sound (m : Mode) {w : List Bool} {g : UnionGuess S z} (h : decodeBody S z m w = some g) :
    ∃ k, modeTag m :: w = g.word ++ List.replicate k false := by
  simp only [decodeBody, Option.bind_eq_some_iff] at h
  obtain ⟨p, hp, oracle, ho, r, hr, hg⟩ := h
  split_ifs at hg with hpad
  simp only [Option.some.injEq] at hg
  subst hg
  refine ⟨r.2.length, ?_⟩
  have hpad' : r.2 = List.replicate r.2.length false :=
    List.eq_replicate_iff.2 ⟨rfl, fun b hb => by simpa using (List.all_eq_true.1 hpad) b hb⟩
  have hw := readNat_sound hp
  have hc := CanonicalWitnessCodec.encodeBooleanCircuit_of_decode ho
  have hv := readVec_sound _ _ (fun w b r h => readVec_sound _ _ (readEntry_sound m _) _ w b r h) _ _ _ _ hr
  rw [word_eq, hw, hv, ← hc, ← hpad']
  simp only [List.cons_append, List.append_assoc]

/-- **Malformed words are rejected**: a word decodes only if it is a canonical guess word followed by zeros. -/
theorem encodeGuess_of_decodeGuess {w : List Bool} {g : UnionGuess S z} (h : decodeGuess S z w = some g) :
    ∃ k, w = encodeGuess g ++ List.replicate k false := by
  match w, h with
  | b :: w, h =>
      have hb : modeTag (if b then Mode.thr else Mode.sym) = b := by cases b <;> rfl
      obtain ⟨k, hk⟩ := decodeBody_sound _ h
      rw [hb] at hk
      exact ⟨k, hk⟩

/-- A guess decoded from a word within the refuter's `⌊N/16⌋` budget meets `UnionAccepts`' word bound. -/
theorem word_le_of_decodeGuess {w : List Bool} {g : UnionGuess S z} (h : decodeGuess S z w = some g)
    (hw : w.length ≤ N / 16) : g.word.length ≤ N / 16 := by
  obtain ⟨k, rfl⟩ := encodeGuess_of_decodeGuess h
  simp only [List.length_append] at hw
  exact le_trans (Nat.le_add_right _ _) hw

end Guess

end NearCubicWires.WireExponent3_5.Transfer
