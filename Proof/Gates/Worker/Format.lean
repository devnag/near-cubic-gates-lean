import Proof.Gates.Worker.Decide
import Proof.MachineModel.OrdinarySignedSortKey

set_option autoImplicit false

namespace NearCubicGates.Close.Worker

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairOrdinary
open NearCubicWires.Bindings.CLW20Lemma311 NearCubicWires.RepairSource.CloseoutLanguage NearCubicWires.ExecutableInterfaces
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close.Interfaces NearCubicGates NearCubicGates.Close.Counter
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.CanonicalWitnessCodec

namespace Format

/-! ## Readers -/

/-- A unary count `1^k 0`. -/
def readCount : List Bool → ℕ × List Bool
  | true :: r => ((readCount r).1 + 1, (readCount r).2)
  | false :: r => (0, r)
  | [] => (0, [])

/-- `ℓ` raw bits (`false` past the end). -/
def readBits (ℓ : ℕ) (w : List Bool) : List Bool × List Bool :=
  (List.ofFn fun i : Fin ℓ => w.getD i.val false, w.drop ℓ)

/-- A bit field: a count, then that many bits. -/
def readField (w : List Bool) : List Bool × List Bool :=
  readBits (readCount w).1 (readCount w).2

/-- A natural number: a bit field, little-endian. -/
def readNum (w : List Bool) : ℕ × List Bool :=
  (value (readField w).1, (readField w).2)

/-- An integer: a sign bit, then a natural number. -/
def readInt (w : List Bool) : ℤ × List Bool :=
  (if w.headD false then -((readNum w.tail).1 : ℤ) else (readNum w.tail).1, (readNum w.tail).2)

/-- `n` items in a row. -/
def readMany {α : Type} (rd : List Bool → α × List Bool) : ℕ → List Bool → List α × List Bool
  | 0, w => ([], w)
  | n + 1, w => ((rd w).1 :: (readMany rd n (rd w).2).1, (readMany rd n (rd w).2).2)

/-- A gate on `q` inputs: the weights, then the threshold. -/
def readGate (q : ℕ) (w : List Bool) : NormalizedThresholdGate q × List Bool :=
  (⟨fun i => (readMany readInt q w).1.getD i.val 0, (readInt (readMany readInt q w).2).1⟩,
    (readInt (readMany readInt q w).2).2)

/-- A circuit: the gate count, the gates, as many coefficients, the table. -/
def readCircuit (q : ℕ) (w : List Bool) : NCircuit q × List Bool :=
  let k := readCount w
  let gs := readMany (readGate q) k.1 k.2
  let cs := readMany readInt k.1 gs.2
  (⟨gs.1, cs.1, (readField cs.2).1⟩, (readField cs.2).2)

theorem readCount_snd : ∀ w : List Bool, (readCount w).2 = w.drop ((readCount w).1 + 1)
  | [] => rfl
  | true :: r => by simp only [readCount, List.drop_succ_cons]; exact readCount_snd r
  | false :: r => rfl

/-- The rest after a field is the word after its `2ℓ + 1` bits. -/
theorem readField_snd (w : List Bool) : (readField w).2 = w.drop (2 * (readCount w).1 + 1) := by
  unfold readField readBits
  simp only [readCount_snd, List.drop_drop]
  congr 1
  omega

/-! ## Honest words -/

def countWord (k : ℕ) : List Bool := List.replicate k true ++ [false]
def fieldWord (b : List Bool) : List Bool := countWord b.length ++ b
def numWord (x : ℕ) : List Bool := fieldWord (binary (natBitLength x) x)
def intWordF (z : ℤ) : List Bool := decide (z < 0) :: numWord z.natAbs
def gateWordF {q : ℕ} (G : NormalizedThresholdGate q) : List Bool :=
  (List.ofFn G.weight).flatMap intWordF ++ intWordF G.threshold
def circuitWordF {q : ℕ} (C : NCircuit q) : List Bool :=
  countWord C.gates.length ++ C.gates.flatMap gateWordF ++ C.coeffs.flatMap intWordF ++ fieldWord C.table

/-! ## Round trips -/

theorem readCount_word (k : ℕ) (r : List Bool) : readCount (countWord k ++ r) = (k, r) := by
  induction k with
  | zero => simp [countWord, readCount]
  | succ k ih =>
    have h : countWord (k + 1) ++ r = true :: (countWord k ++ r) := by
      simp [countWord, List.replicate_succ]
    rw [h, readCount, ih]

theorem readBits_append (b r : List Bool) : readBits b.length (b ++ r) = (b, r) := by
  unfold readBits
  refine Prod.ext ?_ (by simp)
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_ofFn]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using h1)]
  simp [List.getElem?_eq_getElem h2]

theorem readField_word (b r : List Bool) : readField (fieldWord b ++ r) = (b, r) := by
  unfold readField fieldWord
  rw [List.append_assoc, readCount_word, readBits_append]

theorem lt_two_pow_natBitLength (x : ℕ) : x < 2 ^ natBitLength x := by
  unfold natBitLength
  exact Nat.lt_pow_succ_log_self (by norm_num) x

theorem readNum_word (x : ℕ) (r : List Bool) : readNum (numWord x ++ r) = (x, r) := by
  unfold readNum numWord
  rw [readField_word]
  simp [binary_value _ _ (lt_two_pow_natBitLength x)]

theorem readInt_word (z : ℤ) (r : List Bool) : readInt (intWordF z ++ r) = (z, r) := by
  unfold readInt intWordF
  simp only [List.cons_append, List.headD_cons, List.tail_cons, readNum_word]
  refine Prod.ext ?_ rfl
  by_cases hz : z < 0
  · simp only [hz, decide_true, ↓reduceIte, Int.natCast_natAbs, abs_of_neg hz, neg_neg]
  · simp only [hz, decide_false, Bool.false_eq_true, ↓reduceIte, Int.natCast_natAbs, abs_of_nonneg (not_lt.1 hz)]

theorem readMany_mem {α : Type} (rd : List Bool → α × List Bool) (enc : α → List Bool) (xs : List α)
    (hrd : ∀ a ∈ xs, ∀ r, rd (enc a ++ r) = (a, r)) (r : List Bool) :
    readMany rd xs.length (xs.flatMap enc ++ r) = (xs, r) := by
  induction xs with
  | nil => simp [readMany]
  | cons a xs ih =>
    have ha := hrd a (by simp)
    have ht := ih (fun b hb => hrd b (by simp [hb]))
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc, readMany, ha, ht]

theorem readMany_word {α : Type} (rd : List Bool → α × List Bool) (enc : α → List Bool)
    (hrd : ∀ a r, rd (enc a ++ r) = (a, r)) (xs : List α) (r : List Bool) :
    readMany rd xs.length (xs.flatMap enc ++ r) = (xs, r) :=
  readMany_mem rd enc xs (fun a _ => hrd a) r

theorem readGate_word {q : ℕ} (G : NormalizedThresholdGate q) (r : List Bool) :
    readGate q (gateWordF G ++ r) = (G, r) := by
  have hm := readMany_word readInt intWordF readInt_word (List.ofFn G.weight) (intWordF G.threshold ++ r)
  rw [List.length_ofFn] at hm
  unfold readGate gateWordF
  rw [List.append_assoc, hm]
  simp only [readInt_word]
  obtain ⟨wt, th⟩ := G
  congr
  funext i
  simp [List.getD_eq_getElem?_getD]

theorem readCircuit_word {q : ℕ} (C : NCircuit q) (hC : C.coeffs.length = C.gates.length) (r : List Bool) :
    readCircuit q (circuitWordF C ++ r) = (C, r) := by
  unfold readCircuit circuitWordF
  simp only [List.append_assoc, readCount_word]
  rw [readMany_word (readGate q) gateWordF readGate_word, ← hC,
    readMany_word readInt intWordF readInt_word, readField_word]

end Format

open Format

/-! ## The guess -/

/-- A fixed oracle for undecodable codes (the machine rejects them, so it is never tested). -/
def defaultOracle (n : ℕ) : BooleanCircuit n where
  nodes := [.const false]
  output := ⟨0, by simp⟩
  wellFormed := by intro i; fin_cases i; trivial

section Guess
variable (s : GateSources) (P : ThreeQueryPCPP) (g : GateParams)

noncomputable def oracleOK (N : ℕ) (w : List Bool) : Bool :=
  (decodeBooleanCircuit (width s g N) (value (readField w).1)).isSome &&
    (decodeBooleanCircuit (width s g N) (value (readField (readField w).2).1)).isSome

/-- Both circuit fields of the word `w` decode, to the pair `B` (the set-up's decoders, `sec:gadget-machine`: "rejecting
malformed descriptions"). -/
def Decodes (q : ℕ) (w : List Bool) (B : Outer.OuterGuess q) : Prop :=
  decodeBooleanCircuit q (value (readField w).1) = some B.src ∧
    decodeBooleanCircuit q (value (readField (readField w).2).1) = some B.pf

theorem oracleOK_of_decodes {N : ℕ} {w : List Bool} {B : Outer.OuterGuess (width s g N)}
    (h : Decodes (width s g N) w B) : oracleOK s g N w = true := by
  unfold oracleOK
  rw [h.1, h.2]
  rfl

theorem exists_decodes_of_oracleOK {N : ℕ} {w : List Bool} (h : oracleOK s g N w = true) :
    ∃ B : Outer.OuterGuess (width s g N), Decodes (width s g N) w B := by
  unfold oracleOK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨b1, h1⟩ := Option.isSome_iff_exists.mp h.1
  obtain ⟨b2, h2⟩ := Option.isSome_iff_exists.mp h.2
  exact ⟨⟨b1, b2⟩, h1, h2⟩

/-- **The total decoder.** -/
noncomputable def decodeGuess (N : ℕ) (x : BitInput N) (w : List Bool) : Guess (width s g N) :=
  let o := readField w
  let o2 := readField o.2
  let O : Outer.OuterGuess (width s g N) :=
    ⟨(decodeBooleanCircuit (width s g N) (value o.1)).getD (defaultOracle _),
      (decodeBooleanCircuit (width s g N) (value o2.1)).getD (defaultOracle _)⟩
  let cs := readMany (readCircuit (width s g N)) ((pcpp s P g x O).proofBits + gadgets s g N) o2.2
  let ws := readMany readField (10 * gadgets s g N) cs.2
  ⟨O, fun j => cs.1.getD j (NCircuit.empty _), fun a t => ws.1.getD (10 * a + t.val) []⟩

theorem decodeGuess_oracle (N : ℕ) (x : BitInput N) (w : List Bool) :
    (decodeGuess s P g N x w).oracle =
      ⟨(decodeBooleanCircuit (width s g N) (value (readField w).1)).getD (defaultOracle _),
        (decodeBooleanCircuit (width s g N) (value (readField (readField w).2).1)).getD (defaultOracle _)⟩ := rfl

theorem decodeGuess_oracle_eq (N : ℕ) (x : BitInput N) (w : List Bool) (B : Outer.OuterGuess (width s g N))
    (h : Decodes (width s g N) w B) : (decodeGuess s P g N x w).oracle = B := by
  rw [decodeGuess_oracle, h.1, h.2]
  rfl

theorem decodeGuess_circuits (N : ℕ) (x : BitInput N) (w : List Bool) (j : ℕ) :
    (decodeGuess s P g N x w).circuits j = (readMany (readCircuit (width s g N))
      ((pcpp s P g x (decodeGuess s P g N x w).oracle).proofBits + gadgets s g N)
        (readField (readField w).2).2).1.getD j (NCircuit.empty _) := rfl

theorem decodeGuess_witnesses (N : ℕ) (x : BitInput N) (w : List Bool) (a : ℕ) (t : Fin 10) :
    (decodeGuess s P g N x w).witnesses a t = (readMany readField (10 * gadgets s g N)
      (readMany (readCircuit (width s g N)) ((pcpp s P g x (decodeGuess s P g N x w).oracle).proofBits +
        gadgets s g N) (readField (readField w).2).2).2).1.getD (10 * a + t.val) [] := rfl

/-- The honest encoding of a guess. -/
noncomputable def encodeGuess {N : ℕ} (x : BitInput N) (G : Guess (width s g N)) : List Bool :=
  numWord (encodeBooleanCircuit G.oracle.src) ++ numWord (encodeBooleanCircuit G.oracle.pf) ++
    ((List.range (G.auxCount P x)).map G.circuits).flatMap circuitWordF ++
    (witnessList G (gadgets s g N)).flatMap fieldWord

theorem getD_map_range {α : Type} (f : ℕ → α) (n j : ℕ) (hj : j < n) (d : α) :
    ((List.range n).map f).getD j d = f j := by
  simp [List.getD_eq_getElem?_getD, hj]

/-- Decoding an honest encoding (any padding after it) gives the oracle and agrees with the guess. -/
theorem decodeGuess_encode {N : ℕ} (x : BitInput N) (G : Guess (width s g N))
    (hC : ∀ j < G.auxCount P x, (G.circuits j).coeffs.length = (G.circuits j).gates.length) (pad : List Bool) :
    oracleOK s g N (encodeGuess s P g x G ++ pad) = true ∧
      Guess.Agree P x (decodeGuess s P g N x (encodeGuess s P g x G ++ pad)) G := by
  set w := encodeGuess s P g x G ++ pad with hw
  set rest := ((List.range (G.auxCount P x)).map G.circuits).flatMap circuitWordF ++
    ((witnessList G (gadgets s g N)).flatMap fieldWord ++ pad) with hrest
  have ho1 : readField w = (binary (natBitLength (encodeBooleanCircuit G.oracle.src))
      (encodeBooleanCircuit G.oracle.src), numWord (encodeBooleanCircuit G.oracle.pf) ++ rest) := by
    rw [hw, hrest]
    unfold encodeGuess numWord
    simp only [List.append_assoc]
    exact readField_word _ _
  have ho2 : readField (readField w).2 = (binary (natBitLength (encodeBooleanCircuit G.oracle.pf))
      (encodeBooleanCircuit G.oracle.pf), rest) := by
    rw [ho1]
    unfold numWord
    exact readField_word _ _
  have hv1 : value (binary (natBitLength (encodeBooleanCircuit G.oracle.src)) (encodeBooleanCircuit G.oracle.src)) =
      encodeBooleanCircuit G.oracle.src := binary_value _ _ (lt_two_pow_natBitLength _)
  have hv2 : value (binary (natBitLength (encodeBooleanCircuit G.oracle.pf)) (encodeBooleanCircuit G.oracle.pf)) =
      encodeBooleanCircuit G.oracle.pf := binary_value _ _ (lt_two_pow_natBitLength _)
  have hdec1 := CanonicalWitnessCodec.decodeBooleanCircuit_encode G.oracle.src
  have hdec2 := CanonicalWitnessCodec.decodeBooleanCircuit_encode G.oracle.pf
  have hO : (decodeGuess s P g N x w).oracle = G.oracle := by
    rw [decodeGuess_oracle, ho2, ho1, hv1, hv2, hdec1, hdec2]
    rfl
  have ho : (readField (readField w).2).2 = rest := by rw [ho2]
  have hcs := readMany_mem (readCircuit (width s g N)) circuitWordF ((List.range (G.auxCount P x)).map G.circuits)
    (fun C hCm r => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hCm
      exact readCircuit_word _ (hC i (List.mem_range.1 hi)) r)
    ((witnessList G (gadgets s g N)).flatMap fieldWord ++ pad)
  rw [List.length_map, List.length_range] at hcs
  have hcirc : ∀ j, (decodeGuess s P g N x w).circuits j =
      ((List.range (G.auxCount P x)).map G.circuits).getD j (NCircuit.empty _) := by
    intro j
    rw [decodeGuess_circuits, hO, ho]
    exact congrArg (fun l => l.1.getD j (NCircuit.empty _)) hcs
  have hws := readMany_word readField fieldWord readField_word (witnessList G (gadgets s g N)) pad
  have hlen : (witnessList G (gadgets s g N)).length = 10 * gadgets s g N := by simp [witnessList]
  rw [hlen] at hws
  have hwit : ∀ a t, (decodeGuess s P g N x w).witnesses a t =
      (witnessList G (gadgets s g N)).getD (10 * a + t.val) [] := by
    intro a t
    rw [decodeGuess_witnesses, hO, ho]
    calc _ = (readMany readField (10 * gadgets s g N) ((witnessList G (gadgets s g N)).flatMap fieldWord ++ pad)).1.getD
          (10 * a + t.val) [] :=
          congrArg (fun l => (readMany readField (10 * gadgets s g N) l.2).1.getD (10 * a + t.val) []) hcs
      _ = _ := by rw [hws]
  refine ⟨?_, hO, ?_, ?_⟩
  · unfold oracleOK
    rw [ho2, ho1, hv1, hv2, hdec1, hdec2]; rfl
  · intro j hj
    have hA : (decodeGuess s P g N x w).auxCount P x = G.auxCount P x := by unfold Guess.auxCount; rw [hO]
    rw [hA] at hj
    rw [hcirc j]
    exact getD_map_range G.circuits _ j hj _
  · intro a ha t
    rw [hwit a t]
    unfold witnessList
    have hi : 10 * a + t.val < 10 * gadgets s g N := by omega
    rw [getD_map_range _ _ _ hi]
    have h1 : (10 * a + t.val) / 10 = a := by omega
    have h2 : (⟨(10 * a + t.val) % 10, Nat.mod_lt _ (by norm_num)⟩ : Fin 10) = t := by ext; simp
    simp only [h1, h2]

/-! ## The verdict: what the worker machine computes -/

/-- **The set-up's flag** (`sec:gadget-machine`): both circuit fields decode, and the decoded pair passes the set-up's guards
(`N = 2^ν`, the onset, `B_src`'s description within `L_ν` bits, CHECK). The set-up machine computes this flag. -/
noncomputable def setupFlag (N : ℕ) (x : BitInput N) (w : List Bool) : Bool := by
  classical
  exact oracleOK s g N w && decide ((decodeGuess s P g N x w).SetupOK x)

/-- **The worker's verdict** on input `x` and witness word `w`: the set-up's flag, and the decoded guess passes the
test. The machine computes exactly this on every input. -/
noncomputable def verdict {B1 B2 : ℕ} (ctr : Counter B1 B2) (budget : ℕ → ℕ) (εT ω : ℚ) (N : ℕ) (x : BitInput N)
    (w : List Bool) : Bool := by
  classical
  exact setupFlag s P g N x w && decide ((decodeGuess s P g N x w).Certified P x ctr budget (εT : ℝ) ω)

/-- An accepted witness word carries a guess passing the test. -/
theorem verdict_sound {B1 B2 : ℕ} (ctr : Counter B1 B2) (budget : ℕ → ℕ) (εT ω : ℚ) (N : ℕ) (x : BitInput N)
    (w : List Bool) (h : verdict s P g ctr budget εT ω N x w = true) :
    ∃ G : Guess (width s g N), G.Certified P x ctr budget (εT : ℝ) ω := by
  classical
  unfold verdict at h
  rw [Bool.and_eq_true, decide_eq_true_iff] at h
  exact ⟨_, h.2⟩

/-- The honest encoding of a guess passing the test is accepted, whatever follows it. -/
theorem verdict_encode {B1 B2 : ℕ} (ctr : Counter B1 B2) (budget : ℕ → ℕ) (εT ω : ℚ) {N : ℕ} (x : BitInput N)
    (G : Guess (width s g N))
    (hC : ∀ j < G.auxCount P x, (G.circuits j).coeffs.length = (G.circuits j).gates.length)
    (hG : G.Certified P x ctr budget (εT : ℝ) ω) (pad : List Bool) :
    verdict s P g ctr budget εT ω N x (encodeGuess s P g x G ++ pad) = true := by
  classical
  have henc := decodeGuess_encode s P g x G hC pad
  have hcert : (decodeGuess s P g N x (encodeGuess s P g x G ++ pad)).Certified P x ctr budget (εT : ℝ) ω :=
    (certified_of_agree s P g ctr budget (εT : ℝ) ω x G _ henc.2).2 hG
  have hsetup : (decodeGuess s P g N x (encodeGuess s P g x G ++ pad)).SetupOK x := hcert.1.2.2.2.2
  unfold verdict setupFlag
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
  exact ⟨⟨henc.1, hsetup⟩, hcert⟩

end Guess

end NearCubicGates.Close.Worker
