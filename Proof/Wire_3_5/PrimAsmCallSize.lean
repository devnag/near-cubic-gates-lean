import Proof.Wire_3_5.PrimAsmPlan
import Proof.Wire_3_5.PrimAsmCodec
import Proof.Amplification.RecoveryWitnessPolicy
import Proof.Foundations.PolynomialSchedule
import Bindings.Williams14_Corollary4_4

/-! # PA params: every call's word has polynomial length

Consumer checks (a residual about a time-bounded machine quantifies only over inputs the machine
can read): every request meeting the per-call hypothesis `I.Call` has a word of polynomial length in `n`, with a
degree fixed by the caller's inputs (`descDeg`, `carrierDeg`, `nameCount`), not by the gate's free constants.

* `word_length_le`: `|req.word| ≤ wordBound descDeg carrierDeg nameCount n` under `I.Call req`: `natWord n`, the mode
  bit, `natWord a` (`a ≤ 4`), the circuit codes (base's canonical code bounds at the parameter `(n+1)^descDeg + …`),
  the carrier codes (at most `nameCount`, each a balanced list of at most `(n+1)^carrierDeg` atom codes), and the
  translation (`r ≤ n/4` codes, each `< 2^s ≤ n + 1`);
* `gate_word_length_le`: the gate's calls (`descDeg = carrierDeg = 26`, `nameCount = 2`);
* `wordBound_poly`: `wordBound 26 26 2` is polynomially bounded (base's `PolynomiallyBounded`).

Donors: base `RecoveryWitnessPolicy` (`encodeNormalized{Symmetric,Threshold}Circuit_bits_le_parameter`,
`encodeBalancedList_bits_le_of_bounds`, `encodeTaggedList_two_bits_le`, `encodeIntList_bits_le_parameter`,
`encodeInt_bits_le_parameter`), `PolynomialSchedule.polynomiallyBounded_*`, `Williams14.natWord_length`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.CallSize
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.CanonicalBinary NearCubicWires.RecoveryWitnessPolicy
open NearCubicWires.SupplierPipeline NearCubicWires.SourceInterfaces NearCubicWires.PolynomialSchedule
open NearCubicWires.WireExponent3_5.PrimAsm.Codec

/-- The code parameter of a call at length `n`: it bounds every circuit description, carrier atom count, atom
description, and the arity. -/
def codeParam (D Cd n : ℕ) : ℕ := (n + 1) ^ D + (n + 1) ^ Cd + n + 4

/-- The bits of a circuit code within the parameter `p`. -/
def circBits (p : ℕ) : ℕ := canonicalSymmetricCircuitCodeBitBound p + canonicalThresholdCircuitCodeBitBound p

/-- The bits of a carrier atom's code (`encodeTaggedList [encodeIntList weights, encodeInt threshold]`). -/
def atomBits (p : ℕ) : ℕ :=
  taggedListBitBound [canonicalBalancedCodeBitBound p (canonicalIntCodeBitBound p), canonicalIntCodeBitBound p]

/-- The bits of a carrier code (a balanced list of atom codes). -/
def carrierBits (p : ℕ) : ℕ := canonicalBalancedCodeBitBound p (atomBits p)

/-- The word-length bound of a call. -/
def wordBound (D Cd K n : ℕ) : ℕ :=
  (2 * n + 3) + 1 + 11 + 4 * (2 * circBits (codeParam D Cd n) + 1) +
    ((2 * K + 3) + K * (2 * carrierBits (codeParam D Cd n) + 1)) + (2 * n + 3) * (n + 1)

theorem natWord_len_le {x m : ℕ} (h : natBitLength x ≤ m) : (RepairRepresentation.natWord x).length ≤ 2 * m + 1 := by
  rw [Bindings.Williams14.natWord_length]; omega

theorem natWord_len_le_self (x : ℕ) : (RepairRepresentation.natWord x).length ≤ 2 * x + 3 := by
  have := CopyNat.natBitLength_le_self_succ x
  rw [Bindings.Williams14.natWord_length]; omega

theorem flatMap_length_le {α β : Type} (l : List α) (f : α → List β) (k : ℕ) (h : ∀ x ∈ l, (f x).length ≤ k) :
    (l.flatMap f).length ≤ l.length * k := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    have h1 := h x (by simp)
    have h2 := ih (fun y hy => h y (by simp [hy]))
    omega

/-- A circuit code within the parameter. -/
theorem code_bits_le (m : Mode) {n : ℕ} (C : m.Circuit n) (p : ℕ) (h4 : 4 ≤ p) (hd : m.descriptionBits C ≤ p) :
    natBitLength (m.code C) ≤ circBits p := by
  unfold circBits
  cases m
  · have := encodeNormalizedThresholdCircuit_bits_le_parameter C h4 hd
    show natBitLength (encodeNormalizedThresholdThresholdCircuit C) ≤ _
    omega
  · have := encodeNormalizedSymmetricCircuit_bits_le_parameter C h4 hd
    show natBitLength (encodeNormalizedSymmetricThresholdCircuit C) ≤ _
    omega

/-- A carrier code within the parameter. -/
theorem carrier_bits_le {n : ℕ} (X : Stars.Carrier n) (deg p : ℕ) (hX : X.WithinEnvelope deg)
    (hp : (n + 1) ^ deg + n ≤ p) : natBitLength X.code ≤ carrierBits p := by
  unfold Stars.Carrier.code carrierBits canonicalBalancedCodeBitBound
  apply encodeBalancedList_bits_le_of_bounds
  · rw [List.length_map]; exact le_trans hX.1 (by omega)
  · intro v hv
    rcases List.mem_map.mp hv with ⟨g, hg, rfl⟩
    have henc := hX.2 g hg
    have hw : ∀ i, intBitLength (g.weight i) ≤ p := by
      intro i
      have hsingle : intBitLength (g.weight i) ≤ ∑ j, intBitLength (g.weight j) :=
        Finset.single_le_sum (f := fun j => intBitLength (g.weight j)) (fun j _ => Nat.zero_le _)
          (Finset.mem_univ i)
      unfold NormalizedThresholdGate.encodingBits at henc
      omega
    have ht : intBitLength g.threshold ≤ p := by
      unfold NormalizedThresholdGate.encodingBits at henc; omega
    unfold atomBits
    exact encodeTaggedList_two_bits_le
      (encodeIntList_bits_le_parameter _ p (by rw [List.length_ofFn]; omega) (by
        intro z hz; rcases List.mem_ofFn.mp hz with ⟨i, rfl⟩; exact hw i))
      (encodeInt_bits_le_parameter ht)

/-- **Every call's word has polynomial length**. -/
theorem word_length_le {kclk : ℕ} {E : Cost.Envelope} {B : Cost.TimeBudget kclk E} (I : PrimitiveInputs B)
    (req : PrimRequest) (h : I.Call req) :
    req.word.length ≤ wordBound I.descDeg I.carrierDeg I.nameCount req.n := by
  obtain ⟨_, hcar, hdesc, hcount, ⟨htlen, htval⟩, hstar, _⟩ := h
  obtain ⟨p, hp⟩ : ∃ p, p = codeParam I.descDeg I.carrierDeg req.n := ⟨_, rfl⟩
  have hpdef : p = (req.n + 1) ^ I.descDeg + (req.n + 1) ^ I.carrierDeg + req.n + 4 := by rw [hp]; rfl
  rw [word_length]
  unfold wordBound
  rw [← hp]
  have h1 := natWord_len_le_self req.n
  have ha := req.ha
  have h2 : (RepairRepresentation.natWord req.a).length ≤ 11 := by
    have := natWord_len_le_self req.a; omega
  have h3 : ((codeList req).flatMap RepairRepresentation.natWord).length ≤ 4 * (2 * circBits p + 1) := by
    have hlen : ∀ c ∈ codeList req, (RepairRepresentation.natWord c).length ≤ 2 * circBits p + 1 := by
      intro c hc
      unfold codeList at hc
      rcases List.mem_ofFn.mp hc with ⟨i, rfl⟩
      exact natWord_len_le (code_bits_le req.mode (req.circuits i) p (by omega) (le_trans (hdesc i) (by omega)))
    calc ((codeList req).flatMap RepairRepresentation.natWord).length
        ≤ (codeList req).length * (2 * circBits p + 1) := flatMap_length_le _ _ _ hlen
      _ ≤ 4 * (2 * circBits p + 1) := Nat.mul_le_mul_right _ (by rw [codeList_length]; exact req.ha)
  have h4 : (RepairRepresentation.natListWord (carrierCodes req)).length ≤
      (2 * I.nameCount + 3) + I.nameCount * (2 * carrierBits p + 1) := by
    unfold RepairRepresentation.natListWord
    rw [List.length_append]
    have hc : (carrierCodes req).length ≤ I.nameCount := by unfold carrierCodes; rw [List.length_map]; exact hcount
    have e1 := natWord_len_le_self (carrierCodes req).length
    have e2 : ((carrierCodes req).flatMap RepairRepresentation.natWord).length ≤
        (carrierCodes req).length * (2 * carrierBits p + 1) := by
      apply flatMap_length_le
      intro c hc'
      unfold carrierCodes at hc'
      rcases List.mem_map.mp hc' with ⟨X, hX, rfl⟩
      exact natWord_len_le (carrier_bits_le X I.carrierDeg p (hcar X hX) (by omega))
    have e3 := Nat.mul_le_mul_right (2 * carrierBits p + 1) hc
    omega
  have h5 : (RepairRepresentation.natListWord req.translation).length ≤ (2 * req.n + 3) * (req.n + 1) := by
    unfold RepairRepresentation.natListWord
    rw [List.length_append]
    have hr4 := hstar.2.2.1
    have hl : req.translation.length ≤ req.n := by rw [htlen]; omega
    have e1 := natWord_len_le_self req.translation.length
    have e2 : (req.translation.flatMap RepairRepresentation.natWord).length ≤
        req.translation.length * (2 * req.n + 3) := by
      apply flatMap_length_le
      intro t ht
      have g1 := htval t ht
      have g2 : 2 ^ Nat.log 2 (req.n / B.rOf req.n + 1) ≤ req.n / B.rOf req.n + 1 :=
        Nat.pow_log_le_self 2 (Nat.succ_ne_zero _)
      have g3 : req.n / B.rOf req.n ≤ req.n := Nat.div_le_self _ _
      have := natWord_len_le_self t
      omega
    have e3 := Nat.mul_le_mul_right (2 * req.n + 3) hl
    have e4 : (2 * req.n + 3) * (req.n + 1) = req.n * (2 * req.n + 3) + (2 * req.n + 3) := by ring
    omega
  omega

/-- **The gate's calls** (`descDeg = carrierDeg = 26`, `nameCount = 2`). -/
theorem gate_word_length_le (l : Literals) (F : Split.GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)
    (req : PrimRequest) (h : (Plan.callInputs l F kclk coef A a ha).Call req) :
    req.word.length ≤ wordBound 26 26 2 req.n := by
  have hD : (Plan.callInputs l F kclk coef A a ha).descDeg = 26 := rfl
  have hC : (Plan.callInputs l F kclk coef A a ha).carrierDeg = 26 := rfl
  have hK : (Plan.callInputs l F kclk coef A a ha).nameCount = 2 := rfl
  have hw := word_length_le _ req h
  rw [hD, hC, hK] at hw
  exact hw

/-! ## The bound is polynomial -/

theorem pb_bal {f : ℕ → ℕ} (hf : PolynomiallyBounded f) :
    PolynomiallyBounded (fun p => canonicalBalancedCodeBitBound p (f p)) :=
  polynomiallyBounded_mono (fun _ => le_of_eq rfl)
    (polynomiallyBounded_add (polynomiallyBounded_constant 1)
      (polynomiallyBounded_mul (polynomiallyBounded_mul (polynomiallyBounded_constant 2)
        (polynomiallyBounded_pow polynomiallyBounded_id 4))
        (polynomiallyBounded_add (polynomiallyBounded_mul polynomiallyBounded_id hf)
          (polynomiallyBounded_constant 1))))

theorem pb_intB : PolynomiallyBounded canonicalIntCodeBitBound :=
  polynomiallyBounded_mono (fun _ => le_of_eq rfl)
    (polynomiallyBounded_mul (polynomiallyBounded_constant 2)
      (polynomiallyBounded_add (polynomiallyBounded_constant 1)
        (polynomiallyBounded_add (polynomiallyBounded_constant 1)
          (polynomiallyBounded_mul (polynomiallyBounded_mul (polynomiallyBounded_constant 2)
            (polynomiallyBounded_pow polynomiallyBounded_id 4))
            (polynomiallyBounded_add polynomiallyBounded_id (polynomiallyBounded_constant 1))))))

theorem pb_natB : PolynomiallyBounded canonicalNatCodeBitBound :=
  polynomiallyBounded_mono (fun _ => le_of_eq rfl)
    (polynomiallyBounded_add (polynomiallyBounded_constant 1)
      (polynomiallyBounded_mul (polynomiallyBounded_mul (polynomiallyBounded_constant 2)
        (polynomiallyBounded_pow (polynomiallyBounded_add polynomiallyBounded_id (polynomiallyBounded_constant 1)) 4))
        (polynomiallyBounded_add (polynomiallyBounded_add polynomiallyBounded_id (polynomiallyBounded_constant 1))
          (polynomiallyBounded_constant 1))))

theorem pb_tag2 {f g : ℕ → ℕ} (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun p => taggedListBitBound [f p, g p]) :=
  polynomiallyBounded_mono (fun _ => le_of_eq rfl)
    (polynomiallyBounded_mul (polynomiallyBounded_constant 4) (polynomiallyBounded_add hf
      (polynomiallyBounded_mul (polynomiallyBounded_constant 4) (polynomiallyBounded_add hg
        (polynomiallyBounded_constant 1)))))

theorem pb_tag3 {f g h : ℕ → ℕ} (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g)
    (hh : PolynomiallyBounded h) : PolynomiallyBounded (fun p => taggedListBitBound [f p, g p, h p]) :=
  polynomiallyBounded_mono (fun _ => le_of_eq rfl)
    (polynomiallyBounded_mul (polynomiallyBounded_constant 4) (polynomiallyBounded_add hf
      (polynomiallyBounded_mul (polynomiallyBounded_constant 4) (polynomiallyBounded_add hg
        (polynomiallyBounded_mul (polynomiallyBounded_constant 4) (polynomiallyBounded_add hh
          (polynomiallyBounded_constant 1)))))))

theorem pb_tag4 {f g h k : ℕ → ℕ} (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g)
    (hh : PolynomiallyBounded h) (hk : PolynomiallyBounded k) :
    PolynomiallyBounded (fun p => taggedListBitBound [f p, g p, h p, k p]) :=
  polynomiallyBounded_mono (fun _ => le_of_eq rfl)
    (polynomiallyBounded_mul (polynomiallyBounded_constant 4) (polynomiallyBounded_add hf
      (polynomiallyBounded_mul (polynomiallyBounded_constant 4) (polynomiallyBounded_add hg
        (polynomiallyBounded_mul (polynomiallyBounded_constant 4) (polynomiallyBounded_add hh
          (polynomiallyBounded_mul (polynomiallyBounded_constant 4) (polynomiallyBounded_add hk
            (polynomiallyBounded_constant 1)))))))))

theorem pb_supB : PolynomiallyBounded canonicalSupportedGateCodeBitBound :=
  pb_tag3 (pb_bal pb_intB) pb_intB (pb_bal (polynomiallyBounded_constant 1))

theorem pb_circBits : PolynomiallyBounded circBits :=
  polynomiallyBounded_add
    (pb_tag4 pb_natB pb_natB (pb_bal pb_supB) (pb_bal (polynomiallyBounded_constant 1)))
    (pb_tag4 pb_natB pb_natB (pb_bal pb_supB) pb_supB)

theorem pb_carrierBits : PolynomiallyBounded carrierBits :=
  pb_bal (pb_tag2 (pb_bal pb_intB) pb_intB)

theorem pb_codeParam : PolynomiallyBounded (codeParam 26 26) :=
  polynomiallyBounded_mono (fun _ => le_of_eq rfl)
    (polynomiallyBounded_add (polynomiallyBounded_add (polynomiallyBounded_add
      (polynomiallyBounded_pow (polynomiallyBounded_add polynomiallyBounded_id (polynomiallyBounded_constant 1)) 26)
      (polynomiallyBounded_pow (polynomiallyBounded_add polynomiallyBounded_id (polynomiallyBounded_constant 1)) 26))
      polynomiallyBounded_id) (polynomiallyBounded_constant 4))

/-- **The gate's word bound is polynomial in `n`.** -/
theorem wordBound_poly : PolynomiallyBounded (wordBound 26 26 2) := by
  have hc := polynomiallyBounded_comp pb_circBits pb_codeParam
  have hk := polynomiallyBounded_comp pb_carrierBits pb_codeParam
  have hn3 := polynomiallyBounded_add (polynomiallyBounded_mul (polynomiallyBounded_constant 2) polynomiallyBounded_id)
    (polynomiallyBounded_constant 3)
  exact polynomiallyBounded_mono (fun _ => le_of_eq rfl)
    (polynomiallyBounded_add (polynomiallyBounded_add (polynomiallyBounded_add (polynomiallyBounded_add
      (polynomiallyBounded_add hn3 (polynomiallyBounded_constant 1)) (polynomiallyBounded_constant 11))
      (polynomiallyBounded_mul (polynomiallyBounded_constant 4) (polynomiallyBounded_add
        (polynomiallyBounded_mul (polynomiallyBounded_constant 2) hc) (polynomiallyBounded_constant 1))))
      (polynomiallyBounded_add (polynomiallyBounded_constant (2 * 2 + 3))
        (polynomiallyBounded_mul (polynomiallyBounded_constant 2) (polynomiallyBounded_add
          (polynomiallyBounded_mul (polynomiallyBounded_constant 2) hk) (polynomiallyBounded_constant 1)))))
      (polynomiallyBounded_mul hn3 (polynomiallyBounded_add polynomiallyBounded_id (polynomiallyBounded_constant 1))))

end NearCubicWires.WireExponent3_5.PrimAsm.CallSize
