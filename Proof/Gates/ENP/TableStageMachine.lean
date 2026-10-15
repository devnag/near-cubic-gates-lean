import Proof.Gates.ENP.TableBackEnd
import Proof.Gates.ENP.TableSerializerPrep
import Proof.CaseAnalysis.RecoveryGraphBudget
import Proof.Hierarchy.HierarchyBinaryPower

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.ENP.TableSearch

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms NearCubicWires.Bindings.MW20
open NearCubicWires.RepairOrdinary.RecoveryRootRound

/-- The emitter's 45 tapes: `1664 …  1708`. -/
def emSlot (k : Fin (3 + 2 + 40)) : Fin (1664 + 53) := ⟨1664 + k.val, by have := k.isLt; omega⟩

/-- The preparation's 15 tapes: its marked-graph and info streams are the emitter's streams 1 and 3 (tapes 2, 4);
its output streams are the serializer's slots `20, 153, 25, 145` and the arity port `144`; cell and registers after
the emitter. -/
def prepVal (k : ℕ) : ℕ :=
  if k = 0 then 1666 else if k = 1 then 1709 else if k = 2 then 1668 else if k = 3 then 20
    else if k = 4 then 153 else if k = 5 then 144 else if k = 6 then 25 else if k = 7 then 145
    else 1702 + k

theorem prepVal_lt (k : ℕ) (hk : k < 15) : prepVal k < 1664 + 53 := by
  unfold prepVal
  split_ifs <;> omega

def prepSlot (k : Fin (6 + 2 + 7)) : Fin (1664 + 53) := ⟨prepVal k.val, prepVal_lt k.val k.isLt⟩

theorem emSlot_injective : Function.Injective emSlot := by
  intro a b h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [emSlot] at this
  omega

theorem prepVal_inj : ∀ a b : Fin 15, prepVal a.val = prepVal b.val → a = b := by decide

theorem prepSlot_injective : Function.Injective prepSlot := by
  intro a b h
  exact prepVal_inj a b (congrArg Fin.val h)

theorem prepVal_ge (k : ℕ) (h : 8 ≤ k) : prepVal k = 1702 + k := by
  unfold prepVal
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- The emitter's input tape. -/
def inPort0 : Fin (1664 + 53) := ⟨1664, by omega⟩

/-- The first machine's input bank: the word on `inPort0`, everything else blank. -/
def bankIn (w : List Bool) : Fin (1664 + 53) → List Bool := fun i => if i = inPort0 then w else []

/-- **The first machine**: builder T's emitter, then the preparation. -/
noncomputable def dockE (P : TProg) :=
  Composition.machine (RecoveryFocus.machine emSlot P.prog.compile)
    (RecoveryFocus.machine prepSlot (WMX.wm prepWM : WMX 6 7).compile)

/-! ## Cold banks -/

theorem coldBank_tStart (w : List Bool) (j : Fin (3 + 2 + 40)) :
    CheckedPCPP.coldBank (tStart w) j = if j.val = 0 then w else [] := by
  fin_cases j <;> rfl

theorem coldBank_stIn (g info : List Bool) (k : Fin (6 + 2 + 7)) :
    CheckedPCPP.coldBank (stIn g info) k =
      if k.val = 0 then Streaming.marks g else if k.val = 2 then info else [] := by
  fin_cases k <;> rfl

/-! ## The first machine's run -/

/-- The first machine's final low tapes (below `1664`): the raw graph on `20`, `1^n` on `153` and `144`, `1^o` on
`25`, `1^{o+1}` on `145`, all others blank. -/
def lowOut (g : List Bool) (n o : ℕ) (i : ℕ) : List Bool :=
  if i = 20 then g else if i = 153 then List.replicate n true else if i = 144 then List.replicate n true
    else if i = 25 then List.replicate o true else if i = 145 then List.replicate (o + 1) true else []

theorem not_emSlot (i : Fin (1664 + 53)) (hi : i.val < 1664) : ∀ k, emSlot k ≠ i := by
  intro k hk
  have := congrArg Fin.val hk
  simp only [emSlot] at this
  omega

set_option maxHeartbeats 1000000 in
/-- **The first machine** (builder T's emitter, then the preparation) halts, all heads at `0`, with `lowOut` on the
low tapes. -/
theorem dock_ready (P : TProg) {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) (post : List Bool) :
    ∃ n1 F, n1 ≤ P.K * (2 ^ ℓ + ((OracleOutput.word ⟨ℓ, C⟩) ++ post).length + 1) ^ P.e ∧
      ClockJoin.ReadyRun (dockE P)
        (n1 + 1 + prepCost (tGraph C).length (2 ^ ℓ) (TCirc.tCircuit C).output.val)
        (bankIn ((OracleOutput.word ⟨ℓ, C⟩) ++ post)) F ∧
      ∀ i : Fin (1664 + 53), i.val < 1664 →
        F i = lowOut (tGraph C) (2 ^ ℓ) (TCirc.tCircuit C).output.val i.val := by
  obtain ⟨cap, n1, junk, hn1, hx⟩ := P.run C post
  set w := (OracleOutput.word ⟨ℓ, C⟩) ++ post with hw
  set g := tGraph C with hg
  set o := (TCirc.tCircuit C).output.val with ho
  obtain ⟨out1, hr1, hs1⟩ := CheckedPCPP.WXExec.ready hx (fun _ => rfl) (fun _ => rfl) rfl (fun _ => rfl)
    (fun _ => rfl)
  have f1 := hr1.focus emSlot emSlot_injective (bankIn w) (by
    intro j
    rw [coldBank_tStart]
    simp only [bankIn, inPort0, emSlot, Fin.ext_iff]
    by_cases hj : j.val = 0
    · simp [hj]
    · rw [if_neg (by omega), if_neg hj])
  set mid := install emSlot (bankIn w) out1 with hmid
  have hm0 : mid (prepSlot 0) = Streaming.marks g := by
    have e : prepSlot 0 = emSlot ⟨2, by omega⟩ := Fin.ext rfl
    rw [e, hmid, install_slot _ emSlot_injective]
    exact hs1 1
  have hm2 : mid (prepSlot 2) = tInfo (2 ^ ℓ) o := by
    have e : prepSlot 2 = emSlot ⟨4, by omega⟩ := Fin.ext rfl
    rw [e, hmid, install_slot _ emSlot_injective]
    exact hs1 3
  have hmo : ∀ k : Fin (6 + 2 + 7), k.val ≠ 0 → k.val ≠ 2 → mid (prepSlot k) = [] := by
    intro k h0 h2
    rw [hmid, install_other]
    · simp only [bankIn, inPort0, Fin.ext_iff, prepSlot]
      have := k.isLt
      rw [if_neg]
      unfold prepVal
      split_ifs <;> omega
    · intro j hj
      have := congrArg Fin.val hj
      have hk := k.isLt
      simp only [emSlot, prepSlot] at this
      unfold prepVal at this
      split_ifs at this <;> omega
  have hpx := prep_exec g (2 ^ ℓ) o
  obtain ⟨out2, hr2, hs2⟩ := CheckedPCPP.WXExec.ready (WXExec.wm (P := prepWM) hpx) (fun _ => rfl) (fun _ => rfl)
    rfl (fun _ => rfl) (fun _ => rfl)
  have f2 := hr2.focus prepSlot prepSlot_injective mid (by
    intro k
    rw [coldBank_stIn]
    by_cases h0 : k.val = 0
    · have : k = 0 := Fin.ext h0
      subst this
      rw [hm0]; rfl
    · by_cases h2 : k.val = 2
      · have : k = 2 := Fin.ext h2
        subst this
        rw [hm2]; rfl
      · rw [hmo k h0 h2, if_neg h0, if_neg h2])
  have whole := ClockJoin.join _ _ _ _ _ _ _ f1 f2
  refine ⟨n1, install prepSlot mid out2, hn1, whole, ?_⟩
  intro i hi
  have hprep : ∀ k : Fin (6 + 2 + 7), prepSlot k = i → install prepSlot mid out2 i = out2 k := by
    intro k hk
    rw [← hk, install_slot _ prepSlot_injective]
  by_cases h20 : i.val = 20
  · rw [hprep 3 (Fin.ext (by rw [h20]; rfl)), show (3 : Fin (6 + 2 + 7)) = sTape 2 from rfl, hs2 2]
    simp [lowOut, h20, stFin]
  by_cases h153 : i.val = 153
  · rw [hprep 4 (Fin.ext (by rw [h153]; rfl)), show (4 : Fin (6 + 2 + 7)) = sTape 3 from rfl, hs2 3]
    simp [lowOut, h153, stFin]
  by_cases h144 : i.val = 144
  · rw [hprep 5 (Fin.ext (by rw [h144]; rfl)), show (5 : Fin (6 + 2 + 7)) = sTape 4 from rfl, hs2 4]
    simp [lowOut, h144, stFin]
  by_cases h25 : i.val = 25
  · rw [hprep 6 (Fin.ext (by rw [h25]; rfl)), show (6 : Fin (6 + 2 + 7)) = sTape 5 from rfl, hs2 5]
    simp [lowOut, h25, stFin]
  by_cases h145 : i.val = 145
  · rw [hprep 7 (Fin.ext (by rw [h145]; rfl)), show (7 : Fin (6 + 2 + 7)) = sTape 6 from rfl, hs2 6]
    simp [lowOut, h145, stFin]
  rw [install_other, hmid, install_other _ _ _ _ (not_emSlot i hi)]
  · simp only [bankIn, inPort0, Fin.ext_iff, lowOut]
    rw [if_neg (by omega), if_neg h20, if_neg h153, if_neg h144, if_neg h25, if_neg h145]
  · intro k hk
    have := congrArg Fin.val hk
    have hkl := k.isLt
    simp only [prepSlot] at this
    unfold prepVal at this
    split_ifs at this <;> omega

/-! ## The serializer entry -/

theorem output_succ {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) :
    (TCirc.tCircuit C).output.val + 1 = (TCirc.tCircuit C).nodes.length := by
  change (TCirc.nodes C).length - 1 + 1 = (TCirc.nodes C).length
  rw [TCirc.nodes_length]
  simp only [TCirc.base, TCirc.S]
  omega

theorem entry_of {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) (H : Fin (1664 + 53) → ℕ) (F : Fin (1664 + 53) → List Bool)
    (hH : ∀ i, H i = 0)
    (hF : ∀ i : Fin (1664 + 53), i.val < 1664 →
      F i = lowOut (tGraph C) (2 ^ ℓ) (TCirc.tCircuit C).output.val i.val) :
    Entry 53 (TCirc.tCircuit C) H F where
  heads := fun _ => hH _
  arityHead := hH _
  arity := by
    rw [hF _ (by simp [serSlot_val])]
    simp [lowOut, serSlot_val]
  tapes := by
    intro j
    rw [hF _ (by have := (RecoveryBoundedGraphSerialize.readySlots j).isLt; rw [serSlot_val]; omega), serSlot_val]
    refine Fin.addCases (m := 1506) (n := 1) (fun i => ?_) (fun i => ?_) j
    · rw [RecoveryBoundedGraphSerialize.ready_old]
      simp only [RecoveryBoundedGraphSerializeReady.input, Fin.addCases_left]
      rw [RecoveryBoundedGraphSerialize.padded_input]
      by_cases h0 : i = 0
      · subst h0
        simp [RecoveryBoundedGraphSerialize.serializerSlots, lowOut]
      by_cases h1 : i = 1062
      · subst h1
        simp [RecoveryBoundedGraphSerialize.serializerSlots, lowOut]
        rfl
      by_cases h2 : i = 1339
      · subst h2
        simp [RecoveryBoundedGraphSerialize.serializerSlots, lowOut]
      by_cases h3 : i = 1342
      · subst h3
        simp [RecoveryBoundedGraphSerialize.serializerSlots, lowOut, ZeroPadding.pad_zero, output_succ]
      have hv : i.val ≠ 0 := fun h => h0 (Fin.ext h)
      simp only [RecoveryBoundedGraphSerialize.serializerSlots, if_neg h0, if_neg h1, if_neg h2, if_neg h3,
        Fin.val_natAdd, lowOut]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    · have hi : i = 0 := Fin.eq_zero i
      subst hi
      simp only [RecoveryBoundedGraphSerializeReady.input, Fin.addCases_right]
      rfl

/-! ## Sizes -/

theorem len_le_flatMap {α : Type} (l : List α) (f : α → List Bool) (h : ∀ a, 1 ≤ (f a).length) :
    l.length ≤ (l.flatMap f).length := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.flatMap_cons, List.length_append, List.length_cons]; have := h a; omega

theorem natWord_pos (x : ℕ) : 1 ≤ (RepairRepresentation.natWord x).length := by
  unfold RepairRepresentation.natWord WilliamsPublishedForm.framedNatBits
  simp only [List.length_append, List.length_replicate, List.length_cons]
  omega

theorem nodeWord_pos {n a : ℕ} (nd : OracleNode n a) : 1 ≤ (oracleNodeWord nd).length := by
  cases nd <;> simp only [oracleNodeWord, List.length_append] <;> have := natWord_pos 0 <;>
    have := natWord_pos 1 <;> have := natWord_pos 2 <;> have := natWord_pos 3 <;> have := natWord_pos 4 <;>
    have := natWord_pos 5 <;> omega

/-- The oracle circuit's node count is at most its word's length. -/
theorem nodes_le_word {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) :
    C.nodes.length ≤ (OracleOutput.word ⟨ℓ, C⟩).length := by
  have h := len_le_flatMap C.nodes oracleNodeWord nodeWord_pos
  simp only [OracleOutput.word, List.length_append]
  omega

/-- **The size of `c_T`** (paper §11.6: the stage-2 formula has size `2^{2ℓ_out} q^{O(1)}`): with
`X ≥ 2^ℓ, |C|`, `c_T` has at most `8 X^4` nodes. -/
theorem tNodes_le {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) (X : ℕ) (hT : 2 ^ ℓ ≤ X) (hm : C.nodes.length ≤ X) :
    (TCirc.tCircuit C).nodes.length ≤ 8 * X ^ 4 := by
  change (TCirc.nodes C).length ≤ _
  rw [TCirc.nodes_length]
  simp only [TCirc.base, TCirc.S, TCirc.L, TCirc.K, TCirc.T]
  have hl : ℓ < 2 ^ ℓ := Nat.lt_two_pow_self
  have hX : 1 ≤ X := le_trans (Nat.one_le_two_pow) hT
  have hK : 2 ^ ℓ * (2 * ℓ + 1) ≤ 3 * X ^ 2 := by nlinarith
  have hmK : C.nodes.length * (2 ^ ℓ * (2 * ℓ + 1)) ≤ 3 * X ^ 3 := by
    calc C.nodes.length * (2 ^ ℓ * (2 * ℓ + 1)) ≤ X * (3 * X ^ 2) := Nat.mul_le_mul hm hK
      _ = 3 * X ^ 3 := by ring
  have hX3 : 1 ≤ X ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hL : 2 ^ ℓ * (C.nodes.length * (2 ^ ℓ * (2 * ℓ + 1)) + 2) ≤ X * (5 * X ^ 3) :=
    Nat.mul_le_mul hT (by omega)
  have hX4 : X ≤ X ^ 4 := Nat.le_self_pow (by omega) X
  have e : X * (5 * X ^ 3) = 5 * X ^ 4 := by ring
  omega

/-! ## The cost -/

theorem pow_mono_aux (X a b : ℕ) (hX : 1 ≤ X) (h : a ≤ b) : X ^ a ≤ X ^ b := Nat.pow_le_pow_right hX h
theorem pow_mul_aux (X a b : ℕ) : (X ^ a) ^ b = X ^ (a * b) := (pow_mul X a b).symm

/-- The stage's cost coefficient. -/
def dockK (P : TProg) : ℕ := P.K + (backCoefficient + 2000) * 9 ^ 144

/-- **The stage's cost** (paper §11.6: SAT formulas of size `2^{O(q)}`; here polynomial in `2^ℓ + |word ++ post|`). -/
theorem total_le (P : TProg) {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) (post : List Bool) (n1 : ℕ)
    (hn1 : n1 ≤ P.K * (2 ^ ℓ + ((OracleOutput.word ⟨ℓ, C⟩) ++ post).length + 1) ^ P.e) :
    cost (n1 + 1 + prepCost (tGraph C).length (2 ^ ℓ) (TCirc.tCircuit C).output.val) (TCirc.tCircuit C) ≤
      dockK P * (2 ^ ℓ + ((OracleOutput.word ⟨ℓ, C⟩) ++ post).length + 1) ^ (P.e + 576) := by
  have hm0 := nodes_le_word C
  have hlen : (OracleOutput.word ⟨ℓ, C⟩).length ≤ ((OracleOutput.word ⟨ℓ, C⟩) ++ post).length := by simp
  have hTpos : 1 ≤ 2 ^ ℓ := Nat.one_le_two_pow
  have hcost : ∀ fuel, cost fuel (TCirc.tCircuit C) = fuel + 1 + (RecoveryBoundedGraphSerializeReady.budget
      (TCirc.tCircuit C) + 2 + 1099511627776 * (RecoveryPrefixCold.radius (RecoveryFormulaPrefix.payload
        (CircuitInputCNF.circuitInputFormula (TCirc.tCircuit C))) (TCirc.T ℓ)) ^ 3) := by
    intro fuel; unfold cost; omega
  rw [hcost]
  generalize hXdef : 2 ^ ℓ + ((OracleOutput.word ⟨ℓ, C⟩) ++ post).length + 1 = X at hn1 ⊢
  have hX1 : 1 ≤ X := by omega
  have hT : 2 ^ ℓ ≤ X := by omega
  have hm : C.nodes.length ≤ X := by omega
  have hN := tNodes_le C X hT hm
  have hX4 : X ≤ X ^ 4 := Nat.le_self_pow (by omega) X
  generalize hW : 8 * X ^ 4 = W at hN
  have hTW : 2 ^ ℓ ≤ W := by omega
  have hback := back_le (TCirc.tCircuit C) W hTW hN
  have hg := RecoveryBoundedGraphBudget.graph_bound (TCirc.tCircuit C) W hTW hN
  change (tGraph C).length ≤ _ at hg
  have ho := output_succ C
  have hW1 : W + 1 ≤ 9 * X ^ 4 := by omega
  have hP144 : (W + 1) ^ 144 ≤ 9 ^ 144 * (X ^ 4) ^ 144 := by
    rw [← Nat.mul_pow]; exact Nat.pow_le_pow_left hW1 _
  have hX576 : (X ^ 4) ^ 144 ≤ X ^ (P.e + 576) :=
    le_trans (pow_mul_aux X 4 144).le (pow_mono_aux X (4 * 144) (P.e + 576) hX1 (by omega))
  have hsq : (W + 1) ^ 2 ≤ (W + 1) ^ 144 := Nat.pow_le_pow_right (by omega) (by omega)
  have hWsq : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have h1 : 1 ≤ (W + 1) ^ 144 := Nat.one_le_pow _ _ (by omega)
  have hprep : prepCost (tGraph C).length (2 ^ ℓ) (TCirc.tCircuit C).output.val + 2 ≤ 2000 * (W + 1) ^ 144 := by
    unfold prepCost
    have h2 : W * (6 * (W + W + 5) + 3) ≤ 33 * (W + 1) ^ 2 := by nlinarith
    omega
  have hXe : X ^ P.e ≤ X ^ (P.e + 576) := Nat.pow_le_pow_right hX1 (by omega)
  have hY1 : 1 ≤ X ^ (P.e + 576) := Nat.one_le_pow _ _ (by omega)
  have hN9 : 1 ≤ (9 : ℕ) ^ 144 := Nat.one_le_pow _ _ (by omega)
  unfold dockK
  generalize backCoefficient = bc at *
  generalize (W + 1) ^ 144 = Q at *
  generalize X ^ (P.e + 576) = Y at *
  generalize (X ^ 4) ^ 144 = Z at *
  generalize X ^ P.e = V at *
  generalize (9 : ℕ) ^ 144 = N at *
  generalize RecoveryBoundedGraphSerializeReady.budget (TCirc.tCircuit C) + 2 +
    1099511627776 * (RecoveryPrefixCold.radius (RecoveryFormulaPrefix.payload
      (CircuitInputCNF.circuitInputFormula (TCirc.tCircuit C))) (TCirc.T ℓ)) ^ 3 = B at *
  generalize prepCost (tGraph C).length (2 ^ ℓ) (TCirc.tCircuit C).output.val = R at *
  have k1 : P.K * V ≤ P.K * Y := Nat.mul_le_mul_left _ hXe
  have k2 : (bc + 2000) * Q ≤ (bc + 2000) * (N * Z) := Nat.mul_le_mul_left _ hP144
  have k3 : (bc + 2000) * (N * Z) ≤ (bc + 2000) * N * Y := by
    rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_left _ hX576
  have k4 : bc * Q + 2000 * Q = (bc + 2000) * Q := by ring
  have k5 : (P.K + (bc + 2000) * N) * Y = P.K * Y + (bc + 2000) * N * Y := by ring
  have k6 : 2000 ≤ (bc + 2000) * N * Y := by
    have : 2000 * 1 ≤ (bc + 2000) * N := Nat.mul_le_mul (by omega) hN9
    nlinarith
  have k7 : Q ≥ 1 := h1
  rw [k5]
  omega

/-! ## The stage -/

def inPortT : Fin (1664 + 53 + 790) := inPort0.castAdd 790

theorem bank_eq (w : List Bool) :
    (Fin.addCases (bankIn w) (fun _ => []) : Fin (1664 + 53 + 790) → List Bool) =
      fun i => if i = inPortT then w else [] := by
  funext i
  refine Fin.addCases (fun k => ?_) (fun k => ?_) i
  · rw [Fin.addCases_left]
    simp only [bankIn, inPortT, inPort0, Fin.ext_iff, Fin.val_castAdd]
  · rw [Fin.addCases_right]
    rw [if_neg]
    intro h
    have := congrArg Fin.val h
    simp only [inPortT, inPort0, Fin.val_castAdd, Fin.val_natAdd] at this
    omega

/-- **Stage 2 of the E^NP recovery** (paper §11.6: "a formula with one variable per oracle address and the constraints
`C^O_{⟨B*_src⟩_ν}(R) = 0` for all `2^{ℓ_out}` inputs `R` … finds the first oracle `O*`"), from builder T's emitter. -/
noncomputable def tStage (P : TProg) : TStage where
  program := program (dockE P)
  inPort := inPortT
  inQuery := by
    intro h
    have h2 : inPortT.val = (queryPort 53).val := congrArg Fin.val (h.trans (program_queryTape _))
    simp [inPortT, inPort0, queryPort] at h2
  flagPort := flagPort 53
  tablePort := tablePort 53
  tableQuery := by
    intro h
    have := congrArg Fin.val h
    rw [program_queryTape] at this
    simp [queryPort, tablePort] at this
  K := dockK P
  e := P.e + 576
  run := by
    intro o post
    obtain ⟨ℓ, C⟩ := o
    obtain ⟨n1, F, hn1, ⟨r, hr, hrt, hrh, hrs⟩, hF⟩ := dock_ready P C post
    obtain ⟨c', hc', final, trace, halt, flag, table, hfh, hth, qlen, qhead⟩ :=
      run (dockE P) _ _ r hr C (entry_of C _ _ hrh (by rw [hrt]; exact hF))
    refine ⟨c', hc'.trans (total_le P C post n1 hn1), final, ?_, halt, flag, table, hfh, hth, ?_, ?_⟩
    · rw [← bank_eq]; exact trace
    · rw [program_queryTape]; exact qlen
    · rw [program_queryTape]; exact qhead

theorem tStageOf : TStageOf := fun ⟨P⟩ _ _ => ⟨tStage P⟩

end NearCubicGates.Close.ENP.TableSearch
