import Proof.Gates.Worker.Sound
import Proof.Gates.Counter.Main

set_option autoImplicit false

namespace NearCubicGates.Close.Worker

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairOrdinary
open NearCubicWires.Bindings.CLW20Lemma311 NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close.Interfaces NearCubicGates NearCubicGates.FiniteAverages NearCubicGates.Gadget

/-! ## Means of bits on the cube -/

theorem bit_real (b : Bool) : (bit b : ℝ) = if b then 1 else 0 := by cases b <;> simp [bit]

theorem mean_bit {q : ℕ} (f : BitInput q → Bool) :
    mean (fun z => (bit (f z) : ℝ)) = ((Finset.univ.filter fun z => f z = true).card : ℝ) / 2 ^ q := by
  classical
  unfold mean
  simp only [bit_real]
  rw [Finset.sum_boole]
  simp

theorem prob_eq_mean (c : Call) : (c.prob : ℝ) = mean (fun z => (bit (c.predicate z) : ℝ)) := by
  rw [mean_bit]
  unfold Call.prob
  push_cast
  rfl

theorem mean_bit_bounds {q : ℕ} (f : BitInput q → Bool) :
    0 ≤ mean (fun z => (bit (f z) : ℝ)) ∧ mean (fun z => (bit (f z) : ℝ)) ≤ 1 := by
  constructor
  · have h := mean_le_mean (fun _ : BitInput q => (0 : ℝ)) (fun z => (bit (f z) : ℝ))
      (fun z => by rw [bit_real]; split_ifs <;> norm_num)
    simpa using h
  · have h := mean_le_mean (fun z => (bit (f z) : ℝ)) (fun _ : BitInput q => (1 : ℝ))
      (fun z => by rw [bit_real]; split_ifs <;> norm_num)
    simpa using h

theorem mean_bit_xor {q : ℕ} (fl : Bool) (f : BitInput q → Bool) :
    mean (fun z => (bit (xor fl (f z)) : ℝ)) =
      if fl = true then 1 - mean (fun z => (bit (f z) : ℝ)) else mean (fun z => (bit (f z) : ℝ)) := by
  cases fl
  · simp
  · have hpt : ∀ z, (bit (xor true (f z)) : ℝ) = 1 + (-1) * (bit (f z) : ℝ) := by
      intro z; cases f z <;> simp [bit]
    simp only [hpt, if_true]
    rw [mean_add, mean_smul, mean_const]
    ring

/-- A flip complements a sound interval. -/
theorem flip_sound (fl : Bool) (X : ℚ × ℚ) (m : ℝ) (h : |(X.1 : ℝ) - m| ≤ (X.2 : ℝ)) :
    |(((if fl = true then (1 - X.1, X.2) else X) : ℚ × ℚ).1 : ℝ) - (if fl = true then 1 - m else m)| ≤
      (((if fl = true then (1 - X.1, X.2) else X) : ℚ × ℚ).2 : ℝ) := by
  cases fl
  · simpa using h
  · simp only [if_true]
    push_cast
    rw [show (1 : ℝ) - (X.1 : ℝ) - (1 - m) = -((X.1 : ℝ) - m) by ring, abs_neg]
    exact h

/-! ## Parities -/

theorem parityOn_eq_foldl {q : ℕ} (S : Finset (Fin q)) (z : BitInput q) :
    parityOn S z = (S.toList.map z).foldl xor false := by
  unfold parityOn
  rw [List.foldl_map]

theorem parityOn_empty {q : ℕ} (z : BitInput q) : parityOn (∅ : Finset (Fin q)) z = false := by
  simp [parityOn]

theorem parityOn_singleton {q : ℕ} (i : Fin q) (z : BitInput q) : parityOn {i} z = z i := by
  simp [parityOn, Finset.toList_singleton]

theorem parityOn_eq_card {q : ℕ} (S : Finset (Fin q)) (z : BitInput q) :
    parityOn S z = decide ((S.filter fun i => z i = true).card % 2 = 1) := by
  classical
  rw [parityOn_eq_foldl, Counter.foldl_xor_count, Counter.count_true_map]
  have h : S.toList.countP z = (S.filter fun i => z i = true).card := by
    rw [Finset.card_def, Finset.filter_val, ← Multiset.countP_eq_card_filter, ← Finset.coe_toList S,
      Multiset.coe_countP]
    simp
  rw [h]

theorem parityOn_symmDiff {q : ℕ} (S T : Finset (Fin q)) (z : BitInput q) :
    xor (parityOn S z) (parityOn T z) = parityOn (symmDiff S T) z := by
  classical
  rw [parityOn_eq_card, parityOn_eq_card, parityOn_eq_card]
  have hf : (symmDiff S T).filter (fun i => z i = true) =
      symmDiff (S.filter fun i => z i = true) (T.filter fun i => z i = true) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_symmDiff]
    tauto
  rw [hf]
  set A := S.filter fun i => z i = true
  set B := T.filter fun i => z i = true
  have hcard : (symmDiff A B).card + 2 * (A ∩ B).card = A.card + B.card := by
    rw [Finset.symmDiff_def, Finset.card_union_of_disjoint disjoint_sdiff_sdiff]
    have h1 := Finset.card_sdiff_add_card_inter A B
    have h2 := Finset.card_sdiff_add_card_inter B A
    rw [Finset.inter_comm] at h2
    omega
  have hc : (symmDiff A B).card % 2 = (A.card % 2 + B.card % 2) % 2 := by omega
  rw [hc]
  rcases Nat.mod_two_eq_zero_or_one A.card with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one B.card with hb | hb <;> simp [ha, hb]

theorem parityOf_canon {q : ℕ} (k : CallKind) (C₁ C₂ : NCircuit q) (ρ : ℚ) (S : Finset (Fin q))
    (z : BitInput q) : Call.parityOf ⟨q, k, C₁, C₂, (canonList S).map Fin.val, ρ⟩ z = parityOn S z := by
  unfold Call.parityOf
  rw [parityOn_canon, ← List.foldl_map (f := z), List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp [i.isLt]

/-- The pure parity call on `S`. -/
def parityCall (q : ℕ) (S : Finset (Fin q)) : Call :=
  ⟨q, .parity, NCircuit.empty q, NCircuit.empty q, (canonList S).map Fin.val, 0⟩

theorem mean_parityOn {q : ℕ} (S : Finset (Fin q)) :
    mean (fun z => (bit (parityOn S z) : ℝ)) = ((parityMean S : ℚ) : ℝ) := by
  classical
  unfold parityMean
  by_cases hS : S.Nonempty
  · rw [if_pos hS]
    obtain ⟨i0, hi0⟩ := hS
    have hcount : (parityCall q S).parity.count i0.val % 2 = 1 := by
      have hnd : ((canonList S).map Fin.val).Nodup := (canonList_nodup S).map Fin.val_injective
      have hmem : i0.val ∈ (canonList S).map Fin.val := List.mem_map.2 ⟨i0, (mem_canonList S i0).2 hi0, rfl⟩
      simp [parityCall, List.count_eq_one_of_mem hnd hmem]
    have hh := Counter.parity_half (parityCall q S) i0 hcount true
    have hpar : ∀ z : BitInput q, (parityCall q S).parityOf z = parityOn S z := fun z =>
      parityOf_canon _ _ _ _ S z
    simp only [hpar] at hh
    have hh' : ((Finset.univ.filter fun z : BitInput q => parityOn S z = true).card : ℚ) = 2 ^ q / 2 := hh
    rw [mean_bit]
    have hr : ((Finset.univ.filter fun z : BitInput q => parityOn S z = true).card : ℝ) = 2 ^ q / 2 := by
      have hc := congrArg (fun t : ℚ => (t : ℝ)) hh'
      push_cast at hc
      exact hc
    rw [hr]
    push_cast
    field_simp
  · rw [if_neg hS, Finset.not_nonempty_iff_eq_empty.1 hS]
    simp [parityOn_empty, bit]

/-! ## Counter calls -/

theorem call_sound {B1 B2 : ℕ} (ctr : Counter B1 B2) (c : Call) (w : List Bool) (f : BitInput c.n → Bool)
    (hf : ∀ z, f z = c.predicate z) :
    |((ctr.value c w).1 : ℝ) - mean (fun z => (bit (f z) : ℝ))| ≤ ((ctr.value c w).2 : ℝ) := by
  have h := ctr.sound c w
  have hm : mean (fun z => (bit (f z) : ℝ)) = (c.prob : ℝ) := by
    rw [prob_eq_mean]
    simp only [hf]
  rw [hm]
  exact_mod_cast h

theorem sysEnc_apply_lt (E : LinearCodeFamily) (q : ℕ) (r : BitInput q) (i : Fin (q + E.length q))
    (h : i.val < q) : sysEnc E q r i = r ⟨i.val, h⟩ := by
  obtain ⟨k, hk⟩ := i
  show sysEnc E q r (Fin.castAdd (E.length q) ⟨k, h⟩) = _
  rw [sysEnc, Fin.addCases_left]

theorem sysEnc_apply_ge (E : LinearCodeFamily) (q : ℕ) (r : BitInput q) (i : Fin (q + E.length q))
    (h : q ≤ i.val) : sysEnc E q r i = E.enc q r ⟨i.val - q, by omega⟩ := by
  obtain ⟨k, hk⟩ := i
  simp only at h ⊢
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  show sysEnc E q r (Fin.natAdd q ⟨m, by omega⟩) = _
  rw [sysEnc, Fin.addCases_right]
  congr 1
  ext
  simp

/-! ## Terms as XORs of operands -/

namespace Guess
variable {s : GateSources} {g : GateParams} (P : ThreeQueryPCPP) {N : ℕ} (x : BitInput N)
  (G : Guess (width s g N))

/-- The value at `r` of the XOR of (flip, atom) operands. -/
noncomputable def opsValue (r : BitInput (width s g N)) (ops : List (Bool × Atom)) : Bool :=
  ops.foldl (fun b o => xor b (xor o.1 (G.atomValue P x r o.2))) false

/-- The value at `r` of the XOR of atoms. -/
noncomputable def atomsXor (r : BitInput (width s g N)) (as : List Atom) : Bool :=
  as.foldl (fun b a => xor b (G.atomValue P x r a)) false

theorem foldl_split (v : Atom → Bool) (ops : List (Bool × Atom)) (a₁ a₂ : Bool) :
    ops.foldl (fun b o => xor b (xor o.1 (v o.2))) (xor a₁ a₂) =
      xor (ops.foldl (fun f o => xor f o.1) a₁) ((ops.map Prod.snd).foldl (fun b a => xor b (v a)) a₂) := by
  induction ops generalizing a₁ a₂ with
  | nil => rfl
  | cons o os ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [← ih]
    congr 1
    generalize o.1 = p
    generalize v o.2 = e
    revert a₁ a₂ p e
    decide

theorem opsValue_split (r : BitInput (width s g N)) (ops : List (Bool × Atom)) :
    G.opsValue P x r ops = xor (ops.foldl (fun f o => xor f o.1) false) (G.atomsXor P x r (ops.map Prod.snd)) := by
  unfold opsValue atomsXor
  rw [← foldl_split]
  rfl

theorem atomValue_sys (r : BitInput (width s g N)) (u : ℕ) :
    G.atomValue P x r (.sys u) = parityOn (G.sysSupport P x u) r := by
  show (if h : u < sysCount s P g x G.oracle then sysEnc P.code (substituted s g x G.oracle).n r ⟨u, h⟩
    else false) = _
  unfold sysSupport
  by_cases h1 : u < width s g N
  · have hu : u < sysCount s P g x G.oracle := Nat.lt_add_right _ h1
    simp only [dif_pos hu, dif_pos h1, parityOn_singleton]
    exact sysEnc_apply_lt P.code _ r ⟨u, hu⟩ h1
  · by_cases h2 : u - width s g N < P.code.length (substituted s g x G.oracle).n
    · have hu : u < sysCount s P g x G.oracle := by
        have : u < width s g N + P.code.length (substituted s g x G.oracle).n := by omega
        exact this
      simp only [dif_pos hu, dif_neg h1, dif_pos h2]
      exact sysEnc_apply_ge P.code _ r ⟨u, hu⟩ (Nat.le_of_not_lt h1)
    · have hu : ¬ u < sysCount s P g x G.oracle := by
        intro hu
        have : u < width s g N + P.code.length (substituted s g x G.oracle).n := hu
        omega
      simp only [dif_neg hu, dif_neg h1, dif_neg h2, parityOn_empty]

theorem atomValue_aux (r : BitInput (width s g N)) (j : ℕ) : G.atomValue P x r (.aux j) = (G.circuits j).eval r :=
  rfl

theorem term_eq (a : Fin (gadgets s g N)) (t : Fin 10) (r : BitInput (width s g N)) :
    (G.family P x).term a t r = G.opsValue P x r (G.operands P x a.val t) := by
  unfold GadgetFamily.term family opsValue operands
  dsimp only
  generalize G.literalParts P x (G.clause P x a.val 0) = l₀
  generalize G.literalParts P x (G.clause P x a.val 1) = l₁
  generalize G.literalParts P x (G.clause P x a.val 2) = l₂
  generalize G.helper P x a.val = hA
  generalize G.atomValue P x r = v
  fin_cases t <;> simp [tenTerms]

theorem singleCall_pos (ω : ℚ) (j : ℕ) (S : Finset (Fin (width s g N))) (hS : S.Nonempty) :
    G.singleCall ω j S = ⟨width s g N, .parity, G.circuits j, NCircuit.empty _, (canonList S).map Fin.val, ω⟩ :=
  if_pos hS

theorem singleCall_neg (ω : ℚ) (j : ℕ) (S : Finset (Fin (width s g N))) (hS : ¬ S.Nonempty) :
    G.singleCall ω j S = ⟨width s g N, .single, G.circuits j, NCircuit.empty _, [], ω⟩ :=
  if_neg hS

/-- A circuit XORed with a parity (either order): one single or parity call. -/
theorem circuitParity_sound {B1 B2 : ℕ} (ctr : Counter B1 B2) (ω : ℚ) (w : List Bool) (j : ℕ)
    (S : Finset (Fin (width s g N))) (f : BitInput (width s g N) → Bool)
    (hf : ∀ r, f r = xor ((G.circuits j).eval r) (parityOn S r)) :
    |((ctr.value (G.singleCall ω j S) w).1 : ℝ) - mean (fun r => (bit (f r) : ℝ))| ≤
      ((ctr.value (G.singleCall ω j S) w).2 : ℝ) := by
  by_cases hS : S.Nonempty
  · rw [G.singleCall_pos ω j S hS]
    exact call_sound ctr ⟨width s g N, .parity, G.circuits j, NCircuit.empty _, (canonList S).map Fin.val, ω⟩ w f
      (fun r => by
      rw [hf r]; simp only [Call.predicate]; rw [parityOf_canon])
  · rw [G.singleCall_neg ω j S hS]
    rw [Finset.not_nonempty_iff_eq_empty.1 hS] at hf
    exact call_sound ctr ⟨width s g N, .single, G.circuits j, NCircuit.empty _, [], ω⟩ w f
      (fun r => by rw [hf r, parityOn_empty]; simp [Call.predicate])

theorem exact_sound (v : ℚ) (f : BitInput (width s g N) → Bool) (hv : mean (fun r => (bit (f r) : ℝ)) = v) :
    |(((v, (0 : ℚ)) : ℚ × ℚ).1 : ℝ) - mean (fun r => (bit (f r) : ℝ))| ≤ (((v, (0 : ℚ)) : ℚ × ℚ).2 : ℝ) := by
  rw [hv]; simp

/-- Every interval of an operand list contains the mean of its XOR. -/
theorem intervalOf_sound {B1 B2 : ℕ} (ctr : Counter B1 B2) (ω : ℚ) (w : List Bool) (ops : List (Bool × Atom)) :
    |((G.intervalOf P x ctr ω w ops).1 : ℝ) - mean (fun r => (bit (G.opsValue P x r ops) : ℝ))| ≤
      ((G.intervalOf P x ctr ω w ops).2 : ℝ) := by
  classical
  simp only [G.opsValue_split P x]
  rw [mean_bit_xor]
  unfold intervalOf
  dsimp only
  generalize ops.foldl (fun f o => xor f o.1) false = fl
  generalize ops.map Prod.snd = as
  have hdef : ∀ m : ℝ, 0 ≤ m → m ≤ 1 → |(((0 : ℚ) : ℝ)) - (if fl = true then 1 - m else m)| ≤ ((1 : ℚ) : ℝ) := by
    intro m h0 h1
    split_ifs <;> rw [abs_le] <;> constructor <;> push_cast <;> linarith
  have hb := mean_bit_bounds (fun r => G.atomsXor P x r as)
  rcases as with _ | ⟨a₁, _ | ⟨a₂, _ | ⟨a₃, rest⟩⟩⟩
  · exact hdef _ hb.1 hb.2
  · cases a₁ with
    | sys u =>
      apply flip_sound
      apply exact_sound
      rw [← mean_parityOn]
      congr 1; funext r
      simp [atomsXor, atomValue_sys]
    | aux j =>
      apply flip_sound
      apply G.circuitParity_sound ctr ω w j ∅
      intro r; simp [atomsXor, atomValue_aux, parityOn_empty]
  · cases a₁ with
    | sys u =>
      cases a₂ with
      | sys v =>
        apply flip_sound
        apply exact_sound
        rw [← mean_parityOn]
        congr 1; funext r
        simp only [atomsXor, List.foldl_cons, List.foldl_nil, Bool.false_xor, atomValue_sys]
        rw [parityOn_symmDiff]
      | aux j =>
        apply flip_sound
        apply G.circuitParity_sound ctr ω w j
        intro r
        simp only [atomsXor, List.foldl_cons, List.foldl_nil, Bool.false_xor, atomValue_sys, atomValue_aux]
        exact Bool.xor_comm _ _
    | aux i =>
      cases a₂ with
      | sys u =>
        apply flip_sound
        apply G.circuitParity_sound ctr ω w i
        intro r
        simp only [atomsXor, List.foldl_cons, List.foldl_nil, Bool.false_xor, atomValue_sys, atomValue_aux]
      | aux j =>
        dsimp only
        by_cases hij : i = j
        · rw [if_pos hij]
          apply flip_sound
          apply exact_sound
          subst hij
          simp [atomsXor, bit]
        · rw [if_neg hij]
          apply flip_sound
          exact call_sound ctr (G.pairCall ω i j) w (fun r => G.atomsXor P x r [.aux i, .aux j]) (fun r => by
            simp only [atomsXor, List.foldl_cons, List.foldl_nil, Bool.false_xor, atomValue_aux, pairCall,
              Call.predicate])
  · cases a₁ <;> cases a₂ <;> exact hdef _ hb.1 hb.2

/-- **Interval soundness** (v2 lines 2216–2228): every term interval of every guess contains its term's mean. -/
theorem termInterval_sound {B1 B2 : ℕ} (ctr : Counter B1 B2) (ω : ℚ) :
    Sound (G.family P x) (fun (a : Fin (gadgets s g N)) (t : Fin 10) => G.termInterval P x ctr ω a.val t) := by
  intro a t
  unfold GadgetFamily.termMean
  simp only [G.term_eq P x a t]
  exact G.intervalOf_sound P x ctr ω (G.witnesses a.val t) (G.operands P x a.val t)

end Guess

theorem meaning_sound {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams} {B1 B2 : ℕ}
    (ctr : Counter B1 B2) (budget : ℕ → ℕ) (ε : ℝ) (ω : ℚ)
    (N : ℕ) (x : BitInput N) (G : Guess (width s g N)) (h : G.Certified P x ctr budget ε ω) :
    (s.hierarchy (fun n => n ^ (g.k + 2)) g.clock).hierarchy.timedView.accepts N x = true :=
  meaning_oneSided ctr budget ε ω N x G (G.termInterval_sound P x ctr ω) h

end NearCubicGates.Close.Worker
