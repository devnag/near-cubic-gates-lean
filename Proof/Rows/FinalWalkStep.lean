import Proof.MachineModel.OrdinaryAdd
import Proof.Amplification.RecoveryTimedExecution
import Proof.Supplier.SupplierWalk

namespace NearCubicWires.RepairOrdinary.FinalWalkStep
open LocalBitMultitape RecoveryExecution RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## 1. Finite control

States `0..3` scan a frame marker, states `4..7` scan a bit; in both groups
bit `1` of the code is the running carry and bit `2` is the delayed passive
bit.  State `8` halts. -/

def markerState (buffered carry : Bool) : Fin 9 :=
  if buffered then (if carry then 3 else 2) else (if carry then 1 else 0)

def bitState (buffered carry : Bool) : Fin 9 :=
  if buffered then (if carry then 7 else 6) else (if carry then 5 else 4)

def bufferOf (q : Fin 9) : Bool := decide (2 ≤ q.val % 4)
def carryOf (q : Fin 9) : Bool := decide (q.val % 2 = 1)

@[simp] theorem bufferOf_marker (b c : Bool) : bufferOf (markerState b c) = b := by
  cases b <;> cases c <;> rfl
@[simp] theorem carryOf_marker (b c : Bool) : carryOf (markerState b c) = c := by
  cases b <;> cases c <;> rfl
@[simp] theorem bufferOf_bit (b c : Bool) : bufferOf (bitState b c) = b := by
  cases b <;> cases c <;> rfl
@[simp] theorem carryOf_bit (b c : Bool) : carryOf (bitState b c) = c := by
  cases b <;> cases c <;> rfl

def stepAction (next : Fin 9) (out : Bool) : Action 3 9 where
  nextControl := next
  write := fun i => if i.val = 2 then some out else none
  move := fun _ => .right

def haltAction (out : Bool) : Action 3 9 where
  nextControl := 8
  write := fun i => if i.val = 2 then some out else none
  move := fun i => if i.val = 2 then .right else .stay

/-- `invert` complements the delayed passive bit, `carryIn` is the initial
carry.  Both are constants of the transition table, not tape data. -/
def machine (invert carryIn : Bool) : Machine 3 9 where
  descriptionBits := 0
  start := markerState false carryIn
  halted := fun q => q.val == 8
  rule := fun q scanned =>
    if q.val < 4 then
      (if scanned 0 then some (stepAction (bitState (bufferOf q) (carryOf q)) true)
        else some (haltAction false))
    else if q.val < 8 then
      some (stepAction
        (markerState (scanned 1)
          (Add.carry (scanned 0) (xor invert (bufferOf q)) (carryOf q)))
        (Add.bit (scanned 0) (xor invert (bufferOf q)) (carryOf q)))
    else none

/-- Both input heads move in lockstep, so one position describes them both. -/
def config (q : Fin 9) (xs ys : List Bool) (pos : ℕ) (out : List Bool) :
    Configuration 3 9 := ⟨q, ![pos, pos, out.length], ![xs, ys, out]⟩

/-! ## 2. The three local transitions -/

theorem marker_step (invert carryIn b c : Bool) (xs ys out : List Bool) (pos : ℕ)
    (hx : readTapeBit xs pos = true) :
    step (machine invert carryIn) (config (markerState b c) xs ys pos out) =
      some (config (bitState b c) xs ys (pos + 1) (out ++ [true])) := by
  cases b <;> cases c <;>
    simp [step, machine, config, Configuration.scanned, hx, markerState, bitState,
      stepAction] <;>
    apply configuration_ext
  all_goals first
    | rfl
    | (funext i; fin_cases i <;>
        simp [applyAction, HeadMove.apply, Streaming.write_append])

theorem halt_step (invert carryIn b c : Bool) (xs ys out : List Bool) (pos : ℕ)
    (hx : readTapeBit xs pos = false) :
    step (machine invert carryIn) (config (markerState b c) xs ys pos out) =
      some (config 8 xs ys pos (out ++ [false])) := by
  cases b <;> cases c <;>
    simp [step, machine, config, Configuration.scanned, hx, markerState,
      haltAction] <;>
    apply configuration_ext
  all_goals first
    | rfl
    | (funext i; fin_cases i <;>
        simp [applyAction, HeadMove.apply, Streaming.write_append])

theorem bit_step (invert carryIn b c a e : Bool) (xs ys out : List Bool) (pos : ℕ)
    (hx : readTapeBit xs pos = a) (hy : readTapeBit ys pos = e) :
    step (machine invert carryIn) (config (bitState b c) xs ys pos out) =
      some (config (markerState e (Add.carry a (xor invert b) c)) xs ys (pos + 1)
        (out ++ [Add.bit a (xor invert b) c])) := by
  cases b <;> cases c <;>
    simp [step, machine, config, Configuration.scanned, hx, hy, markerState,
      bitState, bufferOf, carryOf, stepAction] <;>
    apply configuration_ext
  all_goals first
    | rfl
    | (funext i; fin_cases i <;>
        simp [applyAction, HeadMove.apply, Streaming.write_append])

/-! ## 3. The delayed (and optionally complemented) passive word -/

def shift (invert : Bool) : Bool → List Bool → List Bool
  | _, [] => []
  | prev, _ :: [] => [xor invert prev]
  | prev, e :: rest => xor invert prev :: shift invert e rest

@[simp] theorem shift_length (invert prev : Bool) (es : List Bool) :
    (shift invert prev es).length = es.length := by
  induction es generalizing prev with
  | nil => rfl
  | cons e es ih =>
    cases es with
    | nil => rfl
    | cons f fs => simpa [shift] using ih e

theorem shift_cons (invert prev e : Bool) (es : List Bool) :
    shift invert prev (e :: es) = xor invert prev :: shift invert e es := by
  cases es <;> rfl

theorem shift_not (prev : Bool) (es : List Bool) :
    shift true prev es = (shift false prev es).map (fun b => !b) := by
  induction es generalizing prev with
  | nil => rfl
  | cons e es ih => simp [shift_cons, ih]

theorem value_map_not (w : List Bool) :
    value (w.map (fun b => !b)) + value w + 1 = 2 ^ w.length := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b <;>
      simp only [List.map_cons, value, List.length_cons, pow_succ,
        Bool.not_true, Bool.not_false, Bool.toNat_true, Bool.toNat_false] at * <;>
      omega

theorem shift_modEq (prev : Bool) (es : List Bool) :
    value (shift false prev es) ≡ prev.toNat + 2 * value es [MOD 2 ^ es.length] := by
  induction es generalizing prev with
  | nil => exact Nat.modEq_one
  | cons e es ih =>
    have h2 : 2 * value (shift false e es) ≡ 2 * (e.toNat + 2 * value es)
        [MOD 2 * 2 ^ es.length] := Nat.ModEq.mul_left' 2 (ih e)
    have h3 := Nat.ModEq.add_left prev.toNat h2
    have hpow : 2 ^ (es.length + 1) = 2 * 2 ^ es.length := by ring
    simpa only [shift_cons, value, Bool.false_xor, List.length_cons, hpow,
      Nat.mul_add, Nat.add_assoc, Nat.mul_left_comm] using h3

/-! ## 4. One sweep -/

theorem sweep_timed (invert carryIn : Bool) :
    ∀ (xs ys : List Bool), xs.length = ys.length →
      ∀ (preX preY tailX tailY out : List Bool), preX.length = preY.length →
        ∀ b c : Bool,
          Timed (machine invert carryIn) (2 * xs.length + 1)
            (config (markerState b c) (preX ++ frame xs ++ tailX)
              (preY ++ frame ys ++ tailY) preX.length out)
            (config 8 (preX ++ frame xs ++ tailX) (preY ++ frame ys ++ tailY)
              (preX.length + 2 * xs.length)
              (out ++ frame (Add.sum xs (shift invert b ys) c))) := by
  intro xs
  induction xs with
  | nil =>
    intro ys hlen preX preY tailX tailY out _hpre b c
    have hys : ys = [] := List.length_eq_zero_iff.mp (by simpa using hlen.symm)
    subst hys
    have hread : readTapeBit (preX ++ frame ([] : List Bool) ++ tailX) preX.length = false := by
      simpa [frame, List.append_assoc] using Streaming.read_append preX tailX false
    have hstep := halt_step invert carryIn b c (preX ++ frame ([] : List Bool) ++ tailX)
      (preY ++ frame ([] : List Bool) ++ tailY) out preX.length hread
    have h := Timed.single (p := machine invert carryIn)
      (by cases b <;> cases c <;> rfl) hstep
    simpa [Add.sum, frame] using h
  | cons a xs ih =>
    intro ys hlen preX preY tailX tailY out hpre b c
    cases ys with
    | nil => simp at hlen
    | cons e ys =>
      have hlen' : xs.length = ys.length := by simpa using hlen
      have hX : preX ++ frame (a :: xs) ++ tailX =
          (preX ++ [true, a]) ++ frame xs ++ tailX := by
        simp [frame, List.append_assoc]
      have hY : preY ++ frame (e :: ys) ++ tailY =
          (preY ++ [true, e]) ++ frame ys ++ tailY := by
        simp [frame, List.append_assoc]
      have hreadMark : readTapeBit (preX ++ frame (a :: xs) ++ tailX) preX.length = true := by
        simpa [frame, List.append_assoc] using
          Streaming.read_append preX (a :: (frame xs ++ tailX)) true
      have hreadX : readTapeBit (preX ++ frame (a :: xs) ++ tailX) (preX.length + 1) = a := by
        have h := Streaming.read_append (preX ++ [true]) (frame xs ++ tailX) a
        simpa [frame, List.append_assoc] using h
      have hreadY : readTapeBit (preY ++ frame (e :: ys) ++ tailY) (preX.length + 1) = e := by
        have h := Streaming.read_append (preY ++ [true]) (frame ys ++ tailY) e
        simp only [List.length_append, List.length_cons, List.length_nil] at h
        rw [hpre]
        simpa [frame, List.append_assoc] using h
      have hfirst := marker_step invert carryIn b c (preX ++ frame (a :: xs) ++ tailX)
        (preY ++ frame (e :: ys) ++ tailY) out preX.length hreadMark
      have hsecond := bit_step invert carryIn b c a e (preX ++ frame (a :: xs) ++ tailX)
        (preY ++ frame (e :: ys) ++ tailY) (out ++ [true]) (preX.length + 1) hreadX hreadY
      have htail := ih ys hlen' (preX ++ [true, a]) (preY ++ [true, e]) tailX tailY
        (out ++ [true, Add.bit a (xor invert b) c]) (by simp [hpre]) e
        (Add.carry a (xor invert b) c)
      rw [← hX, ← hY] at htail
      have hplen : (preX ++ [true, a]).length = preX.length + 2 := by simp
      rw [hplen] at htail
      have hjoin := (Timed.single (p := machine invert carryIn)
          (by cases b <;> cases c <;> rfl) hfirst).trans
        ((Timed.single (p := machine invert carryIn)
          (by cases b <;> cases c <;> rfl) hsecond).trans
          (by simpa [List.append_assoc] using htail))
      have htime : 1 + (1 + (2 * xs.length + 1)) = 2 * (a :: xs).length + 1 := by
        simp; omega
      have hpos : preX.length + 2 + 2 * xs.length = preX.length + 2 * (a :: xs).length := by
        simp; omega
      rw [htime, hpos] at hjoin
      simpa [shift_cons, Add.sum, frame, List.append_assoc] using hjoin

theorem sweep_run (invert carryIn : Bool) (xs ys : List Bool) (hlen : xs.length = ys.length) :
    ∃ r : ExecutionReceipt 3 9,
      run (machine invert carryIn) (2 * xs.length + 1) ![frame xs, frame ys, []] = some r ∧
        r.steps = 2 * xs.length + 1 ∧
        r.final.tapes 0 = frame xs ∧ r.final.tapes 1 = frame ys ∧
        r.final.tapes 2 = frame (Add.sum xs (shift invert false ys) carryIn) := by
  have h := sweep_timed invert carryIn xs ys hlen [] [] [] [] [] rfl false carryIn
  simp only [List.nil_append, List.append_nil, List.length_nil, Nat.zero_add] at h
  obtain ⟨r, hr, hf, hs⟩ := h.run (by rfl)
  refine ⟨r, ?_, hs, ?_, ?_, ?_⟩
  · have hcfg : config (markerState false carryIn) (frame xs) (frame ys) 0 [] =
        initialConfiguration (machine invert carryIn) ![frame xs, frame ys, []] := by
      apply configuration_ext
      · rfl
      · funext i; fin_cases i <;> rfl
      · rfl
    rw [hcfg] at hr
    exact hr
  · rw [hf]; rfl
  · rw [hf]; rfl
  · rw [hf]; rfl

/-! ## 5. The encoding and its arithmetic -/

instance twoPowNeZero (r : ℕ) : NeZero (2 ^ r) := ⟨by positivity⟩

def coordEncode (r : ℕ) (a : ZMod (2 ^ r)) : List Bool := SignedSortKey.binary r a.val

def coordDecode (r : ℕ) (w : List Bool) : ZMod (2 ^ r) := (value w : ZMod (2 ^ r))

def unframe : List Bool → List Bool
  | [] => []
  | [_] => []
  | m :: b :: rest => if m then b :: unframe rest else []

@[simp] theorem unframe_frame (w : List Bool) : unframe (frame w) = w := by
  induction w with
  | nil => rfl
  | cons b w ih => simpa [frame, unframe] using ih

@[simp] theorem coordEncode_length (r : ℕ) (a : ZMod (2 ^ r)) :
    (coordEncode r a).length = r := by simp [coordEncode]

@[simp] theorem coordDecode_encode (r : ℕ) (a : ZMod (2 ^ r)) :
    coordDecode r (coordEncode r a) = a := by
  rw [coordDecode, coordEncode, SignedSortKey.binary_value _ _ (ZMod.val_lt a)]
  simp [ZMod.natCast_val, ZMod.cast_id]

/-- Truncating addition of two `r`-bit words is the residue sum. -/
theorem sum_eq_binary (r : ℕ) (L R : List Bool) (c : Bool)
    (hL : L.length = r) (hR : R.length = r) :
    Add.sum L R c = SignedSortKey.binary r ((value L + value R + c.toNat) % 2 ^ r) := by
  have hw : L.length = R.length := by rw [hL, hR]
  have hv := Add.sum_value L R c hw
  have hlt : value (Add.sum L R c) < 2 ^ r := by
    have h := value_lt (Add.sum L R c)
    rwa [Add.sum_length L R c hw, hL] at h
  have hmod : (value L + value R + c.toNat) % 2 ^ r = value (Add.sum L R c) := by
    rw [← hv, hL, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  rw [hmod]
  have he := BoundedCounter.binary_of_value (Add.sum L R c)
  rw [Add.sum_length L R c hw, hL] at he
  exact he.symm

theorem shift_cast (r : ℕ) (invert : Bool) (b : ZMod (2 ^ r)) :
    ((value (shift invert false (coordEncode r b)) : ℕ) : ZMod (2 ^ r)) =
      (if invert then -(2 * b) - 1 else 2 * b) := by
  have hval : value (coordEncode r b) = b.val := by
    rw [coordEncode, SignedSortKey.binary_value _ _ (ZMod.val_lt b)]
  have hlen : (coordEncode r b).length = r := by simp
  have hplain : ((value (shift false false (coordEncode r b)) : ℕ) : ZMod (2 ^ r)) = 2 * b := by
    have h := shift_modEq false (coordEncode r b)
    rw [hlen, hval] at h
    have hc : ((value (shift false false (coordEncode r b)) : ℕ) : ZMod (2 ^ r)) =
        ((false.toNat + 2 * b.val : ℕ) : ZMod (2 ^ r)) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
    rw [hc]
    push_cast
    simp [ZMod.natCast_val, ZMod.cast_id]
  cases invert with
  | false => simpa using hplain
  | true =>
    have hnot := value_map_not (shift false false (coordEncode r b))
    rw [shift_length, hlen] at hnot
    have hcast : ((value (shift true false (coordEncode r b)) : ℕ) : ZMod (2 ^ r)) +
        ((value (shift false false (coordEncode r b)) : ℕ) : ZMod (2 ^ r)) + 1 = 0 := by
      rw [shift_not]
      have h := congrArg (fun n : ℕ => ((n : ℕ) : ZMod (2 ^ r))) hnot
      simp only [Nat.cast_add, Nat.cast_one, ZMod.natCast_self] at h
      exact h
    rw [hplain] at hcast
    have hgoal : ((value (shift true false (coordEncode r b)) : ℕ) : ZMod (2 ^ r)) =
        -(2 * b) - 1 := by linear_combination hcast
    simpa using hgoal

theorem step_word (r : ℕ) (invert carryIn : Bool) (a b : ZMod (2 ^ r)) :
    Add.sum (coordEncode r a) (shift invert false (coordEncode r b)) carryIn =
      coordEncode r (a + (if invert then -(2 * b) - 1 else 2 * b) +
        (if carryIn then 1 else 0)) := by
  have hL : (coordEncode r a).length = r := by simp
  have hR : (shift invert false (coordEncode r b)).length = r := by
    rw [shift_length]; simp
  have hval : value (coordEncode r a) = a.val := by
    rw [coordEncode, SignedSortKey.binary_value _ _ (ZMod.val_lt a)]
  have hkey : ((a.val + value (shift invert false (coordEncode r b)) + carryIn.toNat : ℕ) :
      ZMod (2 ^ r)) =
      a + (if invert then -(2 * b) - 1 else 2 * b) + (if carryIn then 1 else 0) := by
    rw [Nat.cast_add, Nat.cast_add, shift_cast r invert b, ZMod.natCast_val, ZMod.cast_id]
    cases carryIn <;> simp
  rw [sum_eq_binary r _ _ carryIn hL hR, hval, ← hkey]
  unfold coordEncode
  rw [ZMod.val_natCast]

/-! ## 6. The eight Margulis labels -/

def labelInvert : Fin 8 → Bool := ![false, false, true, true, false, false, true, true]
def labelCarry : Fin 8 → Bool := ![false, true, true, false, false, true, true, false]

def active {r : ℕ} (label : Fin 8) (v : SourceInterfaces.MargulisVertex (2 ^ r)) :
    ZMod (2 ^ r) := if label.val < 4 then v.1 else v.2
def passive {r : ℕ} (label : Fin 8) (v : SourceInterfaces.MargulisVertex (2 ^ r)) :
    ZMod (2 ^ r) := if label.val < 4 then v.2 else v.1
def vertexOf {r : ℕ} (label : Fin 8) (p q : ZMod (2 ^ r)) :
    SourceInterfaces.MargulisVertex (2 ^ r) := if label.val < 4 then (p, q) else (q, p)

theorem vertexOf_active {r : ℕ} (label : Fin 8) (v : SourceInterfaces.MargulisVertex (2 ^ r)) :
    vertexOf label (active label v) (passive label v) = v := by
  unfold vertexOf active passive
  by_cases h : label.val < 4 <;> simp [h]

theorem active_neighbor {r : ℕ} (label : Fin 8) (v : SourceInterfaces.MargulisVertex (2 ^ r)) :
    active label (SourceInterfaces.margulisNeighbor label v) =
      active label v + (if labelInvert label then -(2 * passive label v) - 1
        else 2 * passive label v) + (if labelCarry label then 1 else 0) := by
  fin_cases label <;>
    simp [active, passive, labelInvert, labelCarry, SourceInterfaces.margulisNeighbor] <;> ring

theorem passive_neighbor {r : ℕ} (label : Fin 8) (v : SourceInterfaces.MargulisVertex (2 ^ r)) :
    passive label (SourceInterfaces.margulisNeighbor label v) = passive label v := by
  fin_cases label <;> simp [passive, SourceInterfaces.margulisNeighbor]

def loadTapes (r : ℕ) (label : Fin 8) (v : SourceInterfaces.MargulisVertex (2 ^ r)) :
    Fin 3 → List Bool :=
  ![frame (coordEncode r (active label v)), frame (coordEncode r (passive label v)), []]

/-- One ordinary `LocalBitMultitape` run applies `margulisNeighbor label` to an
encoded vertex of `ZMod (2^r) × ZMod (2^r)` in exactly `2 * r + 1` steps. -/
theorem walk_step_run (r : ℕ) (label : Fin 8) (v : SourceInterfaces.MargulisVertex (2 ^ r)) :
    ∃ rec : ExecutionReceipt 3 9,
      run (machine (labelInvert label) (labelCarry label)) (2 * r + 1)
          (loadTapes r label v) = some rec ∧
        rec.steps = 2 * r + 1 ∧
        rec.final.tapes 0 = frame (coordEncode r (active label v)) ∧
        rec.final.tapes 1 =
          frame (coordEncode r (passive label (SourceInterfaces.margulisNeighbor label v))) ∧
        rec.final.tapes 2 =
          frame (coordEncode r (active label (SourceInterfaces.margulisNeighbor label v))) := by
  obtain ⟨rec, hrun, hsteps, h0, h1, h2⟩ :=
    sweep_run (labelInvert label) (labelCarry label) (coordEncode r (active label v))
      (coordEncode r (passive label v)) (by simp)
  rw [coordEncode_length] at hrun hsteps
  refine ⟨rec, ?_, hsteps, h0, ?_, ?_⟩
  · exact hrun
  · rw [h1, passive_neighbor]
  · rw [h2, step_word, active_neighbor]

/-- The same run, read back through the decoder: the output word is the encoded
Margulis neighbour of the decoded input word. -/
theorem walk_step_decode (r : ℕ) (label : Fin 8) (v : SourceInterfaces.MargulisVertex (2 ^ r)) :
    vertexOf label (coordDecode r (unframe (loadTapes r label v 0)))
        (coordDecode r (unframe (loadTapes r label v 1))) = v ∧
      ∃ rec : ExecutionReceipt 3 9,
        run (machine (labelInvert label) (labelCarry label)) (2 * r + 1)
            (loadTapes r label v) = some rec ∧
          rec.steps = 2 * r + 1 ∧
          vertexOf label (coordDecode r (unframe (rec.final.tapes 2)))
              (coordDecode r (unframe (rec.final.tapes 1))) =
            SourceInterfaces.margulisNeighbor label v := by
  obtain ⟨rec, hrun, hsteps, _h0, h1, h2⟩ := walk_step_run r label v
  refine ⟨?_, rec, hrun, hsteps, ?_⟩
  · simp only [loadTapes, Matrix.cons_val_zero, Matrix.cons_val_one,
      unframe_frame, coordDecode_encode]
    exact vertexOf_active label v
  · rw [h1, h2, unframe_frame, unframe_frame, coordDecode_encode, coordDecode_encode]
    exact vertexOf_active label (SourceInterfaces.margulisNeighbor label v)

end NearCubicWires.RepairOrdinary.FinalWalkStep
