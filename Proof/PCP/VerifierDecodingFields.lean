import Proof.Foundations.VerifierEncoding
import Proof.MachineModel.OrdinarySignedSortKey

/-! Literal decoding of the fixed-width fields in the frozen verifier code.
These are bounded list computations. Ordinary execution is attached at the
guarded enclosing decoder/lookup, rather than inferred from these functions. -/
namespace NearCubicWires.RepairSource.VerifierDecoding
open LocalBitMultitape VerifierEncoding RepairOrdinary.RadixSemantics
open RepairOrdinary.SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def unary : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false :: tail => some (0, tail)
  | true :: tail => (unary tail).map fun result => (result.1+1, result.2)

theorem unary_encoded (n : ℕ) (tail : List Bool) :
    unary (List.replicate n true ++ false :: tail) = some (n, tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, unary, ih]

theorem unary_bounded {word tail : List Bool} {n : ℕ}
    (h : unary word = some (n, tail)) : n + 1 + tail.length = word.length := by
  induction word generalizing n with
  | nil => simp [unary] at h
  | cons bit word ih =>
    cases bit with
    | false => simp only [unary, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl,rfl⟩ := h; simp; omega
    | true =>
      cases hu : unary word with
      | none => simp [unary, hu] at h
      | some result =>
        rcases result with ⟨count, rest⟩
        simp only [unary, hu, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hb := ih hu
        simp only [List.length_cons]
        omega

theorem fixedBits_binary (width n : ℕ) : fixedBits width n = binary width n := by
  induction width generalizing n with
  | zero => simp [fixedBits, binary]
  | succ width ih =>
    rw [fixedBits, List.ofFn_succ]
    simp only [Fin.val_zero, Fin.val_succ, Nat.testBit_succ]
    change n.testBit 0 :: fixedBits width (n / 2) = _
    rw [ih]
    by_cases h : n % 2 = 1 <;> simp [binary, Nat.testBit_eq_decide_div_mod_eq, h]

@[simp] theorem fixedBits_length (width n : ℕ) : (fixedBits width n).length = width := List.length_ofFn

theorem fixedBits_value (width n : ℕ) (hn : n < 2^width) :
    value (fixedBits width n) = n := by
  rw [fixedBits_binary]
  exact binary_value width n hn

def slice (word : List Bool) (offset width : ℕ) : List Bool := (word.drop offset).take width

theorem slice_flat {n width : ℕ} (fields : Fin n → List Bool)
    (hl : ∀ i, (fields i).length = width) (index : Fin n) :
    slice (List.ofFn fields).flatten (index.val*width) width = fields index := by
  induction n with
  | zero => exact Fin.elim0 index
  | succ n ih =>
    rw [List.ofFn_succ, List.flatten_cons]
    refine Fin.cases ?_ (fun i => ?_) index
    · simp [slice, ← hl 0]
    · have hd : ((fields 0 ++ (List.ofFn fun i => fields i.succ).flatten).drop
          ((i.val+1)*width)) =
          (List.ofFn fun i => fields i.succ).flatten.drop (i.val*width) := by
        rw [show (i.val+1)*width = (fields 0).length + i.val*width by rw [hl]; ring]
        rw [← List.drop_drop, List.drop_left]
      change ((fields 0 ++ (List.ofFn fun i => fields i.succ).flatten).drop
        ((i.val+1)*width)).take width = fields i.succ
      rw [hd]
      exact ih (fun j => fields j.succ) (fun j => hl j.succ) i

def decodeWrite : List Bool → Option Bool
  | true :: bit :: _ => some bit
  | _ => none

def decodeMove : List Bool → HeadMove
  | false :: false :: _ => .left
  | false :: true :: _ => .right
  | _ => .stay

@[simp] theorem decodeWrite_code (write : Option Bool) : decodeWrite (writeCode write) = write := by
  cases write with
  | none => rfl
  | some bit => cases bit <;> rfl

@[simp] theorem decodeMove_code (move : HeadMove) : decodeMove (moveCode move) = move := by
  cases move <;> rfl

@[simp] theorem writeCode_length (write : Option Bool) : (writeCode write).length = 2 := by
  cases write with
  | none => rfl
  | some bit => cases bit <;> rfl

@[simp] theorem moveCode_length (move : HeadMove) : (moveCode move).length = 2 := by
  cases move <;> rfl

def decodeAction {t s : ℕ} (width : ℕ) (word : List Bool) : Option (Action t s) :=
  if word.headD false then
    let next := value (slice word 1 width)
    if hn : next < s then
      let payload := word.drop (1+width)
      some { nextControl := ⟨next, hn⟩
             write := fun i => decodeWrite ((slice payload (i.val*4) 4).take 2)
             move := fun i => decodeMove ((slice payload (i.val*4) 4).drop 2) }
    else none
  else none

theorem decodeAction_code {t s : ℕ} (width : ℕ) (hs : s ≤ 2^width)
    (action : Option (Action t s)) : decodeAction width (actionCode width action) = action := by
  cases action with
  | none => simp [decodeAction, actionCode]
  | some action =>
    have hnext : value (slice (actionCode width (some action)) 1 width) = action.nextControl.val := by
      simp only [actionCode, slice, List.drop_succ_cons, List.drop_zero]
      have ht := List.take_left (l₁ := fixedBits width action.nextControl.val)
        (l₂ := (List.ofFn fun i : Fin t => writeCode (action.write i) ++ moveCode (action.move i)).flatten)
      simp only [fixedBits_length] at ht
      rw [ht]
      exact fixedBits_value width _ (action.nextControl.isLt.trans_le hs)
    have hpayload : (actionCode width (some action)).drop (1+width) =
        (List.ofFn fun i : Fin t => writeCode (action.write i) ++ moveCode (action.move i)).flatten := by
      simp only [actionCode, Nat.add_comm 1 width, List.drop_succ_cons]
      simpa only [fixedBits, List.length_ofFn] using
        (List.drop_left (l₁ := fixedBits width action.nextControl.val)
          (l₂ := (List.ofFn fun i : Fin t => writeCode (action.write i) ++ moveCode (action.move i)).flatten))
    have hchunk (i : Fin t) : slice ((actionCode width (some action)).drop (1+width)) (i.val*4) 4 =
        writeCode (action.write i) ++ moveCode (action.move i) := by
      rw [hpayload]
      exact slice_flat _ (by intro i; simp) i
    have hw : (fun i : Fin t => decodeWrite
        ((slice ((actionCode width (some action)).drop (1+width)) (i.val*4) 4).take 2)) = action.write := by
      funext i
      rw [hchunk]
      rw [← writeCode_length (action.write i), List.take_left]
      exact decodeWrite_code _
    have hm : (fun i : Fin t => decodeMove
        ((slice ((actionCode width (some action)).drop (1+width)) (i.val*4) 4).drop 2)) = action.move := by
      funext i
      rw [hchunk]
      rw [← writeCode_length (action.write i), List.drop_left]
      exact decodeMove_code _
    have hhead : (actionCode width (some action)).headD false = true := rfl
    have hb : value (slice (actionCode width (some action)) 1 width) < s := by
      rw [hnext]; exact action.nextControl.isLt
    have hnfin : (⟨value (slice (actionCode width (some action)) 1 width), hb⟩ : Fin s) =
        action.nextControl := Fin.ext hnext
    simp only [decodeAction, hhead, ↓reduceIte, dif_pos hb, Option.some.injEq]
    rw [hnfin, hw, hm]

end NearCubicWires.RepairSource.VerifierDecoding
