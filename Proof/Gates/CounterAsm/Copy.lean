import Proof.Gates.Recovery.HTParts4
import Proof.Gates.Codec.FieldInt
import Proof.Gates.Codec.PairFrame

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.CounterAsm

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Recovery.HTParts
open NearCubicGates.Close.CheckedPCPP.LitDecode (rtb_off rtb_off0)

variable {ns nr : ℕ} (cap : ℕ)

/-! ## The shape of a natural word -/

theorem nbl_pos (v : ℕ) : 1 ≤ natBitLength v := by unfold natBitLength; omega

theorem natWord_shape (v : ℕ) : natWord v = List.replicate (natBitLength v) true ++
    false :: NearCubicWires.WilliamsPublishedForm.fixedWidthNatBits (natBitLength v) v := rfl

theorem fixedWidth_length (m v : ℕ) : (NearCubicWires.WilliamsPublishedForm.fixedWidthNatBits m v).length = m := by simp [NearCubicWires.WilliamsPublishedForm.fixedWidthNatBits]

theorem natWord_len (v : ℕ) : (natWord v).length = 2 * natBitLength v + 1 := by
  rw [natWord_shape]; simp [fixedWidth_length]; omega

theorem natWord_head (v : ℕ) (rest : List Bool) : (natWord v ++ rest).headD false = true := by
  rw [natWord_shape]
  obtain ⟨m, hm⟩ : ∃ m, natBitLength v = m + 1 := ⟨natBitLength v - 1, by have := nbl_pos v; omega⟩
  rw [hm]; simp [List.replicate_succ]

theorem natWord_cons (v : ℕ) : ∃ t, natWord v = true :: t := by
  rw [natWord_shape]
  obtain ⟨m, hm⟩ : ∃ m, natBitLength v = m + 1 := ⟨natBitLength v - 1, by have := nbl_pos v; omega⟩
  rw [hm]
  exact ⟨List.replicate m true ++ false :: NearCubicWires.WilliamsPublishedForm.fixedWidthNatBits (m + 1) v,
    by rw [List.replicate_succ]; rfl⟩

theorem frame_cons {x : List Bool} (hx : x ≠ []) : ∃ t, RepairOrdinary.frame x = true :: t := by
  obtain ⟨b, x', rfl⟩ := List.exists_cons_of_ne_nil hx
  exact ⟨b :: RepairOrdinary.frame x', by simp [RepairOrdinary.frame]⟩

theorem frame_head {x : List Bool} (hx : x ≠ []) (rest : List Bool) : (RepairOrdinary.frame x ++ rest).headD false = true := by
  obtain ⟨b, x', rfl⟩ := List.exists_cons_of_ne_nil hx
  simp [RepairOrdinary.frame]

section Loops
variable {src dst : Fin (ns + 1)} {OP SC : Fin nr}

/-- A unary run `1^R`, counted in `K`. -/
def unaryK (src : Fin (ns + 1)) (SC K : Fin nr) (E : Bool → WM ns nr) : WM ns nr :=
  .whs src (.seq (cellE src SC E) (.inc K))

theorem unaryK_spec (hsd : src ≠ dst) (hOS : OP ≠ SC) {K : Fin nr} (hKO : K ≠ OP) (hKS : K ≠ SC)
    {e : Bool → List Bool} {E : Bool → WM ns nr} {c : ℕ}
    (hE : Emits cap dst OP e E c) (rest : List Bool) (hrest : rest.headD false = false) :
    ∀ (R : ℕ) (pre : List Bool) (σ : WState ns nr), σ.st src = pre ++ List.replicate R true ++ rest →
      σ.sh src = pre.length → σ.sh dst = (σ.st dst).length → σ.val OP + R * (e true).length ≤ cap →
      σ.val SC + R < cap + 1 → σ.val K + R < cap + 1 →
      WExec cap (unaryK src SC K E) σ
        ((adv src dst OP SC σ ((List.replicate R true).flatMap e) R).setv K (σ.val K + R)) (R * (c + 13) + 1)
  | 0, pre, σ, hst, hsh, _, _, _, _ => by
    simp only [List.replicate_zero, List.flatMap_nil, adv_zero, Nat.zero_mul, Nat.zero_add, Nat.add_zero, wsetv_same]
    refine WExec.whsF ?_
    unfold wbit; rw [hst, hsh]; simp [rtb_off0]
    cases rest with
    | nil => rfl
    | cons a r => simp at hrest; subst hrest; rfl
  | R + 1, pre, σ, hst, hsh, hd, hOc, hSc, hKc => by
    have hst' : σ.st src = pre ++ (true :: (List.replicate R true ++ rest)) := by
      rw [hst]; simp [List.replicate_succ]
    have hw : wbit σ src = true := by unfold wbit; rw [hst', hsh, rtb_off0]; rfl
    have hm : readTapeBit (σ.st src) (σ.sh src) = true := by rw [hst', hsh, rtb_off0]; rfl
    have x1 := cellE_spec cap hsd hOS hE σ hd (by rw [hm]; nlinarith) (by omega)
    rw [hm] at x1
    set σ1 := adv src dst OP SC σ (e true) 1 with hσ1
    have x2 := WExec.inc (cap := cap) K σ1 (by rw [hσ1, adv_val_other _ _ _ K hKO hKS]; omega)
    set σ2 := σ1.setv K (σ1.val K + 1) with hσ2
    have hK1 : σ1.val K = σ.val K := by rw [hσ1, adv_val_other _ _ _ K hKO hKS]
    have ih := unaryK_spec hsd hOS hKO hKS hE rest hrest R (pre ++ [true]) σ2
      (by rw [hσ2]; simp only [WState.setv_st]; rw [hσ1, adv_st_src hsd, hst]; simp [List.replicate_succ])
      (by rw [hσ2]; simp only [WState.setv_sh]; rw [hσ1, adv_sh_src, hsh]; simp)
      (by rw [hσ2]; simp only [WState.setv_sh, WState.setv_st]; rw [hσ1, adv_sh_dst hsd, adv_st_dst]; simp [hd])
      (by rw [hσ2]; simp only [WState.setv_val]; rw [Function.update_of_ne hKO.symm, hσ1, adv_val_OP hOS]; nlinarith)
      (by rw [hσ2]; simp only [WState.setv_val]; rw [Function.update_of_ne hKS.symm, hσ1, adv_val_SC]; omega)
      (by rw [hσ2]; simp only [WState.setv_val, Function.update_self]; omega)
    refine WExec.mono (WExec.cast cap (WExec.whsT hw (WExec.seq x1 x2) ih) ?_ le_rfl) (by ring_nf; omega)
    rw [hσ2, adv_setv _ _ _ K _ hKO hKS, hσ1, adv_adv hsd hOS]
    simp only [WState.setv_val, Function.update_self, wsetv_setv]
    rw [hK1]
    simp only [List.replicate_succ, List.flatMap_cons]
    apply WState.eq
    · funext q; simp only [adv, appendO, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
      split_ifs <;> omega
    · rfl
    · funext q; simp only [adv, appendO, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
      split_ifs <;> omega
    · rfl

/-- One natural word, through an emitter. -/
def natCopy (src : Fin (ns + 1)) (SC K : Fin nr) (E : Bool → WM ns nr) : WM ns nr :=
  .seq (unaryK src SC K E) (.seq (cellE src SC E) (cntLoop src SC K E))

/-- Emitted length bound of an emitter. -/
def EmitLen (e : Bool → List Bool) (d : ℕ) : Prop := ∀ b, (e b).length ≤ d

theorem flatMap_emit_le {e : Bool → List Bool} {d : ℕ} (he : EmitLen e d) :
    ∀ w : List Bool, (w.flatMap e).length ≤ d * w.length
  | [] => by simp
  | b :: w => by
    have := flatMap_emit_le he w; have := he b
    simp only [List.flatMap_cons, List.length_append, List.length_cons]; nlinarith

theorem natCopy_spec (hsd : src ≠ dst) (hOS : OP ≠ SC) {K : Fin nr} (hKO : K ≠ OP) (hKS : K ≠ SC)
    {e : Bool → List Bool} {E : Bool → WM ns nr} {c d : ℕ} (hE : Emits cap dst OP e E c) (hd' : EmitLen e d)
    (v : ℕ) (pre rest : List Bool) (σ : WState ns nr) (hst : σ.st src = pre ++ natWord v ++ rest)
    (hsh : σ.sh src = pre.length) (hd : σ.sh dst = (σ.st dst).length) (hK : σ.val K = 0)
    (hOc : σ.val OP + d * (natWord v).length ≤ cap) (hSc : σ.val SC + (natWord v).length < cap + 1)
    (hKc : (natWord v).length < cap + 1) :
    WExec cap (natCopy src SC K E) σ (adv src dst OP SC σ ((natWord v).flatMap e) (natWord v).length)
      ((natWord v).length * (c + 13)) := by
  set m := natBitLength v with hm
  set bs := NearCubicWires.WilliamsPublishedForm.fixedWidthNatBits m v with hbs
  have hbl : bs.length = m := fixedWidth_length m v
  have hnw : natWord v = List.replicate m true ++ false :: bs := natWord_shape v
  have hlen : (natWord v).length = 2 * m + 1 := by rw [hnw]; simp [hbl]; omega
  have hm1 : 1 ≤ m := nbl_pos v
  have he1 := hd' true
  have heF := hd' false
  have hbe := flatMap_emit_le hd' bs
  have hre := flatMap_emit_le hd' (List.replicate m true)
  simp only [List.length_replicate] at hre
  -- the unary run
  have x1 := unaryK_spec cap hsd hOS hKO hKS hE (false :: bs ++ rest) (by simp) m pre σ
    (by rw [hst, hnw]; simp [List.append_assoc]) hsh hd
    (by have : m * (e true).length ≤ d * (natWord v).length := by rw [hlen]; nlinarith
        omega)
    (by omega) (by rw [hK]; omega)
  set σ1 := (adv src dst OP SC σ ((List.replicate m true).flatMap e) m).setv K (σ.val K + m) with hσ1
  have hσ1s : σ1.st src = pre ++ List.replicate m true ++ (false :: bs ++ rest) := by
    rw [hσ1]; simp only [WState.setv_st]; rw [adv_st_src hsd, hst, hnw]; simp [List.append_assoc]
  have hσ1h : σ1.sh src = (pre ++ List.replicate m true).length := by
    rw [hσ1]; simp only [WState.setv_sh]; rw [adv_sh_src, hsh]; simp
  have hb0 : readTapeBit (σ1.st src) (σ1.sh src) = false := by
    rw [hσ1s, hσ1h, rtb_off0]; rfl
  -- the separator
  have x2 := cellE_spec cap hsd hOS hE σ1
    (by rw [hσ1]; simp only [WState.setv_st, WState.setv_sh]; rw [adv_sh_dst hsd, adv_st_dst]; simp [hd])
    (by rw [hb0, hσ1]; simp only [WState.setv_val]; rw [Function.update_of_ne hKO.symm, adv_val_OP hOS]
        have : d * m + d ≤ d * (natWord v).length := by rw [hlen]; nlinarith
        omega)
    (by rw [hσ1]; simp only [WState.setv_val]; rw [Function.update_of_ne hKS.symm, adv_val_SC]; omega)
  rw [hb0] at x2
  set σ2 := adv src dst OP SC σ1 (e false) 1 with hσ2
  -- the bits
  have x3 := cntLoop_spec cap hsd hOS hKO hKS hE rest bs (pre ++ List.replicate m true ++ [false]) σ2
    (by rw [hσ2, adv_st_src hsd, hσ1s]; simp [List.append_assoc])
    (by rw [hσ2, adv_sh_src, hσ1h]; simp <;> omega)
    (by rw [hσ2, adv_sh_dst hsd, adv_st_dst, hσ1]; simp only [WState.setv_st, WState.setv_sh]
        rw [adv_sh_dst hsd, adv_st_dst]; simp [hd] <;> omega)
    (by rw [hσ2, adv_val_other _ _ _ K hKO hKS, hσ1]; simp [hK, hbl])
    (by omega)
    (by rw [hσ2, adv_val_OP hOS, hσ1]; simp only [WState.setv_val]; rw [Function.update_of_ne hKO.symm, adv_val_OP hOS]
        have : d * m + d + d * bs.length ≤ d * (natWord v).length := by rw [hlen, hbl]; nlinarith
        omega)
    (by rw [hσ2, adv_val_SC, hσ1]; simp only [WState.setv_val]; rw [Function.update_of_ne hKS.symm, adv_val_SC]
        omega)
  refine WExec.mono (WExec.cast cap (WExec.seq x1 (WExec.seq x2 x3)) ?_ le_rfl) (by rw [hlen, hbl]; nlinarith)
  rw [hσ2, hσ1, adv_setv _ _ _ K _ hKO hKS, adv_adv hsd hOS, adv_setv _ _ _ K _ hKO hKS, adv_adv hsd hOS, wsetv_setv]
  have hfix : ∀ τ : WState ns nr, τ.val K = 0 → τ.setv K 0 = τ := fun τ h => by rw [← h]; exact wsetv_same τ K
  rw [hfix _ (by rw [adv_val_other _ _ _ K hKO hKS, hK]), hnw]
  simp only [List.flatMap_append, List.flatMap_cons, List.length_append, List.length_replicate, List.length_cons, hbl,
    List.flatMap_nil, List.append_nil]
  congr 1
  · simp [List.append_assoc]
  · omega

/-- A list of natural words, up to the first `0` cell after them. -/
def natLoop (src : Fin (ns + 1)) (SC K : Fin nr) (E : Bool → WM ns nr) : WM ns nr := .whs src (natCopy src SC K E)

theorem natLoop_spec (hsd : src ≠ dst) (hOS : OP ≠ SC) {K : Fin nr} (hKO : K ≠ OP) (hKS : K ≠ SC)
    {e : Bool → List Bool} {E : Bool → WM ns nr} {c d : ℕ} (hE : Emits cap dst OP e E c) (hd' : EmitLen e d)
    (rest : List Bool) (hrest : rest.headD false = false) :
    ∀ (vs : List ℕ) (pre : List Bool) (σ : WState ns nr), σ.st src = pre ++ vs.flatMap natWord ++ rest →
      σ.sh src = pre.length → σ.sh dst = (σ.st dst).length → σ.val K = 0 →
      σ.val OP + d * (vs.flatMap natWord).length ≤ cap → σ.val SC + (vs.flatMap natWord).length < cap + 1 →
      (vs.flatMap natWord).length < cap + 1 →
      WExec cap (natLoop src SC K E) σ
        (adv src dst OP SC σ ((vs.flatMap natWord).flatMap e) (vs.flatMap natWord).length)
        ((vs.flatMap natWord).length * (c + 15) + 1)
  | [], pre, σ, hst, hsh, _, _, _, _, _ => by
    simp only [List.flatMap_nil, List.length_nil, adv_zero, Nat.zero_mul, Nat.zero_add]
    refine WExec.whsF ?_
    unfold wbit; rw [hst, hsh]; simp [rtb_off0]
    cases rest with
    | nil => rfl
    | cons a r => simp at hrest; subst hrest; rfl
  | v :: vs, pre, σ, hst, hsh, hd, hK, hOc, hSc, hKc => by
    have hL : ((v :: vs).flatMap natWord).length = (natWord v).length + (vs.flatMap natWord).length := by simp
    rw [hL] at hOc hSc hKc
    have hw : wbit σ src = true := by
      obtain ⟨t, ht⟩ := natWord_cons v
      unfold wbit; rw [hst, hsh]; simp only [List.flatMap_cons, List.append_assoc]
      rw [rtb_off0, ht]; rfl
    have x1 := natCopy_spec cap hsd hOS hKO hKS hE hd' v pre (vs.flatMap natWord ++ rest) σ
      (by rw [hst]; simp [List.append_assoc]) hsh hd hK (by nlinarith) (by omega) (by omega)
    set σ1 := adv src dst OP SC σ ((natWord v).flatMap e) (natWord v).length with hσ1
    have ih := natLoop_spec hsd hOS hKO hKS hE hd' rest hrest vs (pre ++ natWord v) σ1
      (by rw [hσ1, adv_st_src hsd, hst]; simp [List.append_assoc])
      (by rw [hσ1, adv_sh_src, hsh]; simp)
      (by rw [hσ1, adv_sh_dst hsd, adv_st_dst]; simp [hd])
      (by rw [hσ1, adv_val_other _ _ _ K hKO hKS, hK])
      (by rw [hσ1, adv_val_OP hOS]
          have := flatMap_emit_le hd' (natWord v); nlinarith)
      (by rw [hσ1, adv_val_SC]; omega) (by omega)
    have hn1 := natWord_len v
    refine WExec.mono (WExec.cast cap (WExec.whsT hw x1 ih) ?_ le_rfl) (by rw [hL]; nlinarith)
    rw [hσ1, adv_adv hsd hOS]
    simp [List.flatMap_append]

/-- One frame through an emitter: the marked pairs, then the end marker. -/
def frameCopy (src : Fin (ns + 1)) (SC : Fin nr) (E : Bool → WM ns nr) : WM ns nr :=
  .seq (pairLoop src SC E E) (cellE src SC E)

theorem frame_flatMap (e : Bool → List Bool) (x : List Bool) :
    (RepairOrdinary.frame x).flatMap e = x.flatMap (fun b => e true ++ e b) ++ e false := by
  rw [Codec.frame_eq_marks]
  induction x with
  | nil => simp [marks]
  | cons b x ih => simp [marks, List.flatMap_cons] at ih ⊢; rw [ih]

theorem pairs_emit_le {e : Bool → List Bool} {d : ℕ} (hd' : EmitLen e d) :
    ∀ x : List Bool, (x.flatMap fun b => e true ++ e b).length ≤ d * (2 * x.length)
  | [] => by simp
  | b :: x => by
    have := pairs_emit_le hd' x; have := hd' true; have := hd' b
    simp only [List.flatMap_cons, List.length_append, List.length_cons]; nlinarith

theorem frameCopy_spec (hsd : src ≠ dst) (hOS : OP ≠ SC) {e : Bool → List Bool} {E : Bool → WM ns nr} {c d : ℕ}
    (hE : Emits cap dst OP e E c) (hd' : EmitLen e d) (x pre rest : List Bool) (σ : WState ns nr)
    (hst : σ.st src = pre ++ RepairOrdinary.frame x ++ rest) (hsh : σ.sh src = pre.length)
    (hd : σ.sh dst = (σ.st dst).length) (hOc : σ.val OP + d * (RepairOrdinary.frame x).length ≤ cap)
    (hSc : σ.val SC + (RepairOrdinary.frame x).length < cap + 1) :
    WExec cap (frameCopy src SC E) σ
      (adv src dst OP SC σ ((RepairOrdinary.frame x).flatMap e) (RepairOrdinary.frame x).length)
      ((RepairOrdinary.frame x).length * (2 * c + 25)) := by
  have hfl : (RepairOrdinary.frame x).length = 2 * x.length + 1 := by rw [Codec.frame_eq_marks]; simp [Codec.marks_length]
  have hfe := frame_flatMap e x
  have hpe := pairs_emit_le hd' x
  have x1 := pairLoop_spec cap hsd hOS hE hE (false :: rest) (by simp) x pre σ
    (by rw [hst, Codec.frame_eq_marks]; simp [List.append_assoc]) hsh hd
    (by rw [hfl] at hOc; nlinarith [hd' false]) (by rw [hfl] at hSc; omega)
  set σ1 := adv src dst OP SC σ (x.flatMap fun b => e true ++ e b) (2 * x.length) with hσ1
  have hb : readTapeBit (σ1.st src) (σ1.sh src) = false := by
    rw [hσ1, adv_st_src hsd, adv_sh_src, hst, hsh, Codec.frame_eq_marks]
    simp only [List.append_assoc]
    rw [rtb_off pre _ (2 * x.length)]
    unfold readTapeBit; simp [Codec.marks_length]
  have x2 := cellE_spec cap hsd hOS hE σ1 (by rw [hσ1, adv_sh_dst hsd, adv_st_dst]; simp [hd])
    (by rw [hb, hσ1, adv_val_OP hOS]; rw [hfl] at hOc; nlinarith [hd' false])
    (by rw [hσ1, adv_val_SC]; rw [hfl] at hSc; omega)
  rw [hb] at x2
  refine WExec.mono (WExec.cast cap (WExec.seq x1 x2) ?_ le_rfl) (by rw [hfl]; nlinarith)
  rw [hσ1, adv_adv hsd hOS, hfe, hfl]

/-- A list of frames of nonempty words, up to the first `0` cell after them. -/
def frameLoop (src : Fin (ns + 1)) (SC : Fin nr) (E : Bool → WM ns nr) : WM ns nr := .whs src (frameCopy src SC E)

theorem frameLoop_spec (hsd : src ≠ dst) (hOS : OP ≠ SC) {e : Bool → List Bool} {E : Bool → WM ns nr} {c d : ℕ}
    (hE : Emits cap dst OP e E c) (hd' : EmitLen e d) (rest : List Bool) (hrest : rest.headD false = false) :
    ∀ (xs : List (List Bool)) (pre : List Bool) (σ : WState ns nr), (∀ x ∈ xs, x ≠ []) →
      σ.st src = pre ++ xs.flatMap RepairOrdinary.frame ++ rest → σ.sh src = pre.length →
      σ.sh dst = (σ.st dst).length → σ.val OP + d * (xs.flatMap RepairOrdinary.frame).length ≤ cap →
      σ.val SC + (xs.flatMap RepairOrdinary.frame).length < cap + 1 →
      WExec cap (frameLoop src SC E) σ
        (adv src dst OP SC σ ((xs.flatMap RepairOrdinary.frame).flatMap e) (xs.flatMap RepairOrdinary.frame).length)
        ((xs.flatMap RepairOrdinary.frame).length * (2 * c + 27) + 1)
  | [], pre, σ, _, hst, hsh, _, _, _ => by
    simp only [List.flatMap_nil, List.length_nil, adv_zero, Nat.zero_mul, Nat.zero_add]
    refine WExec.whsF ?_
    unfold wbit; rw [hst, hsh]; simp [rtb_off0]
    cases rest with
    | nil => rfl
    | cons a r => simp at hrest; subst hrest; rfl
  | x :: xs, pre, σ, hne, hst, hsh, hd, hOc, hSc => by
    have hL : ((x :: xs).flatMap RepairOrdinary.frame).length =
        (RepairOrdinary.frame x).length + (xs.flatMap RepairOrdinary.frame).length := by simp
    rw [hL] at hOc hSc
    have hw : wbit σ src = true := by
      obtain ⟨t, ht⟩ := frame_cons (hne x (by simp))
      unfold wbit; rw [hst, hsh]; simp only [List.flatMap_cons, List.append_assoc]
      rw [rtb_off0, ht]; rfl
    have x1 := frameCopy_spec cap hsd hOS hE hd' x pre (xs.flatMap RepairOrdinary.frame ++ rest) σ
      (by rw [hst]; simp [List.append_assoc]) hsh hd (by nlinarith) (by omega)
    set σ1 := adv src dst OP SC σ ((RepairOrdinary.frame x).flatMap e) (RepairOrdinary.frame x).length with hσ1
    have ih := frameLoop_spec hsd hOS hE hd' rest hrest xs (pre ++ RepairOrdinary.frame x) σ1
      (fun y hy => hne y (by simp [hy]))
      (by rw [hσ1, adv_st_src hsd, hst]; simp [List.append_assoc])
      (by rw [hσ1, adv_sh_src, hsh]; simp)
      (by rw [hσ1, adv_sh_dst hsd, adv_st_dst]; simp [hd])
      (by rw [hσ1, adv_val_OP hOS]
          have := flatMap_emit_le hd' (RepairOrdinary.frame x); nlinarith)
      (by rw [hσ1, adv_val_SC]; omega)
    have hn1 : (RepairOrdinary.frame x).length = 2 * x.length + 1 := by
      rw [Codec.frame_eq_marks]; simp [Codec.marks_length]
    refine WExec.mono (WExec.cast cap (WExec.whsT hw x1 ih) ?_ le_rfl) (by rw [hL]; nlinarith)
    rw [hσ1, adv_adv hsd hOS]
    simp [List.flatMap_append]

end Loops

end NearCubicGates.Close.CounterAsm
