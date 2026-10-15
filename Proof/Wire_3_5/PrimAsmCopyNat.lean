import Proof.Wire_3_5.PrimAsmWriteNat

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.CopyNat
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks)

variable {ns nr : ℕ} (cap : ℕ)

/-! ## One logical bit -/

/-- Copy the current logical bit of source `s` to the end of `o` as `[true, b]`, and step `s` to the next bit. -/
def copyBit (ε : Bool) (s o : Fin (ns + 1)) (OP : Fin nr) : WM ns nr :=
  .seq (preE ε s) (.seq (.ifs s (emitPair o OP true) (emitPair o OP false)) (.fwd s))

theorem copyBit_spec (ε : Bool) (s o : Fin (ns + 1)) (hso : s ≠ o) (OP : Fin nr) (σ : WState ns nr)
    (ho : σ.sh o = (σ.st o).length) (hc : σ.val OP + 2 ≤ cap) :
    WExec cap (copyBit ε s o OP) σ
      ((appendO σ o OP [true, readTapeBit (σ.st s) (σ.sh s + off ε)]).seth s (σ.sh s + stp ε)) 20 := by
  have hs := stp_eq ε
  have hoff := off_le ε
  have h1 := preE_spec cap ε s σ
  set σ1 := σ.seth s (σ.sh s + off ε) with hσ1
  have hσ1o : σ1.sh o = (σ1.st o).length := by simp [σ1, Function.update_apply, Ne.symm hso, ho]
  have hσ1c : σ1.val OP + 2 ≤ cap := by simp [σ1]; omega
  set b := readTapeBit (σ.st s) (σ.sh s + off ε) with hb
  have hbit : wbit σ1 s = b := by simp [σ1, wbit, b]
  have h2 : WExec cap (.ifs s (emitPair o OP true) (emitPair o OP false)) σ1 (appendO σ1 o OP [true, b]) 16 := by
    cases hbv : b with
    | true => exact WExec.ifsT (by rw [hbit, hbv]) (emitPair_spec cap o OP true σ1 hσ1o hσ1c)
    | false => exact WExec.ifsF (by rw [hbit, hbv]) (emitPair_spec cap o OP false σ1 hσ1o hσ1c)
  have h3 := WExec.fwd (cap := cap) s (appendO σ1 o OP [true, b])
  refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 h3)) ?_ (by omega)
  apply WState.eq
  · funext j
    by_cases hjs : j = s
    · subst hjs; simp [σ1, Function.update_apply, hso]; omega
    · by_cases hjo : j = o
      · subst hjo; simp [σ1, Function.update_apply, hjs, Ne.symm hso]
      · simp [σ1, Function.update_apply, hjs, hjo]
  · funext j
    by_cases hjo : j = o
    · subst hjo; simp [σ1, Function.update_apply, Ne.symm hso]
    · simp [σ1, Function.update_apply, hjo]
  · simp [σ1]
  · simp [σ1]

/-! ## The unary prefix -/

/-- The unary prefix, copied: while the flag `f` is set, copy one logical bit; on `1` count it in `c`, on `0` clear
`f`. -/
def copyUnary (ε : Bool) (s o : Fin (ns + 1)) (f c OP : Fin nr) : WM ns nr :=
  .whr f (.seq (preE ε s) (.ifs s (.seq (emitPair o OP true) (.seq (.inc c) (.fwd s)))
    (.seq (emitPair o OP false) (.seq (.dec f) (.fwd s)))))

theorem copyUnary_spec (ε : Bool) (s o : Fin (ns + 1)) (hso : s ≠ o) (f c OP : Fin nr) (hfc : f ≠ c)
    (hfO : f ≠ OP) (hcO : c ≠ OP) (hcap1 : 1 ≤ cap) :
    ∀ (r : ℕ) (σ : WState ns nr), σ.val f = 1 → σ.sh o = (σ.st o).length →
      (∀ k < r, readTapeBit (σ.st s) (σ.sh s + stp ε * k + off ε) = true) →
      readTapeBit (σ.st s) (σ.sh s + stp ε * r + off ε) = false → σ.val c + r ≤ cap →
      σ.val OP + 2 * r + 2 ≤ cap →
      WExec cap (copyUnary ε s o f c OP) σ
        (((appendO σ o OP (marks (List.replicate r true ++ [false]))).seth s (σ.sh s + stp ε * r + stp ε)).setv c
          (σ.val c + r) |>.setv f 0) (30 * r + 30)
  | 0, σ, hf, ho, _, hend, _, hOP => by
    have hs := stp_eq ε
    have hoff := off_le ε
    have h1 := preE_spec cap ε s σ
    set σ1 := σ.seth s (σ.sh s + off ε) with hσ1
    have hσ1o : σ1.sh o = (σ1.st o).length := by simp [σ1, Function.update_apply, Ne.symm hso, ho]
    have hbit : wbit σ1 s = false := by simpa [σ1, wbit] using hend
    have h2 := emitPair_spec cap o OP false σ1 hσ1o (by simp [σ1]; omega)
    set σ2 := appendO σ1 o OP [true, false] with hσ2
    have h3 := WExec.dec (cap := cap) f σ2 (by simp [σ2, σ1, Function.update_apply, hfO, hf]; omega)
    set σ3 := σ2.setv f (σ2.val f - 1) with hσ3
    have h4 := WExec.fwd (cap := cap) s σ3
    set σ4 := σ3.seth s (σ3.sh s + 1) with hσ4
    have hσ4f : σ4.val f = 0 := by simp [σ4, σ3, σ2, σ1, Function.update_apply, hfO, hf]
    have hbody := WExec.seq h1 (WExec.ifsF (P := .seq (emitPair o OP true) (.seq (.inc c) (.fwd s))) hbit
      (WExec.seq h2 (WExec.seq h3 h4)))
    have hloop := WExec.whrT (by omega) hbody (WExec.whrF (P := .seq (preE ε s) (.ifs s (.seq (emitPair o OP true)
      (.seq (.inc c) (.fwd s))) (.seq (emitPair o OP false) (.seq (.dec f) (.fwd s))))) hσ4f)
    refine WExec.cast cap hloop ?_ (by omega)
    apply WState.eq
    · funext j
      by_cases hjs : j = s
      · subst hjs; simp [σ4, σ3, σ2, σ1, Function.update_apply, hso]; omega
      · by_cases hjo : j = o
        · subst hjo; simp [σ4, σ3, σ2, σ1, Function.update_apply, hjs, Ne.symm hso, marks]
        · simp [σ4, σ3, σ2, σ1, Function.update_apply, hjs, hjo]
    · funext j
      by_cases hjo : j = o
      · subst hjo; simp [σ4, σ3, σ2, σ1, Function.update_apply, Ne.symm hso, marks]
      · simp [σ4, σ3, σ2, σ1, Function.update_apply, hjo]
    · funext j
      by_cases hjf : j = f
      · subst hjf; simp [σ4, σ3, σ2, σ1, Function.update_apply, hfO, hf]
      · by_cases hjc : j = c
        · subst hjc; simp [σ4, σ3, σ2, σ1, Function.update_apply, hjf, hcO]
        · by_cases hjO : j = OP
          · subst hjO; simp [σ4, σ3, σ2, σ1, Function.update_apply, hjf, hjc, marks]
          · simp [σ4, σ3, σ2, σ1, Function.update_apply, hjf, hjc, hjO]
    · simp [σ4, σ3, σ2, σ1]
  | r + 1, σ, hf, ho, hones, hend, hc, hOP => by
    have hs := stp_eq ε
    have hoff := off_le ε
    have h1 := preE_spec cap ε s σ
    set σ1 := σ.seth s (σ.sh s + off ε) with hσ1
    have hσ1o : σ1.sh o = (σ1.st o).length := by simp [σ1, Function.update_apply, Ne.symm hso, ho]
    have hbit : wbit σ1 s = true := by have := hones 0 (by omega); simpa [σ1, wbit] using this
    have h2 := emitPair_spec cap o OP true σ1 hσ1o (by simp [σ1]; omega)
    set σ2 := appendO σ1 o OP [true, true] with hσ2
    have h3 := WExec.inc (cap := cap) c σ2 (by simp [σ2, σ1, Function.update_apply, hcO]; omega)
    set σ3 := σ2.setv c (σ2.val c + 1) with hσ3
    have h4 := WExec.fwd (cap := cap) s σ3
    set τ := σ3.seth s (σ3.sh s + 1) with hτ
    have hτsh : τ.sh s = σ.sh s + stp ε := by simp [τ, σ3, σ2, σ1, Function.update_apply, hso]; omega
    have hτst : τ.st s = σ.st s := by simp [τ, σ3, σ2, σ1, Function.update_apply, hso]
    have hτf : τ.val f = 1 := by simp [τ, σ3, σ2, σ1, Function.update_apply, hfc, hfO, hf]
    have hτo : τ.sh o = (τ.st o).length := by
      simp [τ, σ3, σ2, σ1, Function.update_apply, Ne.symm hso, ho] <;> ring
    have hτc : τ.val c = σ.val c + 1 := by simp [τ, σ3, σ2, σ1, Function.update_apply, hcO]
    have hτOP : τ.val OP = σ.val OP + 2 := by simp [τ, σ3, σ2, σ1, Function.update_apply, Ne.symm hcO]
    have ih := copyUnary_spec ε s o hso f c OP hfc hfO hcO hcap1 r τ hτf hτo
      (fun k hk => by
        rw [hτst, hτsh, show σ.sh s + stp ε + stp ε * k + off ε = σ.sh s + stp ε * (k + 1) + off ε by ring]
        exact hones (k + 1) (by omega))
      (by rw [hτst, hτsh, show σ.sh s + stp ε + stp ε * r + off ε = σ.sh s + stp ε * (r + 1) + off ε by ring]
          exact hend)
      (by rw [hτc]; omega) (by rw [hτOP]; omega)
    have hbody := WExec.seq h1 (WExec.ifsT (Q := .seq (emitPair o OP false) (.seq (.dec f) (.fwd s))) hbit
      (WExec.seq h2 (WExec.seq h3 h4)))
    refine WExec.cast cap (WExec.whrT (by omega) hbody ih) ?_ (by omega)
    have hm : marks (List.replicate (r + 1) true ++ [false]) = [true, true] ++ marks (List.replicate r true ++ [false]) := by
      simp [marks, List.replicate_succ]
    apply WState.eq
    · funext j
      by_cases hjs : j = s
      · subst hjs; simp [τ, σ3, σ2, σ1, Function.update_apply, hso]; ring_nf; omega
      · by_cases hjo : j = o
        · subst hjo; simp [τ, σ3, σ2, σ1, Function.update_apply, hjs, Ne.symm hso, hm]; ring
        · simp [τ, σ3, σ2, σ1, Function.update_apply, hjs, hjo]
    · funext j
      by_cases hjo : j = o
      · subst hjo; simp [τ, σ3, σ2, σ1, Function.update_apply, Ne.symm hso, hm]
      · simp [τ, σ3, σ2, σ1, Function.update_apply, hjo]
    · funext j
      by_cases hjf : j = f
      · subst hjf; simp [Function.update_apply]
      · by_cases hjc : j = c
        · subst hjc; simp [τ, σ3, σ2, σ1, Function.update_apply, hjf, hcO]; ring
        · by_cases hjO : j = OP
          · subst hjO; simp [τ, σ3, σ2, σ1, Function.update_apply, hjf, hjc, hm]; ring
          · simp [τ, σ3, σ2, σ1, Function.update_apply, hjf, hjc, hjO]
    · simp [τ, σ3, σ2, σ1]

/-! ## One whole field -/

/-- **Copy one field** `enc ε (natWord x)` of source `s` to the end of `o` as `marks (natWord x)` (bit by bit, in time
linear in its length), leaving `s` just past the field; the flag `f` and counter `c` are `0` again. -/
def copyNatM (ε : Bool) (s o : Fin (ns + 1)) (f c OP : Fin nr) : WM ns nr :=
  .seq (.inc f) (.seq (copyUnary ε s o f c OP) (.whr c (.seq (.dec c) (copyBit ε s o OP))))

/-- The payload copy's state after `j` bits. -/
def copyState (σ : WState ns nr) (s o : Fin (ns + 1)) (c OP : Fin nr) (ε : Bool) (L : ℕ) (bs : List Bool) (j : ℕ) :
    WState ns nr :=
  ((appendO σ o OP (marks (bs.take j))).seth s (σ.sh s + stp ε * j)).setv c (L - j)

theorem copyNatM_spec (ε : Bool) (s o : Fin (ns + 1)) (hso : s ≠ o) (f c OP : Fin nr) (hfc : f ≠ c) (hfO : f ≠ OP)
    (hcO : c ≠ OP) (x : ℕ) (pre rest : List Bool) (σ : WState ns nr)
    (hst : σ.st s = pre ++ enc ε (RepairRepresentation.natWord x) ++ rest) (hsh : σ.sh s = pre.length)
    (ho : σ.sh o = (σ.st o).length) (hf : σ.val f = 0) (hc : σ.val c = 0)
    (hcap : σ.val OP + 2 * (RepairRepresentation.natWord x).length + 2 ≤ cap) :
    WExec cap (copyNatM ε s o f c OP) σ
      ((appendO σ o OP (marks (RepairRepresentation.natWord x))).seth s
        (pre.length + stp ε * (RepairRepresentation.natWord x).length))
      (60 * (RepairRepresentation.natWord x).length + 60) := by
  set L := natBitLength x with hL
  have hlen := natWord_length x
  have hs := stp_eq ε
  have hoff := off_le ε
  have hf1 := WExec.inc (cap := cap) f σ (by omega)
  set σ1 := σ.setv f (σ.val f + 1) with hσ1
  have hσ1st : σ1.st s = pre ++ (enc ε (RepairRepresentation.natWord x) ++ rest) := by
    simp [σ1, hst, List.append_assoc]
  have hσ1sh : σ1.sh s = pre.length := by simp [σ1, hsh]
  have hread : ∀ k, k < (RepairRepresentation.natWord x).length →
      readTapeBit (σ1.st s) (σ1.sh s + stp ε * k + off ε) = (RepairRepresentation.natWord x).getD k false := by
    intro k hk
    rw [hσ1st, hσ1sh, Nat.add_assoc, read_pre]
    exact read_enc_bit ε rest _ k hk
  have h2 := copyUnary_spec cap ε s o hso f c OP hfc hfO hcO (by omega) L σ1 (by simp [σ1, hf])
    (by simpa [σ1] using ho)
    (fun k hk => by rw [hread k (by omega)]; exact natWord_getD_one x k hk)
    (by rw [hread L (by omega)]; exact natWord_getD_zero x)
    (by simp [σ1, Function.update_apply, hfc.symm, hc]; omega)
    (by simp [σ1, Function.update_apply, hfO.symm]; omega)
  set σ2 := (((appendO σ1 o OP (marks (List.replicate L true ++ [false]))).seth s (σ1.sh s + stp ε * L + stp ε)).setv
    c (σ1.val c + L) |>.setv f 0) with hσ2
  set bs := WilliamsPublishedForm.fixedWidthNatBits L x with hbs
  have hbsl : bs.length = L := by simp [bs, WilliamsPublishedForm.fixedWidthNatBits]
  have hσ2c : σ2.val c = L := by simp [σ2, σ1, Function.update_apply, hfc, hfc.symm, hcO, hc]
  have hmarksL : (marks (List.replicate L true ++ [false])).length = 2 * L + 2 := by simp [marks]; ring
  have hS0 : copyState σ2 s o c OP ε L bs 0 = σ2 := by
    apply WState.eq
    · simp [copyState, marks]
    · simp [copyState, marks]
    · funext j
      by_cases hjc : j = c
      · subst hjc; simp [copyState, Function.update_apply, hσ2c, marks]
      · by_cases hjO : j = OP
        · subst hjO; simp [copyState, Function.update_apply, hjc, marks]
        · simp [copyState, Function.update_apply, hjc, hjO]
    · simp [copyState]
  have hσ2sh : σ2.sh s = pre.length + stp ε * (L + 1) := by
    simp [σ2, σ1, Function.update_apply, hso, hsh]; ring
  have hσ2st : σ2.st s = σ1.st s := by simp [σ2, σ1, Function.update_apply, hso]
  have hσ2o : σ2.sh o = (σ2.st o).length := by
    simp [σ2, σ1, Function.update_apply, Ne.symm hso, ho] <;> ring
  have hσ2OP : σ2.val OP = σ.val OP + (2 * L + 2) := by
    simp [σ2, σ1, Function.update_apply, hcO.symm, hfO.symm, hmarksL]
  have hloop := UnionMachine.Round.wloop cap c (copyBit ε s o OP) 20 L (copyState σ2 s o c OP ε L bs)
    (fun k _ => by simp [copyState, Function.update_apply])
    (by omega)
    (fun k hk => by
      set T := (copyState σ2 s o c OP ε L bs k).setv c (L - k - 1) with hT
      have hTo : T.sh o = (T.st o).length := by
        simp [T, copyState, Function.update_apply, Ne.symm hso, hσ2o] <;> ring
      have hlenk : (marks (bs.take k)).length = 2 * k := by
        simp [marks, List.length_take, hbsl]; omega
      have hTOP : T.val OP = σ.val OP + (2 * L + 2) + 2 * k := by
        simp [T, copyState, Function.update_apply, hcO.symm, hσ2OP, hlenk]
      have h := copyBit_spec cap ε s o hso OP T hTo (by rw [hTOP]; omega)
      refine WExec.cast cap h ?_ le_rfl
      have hbit : readTapeBit (T.st s) (T.sh s + off ε) = bs.getD k false := by
        have e1 : T.st s = σ1.st s := by simp [T, copyState, Function.update_apply, hso, hσ2st]
        have e2 : T.sh s = pre.length + stp ε * (L + 1) + stp ε * k := by
          simp [T, copyState, hσ2sh]
        rw [e1, e2, hσ1st, show pre.length + stp ε * (L + 1) + stp ε * k + off ε =
          pre.length + (stp ε * (L + 1 + k) + off ε) by ring, read_pre, read_enc_bit ε rest _ _ (by omega),
          natWord_getD_payload x k (by omega)]
        rw [List.getD_eq_getElem _ _ (by omega)]
        simp [bs, WilliamsPublishedForm.fixedWidthNatBits]
      have htake : bs.take (k + 1) = bs.take k ++ [bs.getD k false] := by
        rw [List.take_add_one, List.getElem?_eq_getElem (by omega), List.getD_eq_getElem _ _ (by omega)]
        rfl
      rw [hbit]
      apply WState.eq
      · funext j
        by_cases hjs : j = s
        · subst hjs; simp [T, copyState, Function.update_apply, hso]; ring
        · by_cases hjo : j = o
          · subst hjo; simp [T, copyState, Function.update_apply, hjs, Ne.symm hso, htake, marks]; ring
          · simp [T, copyState, Function.update_apply, hjs, hjo]
      · funext j
        by_cases hjo : j = o
        · subst hjo; simp [T, copyState, Function.update_apply, Ne.symm hso, htake, marks]
        · simp [T, copyState, Function.update_apply, hjo]
      · funext j
        by_cases hjc : j = c
        · subst hjc; simp [T, copyState, Function.update_apply, hcO]; omega
        · by_cases hjO : j = OP
          · subst hjO; simp [T, copyState, Function.update_apply, hjc, htake, marks]; ring
          · simp [T, copyState, Function.update_apply, hjc, hjO]
      · simp [T, copyState])
  rw [hS0] at hloop
  refine WExec.cast cap (WExec.seq hf1 (WExec.seq h2 hloop)) ?_ ?_
  · have htk : bs.take L = bs := List.take_of_length_le (le_of_eq hbsl)
    have hnw : marks (RepairRepresentation.natWord x) = marks (List.replicate L true ++ [false]) ++ marks bs := by
      rw [natWord_eq]; simp [marks, bs, hL]
    apply WState.eq
    · funext j
      by_cases hjs : j = s
      · subst hjs; simp [copyState, σ2, σ1, Function.update_apply, hso, hsh, hlen]; ring
      · by_cases hjo : j = o
        · subst hjo; simp [copyState, σ2, σ1, Function.update_apply, hjs, Ne.symm hso, htk, hnw, hlen, hmarksL]
          simp [marks, bs]; ring
        · simp [copyState, σ2, σ1, Function.update_apply, hjs, hjo]
    · funext j
      by_cases hjo : j = o
      · subst hjo; simp [copyState, σ2, σ1, Function.update_apply, Ne.symm hso, htk, hnw]
      · simp [copyState, σ2, σ1, Function.update_apply, hjo]
    · funext j
      by_cases hjc : j = c
      · subst hjc; simp [copyState, Function.update_apply, hcO, hc]
      · by_cases hjO : j = OP
        · subst hjO; simp [copyState, σ2, σ1, Function.update_apply, hjc, hfO.symm, htk, hnw, hmarksL]
          simp [marks, bs]; ring
        · by_cases hjf : j = f
          · subst hjf; simp [copyState, σ2, σ1, Function.update_apply, hjc, hjO, hf]
          · simp [copyState, σ2, σ1, Function.update_apply, hjc, hjO, hjf]
    · simp [copyState, σ2, σ1]
  · rw [hlen]; nlinarith

/-! ## A flag and a constant word -/

/-- Write the flag `fl ∈ {0, 1}` as one framed bit. -/
def writeBitM (o : Fin (ns + 1)) (OP fl : Fin nr) : WM ns nr := .ifr fl (emitPair o OP true) (emitPair o OP false)

theorem writeBitM_spec (o : Fin (ns + 1)) (OP fl : Fin nr) (σ : WState ns nr) (ho : σ.sh o = (σ.st o).length)
    (hc : σ.val OP + 2 ≤ cap) :
    WExec cap (writeBitM o OP fl) σ (appendO σ o OP [true, decide (σ.val fl ≠ 0)]) 16 := by
  by_cases h : σ.val fl = 0
  · have e : decide (σ.val fl ≠ 0) = false := by simp [h]
    rw [e]; exact WExec.ifrF h (emitPair_spec cap o OP false σ ho hc)
  · have e : decide (σ.val fl ≠ 0) = true := by simp [h]
    rw [e]; exact WExec.ifrT h (emitPair_spec cap o OP true σ ho hc)

/-- Write the constant word `u` framed. -/
def emitWordM (o : Fin (ns + 1)) (OP : Fin nr) : List Bool → WM ns nr
  | [] => .skip
  | b :: u => .seq (emitPair o OP b) (emitWordM o OP u)

theorem emitWordM_spec (o : Fin (ns + 1)) (OP : Fin nr) :
    ∀ (u : List Bool) (σ : WState ns nr), σ.sh o = (σ.st o).length → σ.val OP + 2 * u.length ≤ cap →
      WExec cap (emitWordM o OP u) σ (appendO σ o OP (marks u)) (16 * u.length)
  | [], σ, _, _ => by
    rw [show marks ([] : List Bool) = [] from rfl, appendO_nil]
    exact WExec.skip σ
  | b :: u, σ, ho, hc => by
    have h1 := emitPair_spec cap o OP b σ ho (by simp at hc; omega)
    have h2 := emitWordM_spec o OP u (appendO σ o OP [true, b]) (by simp [ho] <;> ring)
      (by simp at hc ⊢; omega)
    refine WExec.cast cap (WExec.seq h1 h2) ?_ (by simp; omega)
    rw [appendO_append]
    simp [marks]

/-! ## A list field -/

theorem enc_append (ε : Bool) (u u' : List Bool) : enc ε (u ++ u') = enc ε u ++ enc ε u' := by
  cases ε <;> simp [ParseNat.enc, marks]

theorem natListWord_eq (xs : List ℕ) :
    RepairRepresentation.natListWord xs =
      RepairRepresentation.natWord xs.length ++ xs.flatMap RepairRepresentation.natWord := rfl

/-- The registers of the list copy: `Q 0 = m` (the count), `Q 1 … Q 6` scratch, `Q 7 = OP`, `Q 8` scratch. -/
def listRegs (Q : Fin 9 ↪ Fin nr) : Fin 8 ↪ Fin nr := (Fin.castSuccEmb).trans Q

/-- **Copy one list field** `enc ε (natListWord xs)` of source `s` to the end of `o` as `marks (natListWord xs)`: the
count into `m` (a unary register; counts are small) and rewritten canonically, then each element copied bit by bit. -/
def copyNatListM (ε : Bool) (s o : Fin (ns + 1)) (Q : Fin 9 ↪ Fin nr) : WM ns nr :=
  .seq (readNatM ε s (Q 1) (Q 2) (Q 0) (Q 3) (Q 6))
    (.seq (writeNatM o (listRegs Q))
      (.whr (Q 0) (.seq (.dec (Q 0)) (copyNatM ε s o (Q 1) (Q 2) (Q 7)))))

theorem Qne (Q : Fin 9 ↪ Fin nr) {i j : Fin 9} (h : i ≠ j) : Q i ≠ Q j := Q.injective.ne h

/-- The element loop: `m` times, copy one field. -/
def elemLoop (ε : Bool) (s o : Fin (ns + 1)) (Q : Fin 9 ↪ Fin nr) : WM ns nr :=
  .whr (Q 0) (.seq (.dec (Q 0)) (copyNatM ε s o (Q 1) (Q 2) (Q 7)))

theorem elemLoop_spec (ε : Bool) (s o : Fin (ns + 1)) (hso : s ≠ o) (Q : Fin 9 ↪ Fin nr) :
    ∀ (ys : List ℕ) (pre rest : List Bool) (σ : WState ns nr),
      σ.st s = pre ++ enc ε (ys.flatMap RepairRepresentation.natWord) ++ rest → σ.sh s = pre.length →
      σ.sh o = (σ.st o).length → σ.val (Q 0) = ys.length → σ.val (Q 1) = 0 → σ.val (Q 2) = 0 →
      σ.val (Q 0) ≤ cap → σ.val (Q 7) + 2 * (ys.flatMap RepairRepresentation.natWord).length + 2 ≤ cap →
      WExec cap (elemLoop ε s o Q) σ
        (((appendO σ o (Q 7) (marks (ys.flatMap RepairRepresentation.natWord))).seth s
          (pre.length + stp ε * (ys.flatMap RepairRepresentation.natWord).length)).setv (Q 0) 0)
        (64 * (ys.flatMap RepairRepresentation.natWord).length + 64 * ys.length + 1)
  | [], pre, rest, σ, _, hsh, _, h0, _, _, _, _ => by
    have e : ((appendO σ o (Q 7) (marks (([] : List ℕ).flatMap RepairRepresentation.natWord))).seth s
        (pre.length + stp ε * (([] : List ℕ).flatMap RepairRepresentation.natWord).length)).setv (Q 0) 0 = σ := by
      simp only [List.flatMap_nil, List.length_nil, Nat.mul_zero, Nat.add_zero]
      rw [show marks ([] : List Bool) = [] from rfl, appendO_nil, ← hsh]
      have e2 : σ.seth s (σ.sh s) = σ := WState.eq (by simp) rfl rfl rfl
      rw [e2, show (0 : ℕ) = σ.val (Q 0) by simpa using h0.symm, wsetv_same]
    rw [e]
    exact WExec.mono (WExec.whrF (by simpa using h0)) (by omega)
  | y :: ys, pre, rest, σ, hst, hsh, ho, h0, h1, h2, hcap0, hcap => by
    have hfl : (y :: ys).flatMap RepairRepresentation.natWord =
        RepairRepresentation.natWord y ++ ys.flatMap RepairRepresentation.natWord := by simp
    have hcap' := hcap
    rw [hfl, List.length_append] at hcap'
    have hlen0 : ys.length + 1 = σ.val (Q 0) := by rw [h0]; rfl
    have d1 := WExec.dec (cap := cap) (Q 0) σ hcap0
    set σ1 := σ.setv (Q 0) (σ.val (Q 0) - 1) with hσ1
    have hσ17 : σ1.val (Q 7) = σ.val (Q 7) := by
      simp [σ1, Function.update_apply, Qne Q (show (7 : Fin 9) ≠ 0 by decide)]
    have hc := copyNatM_spec cap ε s o hso (Q 1) (Q 2) (Q 7) (Qne Q (by decide)) (Qne Q (by decide))
      (Qne Q (by decide)) y pre (enc ε (ys.flatMap RepairRepresentation.natWord) ++ rest) σ1
      (by simp [σ1, hst, hfl, enc_append, List.append_assoc]) (by simp [σ1, hsh])
      (by simpa [σ1] using ho)
      (by simp [σ1, Function.update_apply, Qne Q (show (1 : Fin 9) ≠ 0 by decide), h1])
      (by simp [σ1, Function.update_apply, Qne Q (show (2 : Fin 9) ≠ 0 by decide), h2])
      (by rw [hσ17]; omega)
    set τ := (appendO σ1 o (Q 7) (marks (RepairRepresentation.natWord y))).seth s
      (pre.length + stp ε * (RepairRepresentation.natWord y).length) with hτ
    have hτ7 : τ.val (Q 7) = σ.val (Q 7) + 2 * (RepairRepresentation.natWord y).length := by
      simp only [τ, WState.seth_val, appendO_val, Function.update_self, hσ17]
      simp [marks]; ring
    have ih := elemLoop_spec ε s o hso Q ys (pre ++ enc ε (RepairRepresentation.natWord y)) rest τ
      (by simp [τ, σ1, Function.update_apply, hso, hst, hfl, enc_append, List.append_assoc])
      (by simp [τ, enc_length])
      (by simp [τ, σ1, Function.update_apply, Ne.symm hso, ho] <;> ring)
      (by simp [τ, σ1, Function.update_apply, Qne Q (show (0 : Fin 9) ≠ 7 by decide)]; omega)
      (by simp [τ, σ1, Function.update_apply, Qne Q (show (1 : Fin 9) ≠ 7 by decide),
        Qne Q (show (1 : Fin 9) ≠ 0 by decide), h1])
      (by simp [τ, σ1, Function.update_apply, Qne Q (show (2 : Fin 9) ≠ 7 by decide),
        Qne Q (show (2 : Fin 9) ≠ 0 by decide), h2])
      (by simp [τ, σ1, Function.update_apply, Qne Q (show (0 : Fin 9) ≠ 7 by decide)]; omega)
      (by rw [hτ7]; omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq d1 hc) ih) ?_ ?_
    · apply WState.eq
      · funext j
        by_cases hjs : j = s
        · subst hjs; simp [τ, σ1, Function.update_apply, hso, hfl, enc_length]; ring
        · by_cases hjo : j = o
          · subst hjo; simp [τ, σ1, Function.update_apply, hjs, Ne.symm hso, hfl, marks]; ring
          · simp [τ, σ1, Function.update_apply, hjs, hjo]
      · funext j
        by_cases hjo : j = o
        · subst hjo; simp [τ, σ1, Function.update_apply, Ne.symm hso, hfl, marks]
        · simp [τ, σ1, Function.update_apply, hjo]
      · funext j
        by_cases hj0 : j = Q 0
        · subst hj0; simp [Function.update_apply]
        · by_cases hj7 : j = Q 7
          · subst hj7; simp [τ, σ1, Function.update_apply, hj0, Qne Q (show (7 : Fin 9) ≠ 0 by decide), hfl, marks]
            ring
          · simp [τ, σ1, Function.update_apply, hj0, hj7]
      · simp [τ, σ1]
    · rw [hfl, List.length_append, List.length_cons]; ring_nf; omega

theorem two_pow_natBitLength_le (m : ℕ) : 2 ^ natBitLength m ≤ 2 * m + 2 := by
  unfold natBitLength
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; simp
  · have := Nat.pow_log_le_self 2 (show m ≠ 0 by omega)
    rw [pow_succ]; omega

theorem natBitLength_le_self_succ (m : ℕ) : natBitLength m ≤ m + 1 := by
  have := Nat.log_lt_self 2 (show m + 1 ≠ 0 by omega)
  have := Nat.log_mono_right (show m ≤ m + 1 by omega) (b := 2)
  simp only [natBitLength]; omega

/-- **Copying one list field**: `enc ε (natListWord xs)` from source `s` to the end of `o` as `marks (natListWord xs)`,
the source head past the field, every register of `Q` except `OP = Q 7` back to its entry value `0`. -/
theorem copyNatListM_spec (ε : Bool) (s o : Fin (ns + 1)) (hso : s ≠ o) (Q : Fin 9 ↪ Fin nr) (xs : List ℕ)
    (pre rest : List Bool) (σ : WState ns nr)
    (hst : σ.st s = pre ++ enc ε (RepairRepresentation.natListWord xs) ++ rest) (hsh : σ.sh s = pre.length)
    (ho : σ.sh o = (σ.st o).length) (hQ : ∀ i : Fin 9, i ≠ 7 → σ.val (Q i) = 0)
    (hcap : σ.val (Q 7) + 8 * xs.length + 2 * (RepairRepresentation.natListWord xs).length + 16 ≤ cap) :
    WExec cap (copyNatListM ε s o Q) σ
      ((appendO σ o (Q 7) (marks (RepairRepresentation.natListWord xs))).seth s
        (pre.length + stp ε * (RepairRepresentation.natListWord xs).length))
      ((xs.length + 12) * (300 * xs.length + 300) + 64 * (RepairRepresentation.natListWord xs).length + 64) := by
  have hnl : RepairRepresentation.natListWord xs =
      RepairRepresentation.natWord xs.length ++ xs.flatMap RepairRepresentation.natWord := rfl
  have hLm := natBitLength_le_self_succ xs.length
  have hP := two_pow_natBitLength_le xs.length
  have hnwlen := natWord_length xs.length
  have hlenW : (RepairRepresentation.natListWord xs).length =
      (RepairRepresentation.natWord xs.length).length + (xs.flatMap RepairRepresentation.natWord).length := by
    rw [hnl, List.length_append]
  -- the count into `m = Q 0`
  have h1 := readNatM_spec cap ε s (Q 1) (Q 2) (Q 0) (Q 3) (Q 6) (Qne Q (by decide)) (Qne Q (by decide))
    (Qne Q (by decide)) (Qne Q (by decide)) (Qne Q (by decide)) (Qne Q (by decide)) (Qne Q (by decide))
    (Qne Q (by decide)) (Qne Q (by decide)) (Qne Q (by decide)) xs.length pre
    (enc ε (xs.flatMap RepairRepresentation.natWord) ++ rest) σ
    (by simp [hst, hnl, enc_append, List.append_assoc]) hsh
    (hQ 1 (by decide)) (hQ 2 (by decide)) (hQ 3 (by decide)) (hQ 6 (by decide))
    (by rw [hQ 0 (by decide), pow_succ]; omega)
  set σ1 := (σ.seth s (pre.length + stp ε * (RepairRepresentation.natWord xs.length).length)).setv (Q 0)
    (σ.val (Q 0) + xs.length) with hσ1
  have hσ1v : ∀ i : Fin 9, i ≠ 7 → i ≠ 0 → σ1.val (Q i) = 0 := by
    intro i h7 h0
    simp [σ1, Function.update_apply, Qne Q h0, hQ i h7]
  have hσ1m : σ1.val (Q 0) = xs.length := by simp [σ1, hQ 0 (by decide)]
  have hσ17 : σ1.val (Q 7) = σ.val (Q 7) := by
    simp [σ1, Function.update_apply, Qne Q (show (7 : Fin 9) ≠ 0 by decide)]
  -- rewrite the count
  have h2 := writeNatM_spec cap o (listRegs Q) σ1
    (by simpa [listRegs] using hσ1v 1 (by decide) (by decide))
    (by simpa [listRegs] using hσ1v 2 (by decide) (by decide))
    (by simpa [listRegs] using hσ1v 3 (by decide) (by decide))
    (by simpa [listRegs] using hσ1v 4 (by decide) (by decide))
    (by simpa [listRegs] using hσ1v 5 (by decide) (by decide))
    (by simpa [listRegs] using hσ1v 6 (by decide) (by decide))
    (by simp [σ1, Function.update_apply, Ne.symm hso, ho])
    (by show σ1.val (Q 0) + σ1.val (Q 7) + 6 * natBitLength (σ1.val (Q 0)) + 6 ≤ cap
        rw [hσ1m, hσ17]; omega)
  have hR0 : (listRegs Q) 0 = Q 0 := rfl
  have hR7 : (listRegs Q) 7 = Q 7 := rfl
  rw [hR0, hR7, hσ1m] at h2
  set σ2 := appendO σ1 o (Q 7) (marks (RepairRepresentation.natWord xs.length)) with hσ2
  have hσ20 : σ2.val (Q 0) = xs.length := by
    simp only [σ2, appendO_val, Function.update_apply, if_neg (Qne Q (show (0 : Fin 9) ≠ 7 by decide)), hσ1m]
  have hσ27 : σ2.val (Q 7) = σ.val (Q 7) + 2 * (RepairRepresentation.natWord xs.length).length := by
    simp only [σ2, appendO_val, Function.update_self, RepairOrdinary.Streaming.marks_length, hσ17]
  -- the elements
  have h3 := elemLoop_spec cap ε s o hso Q xs (pre ++ enc ε (RepairRepresentation.natWord xs.length)) rest σ2
    (by simp [σ2, σ1, Function.update_apply, hso, hst, hnl, enc_append, List.append_assoc])
    (by simp [σ2, σ1, Function.update_apply, hso, enc_length])
    (by simp [σ2, σ1, Function.update_apply, Ne.symm hso, ho] <;> ring)
    hσ20
    (by simp [σ2, Function.update_apply, Qne Q (show (1 : Fin 9) ≠ 7 by decide), hσ1v 1 (by decide) (by decide)])
    (by simp [σ2, Function.update_apply, Qne Q (show (2 : Fin 9) ≠ 7 by decide), hσ1v 2 (by decide) (by decide)])
    (by rw [hσ20]; omega)
    (by rw [hσ27]; omega)
  refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 h3)) ?_ ?_
  · apply WState.eq
    · funext j
      by_cases hjs : j = s
      · subst hjs; simp [σ2, σ1, Function.update_apply, hso, enc_length, hlenW]; ring
      · by_cases hjo : j = o
        · subst hjo; simp [σ2, σ1, Function.update_apply, hjs, Ne.symm hso, hnl, marks]; ring
        · simp [σ2, σ1, Function.update_apply, hjs, hjo]
    · funext j
      by_cases hjo : j = o
      · subst hjo; simp [σ2, σ1, Function.update_apply, Ne.symm hso, hnl, marks]
      · simp [σ2, σ1, Function.update_apply, hjo]
    · funext j
      by_cases hj0 : j = Q 0
      · subst hj0; simp [Function.update_apply, hQ 0 (by decide)]
      · by_cases hj7 : j = Q 7
        · subst hj7; simp [σ2, σ1, Function.update_apply, hj0, Qne Q (show (7 : Fin 9) ≠ 0 by decide), hnl,
            marks]; ring
        · simp [σ2, σ1, Function.update_apply, hj0, hj7]
    · simp [σ2, σ1]
  · skip
    have hb1 : (natBitLength xs.length + 2) * (40 * 2 ^ natBitLength xs.length + 40) ≤
        (xs.length + 3) * (80 * xs.length + 120) := by
      have : 40 * 2 ^ natBitLength xs.length + 40 ≤ 80 * xs.length + 120 := by omega
      exact Nat.mul_le_mul (by omega) this
    have hb2 : (natBitLength xs.length + 10) * (100 * xs.length + 200) ≤ (xs.length + 11) * (100 * xs.length + 200) :=
      Nat.mul_le_mul_right _ (by omega)
    rw [hlenW]
    nlinarith

end NearCubicWires.WireExponent3_5.PrimAsm.CopyNat
