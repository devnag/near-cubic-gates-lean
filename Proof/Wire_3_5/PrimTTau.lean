import Proof.Wire_3_5.FinalPassWordMul
import Proof.Wire_3_5.FinalPassWordAux
import Proof.Wire_3_5.FinalPassHashTable
import Proof.Wire_3_5.GFTrace

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimT
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.WireExponent3_5.GF2 NearCubicWires.WireExponent3_5.GF NearCubicWires.WireExponent3_5.FinalPass.Tm

/-! ## The references -/

/-- The trace fold with the machine's product (`fmulShift`). -/
def trW (p ℓ a k : ℕ) : ℕ × ℕ :=
  (List.range k).foldl (fun st _ => (st.1 ^^^ st.2, fmulShift p ℓ st.2 st.2)) (0, a)

theorem trW_succ (p ℓ a k : ℕ) :
    trW p ℓ a (k + 1) = ((trW p ℓ a k).1 ^^^ (trW p ℓ a k).2, fmulShift p ℓ (trW p ℓ a k).2 (trW p ℓ a k).2) := by
  unfold trW
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem trW_eq (p ℓ a : ℕ) (hp : ModulusOk p ℓ) (ha : a < 2 ^ ℓ) :
    ∀ k, trW p ℓ a k = (List.range k).foldl (trStep p ℓ) (0, a)
  | 0 => rfl
  | k + 1 => by
    rw [trW_succ, trW_eq p ℓ a hp ha k, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨_, h2, _, _⟩ := trace_fold p ℓ a hp ha k
    have hs := fmulShift_spec p ℓ _ _ hp h2 h2
    have hf := fmul_spec p ℓ _ _ hp h2 h2
    show (_, _) = (_, fmul p ℓ _ _)
    congr 1
    exact rep_injOn p ℓ _ _ hp hs.1 hf.1 (hs.2.trans hf.2.symm)

theorem trW_lt (p ℓ a : ℕ) (hp : ModulusOk p ℓ) (ha : a < 2 ^ ℓ) (k : ℕ) :
    (trW p ℓ a k).1 < 2 ^ ℓ ∧ (trW p ℓ a k).2 < 2 ^ ℓ := by
  rw [trW_eq p ℓ a hp ha]
  exact ⟨(trace_fold p ℓ a hp ha k).1, (trace_fold p ℓ a hp ha k).2.1⟩

theorem trW_trace (p ℓ a : ℕ) (hp : ModulusOk p ℓ) (ha : a < 2 ^ ℓ) : (trW p ℓ a ℓ).1 = GF2.trace p ℓ a := by
  rw [trW_eq p ℓ a hp ha, trace_eq]

/-- The trace is a bit. -/
theorem trace_lt_two (p ℓ a : ℕ) (hc : PrimitiveCert p ℓ) (ha : a < 2 ^ ℓ) : GF2.trace p ℓ a < 2 := by
  rw [traceRef_val p ℓ a hc ha]
  exact ZMod.val_lt _

/-- The mask's bits are the traces' low bits. -/
theorem binary_tau (p ℓ : ℕ) (hc : PrimitiveCert p ℓ) :
    binary ℓ (GF2.tau p ℓ) = (List.range ℓ).map (fun b => (GF2.trace p ℓ (2 ^ b)).testBit 0) := by
  apply List.ext_getElem
  · simp [binary_length]
  · intro i h1 h2
    have hi : i < ℓ := by simpa [binary_length] using h1
    rw [binary_getElem, testBit_tau, List.getElem_map, List.getElem_range]
    have hlt := trace_lt_two p ℓ (2 ^ i) hc (Nat.pow_lt_pow_right (by norm_num) hi)
    interval_cases h : GF2.trace p ℓ (2 ^ i) <;> simp [hi, h]

/-- The zero word with bit `b` set. -/
theorem binary_set_two_pow (ℓ b : ℕ) : (binary ℓ 0).set b true = binary ℓ (2 ^ b) := by
  apply List.ext_getElem
  · simp [binary_length]
  · intro i h1 h2
    rw [List.getElem_set, binary_getElem, binary_getElem, Nat.testBit_two_pow]
    by_cases hi : b = i
    · subst hi; simp
    · simp [hi, Ne.symm hi]

theorem binary_reset_two_pow (ℓ b : ℕ) : (binary ℓ (2 ^ b)).set b false = binary ℓ 0 := by
  apply List.ext_getElem
  · simp [binary_length]
  · intro i h1 h2
    rw [List.getElem_set, binary_getElem, binary_getElem, Nat.testBit_two_pow]
    by_cases hi : b = i
    · subst hi; simp
    · simp [hi, Ne.symm hi]

/-- The partial mask word after `b` bits. -/
def maskBits (p ℓ b : ℕ) : List Bool :=
  (List.range b).map (fun j => (GF2.trace p ℓ (2 ^ j)).testBit 0) ++ List.replicate (ℓ - b) false

theorem maskBits_length (p ℓ b : ℕ) (hb : b ≤ ℓ) : (maskBits p ℓ b).length = ℓ := by
  simp [maskBits]; omega

theorem maskBits_zero (p ℓ : ℕ) : maskBits p ℓ 0 = binary ℓ 0 := by
  simp [maskBits, binary_zero']

theorem maskBits_set (p ℓ b : ℕ) (hb : b < ℓ) (v : Bool) (hv : v = (GF2.trace p ℓ (2 ^ b)).testBit 0) :
    (maskBits p ℓ b).set b v = maskBits p ℓ (b + 1) := by
  unfold maskBits
  rw [List.set_append_right _ _ (by simp), List.length_map, List.length_range, Nat.sub_self]
  obtain ⟨m, hm⟩ : ∃ m, ℓ - b = m + 1 := ⟨ℓ - b - 1, by omega⟩
  rw [hm, List.replicate_succ, List.set_cons_zero, List.range_succ, List.map_append, List.append_assoc]
  simp only [List.map_cons, List.map_nil, List.singleton_append, hv]
  rw [show ℓ - (b + 1) = m by omega]

theorem maskBits_full (p ℓ : ℕ) (hc : PrimitiveCert p ℓ) : maskBits p ℓ ℓ = binary ℓ (GF2.tau p ℓ) := by
  rw [binary_tau p ℓ hc]
  simp [maskBits]

/-! ## The word program -/

section Prog
variable {ns nr : ℕ} (Sm : Fin 7 ↪ Fin (ns + 1)) (Rg : Fin 9 ↪ Fin nr)

/-- Write bit `v` at position `b` of `CUR` (head at `0` before and after). -/
def setBitW (v : Bool) : WM ns nr :=
  .seq (advC (Sm 2) (Rg 5) (Rg 7) (Rg 8)) (.seq (.fwd (Sm 2)) (.seq (.wr (Sm 2) v) (.seq (.bwd (Sm 2))
    (retC (Sm 2) (Rg 5) (Rg 7) (Rg 8)))))

/-- One step of the trace: `S ^= T; T := T·T`. -/
def innerW : WM ns nr :=
  .seq (mapPass xorOut keepS (Sm 6) (Sm 3) (Rg 0) (Rg 2)) (.seq (mapPass copyOut keepS (Sm 4) (Sm 3) (Rg 0) (Rg 2))
    (.seq (mapPass zeroOut keepS (Sm 5) (Sm 3) (Rg 0) (Rg 2))
    (.seq (fmulW (Sm 4) (Sm 5) (Sm 3) (Sm 0) (Rg 0) (Rg 1) (Rg 2) (Rg 3))
    (.seq (mapPass copyOut keepS (Sm 3) (Sm 5) (Rg 0) (Rg 2)) (.dec (Rg 6))))))

/-- The trace of `CUR` into `S`. -/
def traceW : WM ns nr :=
  .seq (mapPass copyOut keepS (Sm 3) (Sm 2) (Rg 0) (Rg 2)) (.seq (mapPass zeroOut keepS (Sm 6) (Sm 2) (Rg 0) (Rg 2))
    (.seq (FinalPass.Hash4.wcopyR (Rg 4) (Rg 6) (Rg 7)) (.whr (Rg 6) (innerW Sm Rg))))

/-- Bit `b` of the mask: the trace's low bit (`OUT`'s head at the bit's mark). -/
def outBitW : WM ns nr :=
  .seq (.fwd (Sm 6)) (.seq (.ifs (Sm 6) (.seq (.fwd (Sm 1)) (.seq (.wr (Sm 1) true) (.bwd (Sm 1)))) .skip)
    (.bwd (Sm 6)))

/-- One bit of the mask. -/
def bodyW : WM ns nr :=
  .seq (setBitW Sm Rg true) (.seq (traceW Sm Rg) (.seq (outBitW Sm) (.seq (setBitW Sm Rg false)
    (.seq (.fwd (Sm 1)) (.seq (.fwd (Sm 1)) (.inc (Rg 5)))))))

/-- **The mask program.** -/
def tauW : WM ns nr :=
  .seq (.whs (Sm 1) (bodyW Sm Rg)) (.seq (retC (Sm 1) (Rg 5) (Rg 7) (Rg 8)) (WM.clear (Rg 5)))

/-- The streams and registers the program touches. -/
def tauS (i : Fin (ns + 1)) : Prop := ∃ j, Sm j = i
def tauR (r : Fin nr) : Prop := ∃ j, Rg j = r
/-- The streams and registers of the trace. -/
def innerS (i : Fin (ns + 1)) : Prop := i = Sm 3 ∨ i = Sm 4 ∨ i = Sm 5 ∨ i = Sm 6
def innerR (r : Fin nr) : Prop := r = Rg 0 ∨ r = Rg 1 ∨ r = Rg 2 ∨ r = Rg 3 ∨ r = Rg 6

theorem mulLayout : MulLayout (Sm 4) (Sm 5) (Sm 3) (Sm 0) (Rg 0) (Rg 1) (Rg 2) (Rg 3) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp

end Prog

/-! ## The trace step -/

section Inner
variable {ns nr : ℕ} (cap : ℕ) (Sm : Fin 7 ↪ Fin (ns + 1)) (Rg : Fin 9 ↪ Fin nr)

theorem frame_binary' (ℓ a : ℕ) : frame (binary ℓ a) = frameP (binary ℓ a) ++ false :: [] := frame_binary ℓ a

/-- The inner invariant after `k` squarings of `a`. -/
def InnerInv (ℓ p a k : ℕ) (σ : WState ns nr) : Prop :=
  σ.st (Sm 0) = frame (binary ℓ p) ∧ σ.sh (Sm 0) = 0 ∧
  σ.st (Sm 3) = frame (binary ℓ (trW p ℓ a k).2) ∧ σ.sh (Sm 3) = 0 ∧
  σ.st (Sm 6) = frame (binary ℓ (trW p ℓ a k).1) ∧ σ.sh (Sm 6) = 0 ∧
  (∃ y, σ.st (Sm 4) = frame (binary ℓ y)) ∧ σ.sh (Sm 4) = 0 ∧
  (∃ c, σ.st (Sm 5) = frame (binary ℓ c)) ∧ σ.sh (Sm 5) = 0 ∧
  σ.val (Rg 0) = 0 ∧ σ.val (Rg 1) = 0 ∧ σ.val (Rg 2) = 0 ∧ σ.val (Rg 3) = 0

def innerCost (ℓ : ℕ) : ℕ := 4 * (ℓ * 41 + 3) + (ℓ * (mulStepCost ℓ + 2) + 14 * ℓ + 3) + 1 + 5

/-- **One trace step**: `S ^= T`, `T := T·T` (the shift-and-XOR product), `I -= 1`. -/
theorem inner_spec (ℓ p a k : ℕ) (hℓ : 1 ≤ ℓ) (hcap : 2 * ℓ + 2 ≤ cap) (σ : WState ns nr)
    (hI : InnerInv Sm Rg ℓ p a k σ) (hi : σ.val (Rg 6) ≤ cap) :
    ∃ τ, WExec cap (innerW Sm Rg) σ τ (innerCost ℓ) ∧ InnerInv Sm Rg ℓ p a (k + 1) τ ∧
      τ.val (Rg 6) = σ.val (Rg 6) - 1 ∧ WFrame (innerS Sm) (innerR Rg) σ τ := by
  obtain ⟨hP, hhP, hT, hhT, hS, hhS, ⟨y, hY⟩, hhY, ⟨c, hA⟩, hhA, hF, hG, hR, hRY⟩ := hI
  set s := (trW p ℓ a k).1 with hs
  set t := (trW p ℓ a k).2 with ht
  -- 1: `S ^= T`
  have s1 := mapPass_spec cap xorOut keepS (Sm 6) (Sm 3) (Rg 0) (Rg 2) (by simp) (by simp) (by omega)
    (binary ℓ s) (binary ℓ t) [] [false] false σ (by simp [binary_length]) (by rw [hS, frame_binary'])
    hhS (by rw [hT, frame_binary']) hhT (by simp [hF]) hR (by simp [binary_length]; omega)
  rw [mapS_xor _ _ _ (by simp [binary_length]), ← binary_xor] at s1
  obtain ⟨σ1, hσ1⟩ : ∃ τ : WState ns nr,
      τ = (σ.sets (Sm 6) (frameP (binary ℓ (s ^^^ t)) ++ false :: [])).setv (Rg 0) (false).toNat := ⟨_, rfl⟩
  rw [← hσ1] at s1
  -- 2: `Y := T`
  have s2 := mapPass_spec cap copyOut keepS (Sm 4) (Sm 3) (Rg 0) (Rg 2) (by simp) (by simp) (by omega)
    (binary ℓ y) (binary ℓ t) [] [false] false σ1 (by simp [binary_length])
    (by rw [hσ1]; simp [Function.update_apply, hY, frame_binary']) (by rw [hσ1]; simp [Function.update_apply, hhY])
    (by rw [hσ1]; simp [Function.update_apply, hT, frame_binary']) (by rw [hσ1]; simp [Function.update_apply, hhT])
    (by rw [hσ1]; simp) (by rw [hσ1]; simp [Function.update_apply, hR]) (by simp [binary_length]; omega)
  rw [mapS_copy _ _ _ (by simp [binary_length])] at s2
  obtain ⟨σ2, hσ2⟩ : ∃ τ : WState ns nr,
      τ = (σ1.sets (Sm 4) (frameP (binary ℓ t) ++ false :: [])).setv (Rg 0) (false).toNat := ⟨_, rfl⟩
  rw [← hσ2] at s2
  -- 3: `ACC := 0`
  have s3 := mapPass_spec cap zeroOut keepS (Sm 5) (Sm 3) (Rg 0) (Rg 2) (by simp) (by simp) (by omega)
    (binary ℓ c) (binary ℓ t) [] [false] false σ2 (by simp [binary_length])
    (by rw [hσ2, hσ1]; simp [Function.update_apply, hA, frame_binary'])
    (by rw [hσ2, hσ1]; simp [Function.update_apply, hhA])
    (by rw [hσ2, hσ1]; simp [Function.update_apply, hT, frame_binary'])
    (by rw [hσ2, hσ1]; simp [Function.update_apply, hhT])
    (by rw [hσ2]; simp) (by rw [hσ2, hσ1]; simp [Function.update_apply, hR]) (by simp [binary_length]; omega)
  rw [mapS_zero _ _ _ (by simp [binary_length]), binary_length, ← binary_zero] at s3
  obtain ⟨σ3, hσ3⟩ : ∃ τ : WState ns nr,
      τ = (σ2.sets (Sm 5) (frameP (binary ℓ 0) ++ false :: [])).setv (Rg 0) (false).toNat := ⟨_, rfl⟩
  rw [← hσ3] at s3
  -- 4: `ACC := T·T` (`T` is the product's state)
  have hM : MulInv (Sm 4) (Sm 5) (Sm 3) (Sm 0) (Rg 0) (Rg 1) (Rg 2) (Rg 3) ℓ p t 0 t 0 σ3 := by
    subst hσ3 hσ2 hσ1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [Function.update_apply, hP, hhP, hT, hhT, hhY, hhA, hF, hG, hR, hRY, frame_binary']
  obtain ⟨σ4, s4, hM4, hF4⟩ := fmulW_spec cap (Sm 4) (Sm 5) (Sm 3) (Sm 0) (Rg 0) (Rg 1) (Rg 2) (Rg 3) (mulLayout Sm Rg)
    ℓ p t t hℓ hcap σ3 hM
  obtain ⟨m4Y, m4hY, m4RY, m4A, m4hA, m4S, m4hS, m4P, m4hP, m4F, m4G, m4R⟩ := hM4
  -- 5: `T := ACC`
  have s5 := mapPass_spec cap copyOut keepS (Sm 3) (Sm 5) (Rg 0) (Rg 2) (by simp) (by simp) (by omega)
    (binary ℓ (mulFrom p ℓ t 0 ℓ 0 t).2) (binary ℓ (fmulShift p ℓ t t)) [] [false] false σ4
    (by simp [binary_length]) (by rw [m4S, frame_binary']) m4hS (by rw [m4A, frame_binary']) m4hA
    (by rw [m4F]; rfl) m4R (by simp [binary_length]; omega)
  rw [mapS_copy _ _ _ (by simp [binary_length])] at s5
  obtain ⟨σ5, hσ5⟩ : ∃ τ : WState ns nr,
      τ = (σ4.sets (Sm 3) (frameP (binary ℓ (fmulShift p ℓ t t)) ++ false :: [])).setv (Rg 0) (false).toNat :=
    ⟨_, rfl⟩
  rw [← hσ5] at s5
  -- 6: `I -= 1`
  have hI5 : σ5.val (Rg 6) = σ.val (Rg 6) := by
    have h6 := hF4.2.1 (Rg 6) (by simp [mulR])
    rw [hσ5]; simp [h6, hσ3, hσ2, hσ1]
  have s6 := WExec.dec (cap := cap) (Rg 6) σ5 (by rw [hI5]; exact hi)
  refine ⟨_, WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 s6)))))
    (by unfold innerCost; simp only [binary_length]; omega), ?_, ?_, ?_⟩
  · have e5 := hF4.1 (Sm 6) (by simp [mulS])
    have e0 := hF4.1 (Sm 0) (by simp [mulS])
    subst hσ5 hσ3 hσ2 hσ1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨t, ?_⟩, ?_, ⟨fmulShift p ℓ t t, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [Function.update_apply, trW_succ, frame_binary', m4P, m4hP, m4Y, m4hY, m4A, m4hA, m4S, m4hS, m4F, m4G,
        m4R, m4RY, e5.1, e5.2, ← hs, ← ht, hhS, hhT, hP, hhP]
  · rw [hI5]
    simp
  · have hF := hF4.mono (S' := innerS Sm) (Rg' := innerR Rg)
      (fun i hi => by rcases hi with h | h | h <;> simp [innerS, h])
      (fun r hr => by rcases hr with h | h | h | h <;> simp [innerR, h])
    have f1 : WFrame (innerS Sm) (innerR Rg) σ σ1 := by
      rw [hσ1]; exact (frame_sets _ _ σ _ _ (by simp [innerS])).trans (frame_setv _ _ _ _ _ (by simp [innerR]))
    have f2 : WFrame (innerS Sm) (innerR Rg) σ1 σ2 := by
      rw [hσ2]; exact (frame_sets _ _ σ1 _ _ (by simp [innerS])).trans (frame_setv _ _ _ _ _ (by simp [innerR]))
    have f3 : WFrame (innerS Sm) (innerR Rg) σ2 σ3 := by
      rw [hσ3]; exact (frame_sets _ _ σ2 _ _ (by simp [innerS])).trans (frame_setv _ _ _ _ _ (by simp [innerR]))
    have f5 : WFrame (innerS Sm) (innerR Rg) σ4 σ5 := by
      rw [hσ5]; exact (frame_sets _ _ σ4 _ _ (by simp [innerS])).trans (frame_setv _ _ _ _ _ (by simp [innerR]))
    exact f1.trans (f2.trans (f3.trans (hF.trans (f5.trans (frame_setv _ _ _ _ _ (by simp [innerR]))))))

end Inner

/-! ## The trace -/

section Trace
variable {ns nr : ℕ} (cap : ℕ) (Sm : Fin 7 ↪ Fin (ns + 1)) (Rg : Fin 9 ↪ Fin nr)

theorem innerLoop_spec (ℓ p a : ℕ) (hℓ : 1 ≤ ℓ) (hcap : 2 * ℓ + 2 ≤ cap) :
    ∀ (n k : ℕ) (σ : WState ns nr), k + n = ℓ → InnerInv Sm Rg ℓ p a k σ → σ.val (Rg 6) = n →
      ∃ τ, WExec cap (.whr (Rg 6) (innerW Sm Rg)) σ τ (n * (innerCost ℓ + 2) + 1) ∧
        InnerInv Sm Rg ℓ p a ℓ τ ∧ τ.val (Rg 6) = 0 ∧ WFrame (innerS Sm) (innerR Rg) σ τ
  | 0, k, σ, hk, hI, hn => by
    obtain rfl : k = ℓ := by omega
    exact ⟨σ, WExec.mono (WExec.whrF hn) (by simp), hI, hn, WFrame.refl _ _ σ⟩
  | n + 1, k, σ, hk, hI, hn => by
    obtain ⟨τ1, h1, hI1, hv1, hF1⟩ := inner_spec cap Sm Rg ℓ p a k hℓ hcap σ hI (by omega)
    obtain ⟨τ, h2, hI2, hv2, hF2⟩ := innerLoop_spec ℓ p a hℓ hcap n (k + 1) τ1 (by omega) hI1 (by omega)
    exact ⟨τ, WExec.mono (WExec.whrT (by omega) h1 h2) (by rw [Nat.succ_mul]; omega), hI2, hv2, hF1.trans hF2⟩

def traceCost (ℓ : ℕ) : ℕ := 2 * (ℓ * 41 + 3) + (18 * ℓ + 3) + (ℓ * (innerCost ℓ + 2) + 1) + 3

/-- **The trace of `CUR`**: `S := Tr(a)` (`ℓ` steps), with `CUR = a` kept. -/
theorem trace_spec (ℓ p a : ℕ) (hℓ : 1 ≤ ℓ) (hcap : 2 * ℓ + 2 ≤ cap)
    (σ : WState ns nr) (hP : σ.st (Sm 0) = frame (binary ℓ p)) (hhP : σ.sh (Sm 0) = 0)
    (hC : σ.st (Sm 2) = frame (binary ℓ a)) (hhC : σ.sh (Sm 2) = 0)
    (t0 y0 c0 s0 : ℕ) (hT : σ.st (Sm 3) = frame (binary ℓ t0)) (hhT : σ.sh (Sm 3) = 0)
    (hY : σ.st (Sm 4) = frame (binary ℓ y0)) (hhY : σ.sh (Sm 4) = 0)
    (hA : σ.st (Sm 5) = frame (binary ℓ c0)) (hhA : σ.sh (Sm 5) = 0)
    (hS : σ.st (Sm 6) = frame (binary ℓ s0)) (hhS : σ.sh (Sm 6) = 0)
    (hF : σ.val (Rg 0) = 0) (hG : σ.val (Rg 1) = 0) (hR : σ.val (Rg 2) = 0) (hRY : σ.val (Rg 3) = 0)
    (hL : σ.val (Rg 4) = ℓ) (hI : σ.val (Rg 6) = 0) (hT1 : σ.val (Rg 7) = 0) :
    ∃ τ, WExec cap (traceW Sm Rg) σ τ (traceCost ℓ) ∧ InnerInv Sm Rg ℓ p a ℓ τ ∧ τ.val (Rg 6) = 0 ∧
      WFrame (innerS Sm) (innerR Rg) σ τ := by
  -- 1: `T := CUR`
  have s1 := mapPass_spec cap copyOut keepS (Sm 3) (Sm 2) (Rg 0) (Rg 2) (by simp) (by simp) (by omega)
    (binary ℓ t0) (binary ℓ a) [] [false] false σ (by simp [binary_length]) (by rw [hT, frame_binary'])
    hhT (by rw [hC, frame_binary']) hhC (by simp [hF]) hR (by simp [binary_length]; omega)
  rw [mapS_copy _ _ _ (by simp [binary_length])] at s1
  obtain ⟨σ1, hσ1⟩ : ∃ τ : WState ns nr,
      τ = (σ.sets (Sm 3) (frameP (binary ℓ a) ++ false :: [])).setv (Rg 0) (false).toNat := ⟨_, rfl⟩
  rw [← hσ1] at s1
  -- 2: `S := 0`
  have s2 := mapPass_spec cap zeroOut keepS (Sm 6) (Sm 2) (Rg 0) (Rg 2) (by simp) (by simp) (by omega)
    (binary ℓ s0) (binary ℓ a) [] [false] false σ1 (by simp [binary_length])
    (by rw [hσ1]; simp [Function.update_apply, hS, frame_binary']) (by rw [hσ1]; simp [Function.update_apply, hhS])
    (by rw [hσ1]; simp [Function.update_apply, hC, frame_binary']) (by rw [hσ1]; simp [Function.update_apply, hhC])
    (by rw [hσ1]; simp) (by rw [hσ1]; simp [Function.update_apply, hR]) (by simp [binary_length]; omega)
  rw [mapS_zero _ _ _ (by simp [binary_length]), binary_length, ← binary_zero] at s2
  obtain ⟨σ2, hσ2⟩ : ∃ τ : WState ns nr,
      τ = (σ1.sets (Sm 6) (frameP (binary ℓ 0) ++ false :: [])).setv (Rg 0) (false).toNat := ⟨_, rfl⟩
  rw [← hσ2] at s2
  -- 3: `I := L`
  have s3 := FinalPass.Hash4.wcopyR_spec cap (Rg 4) (Rg 6) (Rg 7) (by simp) (by simp) (by simp) σ2
    (by rw [hσ2, hσ1]; simp [Function.update_apply, hI]) (by rw [hσ2, hσ1]; simp [Function.update_apply, hT1])
    (by rw [hσ2, hσ1]; simp [Function.update_apply, hL]; omega)
  have hL2 : σ2.val (Rg 4) = ℓ := by rw [hσ2, hσ1]; simp [Function.update_apply, hL]
  rw [hL2] at s3
  -- 4: the loop
  have hI3 : InnerInv Sm Rg ℓ p a 0 (σ2.setv (Rg 6) ℓ) := by
    subst hσ2 hσ1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨y0, ?_⟩, ?_, ⟨c0, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [Function.update_apply, trW, frame_binary', hP, hhP, hhT, hhS, hY, hhY, hA, hhA, hG, hR, hRY]
  obtain ⟨τ, s4, hI4, hv4, hF4⟩ := innerLoop_spec cap Sm Rg ℓ p a hℓ hcap ℓ 0 (σ2.setv (Rg 6) ℓ) (by omega) hI3
    (by simp)
  have f12 : WFrame (innerS Sm) (innerR Rg) σ σ2 := by
    rw [hσ2, hσ1]
    exact (((frame_sets _ _ σ _ _ (by simp [innerS])).trans (frame_setv _ _ _ _ _ (by simp [innerR]))).trans
      (frame_sets _ _ _ _ _ (by simp [innerS]))).trans (frame_setv _ _ _ _ _ (by simp [innerR]))
  have hc : (binary ℓ t0).length * 41 + 3 + 1 + (ℓ * 41 + 3 + 1 + (18 * ℓ + 3 + 1 + (ℓ * (innerCost ℓ + 2) + 1))) ≤
      traceCost ℓ := by unfold traceCost; simp only [binary_length]; omega
  exact ⟨τ, WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) hc, hI4, hv4,
    f12.trans ((frame_setv _ _ _ _ _ (by simp [innerR])).trans hF4)⟩

end Trace

/-! ## One bit -/

section Bit
variable {ns nr : ℕ} (cap : ℕ) (Sm : Fin 7 ↪ Fin (ns + 1)) (Rg : Fin 9 ↪ Fin nr)

/-- **Writing bit `b` of `CUR`** (at the register `B = b`), every head and counter back. -/
theorem setBit_spec (ws : List Bool) (b : ℕ) (v : Bool) (hb : b < ws.length) (hcb : 2 * b ≤ cap)
    (σ : WState ns nr) (hC : σ.st (Sm 2) = frameP ws ++ false :: []) (hhC : σ.sh (Sm 2) = 0)
    (hB : σ.val (Rg 5) = b) (hT1 : σ.val (Rg 7) = 0) (hPC : σ.val (Rg 8) = 0) :
    WExec cap (setBitW Sm Rg v) σ (σ.sets (Sm 2) (frameP (ws.set b v) ++ false :: [])) (48 * b + 13) := by
  have a1 := advC_spec cap (Sm 2) (Rg 5) (Rg 7) (Rg 8) (by simp) (by simp) (by simp) b σ hB hT1 (by omega)
    (by rw [hPC]; omega)
  obtain ⟨σa, hσa⟩ : ∃ τ : WState ns nr,
      τ = (σ.seth (Sm 2) (σ.sh (Sm 2) + 2 * b)).setv (Rg 8) (σ.val (Rg 8) + 2 * b) := ⟨_, rfl⟩
  rw [← hσa] at a1
  have a2 := WExec.fwd (cap := cap) (Sm 2) σa
  have a3 := WExec.wr (cap := cap) (Sm 2) v (σa.seth (Sm 2) (σa.sh (Sm 2) + 1))
  obtain ⟨σc, hσc⟩ : ∃ τ : WState ns nr,
      τ = (σa.seth (Sm 2) (σa.sh (Sm 2) + 1)).sets (Sm 2)
        (writeTapeBit ((σa.seth (Sm 2) (σa.sh (Sm 2) + 1)).st (Sm 2)) ((σa.seth (Sm 2) (σa.sh (Sm 2) + 1)).sh (Sm 2)) v) :=
    ⟨_, rfl⟩
  rw [← hσc] at a3
  have a4 := WExec.bwd (cap := cap) (Sm 2) σc
  have hc5 : (σc.seth (Sm 2) (σc.sh (Sm 2) - 1)).val (Rg 5) = b := by rw [hσc, hσa]; simp [hB]
  have hc7 : (σc.seth (Sm 2) (σc.sh (Sm 2) - 1)).val (Rg 7) = 0 := by rw [hσc, hσa]; simp [hT1]
  have hc8 : (σc.seth (Sm 2) (σc.sh (Sm 2) - 1)).val (Rg 8) = 2 * b := by rw [hσc, hσa]; simp [hPC]
  have a5 := retC_spec cap (Sm 2) (Rg 5) (Rg 7) (Rg 8) (by simp) (by simp) (by simp) b
    (σc.seth (Sm 2) (σc.sh (Sm 2) - 1)) hc5 hc7 (by omega) (by rw [hc8]; omega)
  refine WExec.cast cap (WExec.seq a1 (WExec.seq a2 (WExec.seq a3 (WExec.seq a4 a5)))) ?_ (by omega)
  have hw : writeTapeBit (frameP ws ++ false :: []) (2 * b + 1) v = frameP (ws.set b v) ++ false :: [] :=
    frameP_set ws b v _ hb
  subst hσc hσa
  apply WState.eq
  · funext j
    by_cases hj : j = Sm 2
    · subst hj; simp [hhC]
    · simp [Function.update_apply, hj]
  · funext j
    by_cases hj : j = Sm 2
    · subst hj; simp [hC, hhC, hw]
    · simp [Function.update_apply, hj]
  · funext r
    by_cases hr : r = Rg 8
    · subst hr; simp [hPC]
    · simp [Function.update_apply, hr]
  · rfl

/-- **The trace's low bit into the mask**: `OUT`'s bit `b` becomes the low bit of `S`. -/
theorem outBit_spec (ws : List Bool) (b s ℓ : ℕ) (hb : b < ws.length) (hℓ : 1 ≤ ℓ) (σ : WState ns nr)
    (hO : σ.st (Sm 1) = frameP ws ++ false :: []) (hhO : σ.sh (Sm 1) = 2 * b)
    (hS : σ.st (Sm 6) = frame (binary ℓ s)) (hhS : σ.sh (Sm 6) = 0) (hw : ws[b]? = some false) :
    WExec cap (outBitW Sm) σ (σ.sets (Sm 1) (frameP (ws.set b (s.testBit 0)) ++ false :: [])) 10 := by
  have b1 := WExec.fwd (cap := cap) (Sm 6) σ
  have hbit : wbit (σ.seth (Sm 6) (σ.sh (Sm 6) + 1)) (Sm 6) = s.testBit 0 := by
    rw [wsbit_seth, hS, hhS]
    have := read_frame_bit (binary ℓ s) 0 (by simp [binary_length]; omega)
    rw [Nat.mul_zero, Nat.zero_add] at this
    rw [this, binary_getElem]
  have hwr : writeTapeBit (frameP ws ++ false :: []) (2 * b + 1) true = frameP (ws.set b true) ++ false :: [] :=
    frameP_set ws b true _ hb
  cases hsb : s.testBit 0
  · -- the bit stays `false`
    rw [hsb] at hbit
    have b2 := WExec.ifsF (P := .seq (.fwd (Sm 1)) (.seq (.wr (Sm 1) true) (.bwd (Sm 1)))) hbit
      (WExec.skip (cap := cap) (σ.seth (Sm 6) (σ.sh (Sm 6) + 1)))
    have b3 := WExec.bwd (cap := cap) (Sm 6) (σ.seth (Sm 6) (σ.sh (Sm 6) + 1))
    refine WExec.cast cap (WExec.seq b1 (WExec.seq b2 b3)) ?_ (by omega)
    have hset : ws.set b false = ws := by
      have hb' : ws[b] = false := by
        rw [List.getElem?_eq_getElem hb] at hw; exact Option.some.inj hw
      have h := List.set_getElem_self hb
      rwa [hb'] at h
    apply WState.eq
    · funext j
      by_cases hj : j = Sm 6
      · subst hj; simp [hhS]
      · simp [Function.update_apply, hj]
    · funext j
      by_cases hj : j = Sm 1
      · subst hj; simp [hO, hset]
      · simp [Function.update_apply, hj]
    · rfl
    · rfl
  · -- the bit becomes `true`
    rw [hsb] at hbit
    obtain ⟨X, hX⟩ : ∃ τ : WState ns nr, τ = σ.seth (Sm 6) (σ.sh (Sm 6) + 1) := ⟨_, rfl⟩
    rw [← hX] at hbit
    have c1 := WExec.fwd (cap := cap) (Sm 1) X
    have c2 := WExec.wr (cap := cap) (Sm 1) true (X.seth (Sm 1) (X.sh (Sm 1) + 1))
    obtain ⟨Z, hZ⟩ : ∃ τ : WState ns nr, τ = (X.seth (Sm 1) (X.sh (Sm 1) + 1)).sets (Sm 1)
        (writeTapeBit ((X.seth (Sm 1) (X.sh (Sm 1) + 1)).st (Sm 1)) ((X.seth (Sm 1) (X.sh (Sm 1) + 1)).sh (Sm 1)) true) :=
      ⟨_, rfl⟩
    rw [← hZ] at c2
    have c3 := WExec.bwd (cap := cap) (Sm 1) Z
    have b2 := WExec.ifsT (Q := .skip) hbit (WExec.seq c1 (WExec.seq c2 c3))
    have b3 := WExec.bwd (cap := cap) (Sm 6) (Z.seth (Sm 1) (Z.sh (Sm 1) - 1))
    rw [← hX] at b1
    refine WExec.cast cap (WExec.seq b1 (WExec.seq b2 b3)) ?_ (by omega)
    subst hZ hX
    apply WState.eq
    · funext j
      by_cases hj : j = Sm 6
      · subst hj; simp [hhS]
      · by_cases hj1 : j = Sm 1
        · subst hj1; simp [hhO]
        · simp [Function.update_apply, hj, hj1]
    · funext j
      by_cases hj : j = Sm 1
      · subst hj; simp [hO, hhO, hwr]
      · simp [Function.update_apply, hj]
    · rfl
    · rfl

end Bit

/-! ## The mask -/

section Mask
variable {ns nr : ℕ} (cap : ℕ) (Sm : Fin 7 ↪ Fin (ns + 1)) (Rg : Fin 9 ↪ Fin nr)

/-- The outer invariant after `b` bits of the mask. -/
def OuterInv (ℓ p b : ℕ) (σ : WState ns nr) : Prop :=
  σ.st (Sm 0) = frame (binary ℓ p) ∧ σ.sh (Sm 0) = 0 ∧
  σ.st (Sm 1) = frameP (maskBits p ℓ b) ++ false :: [] ∧ σ.sh (Sm 1) = 2 * b ∧
  σ.st (Sm 2) = frame (binary ℓ 0) ∧ σ.sh (Sm 2) = 0 ∧
  (∃ t, σ.st (Sm 3) = frame (binary ℓ t)) ∧ σ.sh (Sm 3) = 0 ∧
  (∃ y, σ.st (Sm 4) = frame (binary ℓ y)) ∧ σ.sh (Sm 4) = 0 ∧
  (∃ c, σ.st (Sm 5) = frame (binary ℓ c)) ∧ σ.sh (Sm 5) = 0 ∧
  (∃ s, σ.st (Sm 6) = frame (binary ℓ s)) ∧ σ.sh (Sm 6) = 0 ∧
  σ.val (Rg 0) = 0 ∧ σ.val (Rg 1) = 0 ∧ σ.val (Rg 2) = 0 ∧ σ.val (Rg 3) = 0 ∧ σ.val (Rg 4) = ℓ ∧
  σ.val (Rg 5) = b ∧ σ.val (Rg 6) = 0 ∧ σ.val (Rg 7) = 0 ∧ σ.val (Rg 8) = 0

def bodyCost (ℓ : ℕ) : ℕ := 2 * (48 * ℓ + 13) + traceCost ℓ + 10 + 25

theorem frame_binary_eq (ℓ a : ℕ) : frameP (binary ℓ a) ++ false :: [] = frame (binary ℓ a) := (frame_binary ℓ a).symm

/-- **One bit of the mask.** -/
theorem body_spec (ℓ p b : ℕ) (hℓ : 1 ≤ ℓ) (hcap : 2 * ℓ + 2 ≤ cap) (hc : PrimitiveCert p ℓ) (hb : b < ℓ)
    (σ : WState ns nr) (hI : OuterInv Sm Rg ℓ p b σ) :
    ∃ τ, WExec cap (bodyW Sm Rg) σ τ (bodyCost ℓ) ∧ OuterInv Sm Rg ℓ p (b + 1) τ ∧ WFrame (tauS Sm) (tauR Rg) σ τ := by
  obtain ⟨hP, hhP, hO, hhO, hC, hhC, ⟨t0, hT⟩, hhT, ⟨y0, hY⟩, hhY, ⟨c0, hA⟩, hhA, ⟨s0, hS⟩, hhS, hF, hG, hR, hRY,
    hL, hB, hI6, hT1, hPC⟩ := hI
  have hp := hc.2.1
  have hab : 2 ^ b < 2 ^ ℓ := Nat.pow_lt_pow_right (by norm_num) hb
  -- 1: `CUR := x^b`
  have s1 := setBit_spec cap Sm Rg (binary ℓ 0) b true (by simp [binary_length]; omega) (by omega) σ
    (by rw [hC, frame_binary']) hhC hB hT1 hPC
  rw [binary_set_two_pow, frame_binary_eq] at s1
  obtain ⟨σ1, hσ1⟩ : ∃ τ : WState ns nr, τ = σ.sets (Sm 2) (frame (binary ℓ (2 ^ b))) := ⟨_, rfl⟩
  rw [← hσ1] at s1
  -- 2: `S := Tr(x^b)`
  obtain ⟨σ2, s2, hI2, hv2, hF2⟩ := trace_spec cap Sm Rg ℓ p (2 ^ b) hℓ hcap σ1
    (by rw [hσ1]; simp [Function.update_apply, hP]) (by rw [hσ1]; simp [hhP])
    (by rw [hσ1]; simp) (by rw [hσ1]; simp [hhC]) t0 y0 c0 s0
    (by rw [hσ1]; simp [Function.update_apply, hT]) (by rw [hσ1]; simp [hhT])
    (by rw [hσ1]; simp [Function.update_apply, hY]) (by rw [hσ1]; simp [hhY])
    (by rw [hσ1]; simp [Function.update_apply, hA]) (by rw [hσ1]; simp [hhA])
    (by rw [hσ1]; simp [Function.update_apply, hS]) (by rw [hσ1]; simp [hhS])
    (by rw [hσ1]; simp [hF]) (by rw [hσ1]; simp [hG]) (by rw [hσ1]; simp [hR]) (by rw [hσ1]; simp [hRY])
    (by rw [hσ1]; simp [hL]) (by rw [hσ1]; simp [hI6]) (by rw [hσ1]; simp [hT1])
  obtain ⟨i2P, i2hP, i2T, i2hT, i2S, i2hS, ⟨y2, i2Y⟩, i2hY, ⟨c2, i2A⟩, i2hA, i2F, i2G, i2R, i2RY⟩ := hI2
  have o2 := hF2.1 (Sm 1) (by simp [innerS])
  have c2' := hF2.1 (Sm 2) (by simp [innerS])
  have v4 := hF2.2.1 (Rg 4) (by simp [innerR])
  have v5 := hF2.2.1 (Rg 5) (by simp [innerR])
  have v7 := hF2.2.1 (Rg 7) (by simp [innerR])
  have v8 := hF2.2.1 (Rg 8) (by simp [innerR])
  rw [trW_trace p ℓ _ hp hab] at i2S
  -- 3: bit `b` of the mask
  have hmb : (maskBits p ℓ b)[b]? = some false := by
    unfold maskBits
    rw [List.getElem?_append_right (by simp)]
    simp only [List.length_map, List.length_range, Nat.sub_self]
    rw [List.getElem?_replicate]
    simp; omega
  have s3 := outBit_spec cap Sm (maskBits p ℓ b) b (GF2.trace p ℓ (2 ^ b)) ℓ
    (by rw [maskBits_length p ℓ b (by omega)]; exact hb) hℓ σ2
    (by rw [o2.1, hσ1]; simp [Function.update_apply, hO]) (by rw [o2.2, hσ1]; simp [hhO]) i2S i2hS hmb
  rw [maskBits_set p ℓ b hb _ rfl] at s3
  obtain ⟨σ3, hσ3⟩ : ∃ τ : WState ns nr, τ = σ2.sets (Sm 1) (frameP (maskBits p ℓ (b + 1)) ++ false :: []) := ⟨_, rfl⟩
  rw [← hσ3] at s3
  -- 4: `CUR := 0`
  have s4 := setBit_spec cap Sm Rg (binary ℓ (2 ^ b)) b false (by simp [binary_length]; omega) (by omega) σ3
    (by rw [hσ3]; simp [Function.update_apply, c2'.1, hσ1, frame_binary']) (by rw [hσ3]; simp [c2'.2, hσ1, hhC])
    (by rw [hσ3]; simp [v5, hσ1, hB]) (by rw [hσ3]; simp [v7, hσ1, hT1]) (by rw [hσ3]; simp [v8, hσ1, hPC])
  rw [binary_reset_two_pow, frame_binary_eq] at s4
  -- 5-7: next mark, next bit
  obtain ⟨σ4, hσ4⟩ : ∃ τ : WState ns nr, τ = σ3.sets (Sm 2) (frame (binary ℓ 0)) := ⟨_, rfl⟩
  rw [← hσ4] at s4
  have s5 := WExec.fwd (cap := cap) (Sm 1) σ4
  obtain ⟨σ5, hσ5⟩ : ∃ τ : WState ns nr, τ = σ4.seth (Sm 1) (σ4.sh (Sm 1) + 1) := ⟨_, rfl⟩
  rw [← hσ5] at s5
  have s6 := WExec.fwd (cap := cap) (Sm 1) σ5
  obtain ⟨σ6, hσ6⟩ : ∃ τ : WState ns nr, τ = σ5.seth (Sm 1) (σ5.sh (Sm 1) + 1) := ⟨_, rfl⟩
  rw [← hσ6] at s6
  -- the fields of `σ6`
  have e_val : ∀ r, σ6.val r = σ2.val r := by intro r; rw [hσ6, hσ5, hσ4, hσ3]; simp
  have e_st : ∀ i, i ≠ Sm 1 → i ≠ Sm 2 → σ6.st i = σ2.st i := by
    intro i h1 h2; rw [hσ6, hσ5, hσ4, hσ3]; simp [Function.update_apply, h1, h2]
  have e_sh : ∀ i, i ≠ Sm 1 → σ6.sh i = σ2.sh i := by
    intro i h1; rw [hσ6, hσ5, hσ4, hσ3]; simp [Function.update_apply, h1]
  have e_O : σ6.st (Sm 1) = frameP (maskBits p ℓ (b + 1)) ++ false :: [] := by rw [hσ6, hσ5, hσ4, hσ3]; simp
  have e_hO : σ6.sh (Sm 1) = 2 * (b + 1) := by
    rw [hσ6, hσ5, hσ4, hσ3]; simp [o2.2, hσ1, hhO]; omega
  have e_C : σ6.st (Sm 2) = frame (binary ℓ 0) := by rw [hσ6, hσ5, hσ4]; simp
  have e_hC : σ6.sh (Sm 2) = 0 := by rw [e_sh _ (by simp), c2'.2, hσ1]; simp [hhC]
  have v5' : σ6.val (Rg 5) = b := by rw [e_val, v5, hσ1]; simp [hB]
  have s7 := WExec.inc (cap := cap) (Rg 5) σ6 (by rw [v5']; omega)
  refine ⟨_, WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 (WExec.seq s6 s7))))))
    (by unfold bodyCost; omega), ?_, ?_⟩
  · rw [v5']
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨(trW p ℓ (2 ^ b) ℓ).2, ?_⟩, ?_, ⟨y2, ?_⟩, ?_, ⟨c2, ?_⟩, ?_,
      ⟨GF2.trace p ℓ (2 ^ b), ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [WState.setv_st, e_st _ (by simp) (by simp), i2P]
    · rw [WState.setv_sh, e_sh _ (by simp), i2hP]
    · rw [WState.setv_st, e_O]
    · rw [WState.setv_sh, e_hO]
    · rw [WState.setv_st, e_C]
    · rw [WState.setv_sh, e_hC]
    · rw [WState.setv_st, e_st _ (by simp) (by simp), i2T]
    · rw [WState.setv_sh, e_sh _ (by simp), i2hT]
    · rw [WState.setv_st, e_st _ (by simp) (by simp), i2Y]
    · rw [WState.setv_sh, e_sh _ (by simp), i2hY]
    · rw [WState.setv_st, e_st _ (by simp) (by simp), i2A]
    · rw [WState.setv_sh, e_sh _ (by simp), i2hA]
    · rw [WState.setv_st, e_st _ (by simp) (by simp), i2S]
    · rw [WState.setv_sh, e_sh _ (by simp), i2hS]
    · simp [e_val, i2F]
    · simp [e_val, i2G]
    · simp [e_val, i2R]
    · simp [e_val, i2RY]
    · simp [e_val, v4, hσ1, hL]
    · simp
    · simp [e_val, hv2]
    · simp [e_val, v7, hσ1, hT1]
    · simp [e_val, v8, hσ1, hPC]
  · have f1 : WFrame (tauS Sm) (tauR Rg) σ σ1 := by rw [hσ1]; exact frame_sets _ _ σ _ _ ⟨2, rfl⟩
    have f2 := hF2.mono (S' := tauS Sm) (Rg' := tauR Rg)
      (fun i hi => by rcases hi with h | h | h | h <;> exact ⟨_, h.symm⟩)
      (fun r hr => by rcases hr with h | h | h | h | h <;> exact ⟨_, h.symm⟩)
    have f3 : WFrame (tauS Sm) (tauR Rg) σ2 σ3 := by rw [hσ3]; exact frame_sets _ _ σ2 _ _ ⟨1, rfl⟩
    have f4 : WFrame (tauS Sm) (tauR Rg) σ3 σ4 := by rw [hσ4]; exact frame_sets _ _ σ3 _ _ ⟨2, rfl⟩
    have f5 : WFrame (tauS Sm) (tauR Rg) σ4 σ5 := by rw [hσ5]; exact frame_seth _ _ _ _ _ ⟨1, rfl⟩
    have f6 : WFrame (tauS Sm) (tauR Rg) σ5 σ6 := by rw [hσ6]; exact frame_seth _ _ _ _ _ ⟨1, rfl⟩
    exact f1.trans (f2.trans (f3.trans (f4.trans (f5.trans (f6.trans (frame_setv _ _ _ _ _ ⟨5, rfl⟩))))))

theorem outerLoop_spec (ℓ p : ℕ) (hℓ : 1 ≤ ℓ) (hcap : 2 * ℓ + 2 ≤ cap) (hc : PrimitiveCert p ℓ) :
    ∀ (n b : ℕ) (σ : WState ns nr), b + n = ℓ → OuterInv Sm Rg ℓ p b σ →
      ∃ τ, WExec cap (.whs (Sm 1) (bodyW Sm Rg)) σ τ (n * (bodyCost ℓ + 2) + 1) ∧ OuterInv Sm Rg ℓ p ℓ τ ∧
        WFrame (tauS Sm) (tauR Rg) σ τ
  | 0, b, σ, hb, hI => by
    obtain rfl : b = ℓ := by omega
    refine ⟨σ, WExec.mono (WExec.whsF ?_) (by simp), hI, WFrame.refl _ _ σ⟩
    unfold wbit
    rw [hI.2.2.1, hI.2.2.2.1, ← frame_eq_frameP]
    have := read_frame_end (maskBits p b b)
    rwa [maskBits_length p b b le_rfl] at this
  | n + 1, b, σ, hb, hI => by
    have hread : wbit σ (Sm 1) = true := by
      unfold wbit
      rw [hI.2.2.1, hI.2.2.2.1, ← frame_eq_frameP]
      exact read_frame_mark _ _ (by rw [maskBits_length p ℓ b (by omega)]; omega)
    obtain ⟨τ1, h1, hI1, hF1⟩ := body_spec cap Sm Rg ℓ p b hℓ hcap hc (by omega) σ hI
    obtain ⟨τ, h2, hI2, hF2⟩ := outerLoop_spec ℓ p hℓ hcap hc n (b + 1) τ1 (by omega) hI1
    exact ⟨τ, WExec.mono (WExec.whsT hread h1 h2) (by rw [Nat.succ_mul]; omega), hI2, hF1.trans hF2⟩

def tauCost (ℓ : ℕ) : ℕ := ℓ * (bodyCost ℓ + 2) + 1 + 1 + (22 * ℓ + 3) + 1 + (3 * ℓ + 1)

theorem tauW_spec (ℓ p : ℕ) (hc : PrimitiveCert p ℓ) (hcap : 2 * ℓ + 2 ≤ cap) (σ : WState ns nr)
    (hP : σ.st (Sm 0) = frame (binary ℓ p)) (hhP : σ.sh (Sm 0) = 0)
    (hO : σ.st (Sm 1) = frame (binary ℓ 0)) (hhO : σ.sh (Sm 1) = 0)
    (hC : σ.st (Sm 2) = frame (binary ℓ 0)) (hhC : σ.sh (Sm 2) = 0)
    (t0 y0 c0 s0 : ℕ) (hT : σ.st (Sm 3) = frame (binary ℓ t0)) (hhT : σ.sh (Sm 3) = 0)
    (hY : σ.st (Sm 4) = frame (binary ℓ y0)) (hhY : σ.sh (Sm 4) = 0)
    (hA : σ.st (Sm 5) = frame (binary ℓ c0)) (hhA : σ.sh (Sm 5) = 0)
    (hS : σ.st (Sm 6) = frame (binary ℓ s0)) (hhS : σ.sh (Sm 6) = 0)
    (hR0 : ∀ j : Fin 9, j ≠ 4 → σ.val (Rg j) = 0) (hL : σ.val (Rg 4) = ℓ) :
    ∃ τ, WExec cap (tauW Sm Rg) σ τ (tauCost ℓ) ∧
      τ.st (Sm 1) = frame (binary ℓ (GF2.tau p ℓ)) ∧ τ.sh (Sm 1) = 0 ∧
      τ.st (Sm 0) = σ.st (Sm 0) ∧ (∀ j : Fin 7, τ.sh (Sm j) = 0) ∧
      τ.val (Rg 4) = ℓ ∧ (∀ j : Fin 9, j ≠ 4 → τ.val (Rg j) = 0) ∧ WFrame (tauS Sm) (tauR Rg) σ τ := by
  have hℓ := hc.1
  have hI0 : OuterInv Sm Rg ℓ p 0 σ := by
    refine ⟨hP, hhP, ?_, by simp [hhO], hC, hhC, ⟨t0, hT⟩, hhT, ⟨y0, hY⟩, hhY, ⟨c0, hA⟩, hhA, ⟨s0, hS⟩, hhS,
      hR0 0 (by decide), hR0 1 (by decide), hR0 2 (by decide), hR0 3 (by decide), hL, hR0 5 (by decide),
      hR0 6 (by decide), hR0 7 (by decide), hR0 8 (by decide)⟩
    rw [hO, maskBits_zero, frame_binary']
  obtain ⟨σ1, h1, hI1, hF1⟩ := outerLoop_spec cap Sm Rg ℓ p hℓ hcap hc ℓ 0 σ (by omega) hI0
  obtain ⟨i1P, i1hP, i1O, i1hO, i1C, i1hC, _, i1hT, _, i1hY, _, i1hA, _, i1hS, i1F, i1G, i1R, i1RY, i1L, i1B, i1I,
    i1T1, i1PC⟩ := hI1
  have h2 := retC_spec cap (Sm 1) (Rg 5) (Rg 7) (Rg 8) (by simp) (by simp) (by simp) ℓ σ1 i1B i1T1 (by omega)
    (by omega)
  obtain ⟨σ2, hσ2⟩ : ∃ τ : WState ns nr,
      τ = (σ1.seth (Sm 1) (σ1.sh (Sm 1) - 2 * ℓ)).setv (Rg 8) (σ1.val (Rg 8) - 2 * ℓ) := ⟨_, rfl⟩
  rw [← hσ2] at h2
  have h3 := wclear_spec cap (Rg 5) ℓ σ2 (by rw [hσ2]; simp [i1B]) (by rw [hσ2]; simp [i1B]; omega)
  refine ⟨_, WExec.mono (WExec.seq h1 (WExec.seq h2 h3)) (by unfold tauCost; omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [WState.setv_st, hσ2]; simp [i1O, maskBits_full p ℓ hc, frame_binary_eq]
  · rw [WState.setv_sh, hσ2]; simp [i1hO]
  · rw [WState.setv_st, hσ2]; simp [i1P, hP]
  · intro j
    rw [WState.setv_sh, hσ2]
    fin_cases j <;> simp [Function.update_apply, i1hP, i1hO, i1hC, i1hT, i1hY, i1hA, i1hS]
  · rw [hσ2]; simp [i1L]
  · intro j hj
    rw [hσ2]
    fin_cases j <;> simp [Function.update_apply, i1F, i1G, i1R, i1RY, i1I, i1T1, i1PC] at hj ⊢
  · rw [hσ2]
    exact (hF1.trans ((frame_seth _ _ _ _ _ ⟨1, rfl⟩).trans (frame_setv _ _ _ _ _ ⟨8, rfl⟩))).trans
      (frame_setv _ _ _ _ _ ⟨5, rfl⟩)

/-- The mask program's cost: `O(ℓ⁴)`. -/
theorem tauCost_le (ℓ : ℕ) : tauCost ℓ ≤ 250 * (ℓ + 1) ^ 4 := by
  unfold tauCost bodyCost traceCost innerCost mulStepCost
  ring_nf
  omega

end Mask

end NearCubicWires.WireExponent3_5.PrimT
