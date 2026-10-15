import Proof.Gates.CheckedPCPP.MatSem
import Proof.Wire_3_5.PrimAsmWriteNat

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CheckedPCPP

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.WordPrograms NearCubicWires.WireExponent3_5.PrimAsm.WriteNat

variable {ns nr : ℕ} {cap : ℕ}

theorem bits_length_le (n : ℕ) : n.bits.length ≤ n := by
  rw [Nat.size_eq_bits_len, Nat.size_le]; exact Nat.lt_two_pow_self

def bitsLoop (IN : Fin (ns + 1)) (N1 H RB : Fin nr) : WMX ns nr :=
  .whr N1 (.seq (.wm (halveM N1 H RB)) (.ifr RB (.seq (emitL IN (quad true)) (WMX.dec RB)) (emitL IN (quad false))))

theorem OutAt.setv {σ : WState ns nr} {X : Fin (ns + 1)} {w : List Bool} (h : OutAt σ X w) (r : Fin nr) (x : ℕ) :
    OutAt (σ.setv r x) X w := h

theorem OutAt.same {σ τ : WState ns nr} {X : Fin (ns + 1)} {w : List Bool} {S : List (Fin (ns + 1))}
    {Rg : List (Fin nr)} (h : OutAt σ X w) (hs : SameExcept σ τ S Rg) (hX : X ∉ S) : OutAt τ X w := by
  unfold OutAt; rw [hs.st hX, hs.sh hX]; exact h

theorem bitsLoop_runs (IN : Fin (ns + 1)) {N1 H RB : Fin nr} (h1 : N1 ≠ H) (h2 : N1 ≠ RB) (h3 : H ≠ RB)
    (v0 : ℕ) (hcap : v0 ≤ cap) (hcap1 : 1 ≤ cap) (σ0 : WState ns nr) (w : List Bool) :
    ∀ k (σ : WState ns nr), (∃ v done, σ.val N1 = v ∧ v.bits.length = k ∧ v ≤ v0 ∧ v0.bits = done ++ v.bits ∧
      OutAt σ IN (w ++ done.flatMap quad) ∧ σ.val H = 0 ∧ σ.val RB = 0 ∧ SameExcept σ0 σ [IN] [N1, H, RB]) →
    Runs cap (bitsLoop IN N1 H RB) σ (k * (9 * v0 + 27 + 2) + 1)
      (fun τ => τ.val N1 = 0 ∧ τ.val H = 0 ∧ τ.val RB = 0 ∧ OutAt τ IN (w ++ v0.bits.flatMap quad) ∧
        SameExcept σ0 τ [IN] [N1, H, RB]) := by
  refine Runs.whr _ _ _ ?_ ?_
  · rintro σ ⟨v, done, hv, hk, -, hb, ho, hH, hR, hs⟩
    have hv0 : v = 0 := by
      by_contra hne
      rw [bits_step v hne] at hk; simp at hk
    subst hv0
    refine ⟨hv, ⟨hv, hH, hR, ?_, hs⟩⟩
    rw [hb]; simpa [Nat.zero_bits] using ho
  · rintro k σ ⟨v, done, hv, hk, hvle, hb, ho, hH, hR, hs⟩
    have hne : v ≠ 0 := by rintro rfl; simp [Nat.zero_bits] at hk
    refine ⟨by rw [hv]; exact hne, ?_⟩
    have hh := halveM_spec cap N1 H RB h1 h2 h3 σ hH hR (by rw [hv]; omega) hcap1
    rw [hv] at hh
    set σ1 := (σ.setv N1 (v / 2)).setv RB (v % 2) with hσ1
    have hk' : (v / 2).bits.length = k := by rw [bits_step v hne] at hk; simpa using hk
    have hb' : v0.bits = (done ++ [decide (v % 2 = 1)]) ++ (v / 2).bits := by
      rw [hb, bits_step v hne]; simp
    have hs1 : SameExcept σ0 σ1 [IN] [N1, H, RB] :=
      (hs.trans (sameExcept_setv _ (by simp) _)).trans (sameExcept_setv _ (by simp) _)
    have ho1 : OutAt σ1 IN (w ++ done.flatMap quad) := (ho.setv _ _).setv _ _
    have hN1 : σ1.val N1 = v / 2 := by simp [hσ1, Function.update_apply, h2]
    have hH1 : σ1.val H = 0 := by simp [hσ1, Function.update_apply, h3, (Ne.symm h1), hH]
    have hR1 : σ1.val RB = v % 2 := by simp [hσ1]
    have post : ∀ τ : WState ns nr, SameExcept σ1 τ [IN] [RB] → τ.val RB = 0 →
        OutAt τ IN (w ++ done.flatMap quad ++ quad (decide (v % 2 = 1))) →
        ∃ v' done', τ.val N1 = v' ∧ v'.bits.length = k ∧ v' ≤ v0 ∧ v0.bits = done' ++ v'.bits ∧
          OutAt τ IN (w ++ done'.flatMap quad) ∧ τ.val H = 0 ∧ τ.val RB = 0 ∧ SameExcept σ0 τ [IN] [N1, H, RB] := by
      intro τ hs2 hRB ho2
      refine ⟨v / 2, done ++ [decide (v % 2 = 1)], by rw [hs2.val (by simp [h2]), hN1], hk', by omega, hb', by
        simpa [List.append_assoc] using ho2, by rw [hs2.val (by simp [h3]), hH1], hRB,
        hs1.trans (hs2.weaken (by simp) (by simp))⟩
    refine Runs.seq' (Runs.of (WXExec.wm hh) rfl) (fun τ hτ => ?_) (show 9 * v + 6 + 1 + 19 ≤ 9 * v0 + 27 by omega)
    subst hτ
    refine Runs.ifr (fun hRB => ?_) (fun hRB => ?_)
    · have hodd : v % 2 = 1 := by rw [hR1] at hRB; omega
      refine Runs.seq' (c2 := 1) (emitL_runs IN (quad true) σ1 _ ho1) (fun τ hτ => ?_) (by simp [quad])
      have hτR : τ.val RB = 1 := by rw [hτ.2.val (by simp), hR1, hodd]
      refine ⟨_, WXExec.dec (cap := cap) RB τ (by omega), ?_⟩
      apply post _ ((hτ.2.weaken (by simp) (by simp)).trans (sameExcept_setv _ (by simp) _)) (by simp [hτR])
      rw [hodd]; exact hτ.1
    · have hev : v % 2 = 0 := by rw [hR1] at hRB; omega
      refine (emitL_runs IN (quad false) σ1 _ ho1).mono (by simp [quad]) (fun τ hτ => ?_)
      apply post _ (hτ.2.weaken (by simp) (by simp)) (by rw [hτ.2.val (by simp), hR1, hev])
      rw [hev]; exact hτ.1

/-- `A` times `quad false`, decrementing `BC` each time. -/
def zerosA (IN : Fin (ns + 1)) (A BC : Fin nr) : WMX ns nr :=
  .whr A (.seq (WMX.dec A) (.seq (WMX.dec BC) (emitL IN (quad false))))

/-- `BC` times `quad false`. -/
def zerosB (IN : Fin (ns + 1)) (BC : Fin nr) : WMX ns nr := .whr BC (.seq (WMX.dec BC) (emitL IN (quad false)))

/-- The encoder's input tape for `⟨Q, e_I⟩`. -/
def msgW (IN : Fin (ns + 1)) (Q I N1 H RB A BC T : Fin nr) : WMX ns nr :=
  .seq (addR Q N1 T) (.seq (bitsLoop IN N1 H RB) (.seq (emitL IN [true, false]) (.seq (addR I A T)
    (.seq (addR Q BC T) (.seq (zerosA IN A BC) (.seq (WMX.dec BC) (.seq (emitL IN (quad true))
      (.seq (zerosB IN BC) (emitL IN [true, false, false])))))))))

/-- The cost bound of `msgW`. -/
def msgCost (n : ℕ) : ℕ := 10 * (n + 7) ^ 2

theorem msgW_runs (IN : Fin (ns + 1)) {Q I N1 H RB A BC T : Fin nr} (hR : [Q, I, N1, H, RB, A, BC, T].Nodup)
    (n i : ℕ) (hn : 2 ≤ n) (hi : i < n) (hcap : 2 * n ≤ cap) (σ : WState ns nr) (w : List Bool)
    (hQ : σ.val Q = n) (hI : σ.val I = i) (hN1 : σ.val N1 = 0) (hH : σ.val H = 0) (hRB : σ.val RB = 0)
    (hA : σ.val A = 0) (hBC : σ.val BC = 0) (hT : σ.val T = 0) (ho : OutAt σ IN w) :
    Runs cap (msgW IN Q I N1 H RB A BC T) σ (msgCost n)
      (fun τ => OutAt τ IN (w ++ frame (NearCubicGates.PublishedSources.PCPP.messageWord (unitReq n i hn))) ∧
        τ.val N1 = 0 ∧ τ.val H = 0 ∧ τ.val RB = 0 ∧ τ.val A = 0 ∧ τ.val BC = 0 ∧
        SameExcept σ τ [IN] [N1, H, RB, A, BC]) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    not_false_eq_true] at hR
  obtain ⟨⟨q1, q2, q3, q4, q5, q6, q7⟩, ⟨i1, i2, i3, i4, i5, i6⟩, ⟨n1, n2, n3, n4, n5⟩, ⟨h1, h2, h3, h4⟩,
    ⟨r1, r2, r3⟩, ⟨a1, a2⟩, b1⟩ := hR

  have e1 := addR_spec cap q2 q7 n5 σ hT (by rw [hN1, hQ]; omega)
  rw [hN1, hQ, Nat.zero_add] at e1
  -- 2. the bits of n
  obtain ⟨τ2, e2, p2N1, p2H, p2RB, p2o, p2s⟩ := bitsLoop_runs (cap := cap) IN n1 n2 h1 n (by omega) (by omega)
    (σ.setv N1 n) w n.bits.length (σ.setv N1 n) ⟨n, [], by simp, rfl, le_rfl, by simp, by simpa using ho.setv N1 n,
      by simp [Function.update_apply, (Ne.symm n1), hH], by simp [Function.update_apply, (Ne.symm n2), hRB],
      SameExcept.refl _ _ _⟩
  have s2 : SameExcept σ τ2 [IN] [N1, H, RB] :=
    ((sameExcept_setv σ (S := [IN]) (Rg := [N1, H, RB]) (by simp) n)).trans p2s
  -- 3. the inner terminator
  obtain ⟨τ3, e3, p3o, p3s⟩ := emitL_runs (cap := cap) IN [true, false] τ2 _ p2o
  have s3 : SameExcept σ τ3 [IN] [N1, H, RB] := s2.trans (p3s.weaken (by simp) (by simp))
  have v3 : ∀ r, r ∉ [N1, H, RB] → τ3.val r = σ.val r := fun r hr => s3.val hr
  -- 4. A := i
  have e4 := addR_spec cap (A := I) (B := A) (T := T) i4 i6 a2 τ3 (by rw [v3 T (by simp [(Ne.symm n5), (Ne.symm h4), (Ne.symm r3)])]; exact hT)
    (by rw [v3 A (by simp [(Ne.symm n3), (Ne.symm h2), (Ne.symm r1)]), v3 I (by simp [i1, i2, i3]), hA, hI]; omega)
  rw [v3 A (by simp [(Ne.symm n3), (Ne.symm h2), (Ne.symm r1)]), v3 I (by simp [i1, i2, i3]), hA, hI, Nat.zero_add] at e4
  -- 5. BC := n
  have hτ4T : (τ3.setv A i).val T = 0 := by
    simp [Function.update_apply, (Ne.symm a2)]; rw [v3 T (by simp [(Ne.symm n5), (Ne.symm h4), (Ne.symm r3)])]; exact hT
  have e5 := addR_spec cap (A := Q) (B := BC) (T := T) q6 q7 b1 (τ3.setv A i) hτ4T
    (by simp [Function.update_apply, (Ne.symm a1), q5]; rw [v3 BC (by simp [(Ne.symm n4), (Ne.symm h3), (Ne.symm r2)]),
      v3 Q (by simp [q2, q3, q4]), hBC, hQ]; omega)
  have hτ4BC : (τ3.setv A i).val BC = 0 := by
    simp [Function.update_apply, (Ne.symm a1)]; rw [v3 BC (by simp [(Ne.symm n4), (Ne.symm h3), (Ne.symm r2)])]; exact hBC
  have hτ4Q : (τ3.setv A i).val Q = n := by
    simp [Function.update_apply, q5]; rw [v3 Q (by simp [q2, q3, q4])]; exact hQ
  rw [hτ4BC, hτ4Q, Nat.zero_add] at e5
  set τ5 := (τ3.setv A i).setv BC n with hτ5
  have s5 : SameExcept σ τ5 [IN] [N1, H, RB, A, BC] :=
    ((s3.weaken (by simp) (by simp)).trans (sameExcept_setv _ (by simp) _)).trans (sameExcept_setv _ (by simp) _)
  have p5o : OutAt τ5 IN (w ++ n.bits.flatMap quad ++ [true, false]) := (p3o.setv _ _).setv _ _
  -- 6. i zeros
  have e6 := Runs.count (cap := cap) (K := A) (body := .seq (WMX.dec BC) (emitL IN (quad false))) 18 i
    (fun k τ => τ.val BC = n - k ∧ OutAt τ IN (w ++ n.bits.flatMap quad ++ [true, false] ++
      (List.replicate k (quad false)).flatten) ∧ SameExcept τ5 τ [IN] [A, BC]) (by omega)
    (fun k hk τ hτ _ => by
      obtain ⟨hb, ho', hs'⟩ := hτ
      have hd := WXExec.dec (cap := cap) BC (τ.setv A (i - k - 1))
        (by simp [Function.update_apply, (Ne.symm a1), hb]; omega)
      refine Runs.seq' (c2 := 16) (Runs.of hd rfl) (fun ρ hρ => ?_) (by norm_num)
      subst hρ
      refine (emitL_runs (cap := cap) IN (quad false) _ _ ((ho'.setv _ _).setv _ _)).mono (by simp [quad])
        (fun ρ hρ => ⟨⟨?_, ?_, ?_⟩, ?_⟩)
      · rw [hρ.2.val (by simp)]; simp [Function.update_apply, (Ne.symm a1), hb]; omega
      · simpa [List.replicate_succ', List.flatten_append, List.append_assoc] using hρ.1
      · exact ((hs'.trans (sameExcept_setv _ (by simp) _)).trans (sameExcept_setv _ (by simp) _)).trans
          (hρ.2.weaken (by simp) (by simp))
      · rw [hρ.2.val (by simp)]; simp [Function.update_apply, a1])
    τ5 ⟨by simp [hτ5], by simpa using p5o, SameExcept.refl _ _ _⟩
    (by simp [hτ5, Function.update_apply, a1])
  obtain ⟨τ6, e6, ⟨p6BC, p6o, p6s⟩, p6A⟩ := e6
  -- 7. BC := n - i - 1
  have e7 := WXExec.dec (cap := cap) BC τ6 (by rw [p6BC]; omega)
  rw [p6BC] at e7
  -- 8. the one
  obtain ⟨τ8, e8, p8o, p8s⟩ := emitL_runs (cap := cap) IN (quad true) (τ6.setv BC (n - i - 1)) _ (p6o.setv _ _)
  -- 9. n - i - 1 zeros
  have e9 := Runs.count (cap := cap) (K := BC) (body := emitL IN (quad false)) 16 (n - i - 1)
    (fun k τ => OutAt τ IN (w ++ n.bits.flatMap quad ++ [true, false] ++ (List.replicate i (quad false)).flatten ++
      quad true ++ (List.replicate k (quad false)).flatten) ∧ SameExcept τ8 τ [IN] [BC]) (by omega)
    (fun k _ τ hτ _ => (emitL_runs (cap := cap) IN (quad false) _ _ (hτ.1.setv _ _)).mono (by simp [quad])
      (fun ρ hρ => ⟨⟨by simpa [List.replicate_succ', List.flatten_append, List.append_assoc] using hρ.1,
        (hτ.2.trans (sameExcept_setv _ (by simp) _)).trans (hρ.2.weaken (by simp) (by simp))⟩,
        by rw [hρ.2.val (by simp)]; simp⟩))
    τ8 ⟨by simpa using p8o, SameExcept.refl _ _ _⟩ (by rw [p8s.val (by simp)]; simp)
  obtain ⟨τ9, e9, ⟨p9o, p9s⟩, p9BC⟩ := e9
  -- 10. the two terminators
  obtain ⟨τ10, e10, p10o, p10s⟩ := emitL_runs (cap := cap) IN [true, false, false] τ9 _ p9o
  refine ⟨τ10, WXExec.mono (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5
    (WXExec.seq e6 (WXExec.seq e7 (WXExec.seq e8 (WXExec.seq e9 e10))))))))) ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hb := bits_length_le n
    have hk : n.bits.length * (9 * n + 27 + 2) ≤ n * (9 * n + 29) := Nat.mul_le_mul_right _ hb
    have hm : (n - i - 1) * (16 + 4) ≤ n * 20 := Nat.mul_le_mul_right _ (by omega)
    have hi' : i * (18 + 4) ≤ n * 22 := Nat.mul_le_mul_right _ (by omega)
    simp only [msgCost, List.length_cons, List.length_nil, quad]
    nlinarith
  · rw [frame_messageWord_unit n i hn hi]
    simpa [List.flatten_append, List.append_assoc] using p10o
  all_goals
    have hch : ∀ r, r ≠ A → r ≠ BC → τ10.val r = τ3.val r := by
      intro r hrA hrB
      rw [p10s.val (by simp), p9s.val (by simp [hrB]), p8s.val (by simp), WState.setv_val,
        Function.update_of_ne hrB, p6s.val (by simp [hrA, hrB]), hτ5, WState.setv_val, Function.update_of_ne hrB,
        WState.setv_val, Function.update_of_ne hrA]
  · rw [hch N1 n3 n4, p3s.val (by simp), p2N1]
  · rw [hch H h2 h3, p3s.val (by simp), p2H]
  · rw [hch RB r1 r2, p3s.val (by simp), p2RB]
  · rw [p10s.val (by simp), p9s.val (by simp [a1]), p8s.val (by simp), WState.setv_val,
      Function.update_of_ne a1, p6A]
  · rw [p10s.val (by simp), p9BC]
  · exact ((((s5.trans (p6s.weaken (by simp) (by simp))).trans (sameExcept_setv _ (by simp) _)).trans
      (p8s.weaken (by simp) (by simp))).trans (p9s.weaken (by simp) (by simp))).trans (p10s.weaken (by simp) (by simp))

end NearCubicGates.Close.CheckedPCPP
