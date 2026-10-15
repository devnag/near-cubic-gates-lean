import Proof.Packets.PacketsMetaVec

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.PacketsGlue.StripH
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.PacketsGlue NearCubicWires.PacketsGlue.NatSum

def nw : Fin 3 → Option Bool := fun _ => none

/-- States: 0 sentinel, 1–2 count the leading ones, 3–4 skip the value bits, 5–6 copy, 7 halt. -/
def machine : Machine 3 8 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 7
  rule := fun q b =>
    if q.val = 0 then some ⟨1, ![none, none, some false], ![.stay, .stay, .right]⟩
    else if q.val = 1 then some (if b 0 then ⟨2, nw, ![.right, .stay, .stay]⟩ else ⟨7, nw, fun _ => .stay⟩)
    else if q.val = 2 then some (if b 0 then ⟨1, ![none, none, some true], ![.right, .stay, .right]⟩
      else ⟨3, nw, ![.right, .stay, .left]⟩)
    else if q.val = 3 then some (if b 2 then ⟨4, nw, ![.right, .stay, .left]⟩ else ⟨5, nw, fun _ => .stay⟩)
    else if q.val = 4 then some ⟨3, nw, ![.right, .stay, .stay]⟩
    else if q.val = 5 then some (if b 0 then ⟨6, nw, ![.right, .stay, .stay]⟩ else ⟨7, nw, fun _ => .stay⟩)
    else if q.val = 6 then some ⟨5, ![none, some (b 0), none], ![.right, .right, .stay]⟩
    else none

/-- Tapes: the framed field `frame u` (head `i`), the output (head at its end), the counter. -/
def cfg (q : Fin 8) (u : List Bool) (i : ℕ) (out C : List Bool) (hc : ℕ) : Configuration 3 8 :=
  ⟨q, ![i, out.length, hc], ![RepairOrdinary.frame u, out, C]⟩

section Steps
variable (u : List Bool) (i : ℕ) (out C : List Bool) (hc : ℕ)

theorem s0 : step machine (cfg 0 u i out C hc) = some (cfg 1 u i out (writeTapeBit C hc false) (hc + 1)) := by
  simp [step, machine, cfg]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction]

theorem s1t (h : readTapeBit (RepairOrdinary.frame u) i = true) :
    step machine (cfg 1 u i out C hc) = some (cfg 2 u (i + 1) out C hc) := by
  simp [step, machine, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction, nw]

theorem s2t (h : readTapeBit (RepairOrdinary.frame u) i = true) :
    step machine (cfg 2 u i out C hc) = some (cfg 1 u (i + 1) out (writeTapeBit C hc true) (hc + 1)) := by
  simp [step, machine, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction]

theorem s2f (h : readTapeBit (RepairOrdinary.frame u) i = false) :
    step machine (cfg 2 u i out C hc) = some (cfg 3 u (i + 1) out C (hc - 1)) := by
  simp [step, machine, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction, nw]

theorem s3t (h : readTapeBit C hc = true) :
    step machine (cfg 3 u i out C hc) = some (cfg 4 u (i + 1) out C (hc - 1)) := by
  simp [step, machine, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction, nw]

theorem s3f (h : readTapeBit C hc = false) :
    step machine (cfg 3 u i out C hc) = some (cfg 5 u i out C hc) := by
  simp [step, machine, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction, nw]

theorem s4 : step machine (cfg 4 u i out C hc) = some (cfg 3 u (i + 1) out C hc) := by
  simp [step, machine, cfg]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction, nw]

theorem s5t (h : readTapeBit (RepairOrdinary.frame u) i = true) :
    step machine (cfg 5 u i out C hc) = some (cfg 6 u (i + 1) out C hc) := by
  simp [step, machine, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction, nw]

theorem s5f (h : readTapeBit (RepairOrdinary.frame u) i = false) :
    step machine (cfg 5 u i out C hc) = some (cfg 7 u i out C hc) := by
  simp [step, machine, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction, nw]

theorem s6 (b : Bool) (h : readTapeBit (RepairOrdinary.frame u) i = b) :
    step machine (cfg 6 u i out C hc) = some (cfg 5 u (i + 1) (out ++ [b]) C hc) := by
  simp [step, machine, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction, Streaming.write_append]

end Steps

theorem one {c d : Configuration 3 8} (hq : c.control.val ≠ 7) (h : step machine c = some d) :
    Timed machine 1 c d :=
  Timed.single (by simp [machine, hq]) h

theorem tr {t u : ℕ} {c d d' e : Configuration 3 8} (h1 : Timed machine t c d) (h2 : Timed machine u d' e)
    (h : d = d') : Timed machine (t + u) c e := by
  subst h
  exact h1.trans h2

/-! ## The word -/

variable (l : ℕ) (bits body : List Bool)

/-- The field: `ℓ` ones, the separator, `ℓ` value bits, then the body. -/
def word : List Bool := List.replicate l true ++ false :: (bits ++ body)

theorem word_length (hb : bits.length = l) : (word l bits body).length = 2 * l + 1 + body.length := by
  simp [word, hb]; omega

theorem get_one (hb : bits.length = l) (j : ℕ) (hj : j < l) :
    readTapeBit (RepairOrdinary.frame (word l bits body)) (2 * j + 1) = true := by
  rw [read_payload _ _ (by rw [word_length l bits body hb]; omega)]
  simp [word, List.getElem_append_left (show j < (List.replicate l true).length by simpa using hj)]

theorem get_sep (hb : bits.length = l) :
    readTapeBit (RepairOrdinary.frame (word l bits body)) (2 * l + 1) = false := by
  rw [read_payload _ _ (by rw [word_length l bits body hb]; omega)]
  simp [word, List.getElem_append_right (show (List.replicate l true).length ≤ l by simp)]

theorem get_body (hb : bits.length = l) (t : ℕ) (ht : t < body.length) :
    readTapeBit (RepairOrdinary.frame (word l bits body)) (2 * (2 * l + 1 + t) + 1) = body[t] := by
  rw [read_payload _ _ (by rw [word_length l bits body hb]; omega)]
  have e : word l bits body = (List.replicate l true ++ false :: bits) ++ body := by simp [word]
  simp only [e]
  rw [List.getElem_append_right (by simp [hb]; omega)]
  congr 1
  simp [hb]; omega

theorem mark (hb : bits.length = l) (j : ℕ) (hj : j < 2 * l + 1 + body.length) :
    readTapeBit (RepairOrdinary.frame (word l bits body)) (2 * j) = true :=
  read_marker _ _ (by rw [word_length l bits body hb]; exact hj)

/-! ## The three phases -/

theorem phase1 (hb : bits.length = l) : ∀ j, j ≤ l →
    Timed machine (2 * (l - j)) (cfg 1 (word l bits body) (2 * j) [] (sent j 0) (j + 1))
      (cfg 1 (word l bits body) (2 * l) [] (sent l 0) (l + 1)) := by
  intro j hj
  induction h : l - j generalizing j with
  | zero =>
    have : j = l := by omega
    subst this
    exact Timed.refl _ _
  | succ k ih =>
    have t1 := one (c := cfg 1 (word l bits body) (2 * j) [] (sent j 0) (j + 1)) (by simp [cfg])
      (s1t _ _ _ _ _ (mark l bits body hb j (by omega)))
    have t2 := one (c := cfg 2 (word l bits body) (2 * j + 1) [] (sent j 0) (j + 1)) (by simp [cfg])
      (s2t _ _ _ _ _ (get_one l bits body hb j (by omega)))
    have t3 := ih (j + 1) (by omega) (by omega)
    have e : writeTapeBit (sent j 0) (j + 1) true = sent (j + 1) 0 := sent_add j 0
    rw [e, show 2 * j + 1 + 1 = 2 * (j + 1) by omega] at t2
    have t := (t1.trans t2).trans t3
    rw [show 1 + 1 + 2 * k = 2 * (k + 1) by omega] at t
    exact t

theorem phase2 : ∀ m, m ≤ l →
    Timed machine (2 * m) (cfg 3 (word l bits body) (2 * l + 2 + 2 * (l - m)) [] (sent l 0) m)
      (cfg 3 (word l bits body) (2 * l + 2 + 2 * l) [] (sent l 0) 0) := by
  intro m
  induction m with
  | zero =>
    intro _
    simpa using Timed.refl machine (cfg 3 (word l bits body) (2 * l + 2 + 2 * l) [] (sent l 0) 0)
  | succ k ih =>
    intro hk
    have hr : readTapeBit (sent l 0) (k + 1) = true := by rw [read_sent]; simp; omega
    have t1 := one (c := cfg 3 (word l bits body) (2 * l + 2 + 2 * (l - (k + 1))) [] (sent l 0) (k + 1))
      (by simp [cfg]) (s3t _ _ _ _ _ hr)
    have t2 := one (c := cfg 4 (word l bits body) (2 * l + 2 + 2 * (l - (k + 1)) + 1) [] (sent l 0) (k + 1 - 1))
      (by simp [cfg]) (s4 _ _ _ _ _)
    have t3 := ih (by omega)
    have tt := tr (t1.trans t2) t3 (by congr 1 <;> omega)
    exact timed_congr' tt (by omega)
where
  timed_congr' {t t' : ℕ} {c d : Configuration 3 8} (h : Timed machine t c d) (ht : t = t') :
      Timed machine t' c d := by
    subst ht; exact h

theorem phase3 (hb : bits.length = l) : ∀ t, t ≤ body.length →
    Timed machine (2 * (body.length - t)) (cfg 5 (word l bits body) (2 * (2 * l + 1 + t)) (body.take t) (sent l 0) 0)
      (cfg 5 (word l bits body) (2 * (2 * l + 1 + body.length)) body (sent l 0) 0) := by
  intro t ht
  induction h : body.length - t generalizing t with
  | zero =>
    have : t = body.length := by omega
    subst this
    simpa using Timed.refl machine (cfg 5 (word l bits body) (2 * (2 * l + 1 + body.length)) body (sent l 0) 0)
  | succ k ih =>
    have t1 := one (c := cfg 5 (word l bits body) (2 * (2 * l + 1 + t)) (body.take t) (sent l 0) 0) (by simp [cfg])
      (s5t _ _ _ _ _ (mark l bits body hb (2 * l + 1 + t) (by omega)))
    have t2 := one (c := cfg 6 (word l bits body) (2 * (2 * l + 1 + t) + 1) (body.take t) (sent l 0) 0)
      (by simp [cfg]) (s6 _ _ _ _ _ body[t] (get_body l bits body hb t (by omega)))
    have t3 := ih (t + 1) (by omega) (by omega)
    have e : body.take t ++ [body[t]] = body.take (t + 1) := by
      rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]; rfl
    rw [e, show 2 * (2 * l + 1 + t) + 1 + 1 = 2 * (2 * l + 1 + (t + 1)) by omega] at t2
    have tt := (t1.trans t2).trans t3
    rw [show 1 + 1 + 2 * k = 2 * (k + 1) by omega] at tt
    exact tt

/-- **Strip the header**: `frame (ones ℓ ++ false :: bits ++ body)` ↦ `body` on tape 1. -/
theorem run (hb : bits.length = l) :
    ∃ H, Step machine (2 * (2 * l + 1 + body.length) + 3) ![0, 0, 0]
      ![RepairOrdinary.frame (word l bits body), [], []] H
      ![RepairOrdinary.frame (word l bits body), body, sent l 0] := by
  have t0 := one (c := cfg 0 (word l bits body) 0 [] [] 0) (by simp [cfg]) (s0 _ _ _ _ _)
  have p1 := phase1 l bits body hb 0 (by omega)
  have ta := one (c := cfg 1 (word l bits body) (2 * l) [] (sent l 0) (l + 1)) (by simp [cfg])
    (s1t _ _ _ _ _ (mark l bits body hb l (by omega)))
  have tb := one (c := cfg 2 (word l bits body) (2 * l + 1) [] (sent l 0) (l + 1)) (by simp [cfg])
    (s2f _ _ _ _ _ (get_sep l bits body hb))
  have p2 := phase2 l bits body l (le_refl l)
  have tc := one (c := cfg 3 (word l bits body) (2 * l + 2 + 2 * l) [] (sent l 0) 0) (by simp [cfg])
    (s3f _ _ _ _ _ (by rw [read_sent]; simp))
  have p3 := phase3 l bits body hb 0 (by omega)
  have td := one (c := cfg 5 (word l bits body) (2 * (2 * l + 1 + body.length)) body (sent l 0) 0) (by simp [cfg])
    (s5f _ _ _ _ _ (by
      have := read_end (word l bits body)
      rw [word_length l bits body hb] at this
      exact this))
  have e0 : writeTapeBit ([] : List Bool) 0 false = sent 0 0 := rfl
  rw [e0] at t0
  have t := tr (tr (tr (tr (tr (tr (tr t0 p1 (by simp)) ta rfl) tb rfl) p2 (by congr 1 <;> omega)) tc
    rfl) p3 (by rw [List.take_zero]; congr 1; omega)) td (by simp)
  obtain ⟨r, hr, hf, hs⟩ := t.run (by simp [machine, cfg])
  refine ⟨_, r, ?_, rfl, by rw [hf]; rfl, by omega⟩
  have hc : (⟨machine.start, ![0, 0, 0], ![RepairOrdinary.frame (word l bits body), [], []]⟩ : Configuration 3 8) =
      cfg 0 (word l bits body) 0 [] [] 0 := rfl
  rw [hc]
  have e : 1 + 2 * (l - 0) + 1 + 1 + 2 * l + 1 + 2 * (body.length - 0) + 1 =
      2 * (2 * l + 1 + body.length) + 3 := by omega
  rw [← e]
  exact hr

end NearCubicWires.PacketsGlue.StripH

