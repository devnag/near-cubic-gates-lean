import SourceAdapters.Refuter.CheckerRun

/-!
# The guessed data of one check, written into a witness (input 7, F01 completeness codec)

proof of `lem:multitape-refuter`: "the hierarchy verifier guesses a positive length `r` in unary"; SFM78 l.222–224:
the guessed "displays". A check reading at position `p` parses `1^r 0`, then one `1` marker and `t`
display bits per guessed step, then a closing `0` (`gun`, `gtrace`, `gend`). `encCheck r ds` is that
word; `chk_encode` shows the check parses exactly `r` and `ds` back from any witness containing it at
`p`, and ends right after it. The bits guessed for the second simulation's witness are read the same
way (`gbits`).
-/

namespace NearCubicGates.Adapters.Refuter.Mach

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicGates.Adapters.Refuter

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-- One guessed step: a `1` marker and the scanned bits. -/
def encDisp {t : ℕ} (d : Fin t → Bool) : List Bool := true :: List.ofFn d

/-- A guessed trace and its closing `0`. -/
def encTrace {t : ℕ} (ds : List (Fin t → Bool)) : List Bool := ds.flatMap encDisp ++ [false]

/-- The guessed data of one check. -/
def encCheck {t : ℕ} (r : ℕ) (ds : List (Fin t → Bool)) : List Bool :=
  List.replicate r true ++ false :: encTrace ds

/-- `g` guessed bits read from logical position `e`. -/
def gbits (wD : List Bool) (e g : ℕ) : List Bool := List.ofFn fun j : Fin g => gbit wD (e + j.val)

theorem encTrace_length {t : ℕ} (ds : List (Fin t → Bool)) :
    (encTrace ds).length = ds.length * (1 + t) + 1 := by
  induction ds with
  | nil => simp [encTrace]
  | cons d ds ih =>
    simp only [encTrace, List.flatMap_cons, List.length_append, List.length_cons, List.length_nil] at ih ⊢
    simp only [encDisp, List.length_cons, List.length_ofFn]
    rw [Nat.add_mul]; omega

theorem encCheck_length {t : ℕ} (r : ℕ) (ds : List (Fin t → Bool)) :
    (encCheck r ds).length = r + 1 + ds.length * (1 + t) + 1 := by
  simp only [encCheck, List.length_append, List.length_replicate, List.length_cons, encTrace_length]; omega

theorem gbit_left (l₁ l₂ : List Bool) {p : ℕ} (h : p < l₁.length) : gbit (l₁ ++ l₂) p = gbit l₁ p := by
  simp [gbit, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem gbit_right (l₁ l₂ : List Bool) (p : ℕ) : gbit (l₁ ++ l₂) (l₁.length + p) = gbit l₂ p := by
  simp [gbit, List.getD_eq_getElem?_getD, List.getElem?_append_right]

theorem gbit_mid (pre : List Bool) (b : Bool) (rest : List Bool) : gbit (pre ++ b :: rest) pre.length = b := by
  simp [gbit, List.getD_eq_getElem?_getD]

theorem gun_encode (pre rest : List Bool) :
    ∀ r f, r < f → gun (pre ++ (List.replicate r true ++ false :: rest)) f pre.length = r := by
  intro r
  induction r generalizing pre with
  | zero =>
    intro f hf
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    simp [gun, gbit_mid]
  | succ r ih =>
    intro f hf
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    have hb : gbit (pre ++ (List.replicate (r + 1) true ++ false :: rest)) pre.length = true := by
      simp [List.replicate_succ, gbit_mid]
    have e : pre ++ (List.replicate (r + 1) true ++ false :: rest) =
        (pre ++ [true]) ++ (List.replicate r true ++ false :: rest) := by
      simp [List.replicate_succ]
    have := ih (pre ++ [true]) f (by omega)
    simp only [List.length_append, List.length_cons, List.length_nil] at this
    simp only [gun, hb, if_true]
    rw [e, this]

theorem gtrace_encode {t : ℕ} (rest : List Bool) :
    ∀ (ds : List (Fin t → Bool)) (pre : List Bool) f, ds.length < f →
      gtrace (pre ++ (encTrace ds ++ rest)) t f pre.length = ds ∧
      gend (pre ++ (encTrace ds ++ rest)) t f pre.length = pre.length + (encTrace ds).length := by
  intro ds
  induction ds with
  | nil =>
    intro pre f hf
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    simp [gtrace, gend, encTrace, gbit_mid]
  | cons d ds ih =>
    intro pre f hf
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    have e : pre ++ (encTrace (d :: ds) ++ rest) = (pre ++ encDisp d) ++ (encTrace ds ++ rest) := by
      simp [encTrace, List.flatMap_cons]
    have hb : gbit (pre ++ (encTrace (d :: ds) ++ rest)) pre.length = true := by
      rw [e, List.append_assoc]
      simp [encDisp, gbit_mid]
    have hd : gdisp (pre ++ (encTrace (d :: ds) ++ rest)) (pre.length + 1) t = d := by
      funext j
      simp only [gdisp]
      rw [e, List.append_assoc]
      have := gbit_right pre (encDisp d ++ (encTrace ds ++ rest)) (1 + j.val)
      rw [show pre.length + 1 + j.val = pre.length + (1 + j.val) by omega, this]
      have h2 : 1 + j.val < (encDisp d).length := by simp [encDisp]; omega
      rw [gbit_left _ _ h2]
      simp [gbit, encDisp, List.getD_eq_getElem?_getD, show 1 + j.val = j.val + 1 by omega]
    have hlen : (pre ++ encDisp d).length = pre.length + 1 + t := by simp [encDisp]; omega
    obtain ⟨h1, h2⟩ := ih (pre ++ encDisp d) f (by simp at hf; omega)
    rw [hlen] at h1 h2
    refine ⟨?_, ?_⟩
    · simp only [gtrace, hb, if_true, hd]
      rw [e, h1]
    · simp only [gend, hb, if_true]
      rw [e, h2, encTrace_length, encTrace_length]
      simp only [List.length_cons]
      rw [Nat.add_mul]; omega

/-- **The check parses its encoded data back** (any prefix `pre`, any continuation `rest`). -/
theorem chk_encode {t : ℕ} (pre rest : List Bool) (r : ℕ) (ds : List (Fin t → Bool)) :
    chkR0 (pre ++ (encCheck r ds ++ rest)) pre.length = r ∧
    chkDs (pre ++ (encCheck r ds ++ rest)) t pre.length = ds ∧
    chkEnd (pre ++ (encCheck r ds ++ rest)) t pre.length = pre.length + (encCheck r ds).length := by
  set wD := pre ++ (encCheck r ds ++ rest) with hwD
  have hlen : wD.length = pre.length + (encCheck r ds).length + rest.length := by
    simp [wD]; omega
  have hcl := encCheck_length r ds
  have hr : chkR0 wD pre.length = r := by
    unfold chkR0
    have := gun_encode pre (encTrace ds ++ rest) r (wD.length + 1) (by omega)
    simpa [wD, encCheck, List.append_assoc] using this
  have e2 : wD = (pre ++ (List.replicate r true ++ [false])) ++ (encTrace ds ++ rest) := by
    simp [wD, encCheck]
  have hl2 : (pre ++ (List.replicate r true ++ [false])).length = pre.length + r + 1 := by simp; omega
  have hds : ds.length < wD.length + 1 := by
    have : ds.length ≤ ds.length * (1 + t) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  obtain ⟨h1, h2⟩ := gtrace_encode rest ds (pre ++ (List.replicate r true ++ [false])) (wD.length + 1) hds
  rw [← e2, hl2] at h1 h2
  refine ⟨hr, ?_, ?_⟩
  · unfold chkDs ptrace; rw [hr]; exact h1
  · unfold chkEnd pend; rw [hr, h2, encTrace_length, hcl]; omega

theorem gbits_encode (pre v rest : List Bool) : gbits (pre ++ (v ++ rest)) pre.length v.length = v := by
  apply List.ext_getElem (by simp [gbits])
  intro j h1 h2
  simp only [gbits, List.getElem_ofFn]
  rw [gbit_right, gbit_left _ _ h2]
  simp [gbit, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

end NearCubicGates.Adapters.Refuter.Mach
