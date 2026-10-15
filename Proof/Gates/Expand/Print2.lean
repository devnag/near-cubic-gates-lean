import Proof.Gates.Expand.Print

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.Expand

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)

variable {ns nr : ℕ}

section Loops
variable {X O : Fin (ns + 1)} {OP : Fin nr} {PR : Fin 4 ↪ Fin nr} {cap : ℕ}

theorem WD.incN (hOP : ∀ i, PR i ≠ OP) {σ τ : WState ns nr} {u : List Bool} {h : ℕ} {r : Fin 4 → ℕ}
    (hd : WD X O OP PR σ τ u h r) (i : Fin 4) (r' : Fin 4 → ℕ) (hc : r i < cap)
    (e : ∀ j, Function.update r i (r i + 1) j = r' j) :
    Runs cap (WMX.inc (PR i)) τ 3 (fun ρ => WD X O OP PR σ ρ u h r') :=
  (hd.inc hOP i hc).post (fun _ hρ => hρ.r_eq (funext e))

theorem WD.decN (hOP : ∀ i, PR i ≠ OP) {σ τ : WState ns nr} {u : List Bool} {h : ℕ} {r : Fin 4 → ℕ}
    (hd : WD X O OP PR σ τ u h r) (i : Fin 4) (r' : Fin 4 → ℕ) (hc : r i ≤ cap)
    (e : ∀ j, Function.update r i (r i - 1) j = r' j) :
    Runs cap (WMX.dec (PR i)) τ 1 (fun ρ => WD X O OP PR σ ρ u h r') :=
  (hd.dec hOP i hc).post (fun _ hρ => hρ.r_eq (funext e))

theorem WD.val {σ τ : WState ns nr} {u : List Bool} {h : ℕ} {r : Fin 4 → ℕ}
    (hd : WD X O OP PR σ τ u h r) (i : Fin 4) : τ.val (PR i) = r i := hd.2.2.2.2.2.2 i

/-- `L += Z`, `Z := 0`. -/
theorem moveZ_spec (hOP : ∀ i, PR i ≠ OP) (σ : WState ns nr) (u : List Bool) (h L p k : ℕ) (hL : L ≤ cap) :
    ∀ m τ, m ≤ L → WD X O OP PR σ τ u h ![L - m, m, p, k] →
      Runs cap (moveZ (PR 1) (PR 0)) τ (m * (5 + 2) + 1) (fun ρ => WD X O OP PR σ ρ u h ![L, 0, p, k]) := by
  intro m τ hm hd
  refine Runs.whr (fun m τ => m ≤ L ∧ WD X O OP PR σ τ u h ![L - m, m, p, k]) 5 _ ?_ ?_ m τ ⟨hm, hd⟩
  · rintro τ ⟨_, hd⟩
    exact ⟨by rw [hd.val 1]; rfl, by simpa using hd⟩
  · rintro m τ ⟨hm, hd⟩
    refine ⟨by rw [hd.val 1]; simp, ?_⟩
    refine (hd.decN hOP 1 ![L - (m + 1), m, p, k] (by simp; omega) (by intro j; fin_cases j <;> simp)).seq'
      (fun ρ hρ => (hρ.incN hOP 0 ![L - m, m, p, k] (by simp; omega)
        (by intro j; fin_cases j <;> simp <;> omega)).post (fun _ h' => ⟨by omega, h'⟩)) (by omega)

/-- One scan step: bit `i` of the frame. -/
theorem scanBody_spec (hOP : ∀ i, PR i ≠ OP) (hXO : X ≠ O) (σ : WState ns nr) (Wb v i : ℕ)
    (hXs : σ.st X = frame (binary Wb v)) (hi : i < Wb) (hcap : 2 * Wb + 1 ≤ cap) (τ : WState ns nr)
    (hd : WD X O OP PR σ τ [] (2 * i) ![szI v i, i - szI v i, 2 * i, 0]) :
    Runs cap (scanBody X PR) τ (7 * Wb + 18)
      (fun ρ => WD X O OP PR σ ρ [] (2 * (i + 1)) ![szI v (i + 1), (i + 1) - szI v (i + 1), 2 * (i + 1), 0]) := by
  have hsz := szI_le v i
  have hS := szI_succ v i
  refine (hd.fwd hXO).seq' (c2 := 7 * Wb + 16) (fun τ1 h1 => ?_) (by omega)
  refine (h1.incN hOP 2 ![szI v i, i - szI v i, 2 * i + 1, 0] (by simp; omega)
    (by intro j; fin_cases j <;> simp)).seq' (c2 := 7 * Wb + 12) (fun τ2 h2 => ?_) (by omega)
  have hb : wbit τ2 X = v.testBit i := by rw [h2.bit, hXs]; exact frame_testBit Wb v i hi
  refine (Runs.ifs (c := 7 * Wb + 5)
    (Q := fun ρ => WD X O OP PR σ ρ [] (2 * i + 1) ![szI v (i + 1), (i + 1) - szI v (i + 1), 2 * i + 1, 0])
    (fun hT => ?_) (fun hF => ?_)).seq' (c2 := 5) (fun τ3 h3 => ?_) (by omega)
  · rw [hb] at hT
    have h2' := h2.r_eq (r' := ![i - (i - szI v i), i - szI v i, 2 * i + 1, 0])
      (by funext j; fin_cases j <;> simp; omega)
    refine ((moveZ_spec hOP σ [] (2 * i + 1) i (2 * i + 1) 0 (by omega) (i - szI v i) τ2 (by omega) h2').seq'
      (fun τ4 h4 => h4.incN hOP 0 ![szI v (i + 1), (i + 1) - szI v (i + 1), 2 * i + 1, 0] (by simp; omega)
        (by intro j; fin_cases j <;> simp [hS, hT])) (by rfl)).cost ?_
    have : (i - szI v i) * (5 + 2) ≤ 7 * Wb := by
      have : i - szI v i ≤ Wb := by omega
      nlinarith
    omega
  · rw [hb] at hF
    exact (h2.incN hOP 1 ![szI v (i + 1), (i + 1) - szI v (i + 1), 2 * i + 1, 0] (by simp; omega)
      (by intro j; fin_cases j <;> simp [hS, hF] <;> omega)).cost (by omega)
  · refine (h3.fwd hXO).seq' (fun τ4 h4 => h4.incN hOP 2 _ (by simp; omega)
      (by intro j; fin_cases j <;> simp <;> omega)) (by omega)

/-- The scan loop. -/
theorem scan_spec (hOP : ∀ i, PR i ≠ OP) (hXO : X ≠ O) (σ : WState ns nr) (Wb v : ℕ)
    (hXs : σ.st X = frame (binary Wb v)) (hcap : 2 * Wb + 1 ≤ cap)
    (hd : WD X O OP PR σ σ [] 0 ![0, 0, 0, 0]) :
    Runs cap (.whs X (scanBody X PR)) σ (Wb * (7 * Wb + 18 + 2) + 1)
      (fun ρ => WD X O OP PR σ ρ [] (2 * Wb) ![szI v Wb, Wb - szI v Wb, 2 * Wb, 0]) := by
  refine Runs.whs (fun k τ => k ≤ Wb ∧ WD X O OP PR σ τ [] (2 * (Wb - k))
      ![szI v (Wb - k), (Wb - k) - szI v (Wb - k), 2 * (Wb - k), 0]) _ _ ?_ ?_ Wb σ ⟨le_rfl, ?_⟩
  · rintro τ ⟨_, hτ⟩
    refine ⟨by rw [hτ.bit, hXs]; simpa using frame_end Wb v, by simpa using hτ⟩
  · rintro k τ ⟨hk, hτ⟩
    refine ⟨by rw [hτ.bit, hXs]; exact NearCubicWires.WireExponent3_5.UnionMachine.RegRat.frame_marker Wb v _ (by omega), ?_⟩
    have := scanBody_spec hOP hXO σ Wb v (Wb - (k + 1)) hXs (by omega) hcap τ hτ
    refine this.post (fun ρ hρ => ⟨by omega, ?_⟩)
    have e : Wb - (k + 1) + 1 = Wb - k := by omega
    rw [e] at hρ; exact hρ
  · simpa [szI_zero] using hd

/-- Rewind `X` by the position counter `PR 2`. -/
theorem rewX_spec (hOP : ∀ i, PR i ≠ OP) (hXO : X ≠ O) (σ : WState ns nr) (u : List Bool) (a b d : ℕ) :
    ∀ k τ, k ≤ cap → WD X O OP PR σ τ u k ![a, b, k, d] →
      Runs cap (rewX X (PR 2)) τ (k * (3 + 2) + 1) (fun ρ => WD X O OP PR σ ρ u 0 ![a, b, 0, d]) := by
  intro k τ hk hd
  refine Runs.whr (fun k τ => k ≤ cap ∧ WD X O OP PR σ τ u k ![a, b, k, d]) 3 _ ?_ ?_ k τ ⟨hk, hd⟩
  · rintro τ ⟨_, hd⟩; exact ⟨by rw [hd.val 2]; rfl, hd⟩
  · rintro k τ ⟨hk, hd⟩
    refine ⟨by rw [hd.val 2]; simp, ?_⟩
    refine (hd.decN hOP 2 ![a, b, k, d] (by simp; omega) (by intro j; fin_cases j <;> simp)).seq'
      (fun ρ hρ => (hρ.bwd hXO).post (fun _ h' => ⟨by omega, by simpa using h'⟩)) (by omega)

/-- Clear `PR 1`. -/
theorem clrZ_spec (hOP : ∀ i, PR i ≠ OP) (σ : WState ns nr) (u : List Bool) (h a c d : ℕ) :
    ∀ k τ, k ≤ cap → WD X O OP PR σ τ u h ![a, k, c, d] →
      Runs cap (clrR (PR 1)) τ (k * (1 + 2) + 1) (fun ρ => WD X O OP PR σ ρ u h ![a, 0, c, d]) := by
  intro k τ hk hd
  refine Runs.whr (fun k τ => k ≤ cap ∧ WD X O OP PR σ τ u h ![a, k, c, d]) 1 _ ?_ ?_ k τ ⟨hk, hd⟩
  · rintro τ ⟨_, hd⟩; exact ⟨by rw [hd.val 1]; rfl, hd⟩
  · rintro k τ ⟨hk, hd⟩
    refine ⟨by rw [hd.val 1]; simp, ?_⟩
    exact (hd.decN hOP 1 ![a, k, c, d] (by simp; omega) (by intro j; fin_cases j <;> simp)).post
      (fun _ h' => ⟨by omega, h'⟩)

/-- `L := max L 1`. -/
theorem fixL_spec (hOP : ∀ i, PR i ≠ OP) (σ τ : WState ns nr) (u : List Bool) (h l b c d : ℕ) (hl : l < cap)
    (hd : WD X O OP PR σ τ u h ![l, b, c, d]) :
    Runs cap (.ifr (PR 0) WMX.skip (WMX.inc (PR 0))) τ (3 + 1)
      (fun ρ => WD X O OP PR σ ρ u h ![if l = 0 then 1 else l, b, c, d]) := by
  refine Runs.ifr (fun hT => ?_) (fun hF => ?_)
  · rw [hd.val 0] at hT
    simp only [Matrix.cons_val_zero] at hT
    exact (Runs.of (WXExec.skip cap τ) (by rw [if_neg hT]; exact hd)).cost (by omega)
  · rw [hd.val 0] at hF
    simp only [Matrix.cons_val_zero] at hF
    exact hd.incN hOP 0 _ (by simp; omega) (by intro j; fin_cases j <;> simp [hF])

/-- Write `1^L` (moving `L` into `K`). -/
theorem onesW_spec (hXO : X ≠ O) (hOP : ∀ i, PR i ≠ OP) (σ : WState ns nr) (hO0 : σ.sh O = (σ.st O).length)
    (h p Lf : ℕ) (hLf : Lf < cap) (hc : σ.val OP + Lf < cap) :
    ∀ m τ, m ≤ Lf → WD X O OP PR σ τ (List.replicate (Lf - m) true) h ![m, 0, p, Lf - m] →
      Runs cap (onesW O OP PR) τ (m * (13 + 2) + 1)
        (fun ρ => WD X O OP PR σ ρ (List.replicate Lf true) h ![0, 0, p, Lf]) := by
  intro m τ hm hd
  refine Runs.whr (fun m τ => m ≤ Lf ∧ WD X O OP PR σ τ (List.replicate (Lf - m) true) h ![m, 0, p, Lf - m])
    13 _ ?_ ?_ m τ ⟨hm, hd⟩
  · rintro τ ⟨_, hd⟩; exact ⟨by rw [hd.val 0]; rfl, by simpa using hd⟩
  · rintro m τ ⟨hm, hd⟩
    refine ⟨by rw [hd.val 0]; simp, ?_⟩
    refine (hd.decN hOP 0 ![m, 0, p, Lf - (m + 1)] (by simp; omega) (by intro j; fin_cases j <;> simp)).seq'
      (fun ρ hρ => (hρ.incN hOP 3 ![m, 0, p, Lf - m] (by simp; omega)
        (by intro j; fin_cases j <;> simp <;> omega)).seq' (fun ρ2 h2 => (h2.emit hXO hOP hO0 true
          (by simp; omega)).post (fun _ h' => ⟨by omega, ?_⟩)) (by rfl)) (by omega)
    have e : List.replicate (Lf - (m + 1)) true ++ [true] = List.replicate (Lf - m) true := by
      rw [← List.replicate_succ']; congr 1; omega
    rwa [e] at h'

/-- Copy the first `Lf` bits of `X`. -/
theorem bitsW_spec (hXO : X ≠ O) (hOP : ∀ i, PR i ≠ OP) (σ : WState ns nr) (hO0 : σ.sh O = (σ.st O).length)
    (Wb v Lf : ℕ) (hXs : σ.st X = frame (binary Wb v)) (hLW : Lf ≤ Wb) (pre : List Bool)
    (hcap : 2 * Wb + 1 ≤ cap) (hc : σ.val OP + pre.length + Lf < cap) :
    ∀ m τ, m ≤ Lf → WD X O OP PR σ τ (pre ++ (List.range (Lf - m)).map v.testBit) (2 * (Lf - m))
        ![0, 0, 2 * (Lf - m), m] →
      Runs cap (bitsW X O OP PR) τ (m * (22 + 2) + 1)
        (fun ρ => WD X O OP PR σ ρ (pre ++ (List.range Lf).map v.testBit) (2 * Lf) ![0, 0, 2 * Lf, 0]) := by
  intro m τ hm hd
  refine Runs.whr (fun m τ => m ≤ Lf ∧ WD X O OP PR σ τ (pre ++ (List.range (Lf - m)).map v.testBit)
    (2 * (Lf - m)) ![0, 0, 2 * (Lf - m), m]) 22 _ ?_ ?_ m τ ⟨hm, hd⟩
  · rintro τ ⟨_, hd⟩; exact ⟨by rw [hd.val 3]; rfl, by simpa using hd⟩
  · rintro m τ ⟨hm, hd⟩
    refine ⟨by rw [hd.val 3]; simp, ?_⟩
    set j := Lf - (m + 1) with hj
    have hjm : Lf - m = j + 1 := by omega
    rw [hjm] at *
    refine (hd.decN hOP 3 ![0, 0, 2 * j, m] (by simp; omega) (by intro j; fin_cases j <;> simp)).seq'
      (c2 := 20) (fun τ1 h1 => ?_) (by omega)
    refine (h1.fwd hXO).seq' (c2 := 18) (fun τ2 h2 => ?_) (by omega)
    refine (h2.incN hOP 2 ![0, 0, 2 * j + 1, m] (by simp; omega) (by intro j; fin_cases j <;> simp)).seq'
      (c2 := 14) (fun τ3 h3 => ?_) (by omega)
    have hb : wbit τ3 X = v.testBit j := by rw [h3.bit, hXs]; exact frame_testBit Wb v j (by omega)
    have hlen : σ.val OP + (pre ++ (List.range j).map v.testBit).length < cap := by simp; omega
    refine (Runs.ifs (c := 7)
      (Q := fun ρ => WD X O OP PR σ ρ (pre ++ (List.range (j + 1)).map v.testBit) (2 * j + 1) ![0, 0, 2 * j + 1, m])
      (fun hT => ?_) (fun hF => ?_)).seq' (c2 := 5) (fun τ4 h4 => ?_) (by omega)
    · rw [hb] at hT
      refine (h3.emit hXO hOP hO0 true hlen).post (fun _ h' => ?_)
      rw [List.range_succ, List.map_append, ← List.append_assoc]; simpa [hT] using h'
    · rw [hb] at hF
      refine (h3.emit hXO hOP hO0 false hlen).post (fun _ h' => ?_)
      rw [List.range_succ, List.map_append, ← List.append_assoc]; simpa [hF] using h'
    · refine (h4.fwd hXO).seq' (fun τ5 h5 => (h5.incN hOP 2 ![0, 0, 2 * (j + 1), m] (by simp; omega)
        (by intro j; fin_cases j <;> simp <;> omega)).post (fun _ h' => ⟨by omega, ?_⟩)) (by rfl)
      have e : 2 * j + 1 + 1 = 2 * (j + 1) := by ring
      rw [e] at h'; exact h'

/-- The writer's clean frame: `u` appended to `O`, only `O` and `OP` changed. -/
def Emitted (O : Fin (ns + 1)) (OP : Fin nr) (σ τ : WState ns nr) (u : List Bool) : Prop :=
  SameExcept σ τ [O] [OP] ∧ τ.st O = σ.st O ++ u ∧ τ.sh O = σ.sh O + u.length ∧ τ.val OP = σ.val OP + u.length

theorem Emitted.refl (σ : WState ns nr) : Emitted O OP σ σ [] :=
  ⟨SameExcept.refl _ _ _, by simp, by simp, by simp⟩

theorem Emitted.trans {σ τ ρ : WState ns nr} {u u' : List Bool} (h1 : Emitted O OP σ τ u)
    (h2 : Emitted O OP τ ρ u') : Emitted O OP σ ρ (u ++ u') :=
  ⟨h1.1.trans h2.1, by rw [h2.2.1, h1.2.1, List.append_assoc], by rw [h2.2.2.1, h1.2.2.1]; simp; ring,
    by rw [h2.2.2.2, h1.2.2.2]; simp; ring⟩

theorem WD.emitted {σ τ : WState ns nr} {u : List Bool} (hd : WD X O OP PR σ τ u 0 ![0, 0, 0, 0])
    (hXh : σ.sh X = 0) (hR : ∀ i, σ.val (PR i) = 0) : Emitted O OP σ τ u := by
  obtain ⟨hs, hX, hO, hOh, hOP', hh, hr⟩ := hd
  refine ⟨⟨fun x hx => ?_, fun q hq => ?_, hs.2.2⟩, hO, hOh, hOP'⟩
  · by_cases e : x = X
    · subst e; exact ⟨hX, by rw [hh, hXh]⟩
    · exact hs.1 x (by simp at hx ⊢; exact ⟨e, hx⟩)
  · by_cases e : ∃ i, q = PR i
    · obtain ⟨i, rfl⟩ := e
      rw [hr i, hR i]; fin_cases i <;> rfl
    · simp only [not_exists] at e
      exact hs.2.1 q (by simp at hq ⊢; exact ⟨hq, e 0, e 1, e 2, e 3⟩)

/-- **The raw `natWord` writer**: append `natWord v` to `O`. -/
theorem natW_spec (hOP : ∀ i, PR i ≠ OP) (hXO : X ≠ O) (σ : WState ns nr) (Wb v : ℕ) (hX : NumOn σ X Wb v)
    (hv : v < 2 ^ Wb) (hW : 1 ≤ Wb) (hR : ∀ i, σ.val (PR i) = 0) (hO0 : σ.sh O = (σ.st O).length)
    (hcap : 2 * Wb + 2 ≤ cap) (hcO : σ.val OP + 2 * Wb + 2 ≤ cap) :
    Runs cap (natW X O OP PR) σ (natWCost Wb) (fun ρ => Emitted O OP σ ρ (natWord v)) := by
  obtain ⟨hXs, hXh⟩ := hX
  have hd0 : WD X O OP PR σ σ [] 0 ![0, 0, 0, 0] :=
    ⟨SameExcept.refl _ _ _, rfl, by simp, by simp, by simp, hXh, by intro i; rw [hR i]; fin_cases i <;> rfl⟩
  have hsz : szI v Wb = Nat.size v := by unfold szI; rw [Nat.mod_eq_of_lt hv]
  have hszW : szI v Wb ≤ Wb := szI_le v Wb
  have hLf : lenF v ≤ Wb := lenF_le v Wb hv hW
  have hLfe : (if szI v Wb = 0 then 1 else szI v Wb) = lenF v := by rw [hsz]; rfl
  have hpost : ∀ ρ, WD X O OP PR σ ρ (natWord v) 0 ![0, 0, 0, 0] → Emitted O OP σ ρ (natWord v) :=
    fun ρ h => h.emitted hXh hR
  refine Runs.cost (c := Wb * (7 * Wb + 18 + 2) + 1 + 1 + ((2 * Wb) * (3 + 2) + 1 + 1 +
    ((Wb - szI v Wb) * (1 + 2) + 1 + 1 + ((3 + 1) + 1 + (lenF v * (13 + 2) + 1 + 1 + (7 + 1 +
      (lenF v * (22 + 2) + 1 + 1 + ((2 * lenF v) * (3 + 2) + 1)))))))) ?_ ?_
  swap
  · have : (Wb - szI v Wb) * (1 + 2) ≤ 3 * Wb := by omega
    unfold natWCost; nlinarith
  refine Runs.seq (scan_spec hOP hXO σ Wb v hXs (by omega) hd0) (fun τ1 h1 => ?_)
  refine Runs.seq (rewX_spec hOP hXO σ [] _ _ 0 (2 * Wb) τ1 (by omega) h1) (fun τ2 h2 => ?_)
  refine Runs.seq (clrZ_spec hOP σ [] 0 _ 0 0 (Wb - szI v Wb) τ2 (by omega) h2) (fun τ3 h3 => ?_)
  refine Runs.seq (fixL_spec hOP σ τ3 [] 0 _ 0 0 0 (by omega) h3) (fun τ4 h4 => ?_)
  rw [hLfe] at h4
  have h4' := h4.r_eq (r' := ![lenF v, 0, 0, lenF v - lenF v]) (by funext j; fin_cases j <;> simp)
  refine Runs.seq (onesW_spec hXO hOP σ hO0 0 0 (lenF v) (by omega) (by omega) (lenF v) τ4 le_rfl
    (by simpa using h4')) (fun τ5 h5 => ?_)
  refine Runs.seq (h5.emit hXO hOP hO0 false (by simp; omega)) (fun τ6 h6 => ?_)
  have h6' := h6.r_eq (r' := ![0, 0, 2 * (lenF v - lenF v), lenF v]) (by funext j; fin_cases j <;> simp)
  refine Runs.seq (bitsW_spec hXO hOP σ hO0 Wb v (lenF v) hXs hLf (List.replicate (lenF v) true ++ [false])
    (by omega) (by simp; omega) (lenF v) τ6 le_rfl (by simpa using h6')) (fun τ7 h7 => ?_)
  refine (rewX_spec hOP hXO σ _ 0 0 0 (2 * lenF v) τ7 (by omega) h7).post (fun ρ hρ => hpost ρ ?_)
  rw [natWord_eq_lenF]; simpa using hρ

end Loops

end NearCubicGates.Close.Expand
