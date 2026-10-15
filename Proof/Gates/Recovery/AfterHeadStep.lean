import Proof.Gates.Recovery.AfterStep

set_option autoImplicit false

namespace NearCubicGates.Close.Recovery.After

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairSource.OrdinaryOracleCompose NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicGates.Close.Transfer NearCubicGates.Close.Gadget

variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams} (K : Kit s P g)

/-- The private blocks from piece `k` on are blank. -/
def BlankFrom (k : ℕ) (A : Fin (T K) → List Bool) : Prop := ∀ x : Fin (T K), off K k ≤ x.val → A x = []

theorem sh_lt_off (i : Fin 32) (k : ℕ) : (sh K i).val < off K k := by
  have := off_ge K k
  have := i.isLt
  simp only [sh_val]
  omega

theorem blank_sh (k : ℕ) (A : Fin (T K) → List Bool) (h : BlankFrom K k A) (x : Fin (T K)) (hx : off K k ≤ x.val) :
    A x = [] := h x hx

theorem off_succ (k : ℕ) : off K (k + 1) = off K k + sz K k := rfl

/-- **A machine piece on a `mkBank` bank.** -/
theorem bank_piece (k : ℕ) (hk : k < 31) {t st : ℕ} (ht : sz K k = t) (l : List (Fin t × Fin 32))
    (h1 : (l.map Prod.fst).Nodup) (h2 : (l.map Prod.snd).Nodup) {M : Machine t st} {n : ℕ}
    {inp out : Fin t → List Bool} (h : RecoveryRootRound.ReadyRun M n inp out) (A : Fin (T K) → List Bool)
    (hport : ∀ p ∈ l, A (sh K p.2) = inp p.1) (hfree : ∀ j, j ∉ l.map Prod.fst → inp j = [])
    (hbl : BlankFrom K k A) :
    Ready RecoveryOracle.correctedSat
        ((ports K).program (ordinary (RecoveryFocus.machine (mkBank K k hk ht l h1 h2).slot M))) n A
        (install (mkBank K k hk ht l h1 h2).slot A out) ∧
      BlankFrom K (k + 1) (install (mkBank K k hk ht l h1 h2).slot A out) ∧
      (∀ i : Fin 32, i ∉ l.map Prod.snd → install (mkBank K k hk ht l h1 h2).slot A out (sh K i) = A (sh K i)) ∧
      (∀ p ∈ l, install (mkBank K k hk ht l h1 h2).slot A out (sh K p.2) = out p.1) := by
  set b := mkBank K k hk ht l h1 h2 with hbdef
  have hmem : ∀ (j : Fin t) (x : Fin (T K)), (j, x) ∈ b.l ↔ ∃ p ∈ l, p.1 = j ∧ sh K p.2 = x := by
    intro j x
    simp only [hbdef, mkBank, List.mem_map, Prod.mk.injEq]
  have hoff : b.off = off K k := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply piece_ordinary (ports K) h b.slot b.injective A
    apply b.input A inp
    · intro p hp
      obtain ⟨q, hq, h1', h2'⟩ := (hmem p.1 p.2).mp hp
      rw [← h2', ← h1']
      exact hport q hq
    · intro j hj
      apply hfree
      intro hm
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
      exact hj (q.1, sh K q.2) ((hmem _ _).mpr ⟨q, hq, rfl, rfl⟩) rfl
    · intro x hx _
      exact hbl x (by rw [hoff] at hx; exact hx)
  · intro x hx
    rw [Bank.install_high b A out x (by rw [hoff]; rw [off_succ] at hx; rw [← ht]; omega)]
    exact hbl x (by rw [off_succ] at hx; omega)
  · intro i hi
    rw [Bank.install_low b A out (sh K i) (by rw [hoff]; exact sh_lt_off K i k)]
    apply updates_not
    intro p hp he
    obtain ⟨q, hq, _, h2'⟩ := (hmem p.1 p.2).mp hp
    have : q.2 = i := (sh_inj K q.2 i).mp (h2'.trans he)
    exact hi (List.mem_map.mpr ⟨q, hq, this⟩)
  · intro p hp
    exact Bank.install_port b A out ((hmem p.1 (sh K p.2)).mpr ⟨p, hp, rfl, rfl⟩)

/-- The copy's log tape is the first tape of block `k`. -/
theorem blk_val (k : ℕ) (hk : k < 31) (hs : 1 ≤ sz K k) : (blk K k hk hs).val = off K k := rfl

theorem tslot_injective (k : ℕ) (hk : k < 31) (hs : 1 ≤ sz K k) (a b : Fin 32) (hab : a ≠ b) :
    Function.Injective (tslot K k hk hs (sh K a) (sh K b)) := by
  have ha := sh_lt_off K a k
  have hb := sh_lt_off K b k
  simp only [sh_val] at ha hb
  intro i j he
  have hv := congrArg Fin.val he
  fin_cases i <;> fin_cases j <;> simp [tslot, blk_val] at hv ⊢ <;> omega

/-- **A framed copy piece** `a → b` with its log in block `k`. -/
theorem copy_piece (k : ℕ) (hk : k < 31) (hs : 1 ≤ sz K k) (a b : Fin 32) (hab : a ≠ b)
    (A : Fin (T K) → List Bool) (bits padding : List Bool) (ha : A (sh K a) = RepairOrdinary.frame bits ++ padding)
    (hb : A (sh K b) = []) (hbl : BlankFrom K k A) :
    ∃ A' : Fin (T K) → List Bool,
      Ready RecoveryOracle.correctedSat ((ports K).program (copyP K k hk hs (sh K a) (sh K b)))
        (4 * bits.length + 4) A A' ∧
      BlankFrom K (k + 1) A' ∧ (∀ i : Fin 32, i ≠ b → A' (sh K i) = A (sh K i)) ∧
      A' (sh K b) = RepairOrdinary.frame bits := by
  classical
  have hl : A (blk K k hk hs) = [] := hbl _ (by rw [blk_val])
  have h := copy_ready (tslot K k hk hs (sh K a) (sh K b)) (tslot_injective K k hk hs a b hab) A bits padding
    ha hb hl
  refine ⟨_, Ready.ordinary (ports K) h, ?_, ?_, ?_⟩
  · intro x hx
    have hx' : x ≠ blk K k hk hs := by
      intro he; rw [he, blk_val, off_succ] at hx; omega
    have hxb : x ≠ sh K b := by
      intro he; have := sh_lt_off K b (k + 1); rw [← he] at this; omega
    change Function.update (Function.update A (sh K b) _) (blk K k hk hs) _ x = []
    rw [Function.update_apply, if_neg hx', Function.update_apply, if_neg hxb]
    exact hbl x (by rw [off_succ] at hx; omega)
  · intro i hi
    have h1 : sh K i ≠ blk K k hk hs := by
      intro he; have := sh_lt_off K i k; rw [he, blk_val] at this; omega
    have h2 : sh K i ≠ sh K b := fun he => hi ((sh_inj K i b).mp he)
    change Function.update (Function.update A (sh K b) _) (blk K k hk hs) _ (sh K i) = _
    rw [Function.update_apply, if_neg h1, Function.update_apply, if_neg h2]
  · have h1 : sh K b ≠ blk K k hk hs := by
      intro he; have := sh_lt_off K b k; rw [he, blk_val] at this; omega
    change Function.update (Function.update A (sh K b) _) (blk K k hk hs) _ (sh K b) = _
    rw [Function.update_apply, if_neg h1, Function.update_apply, if_pos rfl]

end NearCubicGates.Close.Recovery.After
