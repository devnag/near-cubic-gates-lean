import Proof.Gates.CheckedPCPP.WMXReady

/-!
# Pieces of the refuter program as word programs (input 7, R: WMX ⇒ head-0 runs)

Each ordinary piece of the call graph (`RProgram.lean`) is ONE compiled word program (`WMX`, L
`Proof/Gates/WordPrograms/WMX.lean`). Between pieces the physical tapes are only known up to what
the word semantics fixes: `Parked E σ a` says the physical tapes `a` read like the word state `σ`
(registers `0`, result cell `false`), and agree exactly with `σ` on the streams in `E` (the streams
whose exact contents matter: the output, the query, every stream a later run copies or appends to).
Streams outside `E` (scratch logs that the word semantics models as preallocated blank cells) only
read alike.

`ready_parked` transports one word derivation `σ → τ` (both parked: heads and registers `0`, cell
`false`) to a physical head-0 run of the compiled machine from ANY parked tapes; it generalizes L's
`CheckedPCPP.WXExec.ready` (which starts from the cold bank only). This is what lets the same STEP
machine run again and again on the tapes the previous round left.
-/

namespace NearCubicGates.Adapters.Refuter.Mach

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP NearCubicWires.WireExponent3_5

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false

variable {ns nr : ℕ}

/-- Physical tapes `a` of a parked word state `σ`: streams read alike and are exact on `E`; the
result cell and every register read blank. -/
structure Parked (E : Fin (ns + 1) → Prop) (σ : WState ns nr) (a : Fin (ns + 2 + nr) → List Bool) : Prop where
  read : ∀ i, RdEq (σ.st i) (a (sTape i))
  exact : ∀ i, E i → a (sTape i) = σ.st i
  cell : RdEq [] (a cTape)
  reg : ∀ r, RdEq [] (a (rTape r))

/-- A word state with every head and register at `0` and the cell `false`. -/
structure Rest (σ : WState ns nr) : Prop where
  sh : ∀ i, σ.sh i = 0
  val : ∀ r, σ.val r = 0
  cell : σ.cell = false

/-- The initial physical tapes are parked for the word state with the same streams. -/
theorem parked_cold (E : Fin (ns + 1) → Prop) (σ : WState ns nr) : Parked E σ (coldBank σ) :=
  ⟨fun i => by rw [coldBank_s]; exact RdEq.refl _, fun i _ => by rw [coldBank_s],
    by rw [coldBank_c]; exact RdEq.refl _, fun r => by rw [coldBank_r]; exact RdEq.refl _⟩

/-- **One parked piece run.** A word derivation between rest states runs physically from any parked
tapes to parked tapes, all heads returning to `0`, within the derivation's step count. -/
theorem ready_parked {cap : ℕ} {P : WMX ns nr} {σ τ : WState ns nr} {n : ℕ} (h : WXExec cap P σ τ n)
    (hσ : Rest σ) (hτ : Rest τ) (E : Fin (ns + 1) → Prop) (a : Fin (ns + 2 + nr) → List Bool)
    (ha : Parked E σ a) :
    ∃ b, ClockJoin.ReadyRun P.compile n a b ∧ Parked E τ b := by
  obtain ⟨r, hr, hh, ht, hs⟩ := WXExec.run cap h hσ.sh hσ.val
  let E' : Fin (ns + 2 + nr) → Prop := fun j => ∃ i, E i ∧ j = sTape i
  have hrel : ConfRel E' (initialConfiguration P.compile (wenc cap σ).A)
      (initialConfiguration P.compile a) := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · intro j
      simp only [initialConfiguration]
      rcases PrimAsm.DockW.tape_cases j with ⟨i, rfl⟩ | rfl | ⟨q, rfl⟩
      · rw [wenc_A_s]; exact ha.read i
      · rw [PrimAsm.DockW.wenc_A_c, hσ.cell]
        exact (rdEq_blank _ (by simp)).trans ha.cell
      · rw [wenc_A_r, hσ.val q, regTape_zero]
        exact (rdEq_blank _ (by simp)).trans (ha.reg q)
    · rintro j ⟨i, hi, rfl⟩
      simp only [initialConfiguration]
      rw [wenc_A_s, ha.exact i hi]
  obtain ⟨r', hr', hrel', hst⟩ := runFrom_rel P.compile E' n hrel r hr
  refine ⟨r'.final.tapes, ⟨r', hr', rfl, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro j
    rw [← hrel'.heads, hh]
    rcases PrimAsm.DockW.tape_cases j with ⟨i, rfl⟩ | rfl | ⟨q, rfl⟩
    · rw [wenc_H_s]; exact hτ.sh i
    · exact PrimAsm.DockW.wenc_H_c cap τ
    · rw [wenc_H_r]; exact hτ.val q
  · rw [hst]; exact hs
  · intro i
    have := hrel'.read (sTape i)
    rw [ht, wenc_A_s] at this
    exact this
  · intro i hi
    rw [← hrel'.exact (sTape i) ⟨i, hi, rfl⟩, ht, wenc_A_s]
  · have := hrel'.read cTape
    rw [ht, PrimAsm.DockW.wenc_A_c, hτ.cell] at this
    exact (rdEq_blank [false] (by simp)).symm.trans this
  · intro q
    have := hrel'.read (rTape q)
    rw [ht, wenc_A_r, hτ.val q, regTape_zero] at this
    exact (rdEq_blank _ (by simp)).symm.trans this

/-- A parked tape set reads, at cell `0` of a stream, the stream's first cell. -/
theorem Parked.read0 {E : Fin (ns + 1) → Prop} {σ : WState ns nr} {a : Fin (ns + 2 + nr) → List Bool}
    (h : Parked E σ a) (i : Fin (ns + 1)) : readTapeBit (a (sTape i)) 0 = readTapeBit (σ.st i) 0 :=
  (h.read i 0).symm

/-- The oracle step's answer write (`RecoveryQueryAnswer.output`: cell `0` of an exact stream `A`)
keeps the tapes parked for the word state with the same write. -/
theorem Parked.answer {E : Fin (ns + 1) → Prop} {σ : WState ns nr} {a : Fin (ns + 2 + nr) → List Bool}
    (h : Parked E σ a) (A : Fin (ns + 1)) (hA : E A) (bit : Bool) :
    Parked E (σ.sets A (writeTapeBit (σ.st A) 0 bit))
      (Function.update a (sTape A) (writeTapeBit (a (sTape A)) 0 bit)) := by
  have hex := h.exact A hA
  have hs : ∀ i : Fin (ns + 1), sTape (nr := nr) i = sTape A → i = A := by
    intro i hi
    have := congrArg Fin.val hi
    simp only [sTape] at this
    ext; split_ifs at this <;> omega
  have hc : ∀ i : Fin (ns + 1), sTape (nr := nr) i ≠ cTape := by
    intro i hi; have := congrArg Fin.val hi; simp only [sTape, cTape] at this; split_ifs at this <;> omega
  have hr : ∀ (i : Fin (ns + 1)) (r : Fin nr), sTape (nr := nr) i ≠ rTape r := by
    intro i r hi; have h1 := congrArg Fin.val hi; simp only [sTape, rTape] at h1
    have := i.isLt; split_ifs at h1 <;> omega
  refine ⟨fun i => ?_, fun i hi => ?_, ?_, fun r => ?_⟩
  · by_cases hi : i = A
    · subst hi; simp [hex, RdEq.refl]
    · rw [Function.update_of_ne (fun h' => hi (hs i h'))]
      simp only [WState.sets_st, Function.update_of_ne hi]
      exact h.read i
  · by_cases hi' : i = A
    · subst hi'; simp [hex]
    · rw [Function.update_of_ne (fun h' => hi' (hs i h'))]
      simp only [WState.sets_st, Function.update_of_ne hi']
      exact h.exact i hi
  · rw [Function.update_of_ne (fun h' => hc A h'.symm)]; exact h.cell
  · rw [Function.update_of_ne (fun h' => hr A r h'.symm)]; exact h.reg r

end NearCubicGates.Adapters.Refuter.Mach
