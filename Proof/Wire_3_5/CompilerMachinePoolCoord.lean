import Proof.Wire_3_5.CompilerMachinePoolBody

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

noncomputable def eLpos := Composition.machine (RecoveryFocus.machine bEmPL emitM) (RecoveryFocus.machine bEmNL emitM)
noncomputable def eLneg := Composition.machine (RecoveryFocus.machine bEmNL emitM) (RecoveryFocus.machine bEmPL emitM)
noncomputable def eRpos := Composition.machine (RecoveryFocus.machine bEmPR emitM) (RecoveryFocus.machine bEmNR emitM)
noncomputable def eRneg := Composition.machine (RecoveryFocus.machine bEmNR emitM) (RecoveryFocus.machine bEmPR emitM)
/-- Append the pair to the side's buffer, swapped when flipped. -/
noncomputable def emitBr := branchM 1 (branchM 2 eLneg eLpos) (branchM 2 eRneg eRpos)

def emitCost (h : ℕ) : ℕ := regCost h + 1 + regCost h + 2 + 2

theorem emit_br (h Pw Nw : ℕ) (tP tN NM SD FR PA NA TM L BL R BR : List Bool) (a sd fr cap : ℕ) (s f : Bool)
    (hs : readTapeBit SD sd = s) (hf : readTapeBit FR fr = f) (hcap : 2 * h + 1 ≤ cap) :
    Step emitBr (emitCost h) (pH a sd fr L.length R.length)
      (pA NM SD FR (frame (binary h Pw) ++ tP) (frame (binary h Nw) ++ tN) (overlay L BL) (overlay R BR) PA NA TM
        (List.replicate cap false))
      (pH a sd fr (if s then L ++ pairF h f (Pw, Nw) else L).length (if s then R else R ++ pairF h f (Pw, Nw)).length)
      (pA NM SD FR (frame (binary h Pw) ++ tP) (frame (binary h Nw) ++ tN)
        (overlay (if s then L ++ pairF h f (Pw, Nw) else L) BL) (overlay (if s then R else R ++ pairF h f (Pw, Nw)) BR)
        PA NA TM (List.replicate cap false)) := by
  have hc : 2 * (binary h Pw).length + 1 ≤ cap := by simp; omega
  have hc' : 2 * (binary h Nw).length + 1 ≤ cap := by simp; omega
  cases s <;> cases f
  · -- right, not flipped
    have e1 := ps_emPR NM SD FR PA NA TM a sd fr cap (binary h Pw) tP (frame (binary h Nw) ++ tN) R BR (overlay L BL)
      L.length hc
    have e2 := ps_emNR NM SD FR PA NA TM a sd fr cap (binary h Nw) tN (frame (binary h Pw) ++ tP)
      (R ++ frame (binary h Pw)) BR (overlay L BL) L.length hc'
    have j := e1.seq e2
    simp only [binary_length] at j
    have b1 := branch_false 2 eRneg j (by simpa [pA, pH] using hf)
    have b2 := branch_false 1 (branchM 2 eLneg eLpos) b1 (by simpa [pA, pH] using hs)
    simp only [pairF, if_false, Bool.false_eq_true, List.append_assoc] at b2 ⊢
    unfold emitCost regCost
    exact b2
  · -- right, flipped
    have e1 := ps_emNR NM SD FR PA NA TM a sd fr cap (binary h Nw) tN (frame (binary h Pw) ++ tP) R BR (overlay L BL)
      L.length hc'
    have e2 := ps_emPR NM SD FR PA NA TM a sd fr cap (binary h Pw) tP (frame (binary h Nw) ++ tN)
      (R ++ frame (binary h Nw)) BR (overlay L BL) L.length hc
    have j := e1.seq e2
    simp only [binary_length] at j
    have b1 := branch_true 2 eRpos j (by simpa [pA, pH] using hf)
    have b2 := branch_false 1 (branchM 2 eLneg eLpos) b1 (by simpa [pA, pH] using hs)
    simp only [pairF, if_true, if_false, Bool.false_eq_true, List.append_assoc] at b2 ⊢
    unfold emitCost regCost
    exact b2
  · -- left, not flipped
    have e1 := ps_emPL NM SD FR PA NA TM a sd fr cap (binary h Pw) tP (frame (binary h Nw) ++ tN) L BL (overlay R BR)
      R.length hc
    have e2 := ps_emNL NM SD FR PA NA TM a sd fr cap (binary h Nw) tN (frame (binary h Pw) ++ tP)
      (L ++ frame (binary h Pw)) BL (overlay R BR) R.length hc'
    have j := e1.seq e2
    simp only [binary_length] at j
    have b1 := branch_false 2 eLneg j (by simpa [pA, pH] using hf)
    have b2 := branch_true 1 (branchM 2 eRneg eRpos) b1 (by simpa [pA, pH] using hs)
    simp only [pairF, if_true, if_false, Bool.false_eq_true, List.append_assoc] at b2 ⊢
    unfold emitCost regCost
    exact b2
  · -- left, flipped
    have e1 := ps_emNL NM SD FR PA NA TM a sd fr cap (binary h Nw) tN (frame (binary h Pw) ++ tP) L BL (overlay R BR)
      R.length hc'
    have e2 := ps_emPL NM SD FR PA NA TM a sd fr cap (binary h Pw) tP (frame (binary h Nw) ++ tN)
      (L ++ frame (binary h Nw)) BL (overlay R BR) R.length hc
    have j := e1.seq e2
    simp only [binary_length] at j
    have b1 := branch_true 2 eLpos j (by simpa [pA, pH] using hf)
    have b2 := branch_true 1 (branchM 2 eRneg eRpos) b1 (by simpa [pA, pH] using hs)
    simp only [pairF, if_true, List.append_assoc] at b2 ⊢
    unfold emitCost regCost
    exact b2

/-- Add the swapped pair into the target accumulators (`PACC += N`, `NACC += P`). -/
noncomputable def addSeq := Composition.machine (RecoveryFocus.machine bZipP (zipM addOut addNxt false))
  (Composition.machine (RecoveryFocus.machine bCpP regCopyM)
    (Composition.machine (RecoveryFocus.machine bZipN (zipM addOut addNxt false)) (RecoveryFocus.machine bCpN regCopyM)))
/-- Add only when the coordinate is flipped. -/
noncomputable def addBr := branchM 2 addSeq (idle 11)

def addCost (h : ℕ) : ℕ := regCost h + 1 + (regCost h + 1 + (regCost h + 1 + regCost h))

/-- The accumulators and scratch register after one coordinate. -/
def accP (fl : Bool) (P Nw : ℕ) : ℕ := if fl then P + Nw else P
def accN (fl : Bool) (N Pw : ℕ) : ℕ := if fl then N + Pw else N
def tmpAfter (h : ℕ) (fl : Bool) (P N Pw Nw : ℕ) (T : List Bool) : List Bool :=
  if fl then overlay (frame (binary h (N + Pw))) (overlay (frame (binary h (P + Nw))) T) else T

theorem add_br (h P N Pw Nw : ℕ) (tP tN NM SD FR OL OR PA0 NA0 T : List Bool) (a sd fr oL oR cap : ℕ) (f : Bool)
    (hf : readTapeBit FR fr = f) (hcap : 2 * h + 1 ≤ cap) :
    Step addBr (addCost h + 2) (pH a sd fr oL oR)
      (pA NM SD FR (frame (binary h Pw) ++ tP) (frame (binary h Nw) ++ tN) OL OR
        (overlay (frame (binary h P)) PA0) (overlay (frame (binary h N)) NA0) T (List.replicate cap false))
      (pH a sd fr oL oR)
      (pA NM SD FR (frame (binary h Pw) ++ tP) (frame (binary h Nw) ++ tN) OL OR
        (overlay (frame (binary h (accP f P Nw))) PA0) (overlay (frame (binary h (accN f N Pw))) NA0)
        (tmpAfter h f P N Pw Nw T) (List.replicate cap false)) := by
  have hc : 2 * (binary h 0).length + 1 ≤ cap := by simp; omega
  cases f
  · have e := idleStep (pH a sd fr oL oR)
      (pA NM SD FR (frame (binary h Pw) ++ tP) (frame (binary h Nw) ++ tN) OL OR
        (overlay (frame (binary h P)) PA0) (overlay (frame (binary h N)) NA0) T (List.replicate cap false))
    have b := branch_false 2 addSeq (e.enlarge (Nat.zero_le (addCost h))) (by simpa [pA, pH] using hf)
    simp only [accP, accN, tmpAfter, if_false, Bool.false_eq_true]
    exact b
  · have hl : (binary h P).length = (binary h Nw).length := by simp
    have hl2 : (binary h N).length = (binary h Pw).length := by simp
    have hbl : ∀ x, 2 * (binary h x).length + 1 ≤ cap := by intro x; simp; omega
    have hrc : ∀ x, 2 * (2 * (binary h x).length + 1) + 2 = regCost h := by intro x; simp [regCost]
    set RPt := frame (binary h Pw) ++ tP
    set RNt := frame (binary h Nw) ++ tN
    set PAi := overlay (frame (binary h P)) PA0
    set NAi := overlay (frame (binary h N)) NA0
    set TMP1 := overlay (frame (binary h (P + Nw))) T
    set PA1 := overlay (frame (binary h (P + Nw))) PA0
    set TMP2 := overlay (frame (binary h (N + Pw))) TMP1
    set NA1 := overlay (frame (binary h (N + Pw))) NA0
    set lg := List.replicate cap false
    have s1 : Step (RecoveryFocus.machine bZipP (zipM addOut addNxt false)) (regCost h) (pH a sd fr oL oR)
        (pA NM SD FR RPt RNt OL OR PAi NAi T lg) (pH a sd fr oL oR) (pA NM SD FR RPt RNt OL OR PAi NAi TMP1 lg) := by
      have z := ps_zipP NM SD FR OL OR a sd fr oL oR cap (binary h P) (PA0.drop (frame (binary h P)).length)
        RPt (binary h Nw) tN NAi T hl (hbl P)
      rw [map_add] at z
      exact z.enlarge (le_of_eq (hrc P))
    have s2 : Step (RecoveryFocus.machine bCpP regCopyM) (regCost h) (pH a sd fr oL oR)
        (pA NM SD FR RPt RNt OL OR PAi NAi TMP1 lg) (pH a sd fr oL oR) (pA NM SD FR RPt RNt OL OR PA1 NAi TMP1 lg) := by
      have c := ps_cpP NM SD FR OL OR a sd fr oL oR cap (binary h (P + Nw)) (T.drop (frame (binary h (P + Nw))).length)
        RPt RNt PAi NAi (hbl (P + Nw))
      have e : overlay (frame (binary h (P + Nw))) PAi = PA1 := overlay_collapse _ _ _ (by simp)
      rw [e] at c
      exact c.enlarge (le_of_eq (hrc (P + Nw)))
    have s3 : Step (RecoveryFocus.machine bZipN (zipM addOut addNxt false)) (regCost h) (pH a sd fr oL oR)
        (pA NM SD FR RPt RNt OL OR PA1 NAi TMP1 lg) (pH a sd fr oL oR) (pA NM SD FR RPt RNt OL OR PA1 NAi TMP2 lg) := by
      have z := ps_zipN NM SD FR OL OR a sd fr oL oR cap (binary h N) (NA0.drop (frame (binary h N)).length)
        RNt (binary h Pw) tP PA1 TMP1 hl2 (hbl N)
      rw [map_add] at z
      exact z.enlarge (le_of_eq (hrc N))
    have s4 : Step (RecoveryFocus.machine bCpN regCopyM) (regCost h) (pH a sd fr oL oR)
        (pA NM SD FR RPt RNt OL OR PA1 NAi TMP2 lg) (pH a sd fr oL oR) (pA NM SD FR RPt RNt OL OR PA1 NA1 TMP2 lg) := by
      have c := ps_cpN NM SD FR OL OR a sd fr oL oR cap (binary h (N + Pw))
        (TMP1.drop (frame (binary h (N + Pw))).length) RPt RNt PA1 NAi (hbl (N + Pw))
      have e : overlay (frame (binary h (N + Pw))) NAi = NA1 := overlay_collapse _ _ _ (by simp)
      rw [e] at c
      exact c.enlarge (le_of_eq (hrc (N + Pw)))
    have j := s1.seq (s2.seq (s3.seq s4))
    have b := branch_true 2 (idle 11) j (by simpa [pA, pH] using hf)
    simp only [accP, accN, tmpAfter, if_true]
    exact b

noncomputable def ldP := RecoveryFocus.machine bLoadP loadM
noncomputable def ldN := RecoveryFocus.machine bLoadN loadM
noncomputable def mvN := RecoveryFocus.machine bMvN moveM
noncomputable def mvS := RecoveryFocus.machine bMvS moveM
noncomputable def mvF := RecoveryFocus.machine bMvF moveM

/-- **One coordinate of the pullback pass.** -/
noncomputable def coordBody := Composition.machine ldP (Composition.machine mvN (Composition.machine ldN
  (Composition.machine mvN (Composition.machine mvS (Composition.machine mvF (Composition.machine emitBr
    (Composition.machine addBr (Composition.machine mvS mvF))))))))

def coordCost (h : ℕ) : ℕ := regCost h + 1 + (1 + 1 + (regCost h + 1 + (1 + 1 + (1 + 1 + (1 + 1 + (emitCost h + 1 +
  ((addCost h + 2) + 1 + (1 + 1 + 1))))))))

theorem coord_step (h Pw Nw P N : ℕ) (pre post SD FR RP0 RN0 L BL R BR PA0 NA0 T : List Bool) (sd fr cap : ℕ)
    (s f : Bool) (hs : readTapeBit SD (sd + 1) = s) (hf : readTapeBit FR (fr + 1) = f) (hcap : 2 * h + 1 ≤ cap) :
    Step coordBody (coordCost h) (pH pre.length sd fr L.length R.length)
      (pA (pre ++ pairEnc h (Pw, Nw) ++ post) SD FR RP0 RN0 (overlay L BL) (overlay R BR)
        (overlay (frame (binary h P)) PA0) (overlay (frame (binary h N)) NA0) T (List.replicate cap false))
      (pH (pre ++ pairEnc h (Pw, Nw)).length (sd + 1 + 1) (fr + 1 + 1)
        (if s then L ++ pairF h f (Pw, Nw) else L).length (if s then R else R ++ pairF h f (Pw, Nw)).length)
      (pA (pre ++ pairEnc h (Pw, Nw) ++ post) SD FR (overlay (frame (binary h Pw)) RP0) (overlay (frame (binary h Nw)) RN0)
        (overlay (if s then L ++ pairF h f (Pw, Nw) else L) BL) (overlay (if s then R else R ++ pairF h f (Pw, Nw)) BR)
        (overlay (frame (binary h (accP f P Nw))) PA0) (overlay (frame (binary h (accN f N Pw))) NA0)
        (tmpAfter h f P N Pw Nw T) (List.replicate cap false)) := by
  have hrc : ∀ x, 2 * (2 * (binary h x).length + 1) + 2 = regCost h := by intro x; simp [regCost]
  have hbl : ∀ x, 2 * (binary h x).length + 1 ≤ cap := by intro x; simp; omega
  set NM := pre ++ pairEnc h (Pw, Nw) ++ post
  set PAi := overlay (frame (binary h P)) PA0
  set NAi := overlay (frame (binary h N)) NA0
  set lg := List.replicate cap false
  have hN1 : NM = pre ++ frame (binary h Pw) ++ (frame (binary h Nw) ++ post) := by
    simp [NM, pairEnc, List.append_assoc]
  have hN2 : NM = (pre ++ frame (binary h Pw)) ++ frame (binary h Nw) ++ post := by
    simp [NM, pairEnc, List.append_assoc]
  have s1 : Step ldP (regCost h) (pH pre.length sd fr L.length R.length)
      (pA NM SD FR RP0 RN0 (overlay L BL) (overlay R BR) PAi NAi T lg)
      (pH (pre.length + 2 * h) sd fr L.length R.length)
      (pA NM SD FR (overlay (frame (binary h Pw)) RP0) RN0 (overlay L BL) (overlay R BR) PAi NAi T lg) := by
    have e := ps_loadP SD FR RP0 RN0 (overlay L BL) (overlay R BR) PAi NAi T sd fr L.length R.length cap pre
      (binary h Pw) (frame (binary h Nw) ++ post) (hbl Pw)
    rw [← hN1, binary_length] at e
    exact e.enlarge (le_of_eq (by simp [regCost]))
  have s2 := ps_mvN NM SD FR (overlay (frame (binary h Pw)) RP0) RN0 (overlay L BL) (overlay R BR) PAi NAi T
    (pre.length + 2 * h) sd fr L.length R.length lg
  have s3 : Step ldN (regCost h) (pH (pre.length + 2 * h + 1) sd fr L.length R.length)
      (pA NM SD FR (overlay (frame (binary h Pw)) RP0) RN0 (overlay L BL) (overlay R BR) PAi NAi T lg)
      (pH ((pre ++ frame (binary h Pw)).length + 2 * h) sd fr L.length R.length)
      (pA NM SD FR (overlay (frame (binary h Pw)) RP0) (overlay (frame (binary h Nw)) RN0) (overlay L BL) (overlay R BR)
        PAi NAi T lg) := by
    have e := ps_loadN SD FR (overlay (frame (binary h Pw)) RP0) RN0 (overlay L BL) (overlay R BR) PAi NAi T sd fr
      L.length R.length cap (pre ++ frame (binary h Pw)) (binary h Nw) post (hbl Nw)
    rw [← hN2, binary_length] at e
    have hl : (pre ++ frame (binary h Pw)).length = pre.length + 2 * h + 1 := by simp; omega
    rw [hl] at e
    rw [hl]
    exact e.enlarge (le_of_eq (by simp [regCost]))
  have s4 := ps_mvN NM SD FR (overlay (frame (binary h Pw)) RP0) (overlay (frame (binary h Nw)) RN0) (overlay L BL)
    (overlay R BR) PAi NAi T ((pre ++ frame (binary h Pw)).length + 2 * h) sd fr L.length R.length lg
  have s5 := ps_mvS NM SD FR (overlay (frame (binary h Pw)) RP0) (overlay (frame (binary h Nw)) RN0) (overlay L BL)
    (overlay R BR) PAi NAi T ((pre ++ frame (binary h Pw)).length + 2 * h + 1) sd fr L.length R.length lg
  have s6 := ps_mvF NM SD FR (overlay (frame (binary h Pw)) RP0) (overlay (frame (binary h Nw)) RN0) (overlay L BL)
    (overlay R BR) PAi NAi T ((pre ++ frame (binary h Pw)).length + 2 * h + 1) (sd + 1) fr L.length R.length lg
  have s7 := emit_br h Pw Nw (RP0.drop (frame (binary h Pw)).length) (RN0.drop (frame (binary h Nw)).length) NM SD FR
    PAi NAi T L BL R BR ((pre ++ frame (binary h Pw)).length + 2 * h + 1) (sd + 1) (fr + 1) cap s f hs hf hcap
  have s8 := add_br h P N Pw Nw (RP0.drop (frame (binary h Pw)).length) (RN0.drop (frame (binary h Nw)).length) NM SD FR
    (overlay (if s then L ++ pairF h f (Pw, Nw) else L) BL) (overlay (if s then R else R ++ pairF h f (Pw, Nw)) BR)
    PA0 NA0 T ((pre ++ frame (binary h Pw)).length + 2 * h + 1) (sd + 1) (fr + 1)
    (if s then L ++ pairF h f (Pw, Nw) else L).length (if s then R else R ++ pairF h f (Pw, Nw)).length cap f hf hcap
  have s9 := ps_mvS NM SD FR (overlay (frame (binary h Pw)) RP0) (overlay (frame (binary h Nw)) RN0)
    (overlay (if s then L ++ pairF h f (Pw, Nw) else L) BL) (overlay (if s then R else R ++ pairF h f (Pw, Nw)) BR)
    (overlay (frame (binary h (accP f P Nw))) PA0) (overlay (frame (binary h (accN f N Pw))) NA0)
    (tmpAfter h f P N Pw Nw T) ((pre ++ frame (binary h Pw)).length + 2 * h + 1) (sd + 1) (fr + 1)
    (if s then L ++ pairF h f (Pw, Nw) else L).length (if s then R else R ++ pairF h f (Pw, Nw)).length lg
  have s10 := ps_mvF NM SD FR (overlay (frame (binary h Pw)) RP0) (overlay (frame (binary h Nw)) RN0)
    (overlay (if s then L ++ pairF h f (Pw, Nw) else L) BL) (overlay (if s then R else R ++ pairF h f (Pw, Nw)) BR)
    (overlay (frame (binary h (accP f P Nw))) PA0) (overlay (frame (binary h (accN f N Pw))) NA0)
    (tmpAfter h f P N Pw Nw T) ((pre ++ frame (binary h Pw)).length + 2 * h + 1) (sd + 1 + 1) (fr + 1)
    (if s then L ++ pairF h f (Pw, Nw) else L).length (if s then R else R ++ pairF h f (Pw, Nw)).length lg
  have j := s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq s10))))))))
  have hend : (pre ++ frame (binary h Pw)).length + 2 * h + 1 = (pre ++ pairEnc h (Pw, Nw)).length := by
    simp [pairEnc]; omega
  rw [hend] at j
  exact j

end NearCubicWires.WireExponent3_5.CompilerMachine.Pool
