import Proof.Hierarchy.CompetitorGcd
import Proof.CaseAnalysis.WitnessGcdPolicy
import Proof.Hierarchy.CompetitorWitnessKind

/-! The guarded consumer's complete cold gcd check. Two paid copies retain
the exact coefficient fields; the existing cold initializer and loop work
only on their copies, and the existing classifier tests the actual gcd. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.RationalGcd
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def leftSlots : Fin 4→Fin 18:=![0,2,3,4]
def rightSlots : Fin 4→Fin 18:=![1,5,6,7]
def gcdSlots : Fin 7→Fin 18:=![2,5,8,9,10,11,12]
def kindSlots : Fin 6→Fin 18:=![8,13,14,15,16,17]
def input (w a b : ℕ) (i : Fin 18):=
  if i=0 then frame (binary w a) else if i=1 then frame (binary w b) else []
def copied (w n : ℕ) : Fin 4→List Bool:=
  ![frame (binary w n),frame (binary w n),List.replicate (2*w+1) false,List.replicate (4*w+3) false]
noncomputable def lbank (w a b : ℕ):=install leftSlots (input w a b) (copied w a)
noncomputable def rbank (w a b : ℕ):=install rightSlots (lbank w a b) (copied w b)
noncomputable def gbank (w a b aa bb : ℕ):=
  install gcdSlots (rbank w a b) (CompetitorGcd.data w aa bb (a.gcd b) true)
def kindOutput (w a b : ℕ):=CompetitorWitnessKind.tapes
  (CompetitorWitnessKind.after (binary w (a.gcd b))) (CompetitorWitnessKind.flags (binary w (a.gcd b))) (2*w+1)
noncomputable def left:=RecoveryFocus.machine leftSlots copyMachine
noncomputable def right:=RecoveryFocus.machine rightSlots copyMachine
noncomputable def gcd:=RecoveryFocus.machine gcdSlots
  (Composition.machine CompetitorGcd.cold CompetitorGcd.machine)
noncomputable def kind:=RecoveryFocus.machine kindSlots CompetitorWitnessKind.machine
noncomputable def first:=Composition.machine left right
noncomputable def second:=Composition.machine first gcd
noncomputable def machine:=Composition.machine second kind
def budget (w a b : ℕ):=(8*w+8)+1+(8*w+8)+1+
  ((12*w+15)+1+(a+b+1)*(32*w+40))+1+(16*w+27)

theorem copy_run (w n : ℕ) : ClockJoin.ReadyRun copyMachine (8*w+8)
    ![frame (binary w n),[],[],[]] (copied w n):=by
  obtain ⟨r,hr,rt,rh,rs⟩:=RecoveryRootRound.copy_ready (binary w n) [] 0 0 (by simp)
  simpa only [binary_length,Nat.zero_max,List.replicate_zero,copied] using
    (show ClockJoin.ReadyRun copyMachine (8*(binary w n).length+8)
      ![frame (binary w n),[],List.replicate 0 false,List.replicate 0 false]
      ![frame (binary w n),frame (binary w n),List.replicate (max 0 (2*(binary w n).length+1)) false,
        List.replicate (max 0 (4*(binary w n).length+3)) false] from ⟨r,hr,rt,rh,rs.le⟩)
theorem right_input (w a b : ℕ) : ∀ i,lbank w a b (rightSlots i)=
    ![frame (binary w b),[],[],[]] i:=by
  intro i;fin_cases i <;> rw [lbank,install_other _ _ _ _ (by decide)] <;> rfl
theorem gcd_input (w a b : ℕ) : ∀ i,rbank w a b (gcdSlots i)=CompetitorGcd.coldInput w a b i:=by
  intro i;fin_cases i
  · rw [rbank,install_other _ _ _ _ (by decide)]
    change install leftSlots _ _ (leftSlots 1)=_
    rw [install_slot _ (by decide)]
    rfl
  · change install rightSlots _ _ (rightSlots 1)=_
    rw [install_slot _ (by decide)]
    rfl
  all_goals
    rw [rbank,install_other _ _ _ _ (by decide),lbank,install_other _ _ _ _ (by decide)]
    rfl
theorem kind_input (w a b aa bb : ℕ) : ∀ i,gbank w a b aa bb (kindSlots i)=
    CompetitorWitnessKind.input (binary w (a.gcd b)) i:=by
  intro i;fin_cases i
  · change install gcdSlots _ _ (gcdSlots 2)=_
    rw [install_slot _ (by decide)]
    rfl
  all_goals
    rw [gbank,install_other _ _ _ _ (by decide),rbank,install_other _ _ _ _ (by decide),
      lbank,install_other _ _ _ _ (by decide)]
    rfl

theorem gcd_run (w a b : ℕ) (ha : a<2^w) (hb : b<2^w) : ∃ output,
    ClockJoin.ReadyRun machine (budget w a b) (input w a b) output ∧
      output 0=frame (binary w a) ∧ output 1=frame (binary w b) ∧
      output 14=[decide (a.gcd b=1)]:=by
  have hl:=(copy_run w a).focus leftSlots (by decide) (input w a b) (by intro i;fin_cases i <;> rfl)
  have hr:=(copy_run w b).focus rightSlots (by decide) (lbank w a b) (right_input w a b)
  obtain ⟨cold,hcold,ct,ch,cs⟩:=CompetitorGcd.cold_ready w a b ha
  have hc:ClockJoin.ReadyRun CompetitorGcd.cold (12*w+15)
      (CompetitorGcd.coldInput w a b) (CompetitorGcd.data w a b a false):=⟨cold,hcold,ct,ch,cs.le⟩
  obtain ⟨t,aa,bb,ht,loop,hloop,lt,lh,ls⟩:=GcdGuard.gcd_ready w a b a ha hb
  have hg:ClockJoin.ReadyRun CompetitorGcd.machine t (CompetitorGcd.data w a b a false)
      (CompetitorGcd.data w aa bb (a.gcd b) true):=⟨loop,hloop,lt,lh,ls.le⟩
  have hg':=ClockJoin.enlarge CompetitorGcd.machine t ((a+b+1)*(32*w+40)) _ _ hg ht
  have hcg:=ClockJoin.join CompetitorGcd.cold CompetitorGcd.machine _ _ _ _ _ hc hg'
  have hfocused:=hcg.focus gcdSlots (by decide) (rbank w a b) (gcd_input w a b)
  obtain ⟨k,hk,kt,kh,ks⟩:=CompetitorWitnessKind.kind_ready (binary w (a.gcd b))
  have hkind:ClockJoin.ReadyRun CompetitorWitnessKind.machine (16*w+27)
      (CompetitorWitnessKind.input (binary w (a.gcd b))) (kindOutput w a b):=by
    simpa only [binary_length,kindOutput] using
      (show ClockJoin.ReadyRun CompetitorWitnessKind.machine (16*(binary w (a.gcd b)).length+27)
        (CompetitorWitnessKind.input (binary w (a.gcd b)))
        (CompetitorWitnessKind.tapes (CompetitorWitnessKind.after (binary w (a.gcd b)))
          (CompetitorWitnessKind.flags (binary w (a.gcd b))) (2*(binary w (a.gcd b)).length+1))
        from ⟨k,hk,kt,kh,ks.le⟩)
  have hk':=hkind.focus kindSlots (by decide) (gbank w a b aa bb) (kind_input w a b aa bb)
  have hall:=ClockJoin.join second kind _ _ _ _ _
    (ClockJoin.join first gcd _ _ _ _ _ (ClockJoin.join left right _ _ _ _ _ hl hr) hfocused) hk'
  let output:=install kindSlots (gbank w a b aa bb) (kindOutput w a b)
  refine ⟨output,hall,?_,?_,?_⟩
  · rw [show output=install kindSlots _ _ by rfl,install_other _ _ _ _ (by decide),
      gbank,install_other _ _ _ _ (by decide),rbank,install_other _ _ _ _ (by decide)]
    change install leftSlots _ _ (leftSlots 0)=_
    rw [install_slot _ (by decide)]
    rfl
  · rw [show output=install kindSlots _ _ by rfl,install_other _ _ _ _ (by decide),
      gbank,install_other _ _ _ _ (by decide)]
    change install rightSlots _ _ (rightSlots 0)=_
    rw [install_slot _ (by decide)]
    rfl
  · change install kindSlots _ _ (kindSlots 2)=_
    rw [install_slot _ (by decide)]
    change [decide (value (binary w (a.gcd b))=1)]=_
    have hfit:a.gcd b<2^w:=by
      by_cases hz:a=0
      · simpa only [hz,Nat.gcd_zero_left] using hb
      · exact (Nat.gcd_le_left b (by omega)).trans_lt ha
    rw [binary_value w _ hfit]

end NearCubicWires.RepairOrdinary.CloseoutWitness.RationalGcd
