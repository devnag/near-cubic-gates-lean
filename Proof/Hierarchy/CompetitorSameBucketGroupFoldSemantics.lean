import Proof.Hierarchy.CompetitorSameBucketGroupLoop

/-! Arithmetic meaning of the executed grouping transducer. Equal-ID runs
accumulate natural positive/negative parts without an intermediate flush. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupMachine
open SignedSortKey RadixSemantics CompetitorSameBucketGroup
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def foldStore (p m : ℕ) (s : Store) : List Entry → Store
  | [] => s
  | e::es => foldStore p m (stepStore s p m e) es

theorem prepared_counts (s : Store) (p m : ℕ) (e : Entry) :
    (prepared s p m e).positive=(if changed s m e then 0 else s.positive) ∧
    (prepared s p m e).negative=(if changed s m e then 0 else s.negative) := by
  unfold prepared
  split <;> unfold tested <;> split <;> exact ⟨rfl,rfl⟩

theorem added_counts (s : Store) :
    (added s).positive=(if s.sign then s.positive else value s.magnitude+s.positive) ∧
    (added s).negative=(if s.sign then value s.magnitude+s.negative else s.negative) := by
  cases h : s.sign <;> simp [added,accumulated,marked,copied,h]

theorem stepStore_counts (s : Store) (p m : ℕ) (e : Entry) (hb : e.coefficient.natAbs<2^p) :
    (stepStore s p m e).positive=(if changed s m e then 0 else s.positive)+e.coefficient.toNat ∧
    (stepStore s p m e).negative=(if changed s m e then 0 else s.negative)+(-e.coefficient).toNat := by
  obtain ⟨hmag,_,_,hsign⟩ := prepared_fields s p m e
  obtain ⟨hp,hn⟩ := prepared_counts s p m e
  have h := added_counts (prepared s p m e)
  rw [hmag,hsign,hp,hn,binary_value p _ hb] at h
  unfold stepStore
  cases he : e.coefficient with
  | ofNat n =>
    have hnot : ¬(n : ℤ)<0 := by omega
    simpa [he,hnot,Nat.add_comm] using h
  | negSucc n => simpa [he,Nat.add_comm] using h

theorem fits_of_counts (w p m : ℕ) (s : Store) (e : Entry)
    (hb : e.coefficient.natAbs<2^p)
    (hp : (if changed s m e then 0 else s.positive)+e.coefficient.toNat<2^w)
    (hn : (if changed s m e then 0 else s.negative)+(-e.coefficient).toNat<2^w) : Fits w p m s e := by
  obtain ⟨hpos,hneg⟩ := prepared_counts s p m e
  unfold Fits selected
  rw [binary_value p _ hb]
  cases he : e.coefficient with
  | ofNat n =>
    have hnot : ¬(n : ℤ)<0 := by omega
    simpa [he,hnot,hpos,Nat.add_comm] using hp
  | negSucc n => simpa [he,hneg,Nat.add_comm] using hn

theorem unchanged_of_current (m : ℕ) (s : Store) (e : Entry)
    (h : s.present=true → s.current=e.ids m) : changed s m e=false := by
  cases hp : s.present
  · simp [changed,hp]
  · simp [changed,hp,h hp]

theorem homogeneous_prefix (w p m : ℕ) (key : List Bool) (es : List Entry) (s : Store)
    (hkey : ∀ e∈es,e.ids m=key) (hcurrent : s.present=true → s.current=key)
    (hbits : ∀ e∈es,e.coefficient.natAbs<2^p)
    (hp : s.positive+positive es<2^w) (hn : s.negative+negative es<2^w) :
    FitsAll w p m s es ∧
    (∀ rest,scanWord w p m s (es++rest)=scanWord w p m (foldStore p m s es) rest) ∧
    (foldStore p m s es).positive=s.positive+positive es ∧
    (foldStore p m s es).negative=s.negative+negative es ∧
    ((foldStore p m s es).present=true → (foldStore p m s es).current=key) ∧
    (es≠[] → (foldStore p m s es).present=true) ∧
    (s.present=true → (foldStore p m s es).present=true) := by
  induction es generalizing s with
  | nil => simpa [FitsAll,foldStore,positive,negative] using hcurrent
  | cons e es ih =>
    have he := hkey e (by simp)
    have hchange := unchanged_of_current m s e (fun h => (hcurrent h).trans he.symm)
    have hb := hbits e (by simp)
    obtain ⟨hpos,hneg⟩ := stepStore_counts s p m e hb
    rw [hchange] at hpos hneg
    simp only [Bool.false_eq_true,↓reduceIte] at hpos hneg
    obtain ⟨_,_,hcur,hpresent⟩ := stepStore_fields s p m e
    have hfit := fits_of_counts w p m s e hb
      (by rw [hchange];simp only [Bool.false_eq_true,↓reduceIte];rw [positive_cons] at hp;omega)
      (by rw [hchange];simp only [Bool.false_eq_true,↓reduceIte];rw [negative_cons] at hn;omega)
    obtain ⟨hf,hw,hp',hn',hk',hpres',hkeep⟩ := ih (stepStore s p m e)
      (fun a ha => hkey a (by simp [ha])) (fun _ => hcur.trans he)
      (fun a ha => hbits a (by simp [ha]))
      (by rw [hpos,positive_cons] at *;omega) (by rw [hneg,negative_cons] at *;omega)
    refine ⟨⟨hfit,hf⟩,?_,?_,?_,hk',?_,?_⟩
    · intro rest
      simpa only [List.cons_append,scanWord,emittedPrefix,hchange,Bool.false_eq_true,
        ↓reduceIte,List.nil_append,foldStore] using hw rest
    · simpa only [foldStore,hpos,positive_cons,Nat.add_assoc] using hp'
    · simpa only [foldStore,hneg,negative_cons,Nat.add_assoc] using hn'
    · intro _
      exact hkeep hpresent
    · intro _
      exact hkeep hpresent

end NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupMachine
