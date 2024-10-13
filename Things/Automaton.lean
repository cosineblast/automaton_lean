import Mathlib.Data.Fintype.Card

import Mathlib.Data.Set.Defs

notation:80 lhs:80 " ^^ " rhs:80 => List.replicate rhs lhs    -- \r~
abbrev replicate n (x : α) := List.replicate n x
abbrev Lang (A : Type) := Set (List A)

structure Automaton (A : Type) where
  K : Type
  δ : K → A → K  -- transition funciton
  s : K -- initial state
  f : Set K -- final states

namespace Automaton

def δs (m : Automaton A) (q : m.K) (str : List A) : m.K :=
  match str with
  | [] => q
  | x :: t => m.δs (m.δ q x) t


theorem δs_nil (m : Automaton A) (q : m.K) : m.δs q [] = q := rfl

theorem δs_cons (m : Automaton A) (q : m.K)
  {h : A}
  {t : List A}
  : m.δs q (h :: t) = m.δs (m.δ q h) t := rfl

def accepts (m : Automaton A) (w: List A) : Prop := (m.δs m.s w) ∈ m.f

@[simp]
theorem δs_append (m : Automaton A) :
  ∀ x y: List A, ∀ q: m.K,
  m.δs q (x ++ y) = m.δs (m.δs q x) y
  := by
  intro x y
  induction x with
  | nil =>
    intro q
    show m.δs q ([] ++ y) = m.δs (m.δs q []) y
    rw [List.nil_append, δs_nil]

  | cons f t ih =>
    intro q
    show m.δs q (f :: t ++ y) = m.δs (m.δs q (f :: t)) y
    rw [List.cons_append]
    rw [δs_cons]
    rw [δs_cons]
    exact ih (m.δ q f)

def is_an_bn (l : List α) (a : α) (b : α) :=
  ∃ n : Nat, l = a ^^ n++ (b ^^ n)

private def ab_pair (l : List α) (a b : α) (n1 n2 : Nat) (_ : l = a ^^ n1 ++ b ^^ n2) : Nat × Nat := (n1, n2)

private theorem list_drop_append_replicate : ∀ (a : α) (l : List α) {n : Nat}, List.drop n (a^^n ++ l) = l := by
  intro a
  intro l
  intro n
  have := List.drop_append 0 (l₁ := (a^^n)) (l₂ := l)
  simp only [Nat.add_zero, List.length_replicate, List.drop_zero] at this
  exact this

private theorem ab_replication_is_injective :
  ∀ n1 n2 m1 m2 : Nat,
  ∀ a b: α, a ≠ b → a ^^ n1 ++ b ^^ m1 = a ^^ n2 ++ b ^^ m2 → (n1, m1) = (n2, m2) := by

  intro n1 n2

  wlog h_n1_lt_n2 : n1 ≤ n2 generalizing n1 n2 with H
  · have : n2 ≤ n1 := by omega
    intro m1 m2
    intro a b
    intro h_a_ne_b
    intro h
    have := H n2 n1 this m2 m1 a b h_a_ne_b (Eq.symm h)
    simp at this
    simp
    apply And.intro
    · simp [this]
    · simp [this]

  intro m1 m2
  intro a b
  intro h_aneb

  intro h_x1_eq_x2
  let x1 := a ^^ n1 ++ b ^^ m1
  let x2 := a ^^ n2 ++ b ^^ m2

  have h0 : x1 = x2 := by assumption
  have h1 : x1.length = x2.length := by simp [h0]

  have h2 : x1.length = n1 + m1 := by simp [x1]
  have h3 : x2.length = n2 + m2 := by simp [x2]

  have : n1 + m1 = n2 + m2 := h2 ▸ (h3 ▸ h1)

  have : n1 = n2 := by
    apply Classical.byContradiction
    intro
    have : n1 ≠ n2 := by assumption

    let k := n2 - n1
    let k' := k - 1

    have : k > 0 := by omega
    have : k = k' + 1 := by omega


    let r1 := List.drop n1 x1
    let r2 := List.drop n1 x2

    have := calc r1
      _ = List.drop n1 x1 := rfl
      _ = List.drop n1 x2 := by rw [‹x1 = x2›]
      _ = r2 := rfl

    have := calc x2
      _ = a^^n2 ++ b^^m2 := rfl
      _ = a^^(n1 + (1 + k')) ++ b^^m2 := by
        have : n2 = n1 + (1 + k') := by omega
        rw [this]
      _ = a^^n1 ++ a ^^(1 + k') ++ b^^m2 := by rw [List.append_replicate_replicate]
      _ = a^^n1 ++ (a ^^(1 + k') ++ b^^m2) := by rw [List.append_assoc]

    have h_r2_a :=
      calc r2
        _ = List.drop n1 x2 := rfl
        _ = List.drop n1 (a^^(n1) ++ (a ^^(1 + k') ++ b^^m2)) := by rw [this]
        _ = a ^^(1 + k') ++ b^^m2 := list_drop_append_replicate a (a ^^(1 + k') ++ b^^m2)
        _ = (a :: a ^^ k') ++ b^^m2 := by rw [Nat.one_add, List.replicate_succ]
        _ = a :: (a ^^ k' ++ b^^m2) := by rw [List.cons_append]


    have : m1 > 0 := by omega
    let t := m1 - 1
    have : m1 = t + 1 := by omega

    have :=
      calc r2
      _ = r1 := Eq.symm ‹r1 = r2›
      _ = List.drop n1 x1 := rfl
      _ = b ^^ m1 := list_drop_append_replicate a (b^^m1)
      _ = b ^^ (t + 1) := by rw [‹m1 = t + 1›]
      _ = b :: (b ^^ t) := by rw [List.replicate_succ]

    have : a = b :=
      have p1 : r2 = a :: (a ^^ k' ++ b^^m2) := by assumption
      have p2 : r2 = b :: (b ^^ t) := by assumption
      have : a :: (a ^^ k' ++ b^^m2) = b :: (b ^^ t) := p1 ▸ p2
      by injection this

    contradiction

  have : m1 = m2 := by omega

  rw [‹n1 = n2›, ‹m1 = m2›]



private theorem exclusive_an_bn_a (n1 n2 : Nat) :
  ∀ l: List α, ∀ a b: α, l = a ^^ n1 ++ b ^^ n2 → is_an_bn l a b → a ≠ b → n1 = n2 := by
  intro l a b
  intro h_n1_n2
  intro l_an_bn
  intro h_a_ne_b

  let ⟨n, h⟩ := l_an_bn
  rw [h_n1_n2] at h
  have := ab_replication_is_injective n1 n n2 n a b h_a_ne_b h
  simp at this
  simp [this]

private theorem bruh {m i j : Nat} (h2 : j ≤ m) (h3 : i < j) : i + (m - j) = m - (j - i) := by omega

private theorem witness_positive_card (α : Type u) [Fintype α] (x: α) : Fintype.card α > 0 :=
  have : Nonempty α := Nonempty.intro x
  Fintype.card_pos

theorem no_an_bn_automaton :
  ¬ ∃ (M : Automaton A),
  ∃ (_ : Fintype M.K),
  ∃ (a b : A),
  a ≠ b ∧
  ∀ l : List A,
  M.accepts l  ↔ is_an_bn l a b

  := by
  intro ⟨M, h_K_finite, a, b, h_aneb, h⟩

  let m := Fintype.card M.K

  let original := ((a ^^ m) ++ (b ^^ m))
  have h_accepts_original : M.f (M.δs (M.δs M.s (a ^^ m)) (b ^^ m)) := by
    rw [←δs_append]
    exact (h original).mpr ⟨m, rfl⟩

  let q  := fun (k : Fin (m+1)) => M.δs M.s (a ^^ k)
  let hq : ∀ k, q k = M.δs M.s (a ^^ k) := fun _ => rfl

  let ⟨i , j , hi_ne_j, h_qi_qj⟩ := Fintype.exists_ne_map_eq_of_card_lt q (by simp)

  wlog i_ne_j : i < j generalizing i j with base
  have : ¬ i < j := i_ne_j
  have : i ≥ j := Nat.not_lt.mp this
  have : i > j := Nat.lt_of_le_of_ne this (Ne.symm (Fin.val_ne_of_ne ‹i ≠ j›))
  exact base j i (Ne.symm ‹i ≠ j›) (Eq.symm ‹q i = q j›) this

  have : ↑j ≤ m := Nat.le_of_lt_succ (by simp)
  have beep : ↑i + (m - ↑j) = m - (↑j - ↑i) := bruh ‹↑j ≤ m› ‹i < j›

  have : m = j + (m-j) := by
    rw [←Nat.add_sub_assoc]
    rw [Nat.add_comm]
    simp
    show ↑j ≤  m
    exact Nat.le_of_lt_succ (by simp)

  have :=
    calc M.δs M.s (a ^^ m ++ b ^^ m)
    _ = M.δs M.s (a ^^ (j + (m-j)) ++ b ^^ m)         := by rw [←this]
    _ = M.δs M.s (a ^^ j ++ a ^^ (m - j) ++ b ^^ m)   := by rw [← List.append_replicate_replicate]
    _ = M.δs M.s (a ^^ j ++ (a ^^ (m - j) ++ b ^^ m)) := by rw [List.append_assoc]
    _ = M.δs (M.δs M.s (a ^^ j)) (a ^^ (m - j) ++ b ^^ m)  := by rw [δs_append]
    _ = M.δs (q j) (a ^^ (m - j) ++ b ^^ m)          := by rw [←hq]
    _ = M.δs (q i) (a ^^ (m - j) ++ b ^^ m)                 := by rw [←h_qi_qj]
    _ = M.δs (M.δs M.s (a ^^ i)) (a ^^ (m - j) ++ b ^^ m)  := by rw [hq]
    _ = M.δs M.s (a ^^ i ++ (a ^^ (m - j) ++ b ^^ m))  := by rw [←δs_append]
    _ = M.δs M.s (a ^^ i ++ a ^^ (m - j) ++ b ^^ m)  := by rw [←List.append_assoc]
    _ = M.δs M.s (a ^^ (i + (m - j)) ++ b ^^ m)  := by rw [List.append_replicate_replicate]
    _ = M.δs M.s (a ^^ (m - (j - i)) ++ b ^^ m)  := by rw [beep]

  let it := (a ^^ (m - (j - i)) ++ b ^^ m)
  have hit : it = a ^^ (m - (j - i)) ++ b ^^ m := rfl

  have : M.accepts it := by
    rw [accepts]
    rw [← this]
    rw [δs_append]
    exact h_accepts_original

  have : ¬ is_an_bn it a b := by
    intro thing
    have _ := exclusive_an_bn_a (m - (j - i)) m it a b hit thing h_aneb

    have : m - (j - i) ≠ m := by
      have : 0 < m := witness_positive_card M.K M.s
      have : 0 < ↑(j - i) :=  by
        have : i < j := by assumption
        have := Nat.sub_lt_sub_right (Nat.le_refl i) ‹i < j›
        rw [show ↑i - ↑i = 0 from by simp] at this
        rw [←Fin.sub_val_of_le (Nat.le_of_lt ‹i < j›)] at this
        exact this

      -- i < j => i - i < j - i => 0 < j - i
      have : m - ↑(j - i) < m - 0 := Nat.sub_lt_sub_left ‹0 < m› ‹0 < j - i›
      rw [show m - 0 = m by simp] at this
      rw [Fin.sub_val_of_le (Nat.le_of_lt ‹i < j›)] at this
      have : m - (j - i) ≠ m := Nat.ne_of_lt this
      exact this

    contradiction



  have : is_an_bn it a b := (h it).mp ‹M.accepts it›

  contradiction



def language (m : Automaton A) : Lang A :=
  setOf (fun w => m.accepts w)

def recognizable {A : Type} (l : Lang A) : Prop :=
  ∃ m : Automaton A, m.language = l

def union (m1 : Automaton A) (m2 : Automaton A) : Automaton A :=
  {
    K := m1.K × m2.K,
    δ := fun ⟨x , y⟩ c => ⟨m1.δ x c, m2.δ y c⟩,
    s := ⟨m1.s, m2.s⟩ ,
    f := setOf (fun ⟨x, y⟩ => x ∈ m1.f ∨ y ∈ m2.f)
  }

theorem union_automaton_rec_union
  (m1 : Automaton A)
  (m2 : Automaton A)
  (w : List A)
  : m1.accepts w ∨ m2.accepts w ↔ (m1.union m2).accepts w
  := by
    let mu := m1.union m2

    have t : ∀ w : List A, ∀ q1 q2, (δs (m := mu) ⟨q1, q2⟩  w) = ⟨(δs (m := m1) q1 w), (δs (m := m2) q2 w)⟩ :=
      by
      intro w q1 q2

      induction w generalizing q1 q2 with
      | nil => rfl
      | cons x _ hi => apply hi

    have : ⟨m1.s, m2.s⟩ = mu.s := rfl

    have : ∀ w : List A, (δs (m := mu) mu.s w) = ⟨(δs (m := m1) m1.s w),(δs (m := m2) m2.s w)⟩ := by
      aesop

    constructor
    · intro
      show mu.accepts w

      have : m1.accepts w ∨ m2.accepts w := by assumption

      cases this
      · apply Or.inl
        aesop

      · apply Or.inr
        aesop

    · intro
      show m1.accepts w ∨ m2.accepts w

      have : mu.accepts w := by assumption
      have : δs (m := mu) mu.s w ∈ mu.f  := this
      have : (δs (m := mu) mu.s w).1 ∈ m1.f ∨ (δs (m := mu) mu.s w).2 ∈ m2.f := this

      cases this
      · apply Or.inl
        aesop

      · apply Or.inr
        aesop


theorem rec_union_rec_rec
  (l : Lang A) (r : Lang A)
  (h1 : recognizable l) (h2 : recognizable r)
  : recognizable (l ∪ r) := by

  show ∃ m : Automaton A, m.language = l ∪ r

  let ⟨m1, hm1⟩ := h1
  let ⟨m2, hm2⟩ := h2

  let mu := m1.union m2


  have : mu.language = l ∪ r := by
    ext x
    have := union_automaton_rec_union m1 m2 x
    constructor
    · intro h
      simp
      rw [←hm1 , ←hm2]
      exact this.mpr h

    · intro h
      simp at h
      rw [←hm1, ←hm2] at h
      exact this.mp h

  exact Exists.intro mu this

def intersect (m1 : Automaton A) (m2 : Automaton A) : Automaton A :=
  {
    K := m1.K × m2.K,
    δ := fun ⟨x , y⟩ c => ⟨m1.δ x c, m2.δ y c⟩,
    s := ⟨m1.s, m2.s⟩ ,
    f := setOf (fun ⟨x, y⟩ => x ∈ m1.f ∧ y ∈ m2.f)
  }

theorem inter_automaton_rec_inter
  (m1 : Automaton A)
  (m2 : Automaton A)
  (w : List A)
  : m1.accepts w ∧ m2.accepts w ↔ (m1.intersect m2).accepts w
  := by
    let mu := m1.intersect m2

    have t : ∀ w : List A, ∀ q1 q2, (δs (m := mu) ⟨q1, q2⟩  w) = ⟨(δs (m := m1) q1 w), (δs (m := m2) q2 w)⟩ :=
      by
      intro w q1 q2
      induction w generalizing q1 q2 with
      | nil => rfl
      | cons x _ hi => apply hi

    have : ⟨m1.s, m2.s⟩ = mu.s := rfl

    have t2 : ∀ w : List A, (δs (m := mu) mu.s w) = ⟨(δs (m := m1) m1.s w),(δs (m := m2) m2.s w)⟩ := by
      intro
      apply t

    constructor
    · intro
      show (δs (m := mu) mu.s w).1 ∈ m1.f ∧ (δs (m := mu) mu.s w).2 ∈ m2.f
      aesop

    · intro h
      have : (δs (m := mu) mu.s w).1 ∈ m1.f ∧ (δs (m := mu) mu.s w).2 ∈ m2.f := h
      aesop


theorem rec_inter_rec
  (l : Lang A) (r : Lang A)
  (h1 : recognizable l) (h2 : recognizable r)
  : recognizable (l ∩ r) := by

  show ∃ m : Automaton A, m.language = l ∩ r

  let ⟨m1, hm1⟩ := h1
  let ⟨m2, hm2⟩ := h2

  let mu := m1.intersect m2


  have : mu.language = l ∩ r := by
    ext x
    have ⟨mp, mpr⟩  := inter_automaton_rec_inter m1 m2 x
    constructor
    · intro h
      simp
      rw [←hm1 , ←hm2]
      exact mpr h

    · intro h
      simp at h
      rw [←hm1, ←hm2] at h
      exact mp h

  exact Exists.intro mu this


def complement (m : Automaton A) : Automaton A :=
  {
    K := m.K,
    δ := m.δ,
    s := m.s,
    f := setOf (fun x => x ∉ m.f)
  }

open Classical

theorem complement_rec_complement (m : Automaton A) :
  ∀ w : List A, m.complement.accepts w ↔ ¬ m.accepts w
  := by
  intro w

  let mc := m.complement

  have h_same_δs : mc.δs = m.δs := by
    ext q xs 
    induction xs generalizing q with 
    | nil => rfl
    | cons x xs' hi => aesop

  have forward : m.accepts w → ¬m.complement.accepts w := by
    intro
    intro
    have : ¬ (m.accepts w) := by aesop
    contradiction

  constructor 
  · intro h
    show (m.δs m.s w ∉ m.f)
    aesop

  · contrapose 
    intro h 

    have : m.accepts w := by 
      have : ¬ (mc.δs mc.s w ∉  m.f) := h
      aesop

    exact not_not_intro this
    


theorem rec_neg_rec
  (l : Lang A)
  (h1 : recognizable l)
  : recognizable (lᶜ) := by
  
  let ⟨m, _⟩ := h1
  let mc := m.complement

  have : mc.language = lᶜ := by 
    ext x
    have := complement_rec_complement m x 
    aesop

  apply Exists.intro mc this


  



end Automaton



















