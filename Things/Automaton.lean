import Mathlib.Data.Fintype.Card

abbrev replicate n (x : α) := List.replicate n x

def ListN n α := { xs : List α // xs.length = n }

instance : GetElem (ListN n α) (Fin n) α (fun _ _ => True) where
  getElem := fun xs' i =>
    let ⟨xs, h⟩ := xs'
    fun _ => xs[i]

class Automaton where
  K : Type
  A : Type -- alphabet
  δ : K → A → K  -- transition funciton
  s : K -- initial state
  f : K → Prop -- final states

namespace Automaton


private def m1 : Automaton :=
  {
    K := Fin 3,
    A := Fin 2,
    δ := fun s i =>
      match s, i with
      | 0, 0 => 0
      | 0, 1 => 1
      | 1, 0 => 2
      | 1, 1 => 1
      | 2, 0 => 1
      | 2, 1 => 1

    s := 0
    f := (· = 1)
  }


-- this sucks
def formally_accepts [Automaton] (w: ListN n A) : Prop :=
  let n1 := n + 1
  let promote := Fin.castLE (Nat.le_succ n)
  ∃ r : ListN n1 K,
  r[(0 : Fin n1)] = s ∧
  (∀ i : Fin n, r[(Fin.succ i)] = δ (r[promote i]) (w[i])) ∧
  f (r[Fin.last n])


example :
  let str : ListN 5 (Fin 2)  := ⟨[0, 1, 1, 0, 1], rfl⟩
  m1.formally_accepts str
  := by
    let r : ListN 6 (Fin 3) := ⟨[0, 0, 1, 1, 2, 1], rfl⟩
    exists r
    constructor
    · rfl

    constructor
    · intro i
      match i with
      | 0 => rfl
      | 1 => rfl
      | 2 => rfl
      | 3 => rfl
      | 4 => rfl

    · rfl


def δs [Automaton] (q : K) (str : List A) : K :=
  match str with
  | [] => q
  | x :: t => δs (δ q x) t

infixl:64   " ↝ " => Automaton.δ   -- \r~
infixl:63   " ↠ " => Automaton.δs  -- \rr-
notation:80 lhs:80 " ^^ " rhs:80 => List.replicate rhs lhs    -- \r~

theorem δs_nil [Automaton] (q : K) : δs q [] = q := rfl

theorem δs_cons [Automaton] (q : K)
  {h : A}
  {t : List A}
  : q ↠ (h :: t) = (q ↝ h) ↠ t := rfl


def accepts [Automaton] (w: List A) : Prop := f (s ↠ w)

example :
  let str : List (Fin 2)  := [0, 1, 1, 0, 1]
  m1.accepts str
  := by rfl


theorem δs_append [Automaton] :
  ∀ x y: List A, ∀ q: K,
  q ↠ (x ++ y) = (q ↠ x) ↠ y
  := by
  intro x y
  induction x with
  | nil =>
    intro q
    show q ↠ ([] ++ y) = (q ↠ []) ↠ y
    rw [List.nil_append, δs_nil]

  | cons f t ih =>
    intro q
    show q ↠ (f :: t ++ y) = (q ↠ (f :: t)) ↠ y
    rw [List.cons_append]
    rw [δs_cons]
    rw [δs_cons]
    exact ih (q ↝ f)

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
  · have : n2 ≤ n1 := by omega -- TODO expand omega
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
  ¬ ∃ (M : Automaton),
  ∃ (_ : Fintype M.K),
  ∃ (a b : A),
  a ≠ b ∧
  ∀ l : List A,
  M.accepts l  ↔ is_an_bn l a b

  := by
  intro ⟨M, h_K_finite, a, b, h_aneb, h⟩

  let m := Fintype.card K

  let original := ((a ^^ m) ++ (b ^^ m))
  have h_accepts_original : f (s ↠  (a ^^ m) ↠ (b ^^ m)) := by
    rw [←δs_append]
    exact (h original).mpr ⟨m, rfl⟩

  let q  := fun (k : Fin (m+1)) => s ↠  (a ^^ k)
  let hq : ∀ k, q k = s ↠  (a ^^ k) := fun _ => rfl

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
    calc s ↠  a ^^ m ++ b ^^ m
    _ = s ↠  a ^^ (j + (m-j)) ++ b ^^ m         := by rw [←this]
    _ = s ↠  a ^^ j ++ a ^^ (m - j) ++ b ^^ m   := by rw [← List.append_replicate_replicate]
    _ = s ↠  a ^^ j ++ (a ^^ (m - j) ++ b ^^ m) := by rw [List.append_assoc]
    _ = s ↠  a ^^ j ↠ (a ^^ (m - j) ++ b ^^ m)  := by rw [δs_append]
    _ = q j ↠ (a ^^ (m - j) ++ b ^^ m)          := by rw [←hq]
    _ = q i ↠ (a ^^ (m - j) ++ b ^^ m)                 := by rw [←h_qi_qj]
    _ = s ↠  a ^^ i ↠ (a ^^ (m - j) ++ b ^^ m)  := by rw [hq]
    _ = s ↠  a ^^ i ++ (a ^^ (m - j) ++ b ^^ m)  := by rw [←δs_append]
    _ = s ↠  a ^^ i ++ a ^^ (m - j) ++ b ^^ m  := by rw [←List.append_assoc]
    _ = s ↠  a ^^ (i + (m - j)) ++ b ^^ m  := by rw [List.append_replicate_replicate]
    _ = s ↠  a ^^ (m - (j - i)) ++ b ^^ m  := by rw [beep]

  let it := (a ^^ (m - (j - i)) ++ b ^^ m)
  have hit : it = a ^^ (m - (j - i)) ++ b ^^ m := rfl

  have : accepts it := by
    rw [accepts]
    rw [← this]
    rw [δs_append]
    exact h_accepts_original

  have : ¬ is_an_bn it a b := by
    intro thing
    have _ := exclusive_an_bn_a (m - (j - i)) m it a b hit thing h_aneb

    have : m - (j - i) ≠ m := by
      have : 0 < m := witness_positive_card K s
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



  have : is_an_bn it a b := (h it).mp ‹accepts it›

  contradiction





end Automaton
















