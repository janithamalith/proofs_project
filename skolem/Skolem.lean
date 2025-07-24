import Mathlib.Tactic

open Function

namespace Skolem

/-- S is the set of functions ℕ → ℕ so that 1, id ∈ S, and S is closed under +, *, and exponentiation. -/
inductive S : (ℕ → ℕ) → Prop
  | one : S (fun _ => 1)
  | id : S (fun n => n)
  | add {f g : ℕ → ℕ} : S f → S g → S (f + g)
  | mul {f g : ℕ → ℕ} : S f → S g → S (f * g)
  | exp {f g : ℕ → ℕ} : S f → S g → S (fun n => f n ^ g n)

#check S.one
#check S.id
#check S.add

def EventuallyLT (f g : ℕ → ℕ) : Prop := ∃ n₀, ∀ n ≥ n₀, f n < g n

infix:50 " ≺ " => EventuallyLT

def EventuallyLE (f g : ℕ → ℕ) : Prop := f ≺ g ∨ f = g

infix:50 " ≼ " => EventuallyLE

example : S (fun n => n^2) := by
  apply S.exp
  exact S.id
  exact S.add S.one S.one

example : S (fun n => n^n) := by
  apply S.exp
  repeat exact S.id

example : S (fun n => n^n^n) := by
  apply S.exp
  apply S.id
  apply S.exp
  repeat apply S.id

example : S (fun n => n^2 + 2 * n + 1) := by
  repeat apply S.add
  apply S.exp
  exact S.id
  apply S.add S.one S.one
  exact S.mul (S.add S.one S.one) S.id
  exact S.one

example : (fun n => n) ≺ (fun n => n^2) := by
  use 2
  intro n h
  refine lt_self_pow₀ h ?_
  norm_num

theorem eq_zero_of_fn_eq_zero {f n} (hf : S f) (h : f n = 0) : n = 0 := by
  induction hf with
  | one => simp at h
  | id => exact h
  | @add f g hf hg ih₁ ih₂ => simp at h; exact ih₁ h.1
  | @mul f g hf hg ih₁ ih₂ =>
    simp at h; rcases h with h | h; exact ih₁ h; exact ih₂ h
  | @exp f g hf hg ih₁ ih₂ => simp at h; exact ih₁ h.1

/-- Proofs of `le_exp₁`, `le_exp₂`, and `growth_prop` are by Vlad. -/

theorem le_exp₁ {a b : ℕ} (h : 2 ≤ b) : a ≤ b ^ a := by
  induction a; simp; rename_i a ha; simp [pow_succ]
  replace ha := Nat.add_le_add_right ha 1; apply ha.trans
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le h; simp [mul_add, mul_two]
  suffices 1 ≤ (2 + b) ^ a + (2 + b) ^ a * b by linarith
  by_contra h; simp at h

theorem le_exp₂ {a b : ℕ} (h : b ≠ 0) : a ≤ a ^ b := by
  cases b; simp at h; rename_i b; simp [pow_add]; cases a
  simp; rename_i a; cases b; simp; rename_i b
  simp [pow_add]; by_contra h₁; simp at h₁

theorem growth_prop (f : ℕ → ℕ) (h : S f) :
    (∃ k, ∀ n ≥ k, f n ≥ n) ∨ (∃ c, ∀ n, c ≠ 0 ∧ f n = c):= by
  suffices h₁ : (∃ c, ∀ (n : ℕ), f n = c + 1) ∨ ∃ k, ∀ n, k ≤ n → n ≤ f n by
    symm; rcases h₁ with ⟨c, h₁⟩ | h₁
    left; use c + 1; simpa; right; exact h₁
  induction h with
  | one => left; use 0; simp
  | id => right; use 0; simp
  | @add f g hf hg ih₁ ih₂ =>
    rcases ih₁ with ⟨c₁, hc₁⟩ | ⟨k₁, hk₁⟩
    · rcases ih₂ with ⟨c₂, hc₂⟩ | ⟨k₂, hk₂⟩
      · left; use c₁ + c₂ + 1; simp [hc₁, hc₂]; ring
      right; use k₂; intro n hn; specialize hk₂ n hn
      simp; linarith
    right; use k₁; intro n hn; specialize hk₁ n hn
    simp; linarith
  | @mul f g hf hg ih₁ ih₂ =>
    rcases ih₁ with ⟨c₁, hc₁⟩ | ⟨k₁, hk₁⟩
    · rcases ih₂ with ⟨c₂, hc₂⟩ | ⟨k₂, hk₂⟩
      · left; use (c₁ + 1) * (c₂ + 1) - 1;
        simp [hc₁, hc₂]; rfl
      right; use k₂; intro n hn; specialize hk₂ n hn
      simp [hc₁]; rw [add_comm, add_mul]; simp
      exact Nat.le_add_right_of_le hk₂
    right; use k₁; intro n hn; specialize hk₁ n hn
    simp; by_cases h₁ : g n = 0
    · have h₂ := eq_zero_of_fn_eq_zero hg h₁; simp [h₂]
    obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero h₁
    simp [hr, mul_add]; exact le_add_of_le_right hk₁
  | @exp f g hf hg ih₁ ih₂ =>
    rcases ih₁ with ⟨c₁, hc₁⟩ | ⟨k₁, hk₁⟩
    · rcases ih₂ with ⟨c₂, hc₂⟩ | ⟨k₂, hk₂⟩
      · left; use (c₁ + 1) ^ (c₂ + 1) - 1; simp [hc₁, hc₂]
        rw [Nat.sub_add_cancel]; apply Nat.one_le_pow'
      cases c₁; left; use 0; simp [hc₁]
      rename_i c₁; right; use k₂; intro n hn
      specialize hk₂ n hn; simp [hc₁]; apply hk₂.trans
      apply le_exp₁; linarith
    right; use k₁; intro n hn; specialize hk₁ n hn
    simp; by_cases h₁ : g n = 0
    · have h₂ := eq_zero_of_fn_eq_zero hg h₁; simp [h₂]
    obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero h₁
    simp [hr]; apply hk₁.trans; apply le_exp₂; simp

theorem growth_prop₁ (f : ℕ → ℕ) (hf₁ : S f) (hf₂ : f ≠ (fun _ => 1)) :
    (∃ c, ∀ n, c > 1 ∧ f n = c) ∨ (∃ k, ∀ n ≥ k, f n ≥ n) := by
  have := growth_prop f hf₁
  rcases this with ⟨k, hk⟩ | ⟨c, hc⟩
  · exact Or.inr ⟨k, hk⟩
  · have c_ne_zero : c ≠ 0 := by
      specialize hc 1
      exact hc.1
    have c_gt_one : c > 1 := by
      apply lt_of_le_of_ne (Nat.pos_of_ne_zero c_ne_zero)
      intro h_eq
      apply hf₂
      ext n
      have : f n = c := by
        specialize hc n
        exact hc.2
      rwa [h_eq]
    left
    use c
    intro n
    constructor
    exact c_gt_one
    specialize hc n
    exact hc.2

instance zero_not_in_S (f : ℕ → ℕ) (h : S f) : f ≠ (fun _ => 0) := by
  intro H
  rcases growth_prop with j
  specialize j f
  have j1 : (∃ k, ∀ n ≥ k, f n ≥ n) ∨ ∃ c, ∀ (n : ℕ), c ≠ 0 ∧ f n = c := by
    exact j h
  rcases j1 with j2|j2
  obtain ⟨k, hk⟩ := j2
  have j3 : f (k + 1) ≥ k + 1 := by
    have : k + 1 ≥ k := by omega
    exact hk (k + 1) this
  have j4 : f (k + 1) = 0 := by
    rw [H]
  omega
  obtain ⟨c, hc⟩ := j2
  specialize hc c
  have j5 : f c = c := by exact hc.2
  rw [H] at j5; simp at j5
  omega

class S_member (f : ℕ → ℕ) : Prop
  where is_in_S : S f

def S_segment (f : ℕ → ℕ) [S_member f] : Set (ℕ → ℕ) := {g | S g ∧ g ≺ f}

instance : S_member (fun _ => 1) := ⟨S.one⟩
instance : S_member (fun n => n) := ⟨S.id⟩

#check S_segment (fun n => n)

theorem non_id_at_zero_pos (f : ℕ → ℕ) (hf₁ : S f) (hf₂ : f ≺ (fun n => n)) : f 0 ≥ 1 := by
  rcases hf₂ with ⟨k, hk⟩
  have growth := growth_prop f hf₁
  rcases growth with ⟨m, hm⟩ | ⟨c, hc⟩
  · let n := max k m
    specialize hk n (le_max_left _ _)
    specialize hm n (le_max_right _ _)
    linarith
  · specialize hc 0
    rcases hc with ⟨hc_ne_zero, hc⟩
    rw [hc]
    exact Nat.pos_of_ne_zero hc_ne_zero

theorem const_in_S (f : ℕ → ℕ) (hf : ∃ c > 0, f = (fun _ => c)) : S f := by
  rcases hf with ⟨c, hc_pos, rfl⟩
  induction c using Nat.strong_induction_on with
  | h c ih =>
    match c with
    | 0 => exact (lt_irrefl 0 hc_pos).elim
    | 1 => exact S.one
    | c'+2 =>
      have : (fun n : ℕ => c'+2) = (fun n => 1) + (fun n => c'+1) := by
        ext n
        simp [Nat.succ_eq_add_one, add_comm]
        ring
      rw [this]
      refine S.add S.one (ih (c'+1) ?_ ?_)
      · omega
      · omega

/-- The segment determined by the identity function is exactly the set of positive natural numbers. -/

theorem id_segment_eq_nat : S_segment (fun n => n) = {g : ℕ → ℕ | ∃ c > 0, ∀ n, g n = c} := by
  ext g
  constructor
  intro ⟨hg, ⟨k, hk⟩⟩
  have : ∀ n ≥ k, g n < n := hk
  use g 0
  constructor
  have g_neq_zero : g ≠ (fun _ => 0) := by
    apply zero_not_in_S
    exact hg
  have g_neq_id : g ≠ (fun n => n) := by
    intro h_eq
    rw [h_eq] at hk
    specialize hk (max k 1) (le_max_left k 1)
    linarith
  apply non_id_at_zero_pos
  exact hg
  use k
  have H : (∃ k, ∀ n ≥ k, g n ≥ n) ∨ (∃ c, ∀ n, c ≠ 0 ∧ g n = c):= by
    apply growth_prop
    exact hg
  have not_case_one : ¬ (∃ k, ∀ n ≥ k, g n ≥ n) := by
    intro G
    obtain ⟨k', hk'⟩ := G
    let m := max k k'
    have G1 : g m < m := by
      specialize this m
      have : m ≥ k := by omega
      exact hk m this
    have G2 : g m ≥ m := by
      specialize hk' m
      have : m ≥ k' := by omega
      exact hk' this
    linarith
  have case_two : ∃ c, ∀ n, c ≠ 0 ∧ g n = c := by tauto
  obtain ⟨c, hc⟩ := case_two
  intro n
  have hc_copy : ∀ (n : ℕ), c ≠ 0 ∧ g n = c := hc
  specialize hc 0
  specialize hc_copy n
  have h_g_zero : g 0 = c := by exact hc.2
  have h_g_n : g n = c := by exact hc_copy.2
  omega
  rintro ⟨c, hc_pos, hc⟩
  constructor
  have hS : S g := by
    apply const_in_S
    use c
    constructor
    exact hc_pos
    exact (Set.eqOn_univ g fun n => c).mp fun ⦃x⦄ a => hc x
  exact hS
  use c + 1
  intro n hn
  rw [hc]
  exact hn


/-- f ∈ S is an additive prime if it cannot be written as g + h for g, h ∈ S. -/

def IsAdditivePrime (f : ℕ → ℕ) : Prop :=
  S f ∧ ∀ g h, S g → S h → f = g + h → False

/-- f ∈ S is a multiplicative prime if, for g, h ∈ S, f = g * h implies g = 1 or h = 1.  -/

def IsMultiplicativePrime (f : ℕ → ℕ) : Prop :=
  S f ∧ ∀ g h, S g → S h → f = g * h → (g = (fun _ => 1) ∨ h = (fun _ => 1))

/-- f ∈ S is a multiplicative prime if, for g, h ∈ S, f = g ^ h implies g = 1 or h = 1. -/

def IsExponentialPrime (f : ℕ → ℕ) : Prop :=
  S f ∧ ∀ g h, S g → S h → f = (fun n => g n ^ h n) →
    g = (fun _ => 1) ∨ h = (fun _ => 1)

/-- f ∈ S is a component if f is both an additive prime and a multiplicative prime. -/
def IsComponent (f : ℕ → ℕ) : Prop :=
  S f ∧ (IsAdditivePrime f ∧ IsMultiplicativePrime f)

/-- The constant function 1 is an additive prime. -/

theorem one_additive_prime : IsAdditivePrime (fun _ => 1) := by
  refine ⟨S.one, ?_⟩
  intro g h hg hh heq
  have H1 : g + h = 1 := by exact id (Eq.symm heq)
  have H2 : (∃ k, ∀ n ≥ k, g n ≥ n) ∨ (∃ c, ∀ n, c ≠ 0 ∧ g n = c) := by
    apply growth_prop
    exact hg
  have H3 : (∃ k, ∀ n ≥ k, h n ≥ n) ∨ (∃ c, ∀ n, c ≠ 0 ∧ h n = c) := by
    apply growth_prop
    exact hh
  rcases H2 with H4|H4
  rcases H3 with H5|H5
  obtain ⟨k₀, hk₀⟩ := H4
  obtain ⟨k₁, hk₁⟩ := H5
  let m₀ := max k₀ k₁
  let n := m₀ + 1
  have h_g_ge_n : g n ≥ n := by
    specialize hk₀ n
    have : n ≥ k₀ := by
      refine Nat.le_add_right_of_le ?_
      exact Nat.le_max_left k₀ k₁
    exact hk₀ this
  have h_h_ge_n : h n ≥ n := by
    specialize hk₁ n
    have : n ≥ k₁ := by
      refine Nat.le_add_right_of_le ?_
      exact Nat.le_max_right k₀ k₁
    exact hk₁ this
  have h_g_add_h_ge_two_n : g n + h n ≥  2 * n := by linarith
  have h_g_add_h_eq_one : (g + h) n = 1 := by
    rw [←heq]
  have : (g + h) n = g n + h n := by exact rfl
  omega
  obtain ⟨k, hk⟩ := H4
  obtain ⟨c, hc⟩ := H5
  have hk_copy : ∀ n ≥ k, g n ≥ n := hk
  specialize hk k
  have h_g_ge_k : g k ≥ k := by omega
  specialize hc k
  have h_h_eq_c : h k = c := by exact hc.2
  have h_g_add_h_eq_one : (g + h) k = 1 := by
    rw [←heq]
  have : (g + h) k = g k + h k := by exact rfl
  rw [h_g_add_h_eq_one, h_h_eq_c] at this
  have ineq_one : 1 ≥ k + c := by linarith
  have ineq_two : 1 ≥ k + 1 := by
    have : c ≠ 0 := by exact hc.1
    omega
  have k_eq_zero : k = 0 := by omega
  rw [k_eq_zero] at hk_copy
  have h_g_two : g 2 ≥ 2 := by
    specialize hk_copy 2
    tauto
  have : (g + h) 2 = 1 := by rw [←heq]
  have : g 2 + h 2 = 1 := by exact this
  have : 1 ≥ 2 := by linarith
  omega
  rcases H3 with H5|H5
  obtain ⟨c, hc⟩ := H4
  obtain ⟨k, hk⟩ := H5
  have hk_copy : ∀ n ≥ k, h n ≥ n := hk
  specialize hk k
  have h_g_ge_k : h k ≥ k := by omega
  specialize hc k
  have h_h_eq_c : g k = c := by exact hc.2
  have h_g_add_h_eq_one : (g + h) k = 1 := by
    rw [←heq]
  have : (g + h) k = g k + h k := by exact rfl
  rw [h_g_add_h_eq_one, h_h_eq_c] at this
  have ineq_one : 1 ≥ k + c := by linarith
  have ineq_two : 1 ≥ k + 1 := by
    have : c ≠ 0 := by exact hc.1
    omega
  have k_eq_zero : k = 0 := by omega
  rw [k_eq_zero] at hk_copy
  have h_g_two : h 2 ≥ 2 := by
    specialize hk_copy 2
    tauto
  have : (g + h) 2 = 1 := by rw [←heq]
  have : g 2 + h 2 = 1 := by exact this
  have : 1 ≥ 2 := by linarith
  omega
  obtain ⟨c₁, hc₁⟩ := H4
  obtain ⟨c₂, hc₂⟩ := H5
  specialize hc₁ 1
  specialize hc₂ 1
  have h_g_one : g 1 = c₁ := by exact hc₁.2
  have h_h_one : h 1 = c₂ := by exact hc₂.2
  have : (g + h) 1 = 1 := by rw [←heq]
  have : g 1 + h 1 = 1 := by exact this
  have : c₁ ≥ 1 := by
    have : c₁ ≠ 0 := by exact hc₁.1
    omega
  have : c₂ ≥ 1 := by
    have : c₂ ≠ 0 := by exact hc₂.1
    omega
  omega

/-- The identity function is an additive prime. -/

theorem id_additive_prime : IsAdditivePrime (fun n => n) := by
  refine ⟨S.id, ?_⟩
  intro g h hg hh heq
  have H1 : (∃ k, ∀ n ≥ k, g n ≥ n) ∨ (∃ c, ∀ n, c ≠ 0 ∧ g n = c) := by
    apply growth_prop
    exact hg
  have H2 : (∃ k, ∀ n ≥ k, h n ≥ n) ∨ (∃ c, ∀ n, c ≠ 0 ∧ h n = c) := by
    apply growth_prop
    exact hh
  rcases H1 with H3 | H3
  rcases H2 with H4 | H4
  obtain ⟨k₁, hk₁⟩ := H3
  obtain ⟨k₂, hk₂⟩ := H4
  let n := max k₁ k₂ + 1
  have h_g_n : g n ≥ n := by
    specialize hk₁ n
    have : n ≥ k₁ := by omega
    omega
  have h_h_n : h n ≥ n := by
    specialize hk₂ n
    have : n ≥ k₂ := by omega
    omega
  have h_plus_g_n : g n + h n = n := by
    have : (g + h) n = n := by
      rw [←heq]
    exact this
  have contr : n ≥ 2 * n := by linarith
  omega
  obtain ⟨k, hk⟩ := H3
  obtain ⟨c, hc⟩ := H4
  have h_g_k : g k ≥ k := by
    specialize hk k
    omega
  have h_h_k : h k = c := by
    specialize hc k
    exact hc.2
  have h_plus_g_n : g k + h k = k := by
    have : (g + h) k = k := by
      rw [←heq]
    exact this
  have c_pos : c > 0 := by
    have : c ≠ 0 := by
      specialize hc k
      exact hc.1
    omega
  omega
  rcases H2 with H4 | H4
  obtain ⟨c, hc⟩ := H3
  obtain ⟨k, hk⟩ := H4
  let n := max k 1
  have h_g_n : h n ≥ n := by
    specialize hk n
    omega
  have h_g_n : g n = c := by
    specialize hc n
    omega
  have h_plus_g_n : g n + h n = n := by
    have : (g + h) n = n := by
      rw [←heq]
    exact this
  have contr : n ≥ n + c := by linarith
  have c_pos : c > 0 := by
    specialize hc n
    have : c ≠ 0 := by exact hc.1
    omega
  omega
  obtain ⟨c₁, hc₁⟩ := H3
  obtain ⟨c₂, hc₂⟩ := H4
  have h_g_c : g c₁ = c₁ := by
    specialize hc₁ c₁
    exact hc₁.2
  have h_h_c : h c₁ = c₂ := by
    specialize hc₂ c₁
    exact  hc₂.2
  have h_plus_g_c₁ : g c₁ + h c₁ = c₁ := by
    have : (g + h) c₁ = c₁ := by
      rw [←heq]
    exact this
  rw [h_g_c, h_h_c] at h_plus_g_c₁
  have c₂_eq_zero : c₂ = 0 := by omega
  have c₂_pos : c₂ ≠ 0 := by
    specialize hc₂ c₂
    exact hc₂.1
  omega


/-- The constant function 1 is a multiplicative prime-/

theorem one_multiplicative_prime : IsMultiplicativePrime (fun _ => 1) := by
  refine ⟨S.one, ?_⟩
  intro g h hg hh heq
  by_contra G
  push_neg at G
  have h_g_neq_one : g ≠ (fun x => 1) := by
    exact G.1
  have h_g_witness : ∃ k, g k ≠ 1 := by exact ne_iff.mp h_g_neq_one
  obtain ⟨k, hk⟩ := h_g_witness
  have mul_k : g k * h k = 1 := by
    have : (g * h) k = 1 := by exact congrFun (id (Eq.symm heq)) k
    exact this
  have : g k = 1 := by exact Nat.eq_one_of_mul_eq_one_right mul_k
  contradiction


/-- The identity function is a multiplicative prime. -/

theorem id_multiplicative_prime : IsMultiplicativePrime (fun n => n) := by
  refine ⟨S.id, ?_⟩
  intro g h hg hh heq
  by_contra G
  push_neg at G
  have h_g_neq_one : g ≠ (fun x => 1) := by exact G.1
  have h_h_neq_one : h ≠ (fun x => 1) := by exact G.2
  have g_growth := growth_prop₁ g hg
  have h_growth := growth_prop₁ h hh
  have g_growth₁ : (∃ c, ∀ (n : ℕ), c > 1 ∧ g n = c) ∨ ∃ k, ∀ n ≥ k, g n ≥ n := by
    exact g_growth h_g_neq_one
  have h_growth₁ : (∃ c, ∀ (n : ℕ), c > 1 ∧ h n = c) ∨ ∃ k, ∀ n ≥ k, h n ≥ n := by
    exact h_growth h_h_neq_one
  rcases g_growth₁ with ⟨k₁, hk₁⟩ | ⟨c₁, hc₁⟩ <;>
  rcases h_growth₁ with ⟨k₂, hk₂⟩ | ⟨c₂, hc₂⟩
  · have h_g_one : g 1 = k₁ := by
      specialize hk₁ 1
      exact hk₁.2
    have h_h_one : h 1 = k₂ := by
      specialize hk₂ 1
      exact hk₂.2
    have mul_eq_one : k₁ * k₂ = 1 := by
      have : g 1 * h 1 = 1 := by
        have : (g * h) 1 = 1 := by
          rw [← heq]
        exact this
      rwa [h_g_one, h_h_one] at this
    have : k₁ = 1 := by exact Nat.eq_one_of_mul_eq_one_right mul_eq_one
    have : k₁ > 1 := by
      specialize hk₁ 1
      exact hk₁.1
    omega
  · let m := max c₂ 1
    have h_m : h m ≥ m := by
      specialize hc₂ m
      omega
    specialize hk₁ m
    have mul_geq : 1 ≥ k₁ := by
      have : g m * h m = m := by
        have : (g * h) m = m := by
          rw [←heq]
        exact this
      have h1 : g m = k₁ := by exact hk₁.2
      rw [h1] at this
      have h1 : m ≥ k₁ * m := by
        calc
          m = k₁ * h m  := by rw [this]
          _ ≥ k₁ * m    := by gcongr
      have : m > 0 := by omega
      exact (mul_le_iff_le_one_left this).mp h1
    have : k₁ > 1 := by exact hk₁.1
    omega
  · let m := max c₁ 1
    have g_m : g m ≥ m := by
      specialize hc₁ m
      omega
    specialize hk₂ m
    have mul_geq : 1 ≥ k₂ := by
      have : g m * h m = m := by
        have : (g * h) m = m := by
          rw [←heq]
        exact this
      have h1 : h m = k₂ := by exact hk₂.2
      rw [h1] at this
      have h1 : m ≥ k₂ * m := by
        calc
          m = k₂ * g m   := by
            rw [mul_comm, this]
          _ ≥ k₂ * m     := by gcongr
      have : m > 0 := by omega
      exact (mul_le_iff_le_one_left this).mp h1
    have : k₂ > 1 := by exact hk₂.1
    omega
  · let k := max (max c₁ c₂) 2
    specialize hc₁ k
    specialize hc₂ k
    have h1 : g k ≥ k := by omega
    have h2 : h k ≥ k := by omega
    have h_mul : g k * h k = k := by
      have : (g * h) k = k := by rw [← heq]
      exact this
    have : k ≥ k * k := by
      have : g k * h k ≥ k * k := by exact Nat.mul_le_mul h1 h2
      linarith
    have : k < k * k := by
      refine (Nat.lt_mul_iff_one_lt_right ?_).mpr ?_
      omega
      refine Nat.one_lt_iff_ne_zero_and_ne_one.mpr ?_
      omega
    omega

/-- The constant function fun _ => 1 is a component. -/

theorem one_component : IsComponent (fun _ => 1) := by
  unfold IsComponent
  constructor
  exact S.one
  exact ⟨one_additive_prime, one_multiplicative_prime⟩

/-- The identity function is a component. -/

theorem id_component : IsComponent (fun n => n) := by
  unfold IsComponent
  constructor
  exact S.id
  exact ⟨id_additive_prime, id_multiplicative_prime⟩

theorem pow_component_form (f g h: ℕ → ℕ) (hf : S f) (hg : S g) (hh : h = (fun n => f n ^ (g n))) (hhh : h ≠ (fun _ => 1))
  (hcomp : IsComponent h) : IsMultiplicativePrime f ∧ IsAdditivePrime g := by
    by_contra G
    have contr : ¬ IsMultiplicativePrime f ∨ ¬ IsAdditivePrime g := by tauto
    rcases contr with G1|G1
    obtain ⟨hS, h_add_prime, h_mul_prime⟩ := hcomp
    rw [IsMultiplicativePrime] at G1
    push_neg at G1
    have : ∃ g h, S g ∧ S h ∧ f = g * h ∧ (g ≠ fun x => 1) ∧ h ≠ fun x => 1 := by
      apply G1
      exact hf
    obtain ⟨f₁, f₂, hf₁, hf₂, heqf, hf1_ne, hf2_ne⟩ := this
    rw [heqf] at hh
    have hh1 : h = fun n => f₁ n ^ g n  * f₂ n ^ g n := by
      ext n
      have : h n = (f₁ n * f₂ n) ^ g n := by exact congrFun hh n
      rwa [←Nat.mul_pow]
    let k₁ := fun n => f₁ n ^ g n
    let k₂ := fun n => f₂ n ^ g n
    have hk₁ : S k₁ := by apply S.exp hf₁ hg
    have hk₂ : S k₂ := by apply S.exp hf₂ hg
    have G2 : k₁ = 1 ∨ k₂ = 1 := by
      have h_decomp : h = k₁ * k₂ := hh1
      exact h_mul_prime.2 k₁ k₂ hk₁ hk₂ h_decomp
    rcases G2 with G3|G3
    have G4 : (∃ k, ∀ n ≥ k, g n ≥ n) ∨ (∃ c, ∀ n, c ≠ 0 ∧ g n = c):= by
      apply growth_prop
      exact hg
    have G5 : (∃ c, ∀ n, c > 1 ∧ f₁ n = c) ∨ (∃ k, ∀ n ≥ k, f₁ n ≥ n) := by
      apply growth_prop₁
      exact hf₁
      exact hf1_ne
    rcases G4 with G6|G6 <;>
    rcases G5 with G7|G7
    obtain ⟨c, hc⟩ := G7
    have f₁_const : ∀ n, f₁ n = c := by
      intro n
      specialize hc n
      exact hc.2
    have c_gt_one : c > 1 := by
      specialize hc 1
      exact hc.1
    have k₁_one : ∀ n, f₁ n ^ g n = 1 := by
      intro n
      have k₁_eq_one : k₁ = (fun _ => 1) := G3
      have f₁_pow_g_eq_one : ∀ n, f₁ n ^ g n = 1 := by
        intro n
        exact congrFun k₁_eq_one n
      exact f₁_pow_g_eq_one n
    obtain ⟨k, hk⟩ := G6
    have : g (k + 1) ≥ 1 := by
      specialize hk (k + 1)
      omega
    have at_one : f₁ (k + 1) ^ g (k + 1) = 1 := k₁_one (k + 1)
    rw [f₁_const] at at_one
    have : c ^ g (k + 1) > 1 := by
      refine Nat.one_lt_pow ?_ c_gt_one
      omega
    linarith
    obtain ⟨m₁, hm₁⟩ := G6
    obtain ⟨m₂, hm₂⟩ := G7
    let m₃ := max m₁ m₂ + 2
    specialize hm₁ m₃ (by omega)
    specialize hm₂ m₃ (by omega)
    have pow_eq_one : ∀ n, f₁ n ^ g n = 1 := by
      rw [G3] at hk₁
      intro n
      have k₁_is_one : k₁ = (fun _ => 1) := G3
      have k₁_def : ∀ n, k₁ n = f₁ n ^ g n := by exact fun n => rfl
      have pow_eq_one : ∀ n, f₁ n ^ g n = 1 := by
        intro n
        rw [←k₁_def, k₁_is_one]
      exact pow_eq_one n
    have at_m₃ : f₁ m₃ ^ g m₃ = 1 := pow_eq_one m₃
    have f1_ge_two : f₁ m₃ ≥ 2 := by
      have : m₃ ≥ 2 := Nat.le_add_left 2 (max m₁ m₂)
      exact Nat.le_trans this hm₂
    have g_ge_two : g m₃ ≥ 2 := by
      have : m₃ ≥ 2 := Nat.le_add_left 2 (max m₁ m₂)
      exact Nat.le_trans this hm₁
    have pow_gt_one : f₁ m₃ ^ g m₃ ≥ 2 ^ 2 := by
      calc
          f₁ m₃ ^ g m₃ ≥ 2 ^ g m₃ := by exact Nat.pow_le_pow_left f1_ge_two (g m₃)
            _ ≥ 2 ^ 2             := Nat.pow_le_pow_right (by linarith) g_ge_two
            _ = 4                 := by norm_num
    have : f₁ m₃ ^ g m₃ ≥ 4 := pow_gt_one
    linarith
    obtain ⟨c₁, hc₁⟩ := G7
    have f₁_const : ∀ n, f₁ n = c₁ := fun n => (hc₁ n).2
    have c₁_gt_one : c₁ > 1 := (hc₁ 0).1
    obtain ⟨c₂, hc₂⟩ := G6
    have g_const : ∀ n, g n = c₂ := fun n => (hc₂ n).2
    have c₂_ne_zero : c₂ ≠ 0 := (hc₂ 0).1
    have k₁_eq_one : ∀ n, f₁ n ^ g n = 1 := by
      rw [G3] at hk₁
      intro n
      have k₁_is_one : k₁ = (fun _ => 1) := G3
      have k₁_def : ∀ n, k₁ n = f₁ n ^ g n := by exact fun n => rfl
      have pow_eq_one : ∀ n, f₁ n ^ g n = 1 := by
        intro n
        rw [←k₁_def, k₁_is_one]
      exact pow_eq_one n
    have at_zero : f₁ 0 ^ g 0 = 1 := k₁_eq_one 0
    rw [f₁_const, g_const] at at_zero
    have pow_eq_one : c₁ ^ c₂ = 1 := at_zero
    have c₂_zero : c₂ = 0 := by
      aesop
    exact c₂_ne_zero c₂_zero
    obtain ⟨c, hc⟩ := G6
    have g_const : ∀ n, g n = c := fun n => (hc n).2
    have c_ne_zero : c ≠ 0 := (hc 0).1
    have k₁_eq_one : ∀ n, f₁ n ^ g n = 1 := by
      rw [G3] at hk₁
      intro n
      have k₁_is_one : k₁ = (fun _ => 1) := G3
      have k₁_def : ∀ n, k₁ n = f₁ n ^ g n := by exact fun n => rfl
      have pow_eq_one : ∀ n, f₁ n ^ g n = 1 := by
        intro n
        rw [←k₁_def, k₁_is_one]
      exact pow_eq_one n
    obtain ⟨k, hk⟩ := G7
    let n := max k (c + 1)
    have f1_ge_n : f₁ n ≥ n := hk n (le_max_left _ _)
    have n_ge_c1 : n ≥ c + 1 := le_max_right _ _
    have pow_eq_one : f₁ n ^ c = 1 := by rw [← g_const, k₁_eq_one]
    have f1_ge_two : f₁ n ≥ 2 := by omega
    have c_zero : c = 0 := by aesop
    exact c_ne_zero c_zero
    have G4 : (∃ k, ∀ n ≥ k, g n ≥ n) ∨ (∃ c, ∀ n, c ≠ 0 ∧ g n = c):= by
      apply growth_prop
      exact hg
    have G5 : (∃ c, ∀ n, c > 1 ∧ f₁ n = c) ∨ (∃ k, ∀ n ≥ k, f₁ n ≥ n) := by
      apply growth_prop₁
      exact hf₁
      exact hf1_ne
    have G5 : (∃ c, ∀ n, c > 1 ∧ f₂ n = c) ∨ (∃ k, ∀ n ≥ k, f₂ n ≥ n) := by
      apply growth_prop₁
      exact hf₂
      exact hf2_ne
    rcases G4 with G6|G6 <;>
    rcases G5 with G7|G7
    obtain ⟨c, hc⟩ := G7
    have f₂_const : ∀ n, f₂ n = c := by
      intro n
      specialize hc n
      exact hc.2
    have c_gt_one : c > 1 := by
      specialize hc 1
      exact hc.1
    have k₂_one : ∀ n, f₂ n ^ g n = 1 := by
      rw [G3] at hk₂
      intro n
      have k₂_is_one : k₂ = (fun _ => 1) := G3
      have k₂_def : ∀ n, k₂ n = f₂ n ^ g n := by exact fun n => rfl
      have pow_eq_one : ∀ n, f₂ n ^ g n = 1 := by
        intro n
        rw [←k₂_def, k₂_is_one]
      exact pow_eq_one n
    obtain ⟨k, hk⟩ := G6
    have : g (k + 1) ≥ 1 := by
      specialize hk (k + 1)
      omega
    have at_one : f₂ (k + 1) ^ g (k + 1) = 1 := k₂_one (k + 1)
    rw [f₂_const] at at_one
    have : c ^ g (k + 1) > 1 := by
      refine Nat.one_lt_pow ?_ c_gt_one
      omega
    linarith
    obtain ⟨m₁, hm₁⟩ := G6
    obtain ⟨m₂, hm₂⟩ := G7
    let m₃ := max m₁ m₂ + 2
    specialize hm₁ m₃ (by omega)
    specialize hm₂ m₃ (by omega)
    have pow_eq_one : ∀ n, f₂ n ^ g n = 1 := by
      rw [G3] at hk₂
      intro n
      have k₂_is_one : k₂ = (fun _ => 1) := G3
      have k₂_def : ∀ n, k₂ n = f₂ n ^ g n := by exact fun n => rfl
      have pow_eq_one : ∀ n, f₂ n ^ g n = 1 := by
        intro n
        rw [←k₂_def, k₂_is_one]
      exact pow_eq_one n
    have at_m₃ : f₂ m₃ ^ g m₃ = 1 := pow_eq_one m₃
    have f1_ge_two : f₂ m₃ ≥ 2 := by
      have : m₃ ≥ 2 := Nat.le_add_left 2 (max m₁ m₂)
      exact Nat.le_trans this hm₂
    have g_ge_two : g m₃ ≥ 2 := by
      have : m₃ ≥ 2 := Nat.le_add_left 2 (max m₁ m₂)
      exact Nat.le_trans this hm₁
    have pow_gt_one : f₂ m₃ ^ g m₃ ≥ 2 ^ 2 := by
      calc
          f₂ m₃ ^ g m₃ ≥ 2 ^ g m₃ := by exact Nat.pow_le_pow_left f1_ge_two (g m₃)
            _ ≥ 2 ^ 2             := Nat.pow_le_pow_right (by linarith) g_ge_two
            _ = 4                 := by norm_num
    have : f₂ m₃ ^ g m₃ ≥ 4 := pow_gt_one
    linarith
    obtain ⟨c₁, hc₁⟩ := G7
    have f₁_const : ∀ n, f₂ n = c₁ := fun n => (hc₁ n).2
    have c₁_gt_one : c₁ > 1 := (hc₁ 0).1
    obtain ⟨c₂, hc₂⟩ := G6
    have g_const : ∀ n, g n = c₂ := fun n => (hc₂ n).2
    have c₂_ne_zero : c₂ ≠ 0 := (hc₂ 0).1
    have k₂_eq_one : ∀ n, f₂ n ^ g n = 1 := by
      rw [G3] at hk₂
      intro n
      have k₂_is_one : k₂ = (fun _ => 1) := G3
      have k₂_def : ∀ n, k₂ n = f₂ n ^ g n := by exact fun n => rfl
      have pow_eq_one : ∀ n, f₂ n ^ g n = 1 := by
        intro n
        rw [←k₂_def, k₂_is_one]
      exact pow_eq_one n
    have at_zero : f₂ 0 ^ g 0 = 1 := k₂_eq_one 0
    rw [f₁_const, g_const] at at_zero
    have pow_eq_one : c₁ ^ c₂ = 1 := at_zero
    have c₂_zero : c₂ = 0 := by
      aesop
    exact c₂_ne_zero c₂_zero
    obtain ⟨c, hc⟩ := G6
    have g_const : ∀ n, g n = c := fun n => (hc n).2
    have c_ne_zero : c ≠ 0 := (hc 0).1
    have k₁_eq_one : ∀ n, f₂ n ^ g n = 1 := by
      rw [G3] at hk₂
      intro n
      have k₂_is_one : k₂ = (fun _ => 1) := G3
      have k₂_def : ∀ n, k₂ n = f₂ n ^ g n := by exact fun n => rfl
      have pow_eq_one : ∀ n, f₂ n ^ g n = 1 := by
        intro n
        rw [←k₂_def, k₂_is_one]
      exact pow_eq_one n
    obtain ⟨k, hk⟩ := G7
    let n := max k (c + 1)
    have f1_ge_n : f₂ n ≥ n := hk n (le_max_left _ _)
    have n_ge_c1 : n ≥ c + 1 := le_max_right _ _
    have pow_eq_one : f₂ n ^ c = 1 := by rw [← g_const, k₁_eq_one]
    have f1_ge_two : f₂ n ≥ 2 := by omega
    have c_zero : c = 0 := by aesop
    exact c_ne_zero c_zero
    rw [IsAdditivePrime] at G1
    push_neg at G1
    have G2 : ∃ g_1 h, S g_1 ∧ S h ∧ g = g_1 + h ∧ ¬False := by aesop
    simp at G2
    obtain ⟨g₁, hg₁, g₂, hg₂, hg_sum⟩ := G2
    let k₁ := fun n => f n ^ g₁ n
    let k₂ := fun n => f n ^ g₂ n
    have hk₁ : S k₁ := by apply S.exp hf hg₁
    have hk₂ : S k₂ := by apply S.exp hf hg₂
    have h_mul_prime := hcomp.2.2
    have h_decomp : h = k₁ * k₂ := by
      ext n
      rw [hh]
      simp only [hg_sum, Pi.add_apply, Nat.pow_add]
      dsimp
    have mul_prime_prop : k₁ = (fun _ => 1) ∨ k₂ = (fun _ => 1) := by
      have h_mul_prime_def := h_mul_prime.2
      apply h_mul_prime_def k₁ k₂ _ _ h_decomp
      · exact hk₁
      · exact hk₂
    rcases mul_prime_prop with H1|H1
    have h_eq_one : h = (fun _ => 1) := by
      have : (fun n => f n ^ g₁ n) = 1 := by exact H1
      have : (fun n => f n) = 1 ∨ (fun n => g₁ n) = 0 := by
        have h_pow_one : ∀ n, f n ^ g₁ n = 1 := by rwa [funext_iff] at this
        left
        have : (∃ k, ∀ n ≥ k, g₁ n ≥ n) ∨ (∃ c, ∀ n, c ≠ 0 ∧ g₁ n = c):= by
          apply growth_prop
          exact hg₁
        rcases this with J1|J1
        by_contra J2
        push_neg at J2
        have : (∃ c, ∀ n, c > 1 ∧ f n = c) ∨ (∃ k, ∀ n ≥ k, f n ≥ n) := by
          apply growth_prop₁
          exact hf
          exact J2
        rcases this with J3|J3
        obtain ⟨k, hk⟩ := J1
        obtain ⟨c, hc⟩ := J3
        let k₀ := max k 2
        specialize h_pow_one k₀
        specialize hk k₀ (by omega)
        specialize hc k₀
        have hc1 : f k₀ = c := by exact hc.2
        rw [hc1] at h_pow_one
        aesop
        obtain ⟨k1, hk1⟩ := J1
        obtain ⟨k2, hk2⟩ := J3
        let k₀ := max k1 k2 + 2
        specialize hk1 k₀ (by omega)
        specialize hk2 k₀ (by omega)
        specialize h_pow_one k₀
        aesop
        obtain ⟨c, hc⟩ := J1
        ext n
        simp
        specialize h_pow_one n
        specialize hc n
        have : g₁ n = c := by exact hc.2
        rw [this] at h_pow_one
        have c_neq_zero : c ≠ 0 := by exact hc.1
        exact (pow_eq_one_iff c_neq_zero).mp h_pow_one
      have : (fun n => g₁ n) ≠ 0 := by
        apply zero_not_in_S
        exact hg₁
      have : (fun n => f n) = 1 := by tauto
      have : h = (fun _ => 1) := by
        ext n
        have hf_one : ∀ n, f n = 1 := by rwa [funext_iff] at this
        rw [hh]
        simp only [Nat.one_pow]
        specialize hf_one n
        rw [hf_one]
        simp
      contradiction
    contradiction
    have h_eq_one : h = (fun _ => 1) := by
      have : (fun n => f n ^ g₂ n) = 1 := by exact H1
      have : (fun n => f n) = 1 ∨ (fun n => g₁ n) = 0 := by
        have h_pow_one : ∀ n, f n ^ g₂ n = 1 := by rwa [funext_iff] at this
        left
        have : (∃ k, ∀ n ≥ k, g₂ n ≥ n) ∨ (∃ c, ∀ n, c ≠ 0 ∧ g₂ n = c):= by
          apply growth_prop
          exact hg₂
        rcases this with J1|J1
        by_contra J2
        push_neg at J2
        have : (∃ c, ∀ n, c > 1 ∧ f n = c) ∨ (∃ k, ∀ n ≥ k, f n ≥ n) := by
          apply growth_prop₁
          exact hf
          exact J2
        rcases this with J3|J3
        obtain ⟨k, hk⟩ := J1
        obtain ⟨c, hc⟩ := J3
        let k₀ := max k 2
        specialize h_pow_one k₀
        specialize hk k₀ (by omega)
        specialize hc k₀
        have hc1 : f k₀ = c := by exact hc.2
        rw [hc1] at h_pow_one
        aesop
        obtain ⟨k1, hk1⟩ := J1
        obtain ⟨k2, hk2⟩ := J3
        let k₀ := max k1 k2 + 2
        specialize hk1 k₀ (by omega)
        specialize hk2 k₀ (by omega)
        specialize h_pow_one k₀
        aesop
        obtain ⟨c, hc⟩ := J1
        ext n
        simp
        specialize h_pow_one n
        specialize hc n
        have : g₂ n = c := by exact hc.2
        rw [this] at h_pow_one
        have c_neq_zero : c ≠ 0 := by exact hc.1
        exact (pow_eq_one_iff c_neq_zero).mp h_pow_one
      have : (fun n => g₁ n) ≠ 0 := by
        apply zero_not_in_S
        exact hg₁
      have : (fun n => f n) = 1 := by tauto
      have : h = (fun _ => 1) := by
        ext n
        have hf_one : ∀ n, f n = 1 := by rwa [funext_iff] at this
        rw [hh]
        simp only [Nat.one_pow]
        specialize hf_one n
        rw [hf_one]
        simp
      contradiction
    contradiction
